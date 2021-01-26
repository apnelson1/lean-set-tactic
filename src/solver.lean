import extensionality
import boolean_algebra_tactic
import finset_tactic
import tactic
import tactic.interactive

open boolean_algebra_extensionality


/-meta def simpl_tactic : tactic unit :=
`[simp only [simpl_sdiff, simpl_eq, ext_le, ext_bot, ext_top, ext_meet, ext_join, ext_compl] at *; tauto!]-/

meta def boolean_algebra_types_in_expr : expr → tactic (list expr)
| e :=
  match e with
  -- This mostly handles basic expressions 
  | expr.local_const unique pretty _ _ :=
    do
      ((do
        `(%%boolalg_typ) <- tactic.infer_type e,
        match boolalg_typ with 
        -- finset T gets returned directly 
        | `(finset %%set_typ) := do return [boolalg_typ]
        -- set T gets returne directly
        | `(set %%set_typ) := do return [boolalg_typ]
        -- work needs to be done if we're not working with sets/finsets,
        -- but with a type with a [boolean_algebra T] instance on it.
        | _ := (do 
          boolalg_hyp <- tactic.to_expr ``(infer_instance : boolean_algebra %%boolalg_typ),
          return [boolalg_typ])
        end)
      <|>
        return [])
  -- applications
  | expr.app e1 e2 := 
    do l1 <- boolean_algebra_types_in_expr e1, 
       l2 <- boolean_algebra_types_in_expr e2,
       return (l1 ++ l2)
  -- abstracts
  | expr.lam _ _ argtyp body :=
    do l1 <- boolean_algebra_types_in_expr argtyp, 
      l2 <- boolean_algebra_types_in_expr body,
      return (l1 ++ l2)
  | expr.pi _ _ argtyp body :=
    do l1 <- boolean_algebra_types_in_expr argtyp, 
      l2 <- boolean_algebra_types_in_expr body,
      return (l1 ++ l2)
  | _ := return []
  end

def unique_list {T: Type}[decidable_eq T]: list T -> list T 
| [] := []
| (x :: xs) := let tl := unique_list xs in
                if list.mem x tl then tl else x :: tl
 
meta def rewrite_for_type (type : expr) : (tactic unit) := do
  name <- tactic.get_unused_name `_instrw,
  instance_type <- tactic.to_expr ``(boolean_algebra_extensionality %%type _),
  expr <- tactic.to_expr ``(by apply_instance : %%instance_type),
  tactic.trace instance_type,
  new_hyp <- tactic.assertv name instance_type expr,
  (tactic.interactive.simp none tt 
              ([``((%%new_hyp).simpl_eq),
                ``((%%new_hyp).ext_le),
                ``((%%new_hyp).ext_bot),
                ``((%%new_hyp).ext_sdiff),
                ``((%%new_hyp).ext_top),
                ``((%%new_hyp).ext_meet),
                ``((%%new_hyp).ext_join),
                ``((%%new_hyp).ext_compl)].map tactic.simp_arg_type.expr)
                  list.nil interactive.loc.wildcard),
  tactic.skip

example (α : Type) [boolean_algebra α] (X Y Z P Q W : α) :
  (X ⊔ (Y ⊔ Z)) ⊔ ((W ⊓ P ⊓ Q)ᶜ ⊔ (P ⊔ W ⊔ Q)) = ⊤ :=
begin
  (do
    goal <- tactic.target,
    types <- boolean_algebra_types_in_expr goal,
    tactic.trace (unique_list types),
    rewrite_for_type (list.head types),
    tactic.skip),
  tauto!,
end

example (T : Type) [fintype T] [decidable_eq T] (X Y Z P Q W : finset T)  :
  (X ⊔ (Y ⊔ Z)) ⊔ ((W ⊓ P ⊓ Q)ᶜ ⊔ (P ⊔ W ⊔ Q)) = ⊤ :=
begin
  (do
    goal <- tactic.target,
    types <- boolean_algebra_types_in_expr goal,
    tactic.trace (unique_list types),
    rewrite_for_type (list.head types),
    tactic.skip),  
    tauto,
end

example (α : Type) [boolean_algebra α]  (A B C D E F G : α) :
  A ≤ B →
  B ≤ C →
  C ≤ D ⊓ E →
  D ≤ Fᶜ →
  (A ⊓ F = ⊥) :=
begin
  (do
    goal <- tactic.target,
    types <- boolean_algebra_types_in_expr goal,
    tactic.trace (unique_list types),
    rewrite_for_type (list.head types),
    tactic.skip), 
  intros,
  split; intro u,
  tauto!, 
end 
/-
example (X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ X₈ X₉ : α) :
  (X₀ ⊔ X₁ ⊔ (X₂ ⊓ X₃) ⊔ X₄ ⊔ X₅ ⊔ (X₆ ⊓ X₇ ⊓ X₈) ⊔ X₉)ᶜ
    ≤ (X₉ᶜ ⊓ ((X₆ᶜ ⊔ ⊥) ⊔ X₈ᶜ ⊔ X₇ᶜᶜᶜ) ⊓ X₅ᶜ ⊓ (X₀ᶜ \ X₁) ⊓ (X₃ᶜ ⊔ X₂ᶜ) ⊓ X₄ᶜ) :=
by tactic.timetac "big" $ boolean_algebra_tactic

example (A B C D E F G : α) :
  A ≤ B →
  B ≤ C →
  C ≤ D ⊓ E →
  A ≤ E :=
begin
  simp only [rw_sdiff, rw_eq, rw_le, rw_bot, rw_top, rw_sup, rw_inf, rw_compl] at *,
  intros H1 H2 H3 u H4,
  specialize (H1 u),
  specialize (H2 u),
  specialize (H3 u),
  tauto!
end

example (A B C D E F G : α) :
  A ≤ B →
  B ≤ C →
  C ≤ D ⊓ E →
  D ≤ Fᶜ →
  (A ⊓ F = ⊥) :=
begin
  simp only [rw_sdiff, rw_eq, rw_le, rw_bot, rw_top, rw_sup, rw_inf, rw_compl] at *,
  intros H1 H2 H3 H4,
  split;
  intro u, specialize (H1 u), specialize (H2 u), specialize (H3 u), specialize (H4 u), tauto!,
  tauto!,
end
-/