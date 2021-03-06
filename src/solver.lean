import .extensionality
import .boolean_algebra_tactic
import .finset_tactic
import tactic
import tactic.interactive
import .set_tactic

/-meta def simpl_tactic : tactic unit :=
`[simp only [simpl_sdiff, simpl_eq, ext_le, ext_bot, ext_top, ext_meet, ext_join, ext_compl] at *; tauto!]-/


-- TODO: Lots of things are boolean algebras.  We should have a way to configure
-- which boolean algebras we want to solve, actually.
--
-- Functions into boolean algebras are usually not useful, so we ignore them by default.
-- Moreover, hypotheses are either Prop or functions which indirectly produce a Prop,
-- so we really should probably ignore function types with Prop in them.
meta def get_boolalg_typ (consider_function_types := ff) (e : expr) : tactic (list expr) :=
  ((do
    `(%%boolalg_typ) <- tactic.infer_type e,
    match boolalg_typ with 
    -- finset T gets returned directly 
    | `(finset %%set_typ) := do return [boolalg_typ]
    -- set T gets returned directly
    | `(set %%set_typ) := do return [boolalg_typ]
    -- work needs to be done if we're not working with sets/finsets,
    -- but with a type with a [boolean_algebra T] instance on it.
    | _ := (do 
        boolalg_hyp <- tactic.to_expr ``(infer_instance : boolean_algebra %%boolalg_typ),
        match boolalg_typ with 
        -- Function types are usually not useful
        | `(_ -> _) := if consider_function_types then return [boolalg_typ] else return []
        -- Prop is not useful
        | `(Prop) := return []
        -- Other types, we can (probably) return
        | _ := return [boolalg_typ]
        end)
    end)
  <|>
    return [])

meta def boolean_algebra_types_in_expr (consider_function_types := ff) : expr → tactic (list expr)
| e :=
  do 
    e_inner <- (match e with
      -- This mostly handles basic expressions 
      | expr.local_const unique pretty _ _ := get_boolalg_typ consider_function_types e
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
      | expr.elet _ argtyp argval body := 
        do l1 <- boolean_algebra_types_in_expr argtyp, 
          l2 <- boolean_algebra_types_in_expr argval,
          l3 <- boolean_algebra_types_in_expr body,
          return (l1 ++ l2 ++ l3)
      | _ := return []
      end),
    e_outer <- get_boolalg_typ consider_function_types e,
    return (e_inner ++ e_outer)

def unique_list {T: Type}[decidable_eq T]: list T -> list T 
| [] := []
| (x :: xs) := let tl := unique_list xs in
                if list.mem x tl then tl else x :: tl

meta def infer_base_simp_lemmas (type : expr) : (tactic (list pexpr)) := do
  name <- tactic.get_unused_name `_instrw,
  instance_type <- tactic.to_expr ``(boolalg_ext_lemmas %%type _),
  expr <- tactic.to_expr ``(by apply_instance : %%instance_type),
  new_hyp <- tactic.assertv name instance_type expr,
  return [``((%%new_hyp).simpl_eq),
          ``((%%new_hyp).simpl_lt),
          ``((%%new_hyp).ext_le),
          ``((%%new_hyp).ext_bot),
          ``((%%new_hyp).ext_sdiff),
          ``((%%new_hyp).ext_meet),
          ``((%%new_hyp).ext_join)]

meta def infer_top_simp_lemmas (type : expr) : (tactic (list pexpr)) := (do
  name <- tactic.get_unused_name `_instrw,
  instance_type <- tactic.to_expr ``(boolalg_ext_lemmas_top %%type _),
  expr <- tactic.to_expr ``(by apply_instance : %%instance_type),
  new_hyp <- tactic.assertv name instance_type expr,
  return [``((%%new_hyp).ext_top)]) <|> return []

meta def infer_compl_simp_lemmas (type : expr) : (tactic (list pexpr)) := (do
  name <- tactic.get_unused_name `_instrw,
  instance_type <- tactic.to_expr ``(boolalg_ext_lemmas_compl %%type _),
  expr <- tactic.to_expr ``(by apply_instance : %%instance_type),
  new_hyp <- tactic.assertv name instance_type expr,
  return [``((%%new_hyp).ext_compl)]) <|> return []

meta def rewrite_for_type (type : expr) : (tactic unit) := do
  simp_lemmas <- infer_base_simp_lemmas type,
  compl_lemmas <- infer_compl_simp_lemmas type,
  top_lemmas <- infer_top_simp_lemmas type,
  tactic.try (tactic.interactive.simp none tt
              ((simp_lemmas ++ compl_lemmas ++ top_lemmas).map tactic.simp_arg_type.expr)
                  list.nil interactive.loc.wildcard),
  tactic.skip

meta def gather_types (consider_function_types := ff) : (tactic (list expr)) := do
  goal <- tactic.target,
  hyps <- tactic.local_context,
  types <- (do 
            types_in_expr <- (goal :: hyps).mmap (boolean_algebra_types_in_expr consider_function_types),
            return (unique_list (list.foldr list.append [] types_in_expr))),
  --tactic.trace "Boolean algebra types:",
  --tactic.trace types,
  return types


meta def set_ext (consider_function_types := ff) : (tactic unit) := do
  tactic.try `[simp only [ne, ge, gt, superset, ssuperset] at *],
  tactic.try cleanup.finset_cleanup,
  tactic.try cleanup.set_cleanup,
  types <- gather_types consider_function_types,
  types.mmap rewrite_for_type,
  tactic.skip 

meta def set_solver (consider_function_types := ff): (tactic unit) := do
  set_ext consider_function_types,
  `[finish]

example (α : Type) [boolean_algebra α] (X Y Z P Q W : α) :
  (X ⊔ (Y ⊔ Z)) ⊔ ((W ⊓ P ⊓ Q)ᶜ ⊔ (P ⊔ W ⊔ Q)) = ⊤ :=
begin
  set_solver,
end

example (T : Type) [fintype T] [decidable_eq T] (X Y Z P Q W : finset T)  :
  (X ⊔ (Y ⊔ Z)) ⊔ ((W ⊓ P ⊓ Q)ᶜ ⊔ (P ⊔ W ⊔ Q)) = ⊤ :=
begin
  set_solver,
end

-- note the lack of fintype T here
example (T : Type) [decidable_eq T] (X Y Z P Q W : finset T)  :
  (X ∪ Y) ≥ X :=
begin
  set_solver,
end

example (T : Type) [decidable_eq T] (x z : T) (Y : set T) :
  x ∈ ({z} : set T) → x = z :=
begin
  set_solver,
end

example (α : Type) [boolean_algebra α]  (A B C D E F G : α) :
  A ≤ B →
  B ≤ C →
  C ≤ D ⊓ E →
  D ≤ Fᶜ →
  (A ⊓ F = ⊥) :=
begin
  tactic.timetac "fast" $ `[(do
    types <- gather_types,
    types.mmap rewrite_for_type,
    tactic.skip),
  intros H1 H2 H3 H4; split; intros e;
  specialize (H1 e);
  specialize (H2 e);
  specialize (H3 e);
  specialize (H4 e); tauto!],
end

example (α : Type) [boolean_algebra α]  (A B C D E F G : α) :
  A ≤ B →
  B ≤ C →
  C ≤ D ⊓ E →
  D ≤ Fᶜ →
  (A ⊓ F = ⊥) :=
begin
  tactic.timetac "slow" $  set_solver,
end
 
example (α : Type)(C E : set α)(hCE : C ⊓ E = ∅):
  C ⊔ (E ⊔ C)ᶜ = Eᶜ := 
by {set_solver, }

example (α : Type)(C E : set α)(h : C ⊓ E = ⊥) : 
  C ⊓ (C ⊔ E)ᶜ = ∅ := 
by {set_solver, } 

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