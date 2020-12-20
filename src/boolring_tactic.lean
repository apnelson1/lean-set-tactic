import freealg 

open interactive
open lean.parser
open tactic
open tactic.interactive 
open freealg

------------------------- Conversion Tactic: [(finset α) or (set α) or boolean_lattice] to [boolean_ring] 

lemma finset.inter_is_inf (α : Type) [decidable_eq α] (X Y : finset α) : X ∩ Y = X ⊓ Y := rfl
lemma finset.union_is_sup (α : Type) [decidable_eq α] (X Y : finset α) : X ∪ Y = X ⊔ Y := rfl
lemma finset.empt_is_bot (α : Type) [decidable_eq α] : (finset.has_emptyc.emptyc : finset α) = ⊥ := rfl
lemma finset.subset_is_le (α : Type) [decidable_eq α] (X Y : finset α) : (X ⊆ Y) = (X ≤ Y) := rfl 
--lemma finset.univ_is_top (α : Type) [decidable_eq α] : (finset.order_top : finset α) = ⊤ := 

lemma set.union_is_sup (α : Type) (X Y : set α) : X ∪ Y = X ⊔ Y := rfl
lemma set.inter_is_inf (α : Type) (X Y : set α) : X ∩ Y = X ⊓ Y := rfl
lemma set.empt_is_bot (α : Type) : (set.has_emptyc.emptyc : set α) = ⊥ := rfl 
lemma set.univ_is_top (α : Type) : (set.univ : set α) = ⊤ := rfl 
lemma set.subset_is_le (α : Type) (X Y : set α) : (X ⊆ Y) = (X ≤ Y) := rfl 

meta def to_ring_eqn : tactic unit := do
`[try {simp only
    [finset.inter_is_inf, finset.union_is_sup, finset.empt_is_bot, finset.subset_is_le,
     set.union_is_sup, set.inter_is_inf, set.empt_is_bot, set.univ_is_top, set.subset_is_le,
     top_to_ring, bot_to_ring, symm_diff_to_ring, inf_to_ring, sup_to_ring, 
      diff_to_ring, compl_to_ring, le_to_ring] at *}]

------------------------------ Normalization Tactics (in a free boolean algebra) -------------------------
meta def ids_list : lean.parser (list name) := types.list_of ident
meta def meta_build_vector : list pexpr -> pexpr
| [] := ``(vector.nil)
| (v :: vs) := ``(vector.cons %%v %%(meta_build_vector vs))
meta def list_with_idx {T : Type} : (list T) → nat -> list (nat × T)
| [] n := []
| (v :: vs) n := (n, v) :: list_with_idx vs (n + 1)

meta def tactic.interactive.introduce_varmap_rewrite (vname : parse ident) (vars : parse ids_list) : tactic unit :=
  do
    names <- vars.mmap (fun name, get_local name),
    («let» vname ``(vector _ %%(vars.length)) $ meta_build_vector (names.map to_pexpr)),
    mmap 
      (λ (pair : (nat × expr)),
        let name := prod.snd pair in
        let idx := prod.fst pair in
        do 
          vname_expr <- get_local vname,
          hname <- get_unused_name `Hv,
          («have» hname ``(%%name = _) ``(on_var %%vname_expr %%idx (by norm_num))),
          hname_expr <- get_local hname,
          tactic.try (rewrite_target hname_expr),
          return ())
      (list_with_idx names 0),
    return ()

meta def tactic.interactive.simplify_sets (sets : parse ids_list): tactic unit :=
  do
    -- TODO: actually check the goal is of the form of some boolalg equation
    --       also -- do something about hypotheses...
    -- Probably makes sense to automatically include sets mentioned in the goal, analogously to linarith 

    vname <- get_unused_name `V,
    tactic.interactive.introduce_varmap_rewrite vname sets,
    vname_expr <- get_local vname,
    to_ring_eqn,
    simp none tt ([``(freealg.on_one %%vname_expr),
                   ``(freealg.on_add %%vname_expr),
                   ``(freealg.on_mul %%vname_expr),
                   ``(freealg.on_zero %%vname_expr),
                   ``(freealg.on_var %%vname_expr)].map simp_arg_type.expr)
                    list.nil loc.wildcard,
    refl


variables {α : Type}


----------------------------- Examples ------------------------------------


lemma foo_alg (A: boolean_algebra α) (X Y Z P Q W: α): 
  (X ⊔ (Y ⊔ Z)) ⊔ ((W ⊓ P ⊓ Q)ᶜ ⊔ (P ⊔ W ⊔ Q)) = ⊤ :=
begin
  simplify_sets [X, Y, Z, P, Q, W],
end

lemma foo_set (X Y Z : set α): 
  X ∩ Y ∩ Z = Z ∩ Y ∩ (X ∩ set.univ) := 
  begin
    simplify_sets [X,Y,Z],
  end

lemma foo_finset [fintype α][decidable_eq α](X Y Z: finset α):
  X ∩ Y ∩ Z = Z ∩ Y ∩ (X ∪ ∅) := 
  begin
    simplify_sets [X,Y,Z],
  end

lemma bar_finset [fintype α][decidable_eq α](X Y Z: finset α):
  X ∩ Y ∩ Z ⊆ (X ∪ Y) ∩ Z := 
  begin
    simplify_sets [X,Y,Z],
  end

lemma foo_big (X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ X₈ X₉ : set α) : 
  (X₀ ∪ X₁ ∪ (X₂ ∩ X₃) ∪ X₄ ∪ X₅ ∪ (X₆ ∩ X₇ ∩ X₈) ∪ X₉)ᶜ ⊆ (X₉ᶜ ∩ ((X₆ᶜ ∪ ∅) ∪ X₈ᶜ ∪ X₇ᶜᶜᶜ) ∩ X₅ᶜ ∩ (X₀ᶜ \ X₁) ∩ (X₃ᶜ ∪ X₂ᶜ) ∩ X₄ᶜ) := 
  begin
    simplify_sets [X₀, X₁, X₂, X₃, X₄, X₅, X₆, X₇, X₈, X₉], 
  end 