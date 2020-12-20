import freealg 

open interactive
open lean.parser
open tactic
open tactic.interactive 
open freealg


meta def set_to_ring_eqn : tactic unit := do
`[try {simp only
    [top_to_ring, bot_to_ring, symm_diff_to_ring, inf_to_ring, sup_to_ring, 
      diff_to_ring, compl_to_ring, le_to_ring] at *}]


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
    vname <- get_unused_name `V,
    tactic.interactive.introduce_varmap_rewrite vname sets,
    vname_expr <- get_local vname,
    set_to_ring_eqn,
    simp none tt ([``(freealg.on_one %%vname_expr),
                   ``(freealg.on_plus %%vname_expr),
                   ``(freealg.on_times %%vname_expr),
                   ``(freealg.on_zero %%vname_expr),
                   ``(freealg.on_var %%vname_expr)].map simp_arg_type.expr)
                    list.nil loc.wildcard,
    refl


variables {α : Type}


----------------------------- Examples ------------------------------------


lemma bar (A: boolean_algebra α) (X Y Z P Q W: α): 
  (X ⊔ (Y ⊔ Z)) ⊔ ((W ⊓ P ⊓ Q)ᶜ ⊔ (P ⊔ W ⊔ Q)) = ⊤ :=
begin
  simplify_sets [X, Y, Z, P, Q, W],
end

lemma bar_set (X Y Z : set α): 
  X ⊓ Y ⊓ Z = Z ⊓ Y ⊓ (X ⊔ ⊥) := 
  begin
    simplify_sets [X,Y,Z],
  end


lemma bar_finset [fintype α][decidable_eq α](X Y Z: finset α):
  X ⊓ Y ⊓ Z = Z ⊓ Y ⊓ (X ⊔ ⊥) := 
  begin
    simplify_sets [X,Y,Z],
  end

-- it isn't great to have to use ⊓/⊔ rather than ∩/∪ in these last two examples. 
-- can we massage this with the tactic? 