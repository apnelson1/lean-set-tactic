import freealg 

open interactive
open lean.parser
open tactic
open tactic.interactive («let» «have» simp refl)
open freealg

------------------------- Conversion Tactic: [(finset α) or (set α) or boolean_lattice] to [boolean_ring] 

lemma finset.inter_is_inf (α : Type) [decidable_eq α] (X Y : finset α) : X ∩ Y = X ⊓ Y := rfl
lemma finset.union_is_sup (α : Type) [decidable_eq α] (X Y : finset α) : X ∪ Y = X ⊔ Y := rfl
lemma finset.empt_is_bot (α : Type) [decidable_eq α] : (finset.has_emptyc.emptyc : finset α) = ⊥ := rfl
lemma finset.subset_is_le (α : Type) [decidable_eq α] (X Y : finset α) : (X ⊆ Y) = (X ≤ Y) := rfl 

lemma set.union_is_sup (α : Type) (X Y : set α) : X ∪ Y = X ⊔ Y := rfl
lemma set.inter_is_inf (α : Type) (X Y : set α) : X ∩ Y = X ⊓ Y := rfl
lemma set.empt_is_bot (α : Type) : (set.has_emptyc.emptyc : set α) = ⊥ := rfl 
lemma set.univ_is_top (α : Type) : (set.univ : set α) = ⊤ := rfl 
lemma set.subset_is_le (α : Type) (X Y : set α) : (X ⊆ Y) = (X ≤ Y) := rfl 

lemma ne_is_not_eq {α : Type} [boolean_algebra α] {X Y : α} : (X ≠ Y) = ¬(X = Y) := rfl 


meta def to_ring_eqn : tactic unit := do
`[
  try {simp only
  [finset.inter_is_inf, finset.union_is_sup, finset.empt_is_bot, finset.subset_is_le] at *}, 
  try {simp only 
  [set.union_is_sup, set.inter_is_inf, set.empt_is_bot, set.univ_is_top, set.subset_is_le] at *}, 
  try {simp only 
  [top_to_ring, bot_to_ring, symm_diff_to_ring,diff_to_ring, compl_to_ring, le_to_ring] at *}, 
  try {simp only [inf_to_ring, sup_to_ring] at *},
  try {simp only [ne_is_not_eq] at *},
  try {rw [bring_to_left] at *}
]

#check and

lemma convert_ands {A B A' B' : Prop} :
  A = A' → B = B' → (A ∧ B) = (A' ∧ B') :=
begin
  cc,
end

meta def get_proof_normalization : expr → tactic (expr × expr)
| e := do
  match e with 
  | `(%%L ∧ %%R) := do
    (pfLT, pfLE) <- get_proof_normalization L,
    (pfRT, pfRE) <- get_proof_normalization R,
    match (pfLT, pfRT) with
    | (`(_ = %%newL), `(_ = %%newR)) := do
      proof_type <- to_expr ``(%%e = (%%newL ∧ %%newR)),
      proof_expr <- to_expr 
        ``(convert_ands %%pfLE %%pfRE : 
            %%proof_type),
      return (proof_type, proof_expr)
    | _ := fail "Not here"
    end
   | `(%%A = %%B) := do
    proof_type <- to_expr ``(%%e = (%%A + %%B + 1 = 1)),
    proof_expr <- to_expr ``(bring_to_left : %%proof_type),
    return (proof_type, proof_expr)
  | _ := fail "Not here"
  end

meta def normalize_target : tactic unit := do
  texpr <- target,
  name <- get_unused_name `Hnormal,
  (newTargetExpr, proofTerm) <- get_proof_normalization texpr,
  hypExpr <- assertv name newTargetExpr proofTerm,
  rewrite_target hypExpr,
  clear hypExpr,
  return ()

meta def find_splittable_hyp : tactic expr := do
  hyps <- local_context,
  hyps <- hyps.mfilter (fun hyp, 
    (do `(%%A ∧ %%B) <- infer_type hyp,
        return tt)
    <|> return ff),
  match hyps with
  | (x :: xs) := return x
  | [] := fail "No splittable hypothesis found"
  end

meta def split_hyps : tactic unit := do
  repeat $ (do
    hyp <- find_splittable_hyp,
    trace_state,
    cases hyp,
    skip)

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
          -- TODO: maybe clean this up with definev/assertv instead.
          («have» hname ``(%%name = _) ``(on_var %%vname_expr %%idx (by norm_num))),
          hname_expr <- get_local hname,
          tactic.try (rewrite_target hname_expr),
          clear hname_expr,
          return ())
      (list_with_idx names 0),
    return ()

meta def find_matching_type (e : expr) : list expr → tactic expr
| []         := tactic.failed
| (H :: Hs)  := do t ← tactic.infer_type H,
                   (tactic.unify e t >> return H) <|> find_matching_type Hs
set_option pp.all false
meta def get_sets_in_expr : expr → tactic (list name) 
-- TODO maybe return the expressions themselves as they're less fragile then raw names
-- something something expressions have a unique and a pretty name, which is slightly concerning
-- (maybe).
| e :=
  match e with
  -- This mostly handles basic expressions 
  | expr.local_const unique pretty _ _ :=
    do
      expr <- get_local pretty,
      ((do
        `(%%typ) <- tactic.infer_type expr,
        boolalg_hyp <- to_expr ``(infer_instance : boolean_algebra %%typ),
        return [pretty])
      <|>
        return [])
  | expr.app e1 e2 := 
    do l1 <- get_sets_in_expr e1, 
       l2 <- get_sets_in_expr e2,
       return (l1 ++ l2)
  | _ := do return []
  end

meta def assert_expr_is_boolalg (e : expr) : tactic unit :=
do
  typ <- tactic.infer_type e,
  boolalg_hyp <- to_expr ``(infer_instance : boolean_algebra %%typ),
  return ()
  
meta def is_boolalg_eqn : expr → tactic bool
| e :=
  ((do `(%%L = %%R) <- (infer_type e),
    assert_expr_is_boolalg L,
    assert_expr_is_boolalg R,
    return tt)
  <|>
  (do `(%%L ≠ %%R) <- (infer_type e),
    assert_expr_is_boolalg L,
    assert_expr_is_boolalg R,
    return tt)
  <|>
  (do `(¬ %%L = %%R) <- (infer_type e),
    assert_expr_is_boolalg L,
    assert_expr_is_boolalg R,
    return tt)
  <|>
  (return ff))

def keep_unique {T: Type}[decidable_eq T]: list T -> list T 
| [] := []
| (x :: xs) := let tl := keep_unique xs in
                if list.mem x tl then tl else x :: tl

/- A bound variable with a de-Bruijn index. -/
-- | var _ := tactic.failed ()
/- A type universe: `Sort u` -/
-- | sort l := do return ()
/- A global constant. These include definitions, constants and inductive type stuff present
in the environment as well as hard-coded definitions. -/
-- | const name l := do return ()
/- [WARNING] Do not trust the types for `mvar` and `local_const`,
they are sometimes dummy values. Use `tactic.infer_type` instead. -/
/- An `mvar` is a 'hole' yet to be filled in by the elaborator or tactic state. -/
-- | mvar unique pretty type := do return ()
/- A local constant. For example, if our tactic state was `h : P ⊢ Q`, `h` would be a local constant. -/
-- | local_const unique pretty binder type := do return ()
/- Function application. -/
-- | app e1 e2 := do return ()
/- Lambda abstraction. eg ```(λ a : α, x)`` -/
-- | lam name binder type body := do return ()
/- Pi type constructor. eg ```(Π a : α, x)`` and ```(α → β)`` -/
-- | pi name binder type body := do return ()
/- An explicit let binding. -/
--| elet name type assignment body := do return ()
/- A macro, see the docstring for `macro_def`.
  The list of expressions are local constants and metavariables that the macro depends on.
  -/
-- | expr.macro macro_def body := do return () 
meta def dummy : tactic unit :=
  do tactic.trace "Hello World"

lemma switch_target {T : Type} [boolean_algebra T] (A B C : T):
  (A = 1) → (A * B = A * C) → B = C :=
  λ h1 h2, by {rw [h1,one_mul, one_mul] at h2, from h2}
    
-- expects that goal is conjunction of ring equations
-- expects that assumptions are just ring equations
meta def simplify_one_set (extra_sets : list name): tactic unit :=
  do   
    -- Convert to ring equations, and also
    -- convert ring hypothesis to be of the form <eqn> = 1

    -- TODO: gather sets from goals and hypothesis evntually
    -- before we convert the goal as that's expensive.
    timetac "rewrite to ring equation" $ to_ring_eqn,
    normalize_target,
    timetac "rewrite ∧ to ring equns" $ try `[apply no_inverses],
    context <- tactic.local_context,
    boolalg_hyps <- timetac "get boolalg hyp" $ context.mfilter is_boolalg_eqn,
    -- Rewrite target to be Π (hypothesis) * original target
    -- Clear original ring hypothesis as they are not needed anymore
    tactic.timetac "rewrite target" $ boolalg_hyps.mmap
      (fun (hyp : expr), do
        `(%%Lh = 1) <- infer_type hyp,
        `(%%Ltarget = %%Rtarget) <- target,
        `[apply (switch_target %%Lh %%Ltarget %%Rtarget %%hyp)],
        return ()
      ),

    -- Gather sets in the goal
    texpr <- target,
    list_of_sets <- timetac "get set names" $ get_sets_in_expr texpr,
    tactic.trace list_of_sets,
    vname <- get_unused_name `V,
    tactic.timetac "rewrite names" $ tactic.interactive.introduce_varmap_rewrite vname
      (keep_unique $ list_of_sets ++ extra_sets),
    vname_expr <- get_local vname,

    -- Some goals are already discharged by this point, so everything else
    -- goes in a try block.
    tactic.timetac "final simp" $
    tactic.try (simp none tt ([``(freealg.on_one %%vname_expr),
                   ``(freealg.on_add %%vname_expr),
                   ``(freealg.on_mul %%vname_expr),
                   ``(freealg.on_zero %%vname_expr),
                   ``(freealg.on_var %%vname_expr)].map simp_arg_type.expr)
                    list.nil loc.wildcard),
    tactic.timetac "evaluate ring stuff" $ tactic.try (refl)

meta def split_goal (solver : tactic unit): tactic unit := do
  texpr <- target,
  match texpr with
  | `(%%A ∨ %%B) := do
    trace $ "splitting: " ++ (to_string A) ++ (to_string B),
    (left >> split_goal <|> right >> split_goal)
  | _ := solver
  end

meta def tactic.interactive.timed_simplify_sets 
  (extra_sets : (parse (optional ids_list))): tactic unit :=
    do timetac "simplify sets" $ simplify_one_set (match extra_sets with | some l := l | none := [] end)

lemma fourlemma (T : Type) (A B C D : set T) : A ⊆ B → C ⊆ Bᶜ → D ⊆ Bᶜ → ((A ∩ C = ∅ ) ∧ (A ∩ D = ∅)):=
begin
  intros,
  timed_simplify_sets,
end

--lemma fourtrans (T : Type) (A B C D : set T) : (A ⊆ B) → (B ⊆ C) → (C ⊆ D) → (A ⊆ D) :=
--begin
--  intros,
--  timed_simplify_sets,
--end

--lemma dummylemma (T: Type) (X Y Z : set T) : (T = nat) → (X ⊆ Y) → (X ∩ Z) ⊆ (Y ∩ Z) :=
--begin
--  intros H1 H2,      
--  simplify_sets,
--end

--lemma foo_alg2 (α : Type) (A: boolean_algebra α) (X Y Z P Q W: α): 
--  (X ⊔ (Y ⊔ Z)) ⊔ ((W ⊓ P ⊓ Q)ᶜ ⊔ (P ⊔ W ⊔ Q)) = ⊤ :=
--begin
--  simplify_sets, 
--end