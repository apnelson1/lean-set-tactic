import tactic

def f {T : Type} [boolean_algebra T] (X Y Z P Q W: T) : Prop :=
  (X ⊔ (Y ⊔ Z)) ⊔ ((W ⊓ P ⊓ Q)ᶜ ⊔ (P ⊔ W ⊔ Q)) = ⊤

lemma foo_alg {α : Type} (A: boolean_algebra α) (X Y Z P Q W: α): 
  f X Y Z P Q W :=
begin
  simp [f],
  sorry
  -- we know this is true as in testing simplify_sets solves this.
end

lemma foo_prop (X Y Z P Q W: Prop): 
  f X Y Z P Q W :=
begin
  simp [f],
  unfold_projs,
  tauto!
end

#print foo_prop
-- how to get from foo_prop to foo_set??
