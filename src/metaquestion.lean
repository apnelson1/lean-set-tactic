import tactic

lemma foo_alg {α : Type} (A: boolean_algebra α) (X Y Z P Q W: α): 
  (X ⊔ (Y ⊔ Z)) ⊔ ((W ⊓ P ⊓ Q)ᶜ ⊔ (P ⊔ W ⊔ Q)) = ⊤ :=
begin
  sorry
end

lemma foo_prop  (X Y Z P Q W: Prop): 
  (X ⊔ (Y ⊔ Z)) ⊔ ((W ⊓ P ⊓ Q)ᶜ ⊔ (P ⊔ W ⊔ Q)) :=
begin
  unfold_projs,
  tauto!
end

#print foo_prop
-- how to get from foo_prop to foo_set??
