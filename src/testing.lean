
import boolring_tactic 
----------------------------- Examples ------------------------------------

variables {α : Type
}
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
  (X₀ ∪ X₁ ∪ (X₂ ∩ X₃) ∪ X₄ ∪ X₅ ∪ (X₆ ∩ X₇ ∩ X₈) ∪ X₉)ᶜ 
    ⊆ (X₉ᶜ ∩ ((X₆ᶜ ∪ ∅) ∪ X₈ᶜ ∪ X₇ᶜᶜᶜ) ∩ X₅ᶜ ∩ (X₀ᶜ \ X₁) ∩ (X₃ᶜ ∪ X₂ᶜ) ∩ X₄ᶜ) := 
  begin
    simplify_sets [X₀, X₁, X₂, X₃, X₄, X₅, X₆, X₇, X₈, X₉], 
  end 


lemma foo_fifty (X Y Z : set α): false := 
begin
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],
  have : Z ∪ Yᶜ ∪ X = X ∪ Yᶜ ∪ Z := by simplify_sets [X,Y,Z],

  

end