import order.boolean_algebra

--------------------------------------------------------------------------------

def atom (A : Type*) [boolean_algebra A] :=
  {a : A // ¬(a ≤ ⊥) ∧ forall (X Y : A), a ≤ (X ⊔ Y) → (a ≤ X) ∨ (a ≤ Y)}

variables {A : Type*} [boolean_algebra A] (a : atom A) (X Y : A)

def elem : Prop := a.val ≤ X

lemma rw_eq : (X = Y) ↔ (X ≤ Y) ∧ (Y ≤ X) := le_antisymm_iff
lemma rw_sdiff : (X \ Y) = X ⊓ Yᶜ := sdiff_eq

lemma rw_bot : elem a ⊥ ↔ false := iff_false_intro a.prop.left
lemma rw_top : elem a ⊤ ↔ true := iff_true_intro le_top
lemma rw_sup : elem a (X ⊔ Y) ↔ (elem a X) ∨ (elem a Y) := iff.intro (a.prop.right X Y) (or.rec le_sup_left_of_le le_sup_right_of_le)
lemma rw_inf : elem a (X ⊓ Y) ↔ (elem a X) ∧ (elem a Y) := le_inf_iff
lemma rw_compl : elem a Xᶜ ↔ ¬ (elem a X) :=
  iff.intro
  (fun hc h, a.prop.left (calc a.val ≤ X ⊓ Xᶜ : le_inf h hc ... = ⊥ : inf_compl_eq_bot))
  (or.resolve_left (a.prop.right X Xᶜ (calc a.val ≤ ⊤ : le_top ... = X ⊔ Xᶜ : sup_compl_eq_top.symm)))

--------------------------------------------------------------------------------

lemma atomic : (X ≤ Y) ↔ forall (a : atom A), (elem a X) → (elem a Y) := sorry

--------------------------------------------------------------------------------

lemma foo_big (X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ X₈ X₉ : A) : 
  (X₀ ⊔ X₁ ⊔ (X₂ ⊓ X₃) ⊔ X₄ ⊔ X₅ ⊔ (X₆ ⊓ X₇ ⊓ X₈) ⊔ X₉)ᶜ 
    ≤ (X₉ᶜ ⊓ ((X₆ᶜ ⊔ ⊥) ⊔ X₈ᶜ ⊔ X₇ᶜᶜᶜ) ⊓ X₅ᶜ ⊓ (X₀ᶜ \ X₁) ⊓ (X₃ᶜ ⊔ X₂ᶜ) ⊓ X₄ᶜ) :=
begin
  simp only [atomic, rw_eq, rw_sdiff, rw_bot, rw_top, rw_sup, rw_inf, rw_compl],
  tauto!,
  done
end
