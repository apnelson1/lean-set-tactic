import extensionality
import boolean_algebra_tactic
import finset_tactic

open boolean_algebra_extensionality

/-meta def simpl_tactic : tactic unit :=
`[simp only [simpl_sdiff, simpl_eq, ext_le, ext_bot, ext_top, ext_meet, ext_join, ext_compl] at *; tauto!]-/

example (α : Type) [boolean_algebra α] (X Y Z P Q W : α) :
  (X ⊔ (Y ⊔ Z)) ⊔ ((W ⊓ P ⊓ Q)ᶜ ⊔ (P ⊔ W ⊔ Q)) = ⊤ :=
begin
  letI : (boolean_algebra_extensionality α (order.boolean_algebra.ultrafilter α)) := begin
    apply_instance,
  end,
  simp only [_inst.simpl_eq, _inst.ext_le, _inst.ext_bot, _inst.ext_top, _inst.ext_meet, _inst.ext_join, _inst.ext_compl],
  tauto!,
end


example (T : Type) [fintype T] (X Y Z P Q W : finset T) [decidable_eq T] :
  (X ⊔ (Y ⊔ Z)) ⊔ ((W ⊓ P ⊓ Q)ᶜ ⊔ (P ⊔ W ⊔ Q)) = ⊤ :=
begin
  letI : (boolean_algebra_extensionality (finset T) T) := begin
    apply_instance,
  end,
  simp only [_inst.simpl_eq, _inst.ext_le, _inst.ext_bot, _inst.ext_top, _inst.ext_meet, _inst.ext_join, _inst.ext_compl],
  tauto,
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