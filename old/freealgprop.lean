import order.boolean_algebra
import freealg

open freealg
--------------------------------------------------------------------------------

def atom_prop {A : Type*} [boolean_algebra A] (a : A) :=
  ¬(a ≤ ⊥) ∧ forall (X Y : A), a ≤ (X ⊔ Y) → (a ≤ X) ∨ (a ≤ Y)
def atom (A : Type*) [boolean_algebra A] :=
  {a : A // atom_prop a}

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

def atomic_freealg : forall {n : nat}, (freealg n) → Prop
| 0 tt := true
| 0 ff := false
| (n + 1) ⟨a, b⟩ := (atomic_freealg a ∧ b = ⊥) ∨ (atomic_freealg b ∧ a = ⊥)

lemma atomic_freealg_is_atom {n : nat} (a : freealg n) :
  atomic_freealg a ↔ (atom_prop a) :=
begin
  induction n,
  {
    split,
    -- atomic_freealg -> atom_prop
    cases a; unfold atom_prop; unfold atomic_freealg;
    unfold_projs; unfold zero; unfold sup; unfold le; simp,
    intros; cases X; cases Y; simp at *; unfold le at *; try {assumption}; simp,
    -- reverse
    cases a; unfold atom_prop; unfold atomic_freealg; unfold_projs; 
    unfold zero; unfold sup; unfold le; simp at *; intro H,
  },
  {
    split,
    -- atomic_freealg -> atom_prop
    {
      cases a; unfold atom_prop; unfold atomic_freealg;
      unfold_projs; unfold zero; unfold sup; unfold le; simp,
      intros Hatom, split,
      -- dealing with the non-triviality case
      {
        rewrite n_ih at Hatom, 
        unfold atom_prop at *,
        unfold_projs at *, 
        intro H, 
        repeat {cases Hatom},
        {cases Hatom_left, contradiction},
        {rewrite n_ih at Hatom_left, cases Hatom_left, assumption}
      },
      -- 
      {
        intros X Y, cases X, cases Y, simp,
        rewrite n_ih at Hatom, rewrite n_ih at Hatom,
        unfold atom_prop at *,
        unfold_projs at *, 
        intros HaXY HbXY,
        cases Hatom,
        {
          sorry,
        },
        {
          sorry,
        },
      }
    }
  }
end

lemma atomic {n : nat} (X Y : freealg n): (X ≤ Y) ↔ 
  forall (a : atom (freealg n)), (elem a X) → (elem a Y) :=
begin
  split,
  {
    intros HXY a,
    cases a, unfold elem, simp only [], 
    intro HaX, apply (le_trans HaX HXY),
  },
  {
    sorry,
  }
end

--------------------------------------------------------------------------------

lemma foo_big (X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ X₈ X₉ : A) : 
  (X₀ ⊔ X₁ ⊔ (X₂ ⊓ X₃) ⊔ X₄ ⊔ X₅ ⊔ (X₆ ⊓ X₇ ⊓ X₈) ⊔ X₉)ᶜ 
    ≤ (X₉ᶜ ⊓ ((X₆ᶜ ⊔ ⊥) ⊔ X₈ᶜ ⊔ X₇ᶜᶜᶜ) ⊓ X₅ᶜ ⊓ (X₀ᶜ \ X₁) ⊓ (X₃ᶜ ⊔ X₂ᶜ) ⊓ X₄ᶜ) :=
begin
  simp only [atomic, rw_eq, rw_sdiff, rw_bot, rw_top, rw_sup, rw_inf, rw_compl],
  tauto!,
  done
end
