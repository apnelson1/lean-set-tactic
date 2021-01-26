import order.lattice 
import order.boolean_algebra

class boolean_algebra_extensionality
  (T : Type) (E : Type) 
  [has_mem E T] 
  [has_sup T] 
  [has_inf T]
  [has_compl T]
  [has_sdiff T]
  [has_bot T]
  [has_top T]
  [has_le T]
   :=
  (simpl_sdiff : ∀ {A B : T}, A \ B = A ⊓ Bᶜ )
  (simpl_eq : ∀ {A B : T}, A = B ↔ A ≤ B ∧ B ≤ A)
  (ext_top : ∀ {e}, e ∈ (⊤ : T) ↔ true)
  (ext_bot : ∀ {e}, e ∈ (⊥ : T) ↔ false)
  (ext_le : ∀ {A B : T}, A ≤ B ↔ ∀ e, e ∈ A →  e ∈ B) 
  (ext_meet : ∀ {A B : T} {e}, e ∈ (A ⊔ B) ↔ e ∈ A ∨ e ∈ B)
  (ext_join : ∀ {A B : T} {e}, e ∈ (A ⊓ B) ↔ e ∈ A ∧ e ∈ B)
  (ext_compl : ∀ {A : T} {e}, e ∈ Aᶜ ↔ ¬ e ∈ A)
