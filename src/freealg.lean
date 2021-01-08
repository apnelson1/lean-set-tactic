import make_ring 
namespace freealg

/----------------------------------------------------------------------------------
 
 Builds a 'free boolean algebra' whose elements are commutative sums of squarefree
 monomials in n indeterminates X₀, X₁, ... with coefficients mod 2. These elements
 are encoded internally as boolean vectors, via a map under which addition is 'xor' and 
 multiplication is 'and', both coordinate-wise. 

------------------------------------------------------------------------------------/

variables {α : Type*}[boolean_algebra α]

def freealg : nat → Type
-- base case is bool
| 0 := bool
-- inductive case is the coefficient on X_n and the coefficient on X_nᶜ
-- where the value of the term is CX_n + DX_nᶜ
-- this determines a region in the Venn diagram that represents the free boolean algebra
| (n+1) := (freealg n) × (freealg n)

def zero : forall {n : nat}, (freealg n)
| 0 := ff
| (n+1) := (zero, zero)

def one : forall {n : nat}, (freealg n)
| 0 := tt
| (n+1) := (one, one)

def var : forall {n : nat} (i : nat), (i < n) → (freealg n)
| 0 i Hi := false.elim (nat.not_lt_zero i Hi)
| (n+1) 0 Hi := (one, zero)
| (n+1) (i+1) Hi := let coeff : freealg n := var i (nat.lt_of_succ_lt_succ Hi) in (coeff, coeff)

def sdiff : forall {n : nat}, (freealg n) → (freealg n) → (freealg n)
| 0 a b := bxor a b 
| (n+1) a b := (sdiff a.1 b.1, sdiff a.2 b.2)

def inf : forall {n : nat}, (freealg n) → (freealg n) → (freealg n)
| 0 a b := band a b
| (n+1) a b := (inf a.1 b.1, inf a.2 b.2)

def sup : forall {n : nat}, (freealg n) → (freealg n) → (freealg n)
| 0 a b := bor a b
| (n + 1) a b := (sup a.1 b.1, sup a.2 b.2)

-- having ring makes it nicer to work with sdiff/inf so we define sup in terms of sdiff and inf.
lemma sup_to_sdiff_and_inf {n : nat} (a b : (freealg n)) :
  sup a b = (sdiff (sdiff a b) (inf a b)) :=
  begin
    induction n,
    {
      unfold sup sdiff inf, cases a; cases b; refl
    },
    {
      unfold sup sdiff inf,
      rewrite (n_ih a.1 b.1),
      rewrite (n_ih a.2 b.2),
    }
  end
  

def map : forall {n : nat} (V : vector α n), (freealg n) → α
| 0 V ff := 0
| 0 V tt := 1
| (n+1) V a := (map V.tail a.1) * V.head + (map V.tail a.2) * (V.head + 1)

lemma on_zero : forall {n : nat} (V : vector α n),
0 = map V zero
  | 0 V := rfl
  | (n+1) V := calc
      0   = 0 * V.head + 0 * (V.head + 1)                                 : by ring
      ... = (map V.tail zero) * V.head + (map V.tail zero) * (V.head + 1) : by rw on_zero

lemma on_one : forall {n : nat} (V : vector α n),
1 = map V one
  | 0 V := rfl
  | (n+1) V := calc
      1   = V.head + (V.head + 1)                                       : (add_self_left _ _).symm
      ... = 1 * V.head + 1 * (V.head + 1)                               : by ring
      ... = (map V.tail one) * V.head + (map V.tail one) * (V.head + 1) : by rw on_one

lemma on_var : forall {n : nat} (V : vector α n) (i : nat) (Hi : i < n),
V.nth ⟨i, Hi⟩ = map V (var i Hi)
  | 0 V i Hi := false.elim (nat.not_lt_zero i Hi)
  | (n+1) V 0 Hi := calc
      V.nth ⟨0, Hi⟩ = V.head                                                       : by simp
      ...           = 1 * V.head + 0 * (V.head + 1)                                : by ring
      ...           = (map V.tail one) * V.head + (map V.tail zero) * (V.head + 1) : by rw [on_zero, on_one]
  | (n+1) V (i+1) Hi := let
      Hip : (i < n) := nat.lt_of_succ_lt_succ Hi,
      tail_var := map V.tail (var i Hip)
      in calc V.nth ⟨i + 1, Hi⟩ = V.tail.nth ⟨i, Hip⟩                         : by rw [vector.nth_tail, fin.succ.equations._eqn_1]
      ...                       = tail_var                                    : on_var _ _ _
      ...                       = _                                           : (add_self_left (tail_var * V.head) _).symm
      ...                       = tail_var * V.head + tail_var * (V.head + 1) : by ring

lemma on_add : forall {n : nat} (V : vector α n) (a b : freealg n),
(map V a) + (map V b) = map V (sdiff a b)
  | 0 V a b :=
      begin
        cases a; cases b; unfold map sdiff bxor; ring,
        exact two_eq_zero,
      end
  | (n+1) V a b :=
      begin
        unfold map sdiff,
        rw [←on_add V.tail a.1 b.1, ←on_add V.tail a.2 b.2],
        ring,
      end

lemma on_mul : forall {n : nat} (V : vector α n) (a b : freealg n),
(map V a) * (map V b) = map V (inf a b)
  | 0 V a b := by cases a; cases b; unfold map inf band; ring
  | (n+1) V a b :=
      begin
        unfold map inf,
        rw [←on_mul V.tail a.1 b.1, ←on_mul V.tail a.2 b.2,←expand_product],
      end

-- Really, there should be a better way to do this.
lemma on_inf : forall {n : nat} (V : vector α n) (a b : freealg n),
(map V a) ⊓ (map V b) = map V (inf a b) :=
begin
  intros,
  change (map V a) * (map V b) = map V (inf a b),
  apply on_mul,
end
lemma on_sup : forall {n : nat} (V : vector α n) (a b : freealg n),
(map V a) ⊔ (map V b) = map V (sup a b) :=
begin
  intros,
  rewrite sup_to_ring,
  rewrite sup_to_sdiff_and_inf,
  rewrite <- on_add, rewrite <- on_add, rewrite <- on_mul,
end


instance  freealg_as_boolalg (n : nat) : (boolean_algebra (freealg n)) := { 
  sup := sup,
  le := _,
  lt := _,
  le_refl := _,
  le_trans := _,
  lt_iff_le_not_le := _,
  le_antisymm := _,
  le_sup_left := _,
  le_sup_right := _,
  sup_le := _,
  inf := inf,
  inf_le_left := _,
  inf_le_right := _,
  le_inf := _,
  le_sup_inf := _,
  top := one,
  le_top := _,
  bot := zero,
  bot_le := _,
  compl := _,
  sdiff := sdiff,
  inf_compl_le_bot := _,
  top_le_sup_compl := _,
  sdiff_eq := _ 
}


end /-namespace-/ freealg
