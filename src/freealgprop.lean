import make_ring 
namespace freealg

/----------------------------------------------------------------------------------
 
 Builds a 'free boolean algebra' whose elements are commutative sums of squarefree
 monomials in n-1 indeterminates X₀, X₁, ... with coefficients mod 2. These elements
 are encoded internally as boolean vectors, via a map under which addition is 'xor' and 
 multiplication is 'and', both coordinate-wise. 

------------------------------------------------------------------------------------/

variables {T : Type*}[boolean_algebra T]{n: nat}

-- want ⊥ ≠ ⊤
def freealg (n : nat) := vector bool (n + 1) 

-- zero is the all false vector
def zero : freealg n := vector.repeat ff (n + 1)
-- one is the all one vector
def one : freealg n := vector.repeat tt (n + 1)

-- mul, add are just what you want
def mul (x y : freealg n) := vector.map₂ band x y 
def add (x y : freealg n) := vector.map₂ bxor x y

-- var just maps to the characteristic vector of the ith element
def var : ∀ {n i : nat}, i < n → freealg n := ??
end freealg 