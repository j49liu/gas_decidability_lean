import Mathlib.Tactic

/-!
# Reward separation in the product-sphere wrapper

Let `sᵢ` be the squared radii of all blocks and put `H=∏ᵢsᵢ`.  The wrapper
replaces a source observable `α` by

```
b = H α - (1-H).
```

On the intended stratum every `sᵢ=1`, hence `b=α`.  On every proper block
face at least one `sᵢ=0`, hence `b=-1`.  These tiny identities are what make
the maximal invariant average exactly `max {β,-1}` after the dynamical face
classification has been supplied.
-/

namespace HGAS

open scoped BigOperators

variable {blocks : ℕ} {R : Type*} [CommRing R]

/-- Product of all squared block radii. -/
def blockRadiusProduct (s : Fin blocks → R) : R :=
  ∏ i, s i

/-- Observable used to separate the intended product-sphere stratum from
all proper radius faces. -/
def wrapperReward (s : Fin blocks → R) (α : R) : R :=
  blockRadiusProduct s * α - (1 - blockRadiusProduct s)

/-- The product is one when every block radius is one. -/
theorem blockRadiusProduct_eq_one
    (s : Fin blocks → R) (hs : ∀ i, s i = 1) :
    blockRadiusProduct s = 1 := by
  simp [blockRadiusProduct, hs]

/-- The wrapper reward agrees exactly with the source reward on the full
product-sphere stratum. -/
theorem wrapperReward_eq_source
    (s : Fin blocks → R) (α : R) (hs : ∀ i, s i = 1) :
    wrapperReward s α = α := by
  rw [wrapperReward, blockRadiusProduct_eq_one s hs]
  ring

/-- A single absent block makes the radius product vanish. -/
theorem blockRadiusProduct_eq_zero_of_coordinate
    (s : Fin blocks → R) {i : Fin blocks} (hi : s i = 0) :
    blockRadiusProduct s = 0 := by
  simp only [blockRadiusProduct]
  exact Finset.prod_eq_zero (Finset.mem_univ i) hi

/-- Every proper block face receives the fixed reward `-1`. -/
theorem wrapperReward_eq_neg_one_of_zero_coordinate
    (s : Fin blocks → R) (α : R)
    {i : Fin blocks} (hi : s i = 0) :
    wrapperReward s α = -1 := by
  rw [wrapperReward, blockRadiusProduct_eq_zero_of_coordinate s hi]
  ring

end HGAS
