import HGAS.Algebra.FiniteEuclidean
import Mathlib.Tactic

/-!
# Degree raising and dimension padding

This file formalizes the pointwise algebra of equation (17.2) in the paper.
If `H` is a cubic field on the `x`-coordinates, first adjoin independent
scalar cubic sinks

```
(x, z) ↦ (H x, fun i ↦ -(z i)^3).
```

Then multiply every component by

```
(‖x‖² + ‖z‖²)^j.
```

The resulting field has degree `3 + 2 * j`.  We prove that statement through
the reusable semantic scaling predicate `ScalesAsDegree`, rather than tying
the construction to one polynomial representation.

The results here are deliberately pointwise.  In particular,
`degreePaddedField_preserves_baseSubspace` says that the coordinate subspace
`z = 0` is invariant at the level of vector-field values, and
`degreePaddedField_eq_directProduct_on_unitSphere` says that degree padding
does not change the field on the unit sphere.  A full GAS equivalence also
requires trajectory, time-change, and forward-completeness arguments and is
therefore not asserted in this algebraic module.
-/

namespace HGAS

open scoped BigOperators

variable {m k : ℕ} {R : Type*}

/-- A point split into an original block of dimension `m` and an auxiliary
block of dimension `k`. -/
abbrev SplitPoint (m k : ℕ) (R : Type*) :=
  FinVector m R × FinVector k R

/-- Semantic homogeneity for a map between two types carrying scalar
actions.  It is intentionally independent of polynomial syntax, so it can
also be used for intermediate vector fields assembled from polynomial
pieces. -/
def ScalesAsDegree
    (R : Type*) {X Y : Type*} [Monoid R] [SMul R X] [SMul R Y]
    (d : ℕ) (F : X → Y) : Prop :=
  ∀ (c : R) (x : X), F (c • x) = c ^ d • F x

/-- The direct product of `H` with independent scalar cubic sinks. -/
def directProductCubic [CommRing R]
    (H : FinVector m R → FinVector m R) :
    SplitPoint m k R → SplitPoint m k R :=
  fun p ↦
    (H p.1, fun i ↦ -(p.2 i) ^ 3)

/-- The algebraic squared radius of a split point. -/
def splitNormSq [CommSemiring R] (p : SplitPoint m k R) : R :=
  normSq p.1 + normSq p.2

/-- The common degree-raising factor in equation (17.2). -/
def degreePaddingFactor [CommSemiring R]
    (j : ℕ) (p : SplitPoint m k R) : R :=
  splitNormSq p ^ j

/-- Equation (17.2): multiply the direct-product cubic field by the `j`th
power of the total squared radius. -/
def degreePaddedField [CommRing R]
    (H : FinVector m R → FinVector m R) (j : ℕ) :
    SplitPoint m k R → SplitPoint m k R :=
  fun p ↦ degreePaddingFactor j p • directProductCubic H p

@[simp]
theorem directProductCubic_fst [CommRing R]
    (H : FinVector m R → FinVector m R) (p : SplitPoint m k R) :
    (directProductCubic H p).1 = H p.1 :=
  rfl

@[simp]
theorem directProductCubic_snd_apply [CommRing R]
    (H : FinVector m R → FinVector m R) (p : SplitPoint m k R)
    (i : Fin k) :
    (directProductCubic H p).2 i = -(p.2 i) ^ 3 :=
  rfl

@[simp]
theorem splitNormSq_base_zero [CommSemiring R]
    (x : FinVector m R) :
    splitNormSq (x, (0 : FinVector k R)) = normSq x := by
  simp [splitNormSq]

/-- Before degree raising, the subspace `z = 0` reproduces `H` exactly. -/
@[simp]
theorem directProductCubic_base_zero [CommRing R]
    (H : FinVector m R → FinVector m R) (x : FinVector m R) :
    directProductCubic (k := k) H (x, 0) = (H x, 0) := by
  apply Prod.ext
  · rfl
  · funext i
    simp [directProductCubic]

/-- On `z = 0`, degree padding only multiplies the original field by
`‖x‖² ^ j`; the auxiliary velocity remains zero. -/
@[simp]
theorem degreePaddedField_base_zero [CommRing R]
    (H : FinVector m R → FinVector m R) (j : ℕ)
    (x : FinVector m R) :
    degreePaddedField (k := k) H j (x, 0) =
      (normSq x ^ j • H x, 0) := by
  simp [degreePaddedField, degreePaddingFactor]

/-- The direct-product field is tangent to the coordinate subspace `z = 0`.
This is the pointwise algebraic content needed to prove that the subspace is
invariant for its ODE. -/
theorem directProductCubic_preserves_baseSubspace [CommRing R]
    (H : FinVector m R → FinVector m R) (x : FinVector m R) :
    (directProductCubic (k := k) H (x, 0)).2 = 0 := by
  simp

/-- The degree-padded field is likewise tangent to the coordinate subspace
`z = 0`. -/
theorem degreePaddedField_preserves_baseSubspace [CommRing R]
    (H : FinVector m R → FinVector m R) (j : ℕ)
    (x : FinVector m R) :
    (degreePaddedField (k := k) H j (x, 0)).2 = 0 := by
  simp

/-- Algebraic unit-sphere membership for the split coordinates. -/
def OnSplitUnitSphere [CommSemiring R] (p : SplitPoint m k R) : Prop :=
  splitNormSq p = 1

/-- The degree-raising factor is exactly one on the unit sphere. -/
theorem degreePaddingFactor_eq_one_on_unitSphere [CommSemiring R]
    (j : ℕ) (p : SplitPoint m k R) (hp : OnSplitUnitSphere p) :
    degreePaddingFactor j p = 1 := by
  change splitNormSq p = 1 at hp
  rw [degreePaddingFactor, hp]
  simp

/-- Consequently, degree padding leaves the direct-product field unchanged
at every point of the unit sphere. -/
theorem degreePaddedField_eq_directProduct_on_unitSphere [CommRing R]
    (H : FinVector m R → FinVector m R) (j : ℕ)
    (p : SplitPoint m k R) (hp : OnSplitUnitSphere p) :
    degreePaddedField H j p = directProductCubic H p := by
  simp [degreePaddedField,
    degreePaddingFactor_eq_one_on_unitSphere j p hp]

/-- Total squared radius has scaling degree two. -/
theorem splitNormSq_smul [CommSemiring R]
    (c : R) (p : SplitPoint m k R) :
    splitNormSq (c • p) = c ^ 2 * splitNormSq p := by
  simp [splitNormSq, normSq_smul]
  ring

/-- The degree-raising factor has scaling degree `2 * j`. -/
theorem degreePaddingFactor_smul [CommSemiring R]
    (j : ℕ) (c : R) (p : SplitPoint m k R) :
    degreePaddingFactor j (c • p) =
      c ^ (2 * j) * degreePaddingFactor j p := by
  simp only [degreePaddingFactor, splitNormSq_smul, mul_pow]
  rw [← pow_mul]

/-- Appending the scalar sinks preserves cubic homogeneity. -/
theorem directProductCubic_scalesAsDegree [CommRing R]
    (H : FinVector m R → FinVector m R)
    (hH : ScalesAsDegree R 3 H) :
    ScalesAsDegree R 3 (directProductCubic (k := k) H) := by
  intro c p
  rcases p with ⟨x, z⟩
  apply Prod.ext
  · simpa [directProductCubic] using hH c x
  · funext i
    simp [directProductCubic, Pi.smul_apply, smul_eq_mul]
    ring

/-- Multiplying a cubic field by the `j`th power of squared radius raises
its scaling degree from three to `3 + 2 * j`. -/
theorem degreePaddedField_scalesAsDegree [CommRing R]
    (H : FinVector m R → FinVector m R) (j : ℕ)
    (hH : ScalesAsDegree R 3 H) :
    ScalesAsDegree R (3 + 2 * j) (degreePaddedField (k := k) H j) := by
  intro c p
  simp only [degreePaddedField]
  rw [degreePaddingFactor_smul,
    directProductCubic_scalesAsDegree H hH c p]
  rw [pow_add]
  simp only [smul_smul]
  congr 1
  ring

end HGAS
