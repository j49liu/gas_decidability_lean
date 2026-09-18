import HGAS.Veronese.RealCone
import HGAS.Veronese.CubicLiftAlgebra
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

/-!
# First-order coordinates for the real Veronese cone

This module develops the elementary differential identities behind the
conormal argument.  After choosing a nonzero source coordinate `x i`,
the pure target coordinate `k e_i` and the adjacent coordinates
`(k-1)e_i+e_j` give the natural first-order chart coordinates.  We
package the differential of the Veronese map, compute its pure
coordinate, and differentiate the identity

```
x^((k-1)e_i+e_j) x_i = x^(k e_i) x_j.
```

The subsequent `AffineConeChart` module uses these coordinates to prove
the exact kernel statement needed for coercivity.  That chart-gauged
form avoids introducing abstract tangent and conormal spaces and is
strong enough for the normalized-error proof of the Morse--Bott
estimate.
-/

namespace HGAS.Veronese

open scoped BigOperators

noncomputable section

variable {n k : ℕ}

/-- The differential of the Veronese map as a linear map in its
direction argument. -/
def dVeroneseLinear (x : Fin n → ℝ) :
    (Fin n → ℝ) →ₗ[ℝ] (MultiIndex n k → ℝ) where
  toFun := dVeronese x
  map_add' := dVeronese_add x
  map_smul' c h := by
    exact dVeronese_smul c x h

@[simp]
theorem dVeroneseLinear_apply
    (x h : Fin n → ℝ) :
    dVeroneseLinear (k := k) x h = dVeronese x h :=
  rfl

/-- Reading the pure and adjacent target coordinates after
differentiation gives a source-space endomorphism. -/
def edgeDifferentialLinear
    (hk : 1 ≤ k) (i : Fin n) (x : Fin n → ℝ) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun := fun h j ↦ dVeronese (k := k) x h (edgeMultiIndex hk i j)
  map_add' h₁ h₂ := by
    funext j
    rw [dVeronese_add]
    rfl
  map_smul' c h := by
    funext j
    rw [dVeronese_smul]
    rfl

@[simp]
theorem edgeDifferentialLinear_apply
    (hk : 1 ≤ k) (i : Fin n) (x h : Fin n → ℝ)
    (j : Fin n) :
    edgeDifferentialLinear hk i x h j =
      dVeronese (k := k) x h (edgeMultiIndex hk i j) :=
  rfl

/-- Directional derivative of a source coordinate variable. -/
theorem sourcePolynomialDirectional_X
    (x h : Fin n → ℝ) (i : Fin n) :
    sourcePolynomialDirectional (MvPolynomial.X i) x h = h i := by
  classical
  simp [sourcePolynomialDirectional, MvPolynomial.pderiv_X,
    Pi.single_apply]

/-- Differential of the pure monomial `x_i^k`. -/
theorem dMonomial_pureMultiIndex
    (x h : Fin n → ℝ) (i : Fin n) :
    dMonomial x h (pureMultiIndex (k := k) i) =
      (k : ℝ) * h i * x i ^ (k - 1) := by
  classical
  unfold dMonomial
  rw [Finset.sum_eq_single i]
  · simp [pureMultiIndex, Pi.single_apply]
  · intro j _ hji
    simp [pureMultiIndex, Pi.single_apply, hji]
  · simp

/-- Source-polynomial form of the adjacent-coordinate identity

`x^((k-1)e_i+e_j) x_i = x^(k e_i) x_j`.
-/
theorem sourcePolynomial_edge_mul_X
    (hk : 1 ≤ k) (i j : Fin n) (hji : j ≠ i) :
      sourceVeronesePolynomial (edgeMultiIndex hk i j) *
        MvPolynomial.X i =
      sourceVeronesePolynomial (pureMultiIndex (k := k) i) *
        MvPolynomial.X j := by
  have hexp :
      multiIndexFinsupp (edgeMultiIndex hk i j) +
          Finsupp.single i 1 =
        multiIndexFinsupp (pureMultiIndex (k := k) i) +
          Finsupp.single j 1 := by
    ext l
    simp only [Finsupp.add_apply, multiIndexFinsupp_apply,
      Finsupp.single_apply]
    rw [edgeMultiIndex_of_ne hk i j hji]
    simpa only [eq_comm] using
      transferMultiIndex_add_single
        (pureMultiIndex (k := k) i) j i hji
        (by simpa using hk) l
  simp only [sourceVeronesePolynomial, MvPolynomial.X,
    MvPolynomial.monomial_mul, one_mul]
  rw [hexp]

/-- Differentiated adjacent-coordinate identity. -/
theorem dMonomial_edge_mul
    (hk : 1 ≤ k) (i j : Fin n) (hji : j ≠ i)
    (x h : Fin n → ℝ) :
      dMonomial x h (edgeMultiIndex hk i j) * x i +
        monomial x (edgeMultiIndex hk i j) * h i =
      dMonomial x h (pureMultiIndex (k := k) i) * x j +
        monomial x (pureMultiIndex (k := k) i) * h j := by
  have hpoly := sourcePolynomial_edge_mul_X hk i j hji
  have hdir :=
    congrArg (fun p ↦ sourcePolynomialDirectional p x h) hpoly
  change
    sourcePolynomialDirectional
        (sourceVeronesePolynomial (edgeMultiIndex hk i j) *
          MvPolynomial.X i) x h =
      sourcePolynomialDirectional
        (sourceVeronesePolynomial (pureMultiIndex (k := k) i) *
          MvPolynomial.X j) x h at hdir
  rw [sourcePolynomialDirectional_mul,
    sourcePolynomialDirectional_mul,
    sourcePolynomialDirectional_sourceVeronesePolynomial,
    sourcePolynomialDirectional_sourceVeronesePolynomial,
    sourcePolynomialDirectional_X,
    sourcePolynomialDirectional_X,
    eval₂Hom_sourceVeronesePolynomial,
    eval₂Hom_sourceVeronesePolynomial,
    MvPolynomial.eval₂Hom_X',
    MvPolynomial.eval₂Hom_X'] at hdir
  exact hdir

end

end HGAS.Veronese
