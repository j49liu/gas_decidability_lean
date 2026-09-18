import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Topology.IsLocalHomeomorph

/-!
# A parameterized complex inverse theorem

Let `r(τ,z)` be complex analytic in both variables.  If its derivative
in the second variable is nonzero at `(τ,z)`, then

```
                       (τ,z) ↦ (τ,r(τ,z))
```

is a local homeomorphism there.

The derivative is block triangular.  Its first component is the identity
on the parameter, and the lower-right scalar is the nonzero partial
derivative of `r`.  The proof below packages that elementary linear
algebra as a reusable continuous linear equivalence and then applies
Mathlib's inverse-function theorem.
-/

namespace HGAS.Topology

open Complex Function Topology

noncomputable section

/-- The block-triangular derivative of `(τ,z) ↦ (τ,r(τ,z))`. -/
def parameterizedComplexCoordinateDerivative
    (D : (ℂ × ℂ) →L[ℂ] ℂ) :
    (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  (ContinuousLinearMap.fst ℂ ℂ ℂ).prod D

@[simp]
theorem parameterizedComplexCoordinateDerivative_apply
    (D : (ℂ × ℂ) →L[ℂ] ℂ)
    (v : ℂ × ℂ) :
    parameterizedComplexCoordinateDerivative D v =
      (v.1, D v) :=
  rfl

/-- The block-triangular derivative is injective when its second
diagonal entry is nonzero. -/
theorem parameterizedComplexCoordinateDerivative_injective
    (D : (ℂ × ℂ) →L[ℂ] ℂ)
    (hD : D (0, 1) ≠ 0) :
    Function.Injective
      (parameterizedComplexCoordinateDerivative D) := by
  intro u v huv
  have hfirst : u.1 = v.1 := by
    have h := congrArg Prod.fst huv
    simpa only [parameterizedComplexCoordinateDerivative_apply] using h
  have hsecond : D u = D v := by
    have h := congrArg Prod.snd huv
    simpa only [parameterizedComplexCoordinateDerivative_apply] using h
  apply Prod.ext hfirst
  have hzero :
      D (u - v) = 0 := by
    rw [map_sub, hsecond, sub_self]
  have hdecompose :
      u - v =
        (u.2 - v.2) • ((0, 1) : ℂ × ℂ) := by
    ext <;> simp [hfirst]
  rw [hdecompose, map_smul] at hzero
  have hproduct :
      (u.2 - v.2) * D (0, 1) = 0 := by
    simpa only [smul_eq_mul] using hzero
  exact sub_eq_zero.mp
    ((mul_eq_zero.mp hproduct).resolve_right hD)

/-- The same derivative is surjective.  The displayed preimage is the
usual back-substitution formula for a triangular matrix. -/
theorem parameterizedComplexCoordinateDerivative_surjective
    (D : (ℂ × ℂ) →L[ℂ] ℂ)
    (hD : D (0, 1) ≠ 0) :
    Function.Surjective
      (parameterizedComplexCoordinateDerivative D) := by
  intro y
  let w : ℂ :=
    (y.2 - D (y.1, 0)) / D (0, 1)
  refine ⟨(y.1, w), ?_⟩
  apply Prod.ext
  · rfl
  · change D (y.1, w) = y.2
    have hdecompose :
        (y.1, w) =
          (y.1, 0) + w • ((0, 1) : ℂ × ℂ) := by
      ext <;> simp
    rw [hdecompose, map_add, map_smul]
    change D (y.1, 0) + w * D (0, 1) = y.2
    dsimp [w]
    rw [div_mul_cancel₀ _ hD]
    ring

/-- Continuous linear equivalence associated with the invertible
block-triangular derivative. -/
def parameterizedComplexCoordinateDerivativeEquiv
    (D : (ℂ × ℂ) →L[ℂ] ℂ)
    (hD : D (0, 1) ≠ 0) :
    (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) :=
  ContinuousLinearEquiv.ofBijective
    (parameterizedComplexCoordinateDerivative D)
    (LinearMap.ker_eq_bot.mpr
      (parameterizedComplexCoordinateDerivative_injective
        D hD))
    (LinearMap.range_eq_top.mpr
      (parameterizedComplexCoordinateDerivative_surjective
        D hD))

@[simp]
theorem parameterizedComplexCoordinateDerivativeEquiv_apply
    (D : (ℂ × ℂ) →L[ℂ] ℂ)
    (hD : D (0, 1) ≠ 0)
    (v : ℂ × ℂ) :
    parameterizedComplexCoordinateDerivativeEquiv D hD v =
      (v.1, D v) :=
  rfl

/-- Pointwise parameterized inverse-function theorem.

The conclusion is deliberately returned as the exact local chart used
by `IsLocalHomeomorph`: an open partial homeomorphism agreeing globally
with `(τ,z) ↦ (τ,r(τ,z))` and containing the chosen point in its source.
-/
theorem exists_parameterizedComplexCoordinate_localHomeomorph
    (r : ℂ × ℂ → ℂ) (p : ℂ × ℂ)
    (hr : AnalyticAt ℂ r p)
    (hpartial :
      deriv (fun z ↦ r (p.1, z)) p.2 ≠ 0) :
    ∃ e : OpenPartialHomeomorph (ℂ × ℂ) (ℂ × ℂ),
      p ∈ e.source ∧
        (e : (ℂ × ℂ) → (ℂ × ℂ)) =
          fun q ↦ (q.1, r q) := by
  let D : (ℂ × ℂ) →L[ℂ] ℂ :=
    fderiv ℂ r p
  have hrD : HasFDerivAt r D p := by
    exact hr.differentiableAt.hasFDerivAt
  have hpartialD :
      D (0, 1) =
        deriv (fun z ↦ r (p.1, z)) p.2 := by
    have hfixed :
        HasDerivAt
            (fun z ↦ r (p.1, z))
            (D (0, 1)) p.2 := by
      simpa only using
        (hrD.comp p.2
          (hasFDerivAt_prodMk_right p.1 p.2)).hasDerivAt
    exact hfixed.deriv.symm
  have hD : D (0, 1) ≠ 0 := by
    rw [hpartialD]
    exact hpartial
  let F : ℂ × ℂ → ℂ × ℂ :=
    fun q ↦ (q.1, r q)
  let L : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
    parameterizedComplexCoordinateDerivative D
  have hFL : HasFDerivAt F L p := by
    exact HasFDerivAt.prodMk hasFDerivAt_fst hrD
  have hstrict : HasStrictFDerivAt F L p := by
    have hraw : HasStrictFDerivAt F (fderiv ℂ F p) p :=
      (analyticAt_fst.prod hr).hasStrictFDerivAt
    rw [hFL.fderiv] at hraw
    exact hraw
  let E : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) :=
    parameterizedComplexCoordinateDerivativeEquiv D hD
  have hstrictE :
      HasStrictFDerivAt F (E : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) p := by
    simpa only [E, L,
      ContinuousLinearEquiv.coe_ofBijective] using hstrict
  let e : OpenPartialHomeomorph (ℂ × ℂ) (ℂ × ℂ) :=
    hstrictE.toOpenPartialHomeomorph F
  exact
    ⟨e, hstrictE.mem_toOpenPartialHomeomorph_source,
      hstrictE.toOpenPartialHomeomorph_coe⟩

/-- Global local-homeomorphism form when the analytic and nonzero
partial-derivative hypotheses hold at every point. -/
theorem isLocalHomeomorph_parameterizedComplexCoordinate
    (r : ℂ × ℂ → ℂ)
    (hr : ∀ p : ℂ × ℂ, AnalyticAt ℂ r p)
    (hpartial :
      ∀ p : ℂ × ℂ,
        deriv (fun z ↦ r (p.1, z)) p.2 ≠ 0) :
    IsLocalHomeomorph
      (fun p : ℂ × ℂ ↦ (p.1, r p)) := by
  intro p
  rcases
      exists_parameterizedComplexCoordinate_localHomeomorph
        r p (hr p) (hpartial p) with
    ⟨e, hp, he⟩
  exact ⟨e, hp, he.symm⟩

end

end HGAS.Topology
