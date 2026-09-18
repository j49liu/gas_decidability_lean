import HGAS.Modular.CanonicalUnaryThetaSolution
import HGAS.Modular.ThetaZeroFree
import HGAS.Modular.UnaryComparisonReconstruction
import HGAS.Modular.UpperHalfPlaneCurve

/-!
# Canonical theta reference in the modular reconstruction

This file connects the abstract two-jet cancellation in
`UnaryComparisonReconstruction` to the canonical theta--Eisenstein state.

For a differentiable lift `T : ℝ → ℍ` with ambient derivative `v(t)`, the
curve

```
                         r(t) = canonicalUnaryTheta (T(t))
```

is a variable-clock unary trajectory with multiplier `πi v(t)`.  Therefore
any generic source trajectory with the same lambda coordinate satisfies
the Riccati reconstruction theorem.  The resulting lift is forced to be
fractional linear.

Pointwise nonvanishing of the canonical `B=θ₃⁴` coordinate is supplied by
`ThetaZeroFree`, whose proof identifies the square of
`H₂H₃H₄` with a nonzero scalar multiple of the modular discriminant.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I
open Complex
open scoped Manifold

noncomputable section

/-- The canonical theta state, composed with a differentiable
upper-half-plane curve, has the variable clock `πi T'`. -/
theorem canonicalUnaryTheta_comp_isVariableScaled
    (T : ℝ → ℍ) (v : ℝ → ℂ)
    (hT : ∀ t,
      HasDerivAt (fun s : ℝ ↦ (T s : ℂ)) (v t) t) :
    IsVariableScaledUnaryModularTrajectory
      (fun t ↦ modularIndependentVariableClock * v t)
      (fun t ↦ canonicalUnaryTheta (T t)) where
  A t := by
    have h :=
      hasDerivAt_comp_upperHalfPlaneCurve
        (fun τ ↦ (canonicalUnaryTheta τ).A)
        canonicalUnaryTheta_A_mdifferentiable
        T t (hT t)
    convert h using 1
    rw [canonicalUnaryTheta_isMathlibNormalized.A_eq]
    simp only [modularIndependentVariableClock]
    ring
  C t := by
    have h :=
      hasDerivAt_comp_upperHalfPlaneCurve
        (fun τ ↦ (canonicalUnaryTheta τ).C)
        canonicalUnaryTheta_C_mdifferentiable
        T t (hT t)
    convert h using 1
    rw [canonicalUnaryTheta_isMathlibNormalized.C_eq]
    simp only [modularIndependentVariableClock]
    ring
  E t := by
    have h :=
      hasDerivAt_comp_upperHalfPlaneCurve
        (fun τ ↦ (canonicalUnaryTheta τ).E)
        canonicalUnaryTheta_E_mdifferentiable
        T t (hT t)
    convert h using 1
    rw [canonicalUnaryTheta_isMathlibNormalized.E_eq]
    simp only [modularIndependentVariableClock]
    ring
  Y t := by
    have h :=
      hasDerivAt_comp_upperHalfPlaneCurve
        (fun τ ↦ (canonicalUnaryTheta τ).Y)
        canonicalUnaryTheta_Y_mdifferentiable
        T t (hT t)
    convert h using 1
    rw [canonicalUnaryTheta_isMathlibNormalized.Y_eq]
    simp only [modularIndependentVariableClock]
    ring

/-- A lambda lift through the canonical theta state supplies the exact
reference-trajectory hypothesis of the abstract comparison theorem. -/
theorem canonicalUnaryTheta_isComparisonReference
    (z : ℝ → UnaryModularState ℂ)
    (T : ℝ → ℍ)
    (hT : ∀ t,
      HasDerivAt
        (fun s : ℝ ↦ (T s : ℂ))
        (unaryComparisonV z
          (fun q ↦ canonicalUnaryTheta (T q)) t) t) :
    IsUnaryComparisonReferenceTrajectory z
      (fun t ↦ canonicalUnaryTheta (T t)) := by
  exact canonicalUnaryTheta_comp_isVariableScaled
    T
    (unaryComparisonV z
      (fun q ↦ canonicalUnaryTheta (T q)))
    hT

/-- **Canonical modular reconstruction.**  A differentiable canonical
lambda lift of a generic unary trajectory is a Riccati two-jet. -/
theorem canonicalUnaryTheta_lift_isRiccatiJetTrajectory
    {z : ℝ → UnaryModularState ℂ}
    {T : ℝ → ℍ}
    (hz :
      IsScaledUnaryModularTrajectory
        modularIndependentVariableClock z)
    (hBz : ∀ t, UnaryModularState.B (z t) ≠ 0)
    (hLambda : ∀ t,
      UnaryModularState.lambdaCoordinate (z t) =
        UnaryModularState.lambdaCoordinate
          (canonicalUnaryTheta (T t)))
    (hT : ∀ t,
      HasDerivAt
        (fun s : ℝ ↦ (T s : ℂ))
        (unaryComparisonV z
          (fun q ↦ canonicalUnaryTheta (T q)) t) t) :
    IsRiccatiJetTrajectory
      (unaryComparisonU z
        (fun q ↦ canonicalUnaryTheta (T q)))
      (unaryComparisonV z
        (fun q ↦ canonicalUnaryTheta (T q)))
      (fun t ↦ (T t : ℂ)) := by
  apply unaryComparison_isRiccatiJetTrajectory
    hz
    (canonicalUnaryTheta_isComparisonReference z T hT)
    hBz (fun t ↦ canonicalUnaryTheta_B_ne_zero (T t)) hLambda
  exact hT

/-- The canonical lift has the explicit global fractional-linear form. -/
theorem canonicalUnaryTheta_lift_eq_fractionalLinear
    {z : ℝ → UnaryModularState ℂ}
    {T : ℝ → ℍ}
    (hz :
      IsScaledUnaryModularTrajectory
        modularIndependentVariableClock z)
    (hBz : ∀ t, UnaryModularState.B (z t) ≠ 0)
    (hLambda : ∀ t,
      UnaryModularState.lambdaCoordinate (z t) =
        UnaryModularState.lambdaCoordinate
          (canonicalUnaryTheta (T t)))
    (hT : ∀ t,
      HasDerivAt
        (fun s : ℝ ↦ (T s : ℂ))
        (unaryComparisonV z
          (fun q ↦ canonicalUnaryTheta (T q)) t) t)
    (t₀ t : ℝ) :
    (T t : ℂ) =
      (T t₀ : ℂ) +
        unaryComparisonV z
            (fun q ↦ canonicalUnaryTheta (T q)) t₀ *
          ((t - t₀ : ℝ) : ℂ) /
          (1 +
            unaryComparisonU z
                (fun q ↦ canonicalUnaryTheta (T q)) t₀ *
              ((t - t₀ : ℝ) : ℂ)) := by
  exact
    (canonicalUnaryTheta_lift_isRiccatiJetTrajectory
      hz hBz hLambda hT).T_eq_fractionalLinear
        t₀ t

end

end HGAS.Modular
