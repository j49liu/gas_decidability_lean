import HGAS.Modular.JacobiThetaWronskians

/-!
# Unconditional projective theta rank

`JacobiThetaInitialRank` proves the reusable algebraic consequences of
three pointwise Wronskian identities.  `JacobiThetaWronskians` proves
those identities from the theta series.  This bridge records the
unconditional canonical consequences while keeping the general
conditional lemmas reusable.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I
open Complex Real

noncomputable section

/-- The canonical theta vector and its elliptic derivative are linearly
independent at every point. -/
theorem canonical_linearIndependent_theta_and_derivative_unconditional
    (z : ℂ) (τ : ℍ) :
    LinearIndependent ℂ
      ![jacobiThetaVector z (τ : ℂ),
        jacobiThetaVectorPrime z (τ : ℂ)] :=
  canonical_linearIndependent_theta_and_derivative
    z τ (canonicalJacobiThetaWronskiansAt z τ)

/-- Unconditional first ratio-derivative identity. -/
theorem hasDerivAt_jacobiTheta2_div_jacobiTheta1_unconditional
    (z : ℂ) (τ : ℍ)
    (h1 : jacobiTheta1 z (τ : ℂ) ≠ 0) :
    HasDerivAt
      (fun w ↦
        jacobiTheta2 w (τ : ℂ) /
          jacobiTheta1 w (τ : ℂ))
      (-π * (canonicalUnaryRoots τ).p2 *
          jacobiTheta3 z (τ : ℂ) *
          jacobiTheta4 z (τ : ℂ) /
        jacobiTheta1 z (τ : ℂ) ^ 2) z :=
  hasDerivAt_jacobiTheta2_div_jacobiTheta1
    z τ h1 (canonicalJacobiThetaWronskiansAt z τ)

/-- Unconditional second ratio-derivative identity. -/
theorem hasDerivAt_jacobiTheta3_div_jacobiTheta1_unconditional
    (z : ℂ) (τ : ℍ)
    (h1 : jacobiTheta1 z (τ : ℂ) ≠ 0) :
    HasDerivAt
      (fun w ↦
        jacobiTheta3 w (τ : ℂ) /
          jacobiTheta1 w (τ : ℂ))
      (-π * (canonicalUnaryRoots τ).p3 *
          jacobiTheta4 z (τ : ℂ) *
          jacobiTheta2 z (τ : ℂ) /
        jacobiTheta1 z (τ : ℂ) ^ 2) z :=
  hasDerivAt_jacobiTheta3_div_jacobiTheta1
    z τ h1 (canonicalJacobiThetaWronskiansAt z τ)

/-- Unconditional third ratio-derivative identity. -/
theorem hasDerivAt_jacobiTheta4_div_jacobiTheta1_unconditional
    (z : ℂ) (τ : ℍ)
    (h1 : jacobiTheta1 z (τ : ℂ) ≠ 0) :
    HasDerivAt
      (fun w ↦
        jacobiTheta4 w (τ : ℂ) /
          jacobiTheta1 w (τ : ℂ))
      (-π * (canonicalUnaryRoots τ).p4 *
          jacobiTheta2 z (τ : ℂ) *
          jacobiTheta3 z (τ : ℂ) /
        jacobiTheta1 z (τ : ℂ) ^ 2) z :=
  hasDerivAt_jacobiTheta4_div_jacobiTheta1
    z τ h1 (canonicalJacobiThetaWronskiansAt z τ)

/-- The canonical initial-value linearization has complex rank three
without any remaining Wronskian hypothesis. -/
theorem
    canonical_jacobiInitialValueLinearization_range_finrank_unconditional
    {S A B : ℂ} (z : ℂ) (τ : ℍ)
    (hS : S ≠ 0)
    (hT1 : jacobiTheta1 z (τ : ℂ) ≠ 0) :
    Module.finrank ℂ
      (jacobiInitialValueLinearization S A B
        (jacobiThetaVector z (τ : ℂ))
        (jacobiThetaVectorPrime z (τ : ℂ))).range =
      3 :=
  canonical_jacobiInitialValueLinearization_range_finrank
    z τ hS hT1
      (canonicalJacobiThetaWronskiansAt z τ)

end

end HGAS.Modular
