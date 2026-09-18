import HGAS.Arithmetic.CanonicalFixedDetectorTrajectory
import HGAS.Arithmetic.DetectorPoissonReciprocalSemantics
import HGAS.Arithmetic.FixedDetectorDriftCode
import HGAS.Modular.JacobiThetaResiduals
import Mathlib.Tactic

/-!
# The canonical detector path lies on every compiled graph

The trajectory theorem says that the explicit theta path solves the
polynomial differential equations.  For the no-instance invariant graph
we also need a stronger pointwise statement: every algebraic validity
residual vanishes along that path.

This file proves that statement layer by layer.  The linked-Jacobi part is
an exact restatement of the theta identities and canonical root
normalizations.  The gauge and reciprocal parts use their literal graph
formulas.
-/

namespace HGAS.CanonicalFixedDetectorGraph

open HGAS
open Modular
open Clocks
open Clocks.ControllerPhaseProductCharacterCode
open _root_.MvPolynomial

noncomputable section

variable {eqs vars : ℕ}

/-! ## The ten linked-Jacobi residuals -/

/-- Every canonical linked theta state satisfies all ten named
linked-Jacobi validity equations. -/
theorem canonicalLinkedJacobiThetaMovingPath_residual_eq_zero
    (ξ : ℝ → ℂ) (T : ℝ → UpperHalfPlane)
    (t : ℝ)
    (hθ₁ : jacobiTheta1 (ξ t) (T t : ℂ) ≠ 0)
    (r : LinkedJacobiResidualIndex) :
    linkedJacobiResidual r
        (canonicalLinkedJacobiThetaMovingPath ξ T t) = 0 := by
  cases r with
  | coefficientCurve =>
      change
        (canonicalUnaryRoots (T t)).p3 ^ 2 -
            (canonicalUnaryRoots (T t)).p2 ^ 2 -
          (canonicalUnaryRoots (T t)).p4 ^ 2 = 0
      rw [canonicalUnaryRoots_p3_sq_eq]
      ring
  | thetaQuadricOne =>
      simpa [linkedJacobiResidual,
        canonicalLinkedJacobiThetaMovingPath,
        canonicalJacobiThetaState,
        JacobiState.residualR1,
        jacobiThetaVector] using
        (canonical_jacobiResidualQ1_jacobiThetaVector
          (ξ t) (T t))
  | thetaQuadricTwo =>
      simpa [linkedJacobiResidual,
        canonicalLinkedJacobiThetaMovingPath,
        canonicalJacobiThetaState,
        JacobiState.residualR2,
        jacobiThetaVector] using
        (canonical_jacobiResidualQ2_jacobiThetaVector
          (ξ t) (T t))
  | reciprocalChart =>
      simp [linkedJacobiResidual,
        canonicalLinkedJacobiThetaMovingPath,
        canonicalJacobiThetaMovingPath,
        canonicalJacobiThetaState,
        JacobiState.residualRU, hθ₁]
  | unaryJacobi =>
      simpa [linkedJacobiResidual,
        canonicalLinkedJacobiThetaMovingPath] using
        (canonicalUnaryTheta_jacobiResidual_eq_zero (T t))
  | coefficientLinkTwo =>
      simpa [linkedJacobiResidual,
        canonicalLinkedJacobiThetaMovingPath,
        canonicalJacobiThetaState,
        LinkedJacobiState.link2,
        UnaryRootState.link2] using
        (canonicalUnaryRoots_link2_eq_zero (T t))
  | coefficientLinkThree =>
      change
        (canonicalUnaryRoots (T t)).p3 ^ 2 -
          (canonicalUnaryTheta (T t)).Y ^ 4 = 0
      have hsigned :
          (canonicalUnaryRoots (T t)).p3 =
            (canonicalUnaryTheta (T t)).Y ^ 2 := by
        exact sub_eq_zero.mp
          (canonicalUnaryRoots_signedLink3_eq_zero (T t))
      rw [hsigned]
      ring
  | coefficientLinkFour =>
      simpa [linkedJacobiResidual,
        canonicalLinkedJacobiThetaMovingPath,
        canonicalJacobiThetaState,
        LinkedJacobiState.link4,
        UnaryRootState.link4] using
        (canonicalUnaryRoots_link4_eq_zero (T t))
  | eisensteinLink =>
      simpa [linkedJacobiResidual,
        canonicalLinkedJacobiThetaMovingPath,
        canonicalJacobiThetaState,
        LinkedJacobiState.linkH,
        UnaryRootState.linkH] using
        (canonicalUnaryRoots_linkH_eq_zero (T t))
  | signedRootLinkThree =>
      change
        (canonicalUnaryRoots (T t)).p3 -
          (canonicalUnaryTheta (T t)).Y ^ 2 = 0
      exact canonicalUnaryRoots_signedLink3_eq_zero (T t)

/-- Family specialization used by the fixed detector path. -/
theorem linkedSourcePath_residual_eq_zero
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Circle)
    (ξ₀ : Fin vars → ℂ)
    (τ₀ : Fin vars → UpperHalfPlane)
    (hθ₁ :
      ∀ j t,
        jacobiTheta1
          (CanonicalFixedDetectorTrajectory.ellipticPath
            (ξ₀ j)
            (CanonicalFixedDetectorTrajectory.omegaFrequency
              parameters controller j)
            (CanonicalFixedDetectorTrajectory.numberFrequency
              parameters I controller j) t)
          (CanonicalFixedDetectorTrajectory.modularPath
            (τ₀ j)
            (CanonicalFixedDetectorTrajectory.omegaFrequency
              parameters controller j) t : ℂ) ≠ 0)
    (t : ℝ) (j : Fin vars)
    (r : LinkedJacobiResidualIndex) :
    linkedJacobiResidual r
        ((CanonicalFixedDetectorTrajectory.linkedSourcePath
          parameters I controller phase₀ ξ₀ τ₀ t).linked j) =
      0 := by
  apply canonicalLinkedJacobiThetaMovingPath_residual_eq_zero
  exact hθ₁ j t

/-! ## The fourth-root gauge graph -/

/-- The corrected canonical gauge

```text
G_j(t) = (1/4) χ_{\gamma_j}(t)
```

lies on every scalar coordinate of the compiled graph
`G_j^4 = (1/256) χ_{4γ_j}`.  This theorem is stated at the scalar-code
level used by the validity energy, so no semantic gap remains between
the displayed complex identity and the emitted sparse polynomials. -/
theorem gaugeSourcePath_residualCode_eq_zero
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Circle)
    (ξ₀ : Fin vars → ℂ)
    (τ₀ : Fin vars → UpperHalfPlane)
    (t : ℝ) :
    ∀ k,
      eval₂Hom (algebraMap ℚ ℝ)
        (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.point
          (CanonicalFixedDetectorTrajectory.gaugeSourcePath
            parameters I controller phase₀ ξ₀ τ₀ t))
        (PolynomialCode.decode
          (DetectorJacobiGaugeData.residualCode
            FixedDetectorValidityEnergyCode.thetaGaugeScale I k)) =
        0 := by
  rw [DetectorJacobiGaugeData.residualCode,
    ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.gaugeResidualCode]
  apply
    (ComplexGaugeFamilyPolynomialCode.forall_eval_residualCode_eq_zero_iff
      FixedDetectorValidityEnergyCode.thetaGaugeScale
      (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.gaugeCharacterBaseCode
        (DetectorJacobiGaugeData.gaugeExponents I))
      (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.rawState
        (CanonicalFixedDetectorTrajectory.gaugeSourcePath
          parameters I controller phase₀ ξ₀ τ₀ t))).2
  intro j
  unfold ComplexGaugeFamilyPolynomialCode.residual
  simp only [
    ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.rawState]
  rw [
    ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.evalPair_gaugeCharacterBaseCode]
  simpa [FixedDetectorValidityEnergyCode.thetaGaugeScale,
    CanonicalFixedDetectorTrajectory.gaugeSourcePath,
    CanonicalFixedDetectorTrajectory.linkedSourcePath_controllers] using
    (CanonicalFixedDetectorTrajectory.gaugePath_graphResidual_eq_zero
      parameters I controller phase₀ t j)

/-! ## The Poisson reciprocal graph -/

/-- Every explicitly inverted Poisson denominator has zero semantic graph
residual. -/
theorem poissonSourcePath_reciprocalGraphResidual_eq_zero
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Circle)
    (ξ₀ : Fin vars → ℂ)
    (τ₀ : Fin vars → UpperHalfPlane)
    (t : ℝ)
    (k : Fin (DetectorPoissonReciprocalCode.reciprocalCount vars)) :
    DetectorPoissonReciprocalCode.reciprocalGraphResidual I
        (CanonicalFixedDetectorTrajectory.poissonSourcePath
          parameters I controller phase₀ ξ₀ τ₀ t) k =
      0 := by
  rw [DetectorPoissonReciprocalCode.reciprocalGraphResidual_eq]
  apply
    (reciprocalResidual_eq_zero_iff_eq_inv
      (((1 / 2 : ℝ) : ℂ))
      (characterValue
        (DetectorPoissonReciprocalCode.reciprocalExponent I k)
        ((CanonicalFixedDetectorTrajectory.poissonSourcePath
          parameters I controller phase₀ ξ₀ τ₀ t).base.source.controllers))
      ((CanonicalFixedDetectorTrajectory.poissonSourcePath
        parameters I controller phase₀ ξ₀ τ₀ t).reciprocal k)
      ?_).2
  · rfl
  · simpa [CanonicalFixedDetectorTrajectory.poissonSourcePath,
      CanonicalFixedDetectorTrajectory.gaugeSourcePath,
      CanonicalFixedDetectorTrajectory.linkedSourcePath,
      CanonicalFixedDetectorTrajectory.poissonCharacterPath] using
      (CanonicalFixedDetectorTrajectory.poissonDenominator_ne_zero
        parameters I controller phase₀ t k)

/-- Scalar sparse-code form of the same reciprocal graph statement. -/
theorem poissonSourcePath_reciprocalResidualCode_eq_zero
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Circle)
    (ξ₀ : Fin vars → ℂ)
    (τ₀ : Fin vars → UpperHalfPlane)
    (t : ℝ) :
    ∀ r,
      eval₂Hom (algebraMap ℚ ℝ)
        (DetectorPoissonReciprocalCode.point
          (CanonicalFixedDetectorTrajectory.poissonSourcePath
            parameters I controller phase₀ ξ₀ τ₀ t))
        (PolynomialCode.decode
          (DetectorPoissonReciprocalCode.residualCode I r)) =
        0 := by
  apply
    (DetectorPoissonReciprocalCode.forall_eval_residualCode_eq_zero_iff_graphResidual
      I
      (CanonicalFixedDetectorTrajectory.poissonSourcePath
        parameters I controller phase₀ ξ₀ τ₀ t)).2
  exact poissonSourcePath_reciprocalGraphResidual_eq_zero
    parameters I controller phase₀ ξ₀ τ₀ t

/-! ## The aggregate validity coordinate -/

/-- Along the complete canonical detector path, the first drift
coordinate is identically zero.  The chart hypothesis is needed only
for the linked-Jacobi reciprocal `U = 1/T₁`; gauge and Poisson graph
validity are unconditional consequences of their explicit formulas. -/
theorem fixedDetectorPath_validityEnergyValue_eq_zero
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Circle)
    (ξ₀ : Fin vars → ℂ)
    (τ₀ : Fin vars → UpperHalfPlane)
    (rhs₀ : Circle)
    (hθ₁ :
      ∀ j t,
        jacobiTheta1
          (CanonicalFixedDetectorTrajectory.ellipticPath
            (ξ₀ j)
            (CanonicalFixedDetectorTrajectory.omegaFrequency
              parameters controller j)
            (CanonicalFixedDetectorTrajectory.numberFrequency
              parameters I controller j) t)
          (CanonicalFixedDetectorTrajectory.modularPath
            (τ₀ j)
            (CanonicalFixedDetectorTrajectory.omegaFrequency
              parameters controller j) t : ℂ) ≠ 0)
    (t : ℝ) :
    FixedDetectorDriftCode.validityEnergyValue I
        (CanonicalFixedDetectorTrajectory.fixedDetectorPath
          parameters I controller phase₀ ξ₀ τ₀ rhs₀ t) =
      0 := by
  apply
    (FixedDetectorDriftCode.validityEnergyValue_eq_zero_iff
      I
      (CanonicalFixedDetectorTrajectory.fixedDetectorPath
        parameters I controller phase₀ ξ₀ τ₀ rhs₀ t)).2
  constructor
  · intro j r
    exact linkedSourcePath_residual_eq_zero
      parameters I controller phase₀ ξ₀ τ₀ hθ₁ t j r
  constructor
  · exact gaugeSourcePath_residualCode_eq_zero
      parameters I controller phase₀ ξ₀ τ₀ t
  · exact poissonSourcePath_reciprocalResidualCode_eq_zero
      parameters I controller phase₀ ξ₀ τ₀ t

end

end HGAS.CanonicalFixedDetectorGraph
