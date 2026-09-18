import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorDriftCode
import HGAS.Arithmetic.CanonicalFixedDetectorGraph
import Mathlib.Tactic

/-!
# The canonical detector graph satisfies the radius-normalized validity

The canonical clock construction already starts every driven phase and
the final RHS oscillator on a genuine unit circle.  Its controller inputs
are constant structured real pairs, so their unit normalization is stated
explicitly as a hypothesis.  Under that one natural hypothesis, the
canonical path lies on the exact zero set of the repaired validity
polynomial.
-/

namespace HGAS.NormalizedCorrectedCanonicalFixedDetectorGraph

open HGAS
open HGAS.Clocks
open HGAS.Modular
open HGAS.NormalizedCorrectedFixedDetectorValidityCode

noncomputable section

variable {eqs vars : ℕ}

/-- Every phase produced by `phasePath` has squared radius one. -/
theorem phasePath_radiusSq
    (ω : ℝ) (phase₀ : Circle) (t : ℝ) :
    Controller.phaseRadiusSq
        (LockedControllerPhaseTrajectory.phasePath ω phase₀ t) =
      1 := by
  have hnorm :=
    Circle.normSq_coe
      (PhaseClockFlow.phaseRotationFlow ω t phase₀)
  simpa [LockedControllerPhaseTrajectory.phasePath,
    PhaseClockFlow.circlePhaseState,
    Controller.phaseRadiusSq, Complex.normSq_apply, pow_two] using
    hnorm

/-- Exact controller normalization along the canonical path. -/
theorem fixedDetectorPath_controllerRadiusSq
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
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (t : ℝ) (i :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars)) :
    Controller.controllerRadiusSq
        (ControllerProductLinkedJacobiFamilyState.controllers
          (CanonicalFixedDetectorTrajectory.fixedDetectorPath
            parameters I controller phase₀ ξ₀ τ₀ rhs₀ t).base.base.source
          i).controller =
      1 := by
  simpa [CanonicalFixedDetectorTrajectory.fixedDetectorPath,
    CanonicalFixedDetectorTrajectory.poissonSourcePath,
    CanonicalFixedDetectorTrajectory.gaugeSourcePath,
    CanonicalFixedDetectorTrajectory.linkedSourcePath,
    CanonicalFixedDetectorTrajectory.clockPath,
    LockedControllerPhaseTrajectory.stateFamily] using
    hcontroller i

/-- Exact phase normalization along the canonical path. -/
theorem fixedDetectorPath_phaseRadiusSq
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
    (t : ℝ) (i :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars)) :
    Controller.phaseRadiusSq
        (ControllerProductLinkedJacobiFamilyState.controllers
          (CanonicalFixedDetectorTrajectory.fixedDetectorPath
            parameters I controller phase₀ ξ₀ τ₀ rhs₀ t).base.base.source
          i).phase =
      1 := by
  change
    Controller.phaseRadiusSq
        (LockedControllerPhaseTrajectory.phasePath
          (LockedControllerPhaseTrajectory.angularVelocity
            parameters controller i)
          (phase₀ i) t) =
      1
  exact phasePath_radiusSq _ _ _

/-- Exact unit-radius normalization of the final RHS oscillator. -/
theorem fixedDetectorPath_rhsRadiusSq
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
    (t : ℝ) :
    Controller.phaseRadiusSq
        (CanonicalFixedDetectorTrajectory.fixedDetectorPath
          parameters I controller phase₀ ξ₀ τ₀ rhs₀ t).rhs =
      1 := by
  change
    Controller.phaseRadiusSq
        (LockedControllerPhaseTrajectory.phasePath
          (-4 *
            CanonicalFixedDetectorTrajectory.rhsFrequency
              parameters I controller)
          rhs₀ t) =
      1
  exact phasePath_radiusSq _ _ _

/-- The added normalization energy vanishes on the canonical path. -/
theorem fixedDetectorPath_normalizationEnergyValue_eq_zero
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
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (t : ℝ) :
    normalizationEnergyValue
          (CanonicalFixedDetectorTrajectory.fixedDetectorPath
            parameters I controller phase₀ ξ₀ τ₀ rhs₀ t) =
      0 := by
  apply
    (normalizationEnergyValue_eq_zero_iff _).2
  exact
    ⟨fixedDetectorPath_controllerRadiusSq
        parameters I controller phase₀ ξ₀ τ₀ rhs₀ hcontroller t,
      fixedDetectorPath_phaseRadiusSq
        parameters I controller phase₀ ξ₀ τ₀ rhs₀ t,
      fixedDetectorPath_rhsRadiusSq
        parameters I controller phase₀ ξ₀ τ₀ rhs₀ t⟩

/-- The complete canonical graph has zero repaired validity energy. -/
theorem fixedDetectorPath_normalizedValidityEnergyValue_eq_zero
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
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
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
    NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue I
        (CanonicalFixedDetectorTrajectory.fixedDetectorPath
          parameters I controller phase₀ ξ₀ τ₀ rhs₀ t) =
      0 := by
  unfold NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue
  unfold totalNormalizedValidityEnergyValue
  change
    FixedDetectorDriftCode.validityEnergyValue I
          (CanonicalFixedDetectorTrajectory.fixedDetectorPath
            parameters I controller phase₀ ξ₀ τ₀ rhs₀ t) +
        normalizationEnergyValue
          (CanonicalFixedDetectorTrajectory.fixedDetectorPath
            parameters I controller phase₀ ξ₀ τ₀ rhs₀ t) =
      0
  rw [
    CanonicalFixedDetectorGraph.fixedDetectorPath_validityEnergyValue_eq_zero
        parameters I controller phase₀ ξ₀ τ₀ rhs₀ hθ₁ t,
    fixedDetectorPath_normalizationEnergyValue_eq_zero
      parameters I controller phase₀ ξ₀ τ₀ rhs₀ hcontroller t,
    add_zero]

end

end HGAS.NormalizedCorrectedCanonicalFixedDetectorGraph
