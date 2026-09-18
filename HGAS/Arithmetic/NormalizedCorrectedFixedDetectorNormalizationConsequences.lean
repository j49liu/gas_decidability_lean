import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorDriftCode
import HGAS.Arithmetic.DetectorPoissonReciprocalSemantics
import HGAS.Clocks.ControllerPhaseProductSphereFlow
import Mathlib.Tactic

/-!
# Consequences of zero normalized detector validity

This file exposes the exact circle hypotheses consumed by the clock and
selector modules.  It also explains why no independent gauge-radius
penalty is needed: the old fourth-root graph equation, together with unit
phase characters, already forces every gauge to be nonzero.
-/

namespace HGAS.NormalizedCorrectedFixedDetectorNormalizationConsequences

open HGAS
open HGAS.Clocks
open HGAS.Clocks.ControllerPhaseProductCharacterCode
open HGAS.Modular
open HGAS.NormalizedCorrectedFixedDetectorDriftCode
open HGAS.Modular.ControllerProductLinkedJacobiGaugeFamilyPolynomialCode

noncomputable section

variable {eqs vars : ℕ}

/-- A real phase pair of squared radius one has complex norm one. -/
theorem norm_phaseValue_eq_one_of_radiusSq
    (z :
      ControllerPhaseProductPolynomialCode.StateFamily
        (FixedDetectorPolynomialCode.clockCount eqs vars) ℝ)
    (i : Fin (FixedDetectorPolynomialCode.clockCount eqs vars))
    (h : Controller.phaseRadiusSq (z i).phase = 1) :
    ‖phaseValue z i‖ = 1 := by
  have hsq : ‖phaseValue z i‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simpa [phaseValue, Controller.phaseRadiusSq, pow_two] using h
  nlinarith [norm_nonneg (phaseValue z i)]

/-- Radius equations in structured clock coordinates imply the phase
character hypothesis used throughout the detector semantics. -/
theorem onPhaseCircles_of_phaseRadiusSq
    (z :
      ControllerPhaseProductPolynomialCode.StateFamily
        (FixedDetectorPolynomialCode.clockCount eqs vars) ℝ)
    (h : ∀ i, Controller.phaseRadiusSq (z i).phase = 1) :
    OnPhaseCircles z :=
  fun i ↦ norm_phaseValue_eq_one_of_radiusSq z i (h i)

/-- Zero repaired validity supplies the exact `OnPhaseCircles` hypothesis
used by signed Laurent characters, gauge graphs, and Poisson inverses. -/
theorem onPhaseCircles_of_validityEnergyValue_eq_zero
    (I : DQLSystem eqs vars)
    (z : FixedDetectorPolynomialCode.State eqs vars)
    (h :
      NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue I z =
        0) :
    OnPhaseCircles z.base.base.source.controllers := by
  have hz :=
    (validityEnergyValue_eq_zero_iff I z).1 h
  exact onPhaseCircles_of_phaseRadiusSq
    z.base.base.source.controllers hz.2.2.1

/-- Zero repaired validity places the raw controller-product coordinates
on the literal compact clock variety used by the clock flow. -/
theorem onClockCircles_of_validityEnergyValue_eq_zero
    (I : DQLSystem eqs vars)
    (z : FixedDetectorPolynomialCode.State eqs vars)
    (h :
      NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue I z =
        0) :
    ControllerPhaseProductSphereFlow.OnClockCircles
      (ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint
        z.base.base.source) := by
  have hz :=
    (validityEnergyValue_eq_zero_iff I z).1 h
  intro i
  change
    Controller.controllerRadiusSq
          (ControllerPhaseProductPolynomialCode.state
            (ControllerPhaseProductPolynomialCode.point
              z.base.base.source.controllers) i).controller =
        1 ∧
      Controller.phaseRadiusSq
          (ControllerPhaseProductPolynomialCode.state
            (ControllerPhaseProductPolynomialCode.point
              z.base.base.source.controllers) i).phase =
        1
  rw [ControllerPhaseProductPolynomialCode.state_point]
  exact ⟨hz.2.1 i, hz.2.2.1 i⟩

/-- The final RHS oscillator cannot vanish on the repaired validity
zero-set. -/
theorem rhs_ne_phaseOrigin_of_validityEnergyValue_eq_zero
    (I : DQLSystem eqs vars)
    (z : FixedDetectorPolynomialCode.State eqs vars)
    (h :
      NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue I z =
        0) :
    z.rhs ≠ (Controller.phaseOrigin : Controller.PhaseState ℝ) := by
  have hradius :=
    ((validityEnergyValue_eq_zero_iff I z).1 h).2.2.2
  intro hz
  rw [hz] at hradius
  simp [Controller.phaseRadiusSq, Controller.phaseOrigin] at hradius

/-- Algebraic core: a nonzero-scale fourth-root graph over a unit complex
character forces the root itself to be nonzero. -/
theorem gauge_ne_zero_of_fourthRootGraph
    (G χ : ℂ)
    (hχ : ‖χ‖ = 1)
    (hgraph :
      G ^ 4 - (((1 / 256 : ℝ) : ℂ)) * χ = 0) :
    G ≠ 0 := by
  have hχne : χ ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hχ
    norm_num at hχ
  intro hG
  have hproduct :
      (((1 / 256 : ℝ) : ℂ)) * χ = 0 := by
    have hEq := sub_eq_zero.mp hgraph
    rw [hG, zero_pow (by norm_num)] at hEq
    simpa using hEq.symm
  exact hχne
    ((mul_eq_zero.mp hproduct).resolve_left (by norm_num))

/-- Hence every compiled fourth-root gauge is nonzero on the normalized
validity zero-set.  No extra gauge-radius square is required. -/
theorem gauge_ne_zero_of_validityEnergyValue_eq_zero
    (I : DQLSystem eqs vars)
    (z : FixedDetectorPolynomialCode.State eqs vars)
    (h :
      NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue I z =
        0)
    (j : Fin vars) :
    z.base.base.gauge j ≠ 0 := by
  have hz :=
    (validityEnergyValue_eq_zero_iff I z).1 h
  have hphase :
      OnPhaseCircles z.base.base.source.controllers :=
    onPhaseCircles_of_phaseRadiusSq
      z.base.base.source.controllers hz.2.2.1
  have hcharacter :
      ‖characterValue (DetectorJacobiGaugeData.gaugeExponents I j)
          z.base.base.source.controllers‖ = 1 :=
    norm_characterValue_eq_one
      (DetectorJacobiGaugeData.gaugeExponents I j)
      z.base.base.source.controllers hphase
  have hcomplex :
      ∀ a,
        ComplexGaugeFamilyPolynomialCode.residual
          FixedDetectorValidityEnergyCode.thetaGaugeScale
          (gaugeCharacterBaseCode
            (DetectorJacobiGaugeData.gaugeExponents I))
          (rawState z.base.base) a =
          0 := by
    apply
      (ComplexGaugeFamilyPolynomialCode.forall_eval_residualCode_eq_zero_iff
          FixedDetectorValidityEnergyCode.thetaGaugeScale
          (gaugeCharacterBaseCode
            (DetectorJacobiGaugeData.gaugeExponents I))
          (rawState z.base.base)).1
    simpa [DetectorJacobiGaugeData.residualCode,
      gaugeResidualCode] using hz.1.2.1
  have hgraph :
      z.base.base.gauge j ^ 4 -
          (((1 / 256 : ℝ) : ℂ)) *
            characterValue
              (DetectorJacobiGaugeData.gaugeExponents I j)
              z.base.base.source.controllers =
        0 := by
    simpa [ComplexGaugeFamilyPolynomialCode.residual,
      rawState,
      FixedDetectorValidityEnergyCode.thetaGaugeScale] using
      hcomplex j
  exact gauge_ne_zero_of_fourthRootGraph
    (z.base.base.gauge j)
    (characterValue (DetectorJacobiGaugeData.gaugeExponents I j)
      z.base.base.source.controllers)
    hcharacter hgraph

end

end HGAS.NormalizedCorrectedFixedDetectorNormalizationConsequences
