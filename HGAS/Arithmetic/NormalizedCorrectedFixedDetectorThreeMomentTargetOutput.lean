import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorThreeMomentSeriesLimits
import HGAS.Modular.AffineBlochQuadraticGeometric
import Mathlib.Tactic

/-!
# From the three corrected moments to a target detector output

This module is the analytic assembly point for one selected detector
column.  It deliberately knows nothing about prime clocks or the
particular canonical theta target.  Its assumptions say only that:

* the physical Bloch seed has an irrational linear/private clock ratio;
* the intended target coefficients are quadratic--geometric; and
* the two initial selector characters cancel the target coefficients at
  indices `1` and `-1`, leaving the compiler's constant `1/256`.

The three corrected moment limits then invoke
`quadraticTrace_eq_target_of_three_moments`.  Finally the normalized
forward-continuation theorem converts the resulting series equality
back into the literal product `gauge * T₁` stored by the detector.
-/

noncomputable section

open Filter Topology

namespace HGAS.NormalizedCorrectedFixedDetectorThreeMomentTargetOutput

open HGAS
open HGAS.Clocks
open HGAS.Modular
open Clocks.ControllerPhaseProductCharacterCode
open NormalizedCorrectedFixedDetectorTwoSidedValidityOrbit
open NormalizedCorrectedFixedDetectorTwoSidedPhysicalMomentAverages
open NormalizedCorrectedFixedDetectorThreeMomentSeriesLimits
open FixedDetectorNormalizedForwardBlochColumn
open FixedDetectorNormalizedForwardClassifiedSeries
open FixedDetectorOrdinaryTimeBlochCrosswalk
open
  NormalizedCorrectedFixedDetectorThreeMomentSeriesLimits.SelectedTwoSidedValidityOrbit

variable {eqs vars : ℕ}
variable
  {u :
    NormalizedCorrectedFixedDetectorCompactSourceCode.CompilerInput
      eqs vars}

namespace SelectedTwoSidedValidityOrbit

variable (O : SelectedTwoSidedValidityOrbit u)

/-- **One-column three-moment target theorem.** -/
theorem gaugedOutput_eq_targetSeries
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (controller :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → Circle)
    (x₀ : Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (j : Fin vars)
    (p : AffineBlochParameters)
    (d : ℂ)
    (t₀ : ℝ)
    (h :
      ClassifiedSeed
        (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
        O.physicalPoint x₀ controller phase₀ j p d t₀)
    (target : ℤ → ℂ)
    (hTarget : IsQuadraticGeometric target)
    (hlinear :
      DetectorCharacterCode.linearCharacter
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u) j ≠ 0)
    (hratio :
      Irrational
        (CanonicalFixedDetectorTrajectory.numberFrequency
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
            (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
            controller j /
          CanonicalFixedDetectorTrajectory.omegaFrequency
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
            controller j))
    (hplusTarget :
      characterValue
            (FixedDetectorMomentCode.jacobiPlusExponent
              (NormalizedCorrectedFixedDetectorCompactSourceCode.system u) j)
            (CanonicalFixedDetectorTrajectory.clockPath
              (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
              controller phase₀ 0) *
          target 1 =
        (1 / 256 : ℂ))
    (hminusTarget :
      characterValue
            (FixedDetectorMomentCode.jacobiMinusExponent
              (NormalizedCorrectedFixedDetectorCompactSourceCode.system u) j)
            (CanonicalFixedDetectorTrajectory.clockPath
              (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
              controller phase₀ 0) *
          target (-1) =
        (1 / 256 : ℂ)) :
    ∀ t : ℝ, 0 ≤ t →
      (FixedDetectorReverseTrajectoryCrosswalk.recoveredState
          O.physicalPoint t).base.base.gauge j *
          ((FixedDetectorReverseTrajectoryCrosswalk.recoveredState
            O.physicalPoint t).base.base.source.linked j).jacobi.T1 =
        quadraticMomentSeries target
          (CanonicalFixedDetectorTrajectory.omegaFrequency
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
            controller j)
          (CanonicalFixedDetectorTrajectory.numberFrequency
              (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
              (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
              controller j /
            CanonicalFixedDetectorTrajectory.omegaFrequency
              (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
              controller j)
          0 0 t := by
  let cPlus : ℂ :=
    characterValue
      (FixedDetectorMomentCode.jacobiPlusExponent
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u) j)
      (CanonicalFixedDetectorTrajectory.clockPath
        (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
        controller phase₀ 0)
  let cMinus : ℂ :=
    characterValue
      (FixedDetectorMomentCode.jacobiMinusExponent
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u) j)
      (CanonicalFixedDetectorTrajectory.clockPath
        (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
        controller phase₀ 0)
  have hcircles :
      OnPhaseCircles
        (CanonicalFixedDetectorTrajectory.clockPath
          (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
          controller phase₀ 0) := by
    exact
      LockedControllerPhaseTrajectory.stateFamily_onPhaseCircles
        (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
        controller phase₀ 0
  have hcPlus : cPlus ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [show ‖cPlus‖ = 1 by
      exact norm_characterValue_eq_one _ _ hcircles]
    norm_num
  have hcMinus : cMinus ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [show ‖cMinus‖ = 1 by
      exact norm_characterValue_eq_one _ _ hcircles]
    norm_num
  have hmean :=
    meanSeries_cesaro_tendsto_one
      O controller phase₀ x₀ j p d t₀ hscale h
  have hplusRaw :=
    plusSeries_cesaro_tendsto_selectorCenter
      O controller phase₀ x₀ j p d t₀ hscale h
  have hminusRaw :=
    minusSeries_cesaro_tendsto_selectorCenter
      O controller phase₀ x₀ j p d t₀ hscale h
  have hselector :
      ((CorrectedJacobiSelectorCentering.selectorCenter
          (NormalizedCorrectedFixedDetectorCompactSourceCode.system u) j :
        ℚ) : ℂ) =
        (1 / 256 : ℂ) := by
    rw [
      CorrectedJacobiSelectorCentering.selectorCenter_eq_of_linearCharacter_ne_zero
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u) j
        hlinear]
    norm_num
  have hplus :
      Tendsto
        (fun n ↦
          HGAS.Analysis.cesaroMeanAt
            (quadraticMomentSeries
              (fun k ↦ cPlus * p.gaugedBlochCoefficient d k)
              (CanonicalFixedDetectorTrajectory.omegaFrequency
                (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
                controller j)
              (CanonicalFixedDetectorTrajectory.numberFrequency
                  (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
                  (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
                  controller j /
                CanonicalFixedDetectorTrajectory.omegaFrequency
                  (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
                  controller j)
              p.a0.re 1)
            (physicalHorizon O n))
        atTop (𝓝 (cPlus * target 1)) := by
    have hvalue : cPlus * target 1 = (1 / 256 : ℂ) := by
      simpa only [cPlus] using hplusTarget
    rw [hvalue]
    rw [hselector] at hplusRaw
    simpa only [cPlus] using hplusRaw
  have hminus :
      Tendsto
        (fun n ↦
          HGAS.Analysis.cesaroMeanAt
            (quadraticMomentSeries
              (fun k ↦ cMinus * p.gaugedBlochCoefficient d k)
              (CanonicalFixedDetectorTrajectory.omegaFrequency
                (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
                controller j)
              (CanonicalFixedDetectorTrajectory.numberFrequency
                  (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
                  (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
                  controller j /
                CanonicalFixedDetectorTrajectory.omegaFrequency
                  (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
                  controller j)
              p.a0.re (-1))
            (physicalHorizon O n))
        atTop (𝓝 (cMinus * target (-1))) := by
    have hvalue : cMinus * target (-1) = (1 / 256 : ℂ) := by
      simpa only [cMinus] using hminusTarget
    rw [hvalue]
    rw [hselector] at hminusRaw
    simpa only [cMinus] using hminusRaw
  have htrace :=
    quadraticTrace_eq_target_of_three_moments
      (p.gaugedBlochCoefficient d) target
      (CanonicalFixedDetectorTrajectory.omegaFrequency
        (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
        controller j)
      (CanonicalFixedDetectorTrajectory.numberFrequency
          (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
          (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
          controller j /
        CanonicalFixedDetectorTrajectory.omegaFrequency
          (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
          controller j)
      p.a0.re
      h.omega_ne_zero hratio
      (p.summable_norm_gaugedBlochCoefficient d)
      (fun l ↦ p.gaugedBlochCoefficient_translate_isScaledQuadraticGeometric d l)
      (fun l ↦
        p.gaugedBlochCoefficient_reflectTranslate_isScaledQuadraticGeometric d l)
      hTarget cPlus cMinus hcPlus hcMinus
      (physicalHorizon_tendsto_atTop O)
      hmean hplus hminus
  intro t ht
  rw [output_eqOn_Ici
    (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
    (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
    O.physicalPoint x₀ controller phase₀ j p d
    h.normalized t ht]
  rw [p.fourthRootGauge_mul_jacobiBlochPath_T1_eq_quadraticMomentSeries
    d
    (a0_im_eq_zero
      (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
      (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
      O.physicalPoint x₀ controller phase₀ j p d t₀ h)
    (h.normalized.clocks.kappa_ne_zero h.omega_ne_zero) t]
  rw [h.normalized.clocks.quadraticOmega_eq,
    h.normalized.clocks.quadraticClockRatio_eq]
  exact htrace t

end SelectedTwoSidedValidityOrbit

end HGAS.NormalizedCorrectedFixedDetectorThreeMomentTargetOutput
