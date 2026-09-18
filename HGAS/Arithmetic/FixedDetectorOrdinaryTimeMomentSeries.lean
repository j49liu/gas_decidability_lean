import HGAS.Arithmetic.FixedDetectorOrdinaryTimeBlochCrosswalk
import Mathlib.Tactic

/-!
# Correct arbitrary-phase fixed-detector moment series

This module restates and proves the three compiled Jacobi moment
identities using
`FixedDetectorOrdinaryTimeBlochCrosswalk.MatchesDetectorClocksRealPi`.
The old clock interface in `FixedDetectorJacobiMomentSeries` accidentally
quantifies over an implicit real variable named `π`; it is not used here.

An arbitrary initial controller phase multiplies the `r=1` and `r=-1`
Fourier rows by their respective initial character values.  These
constants are absorbed coefficientwise.  The mean row `r=0` is unchanged.
-/

namespace HGAS

open Modular
open Clocks
open Clocks.ControllerPhaseProductCharacterCode

noncomputable section

namespace FixedDetectorOrdinaryTimeMomentSeries

open FixedDetectorOrdinaryTimeBlochCrosswalk

variable {eqs vars : ℕ}

/-- Correct `Real.pi` arbitrary-phase form of the `(1,1)` character
crosswalk. -/
theorem jacobiPlusCharacter_mul_gaugedBlochOutput_eq_series_phase
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → Circle)
    (j : Fin vars)
    (p : AffineBlochParameters) (d : ℂ)
    (hclocks :
      MatchesDetectorClocksRealPi p
        (CanonicalFixedDetectorTrajectory.omegaFrequency
          parameters controller j)
        (CanonicalFixedDetectorTrajectory.numberFrequency
          parameters I controller j))
    (ha : p.a0.im = 0)
    (hω :
      CanonicalFixedDetectorTrajectory.omegaFrequency
        parameters controller j ≠ 0)
    (t : ℝ) :
    let ω :=
      CanonicalFixedDetectorTrajectory.omegaFrequency
        parameters controller j
    let N :=
      CanonicalFixedDetectorTrajectory.numberFrequency
        parameters I controller j
    let c :=
      characterValue
        (FixedDetectorMomentCode.jacobiPlusExponent I j)
        (CanonicalFixedDetectorTrajectory.clockPath
          parameters controller phase₀ 0)
    (p.fourthRootGauge d t * (p.jacobiBlochPath t).T1) *
        characterValue
          (FixedDetectorMomentCode.jacobiPlusExponent I j)
          (CanonicalFixedDetectorTrajectory.clockPath
            parameters controller phase₀ t) =
      quadraticMomentSeries
        (fun k => c * p.gaugedBlochCoefficient d k)
        ω (N / ω) p.a0.re 1 t := by
  dsimp only
  rw [FixedDetectorMomentCode.characterValue_jacobiPlusExponent_phase]
  rw [show
      -(CanonicalFixedDetectorTrajectory.omegaFrequency
            parameters controller j +
          CanonicalFixedDetectorTrajectory.numberFrequency
            parameters I controller j) =
        -(CanonicalFixedDetectorTrajectory.omegaFrequency
            parameters controller j) *
          (1 +
            CanonicalFixedDetectorTrajectory.numberFrequency
              parameters I controller j /
            CanonicalFixedDetectorTrajectory.omegaFrequency
              parameters controller j) by
    field_simp [hω]]
  let c : ℂ :=
    characterValue
      (FixedDetectorMomentCode.jacobiPlusExponent I j)
      (CanonicalFixedDetectorTrajectory.clockPath
        parameters controller phase₀ 0)
  have hbase :=
    p.fourthRootGauge_mul_jacobiBlochPath_T1_eq_quadraticMomentSeries
      d ha (hclocks.kappa_ne_zero hω) t
  rw [hclocks.quadraticOmega_eq,
    hclocks.quadraticClockRatio_eq] at hbase
  calc
    (p.fourthRootGauge d t * (p.jacobiBlochPath t).T1) *
          (c *
            HGAS.Analysis.realFrequencyExponential
              (-(CanonicalFixedDetectorTrajectory.omegaFrequency
                    parameters controller j) *
                (1 +
                  CanonicalFixedDetectorTrajectory.numberFrequency
                      parameters I controller j /
                    CanonicalFixedDetectorTrajectory.omegaFrequency
                      parameters controller j)) t) =
        c *
          (HGAS.Analysis.realFrequencyExponential
              (-(CanonicalFixedDetectorTrajectory.omegaFrequency
                    parameters controller j) *
                (1 +
                  CanonicalFixedDetectorTrajectory.numberFrequency
                      parameters I controller j /
                    CanonicalFixedDetectorTrajectory.omegaFrequency
                      parameters controller j)) t *
            (p.fourthRootGauge d t *
              (p.jacobiBlochPath t).T1)) := by ring
    _ =
        c *
          quadraticMomentSeries
            (p.gaugedBlochCoefficient d)
            (CanonicalFixedDetectorTrajectory.omegaFrequency
              parameters controller j)
            (CanonicalFixedDetectorTrajectory.numberFrequency
                parameters I controller j /
              CanonicalFixedDetectorTrajectory.omegaFrequency
                parameters controller j)
            p.a0.re 1 t := by
      rw [hbase]
      rw [quadraticMomentSeries_plus_character]
    _ =
        quadraticMomentSeries
          (fun k => c * p.gaugedBlochCoefficient d k)
          (CanonicalFixedDetectorTrajectory.omegaFrequency
            parameters controller j)
          (CanonicalFixedDetectorTrajectory.numberFrequency
              parameters I controller j /
            CanonicalFixedDetectorTrajectory.omegaFrequency
              parameters controller j)
          p.a0.re 1 t :=
      const_mul_quadraticMomentSeries
        _ _ _ _ _ _ _

/-- Correct `Real.pi` arbitrary-phase form of the `(1,-1)` character
crosswalk. -/
theorem jacobiMinusCharacter_mul_gaugedBlochOutput_eq_series_phase
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → Circle)
    (j : Fin vars)
    (p : AffineBlochParameters) (d : ℂ)
    (hclocks :
      MatchesDetectorClocksRealPi p
        (CanonicalFixedDetectorTrajectory.omegaFrequency
          parameters controller j)
        (CanonicalFixedDetectorTrajectory.numberFrequency
          parameters I controller j))
    (ha : p.a0.im = 0)
    (hω :
      CanonicalFixedDetectorTrajectory.omegaFrequency
        parameters controller j ≠ 0)
    (t : ℝ) :
    let ω :=
      CanonicalFixedDetectorTrajectory.omegaFrequency
        parameters controller j
    let N :=
      CanonicalFixedDetectorTrajectory.numberFrequency
        parameters I controller j
    let c :=
      characterValue
        (FixedDetectorMomentCode.jacobiMinusExponent I j)
        (CanonicalFixedDetectorTrajectory.clockPath
          parameters controller phase₀ 0)
    (p.fourthRootGauge d t * (p.jacobiBlochPath t).T1) *
        characterValue
          (FixedDetectorMomentCode.jacobiMinusExponent I j)
          (CanonicalFixedDetectorTrajectory.clockPath
            parameters controller phase₀ t) =
      quadraticMomentSeries
        (fun k => c * p.gaugedBlochCoefficient d k)
        ω (N / ω) p.a0.re (-1) t := by
  dsimp only
  rw [FixedDetectorMomentCode.characterValue_jacobiMinusExponent_phase]
  rw [show
      -CanonicalFixedDetectorTrajectory.omegaFrequency
            parameters controller j +
          CanonicalFixedDetectorTrajectory.numberFrequency
            parameters I controller j =
        -(CanonicalFixedDetectorTrajectory.omegaFrequency
            parameters controller j) *
          (1 -
            CanonicalFixedDetectorTrajectory.numberFrequency
              parameters I controller j /
            CanonicalFixedDetectorTrajectory.omegaFrequency
              parameters controller j) by
    field_simp [hω]
    ring]
  let c : ℂ :=
    characterValue
      (FixedDetectorMomentCode.jacobiMinusExponent I j)
      (CanonicalFixedDetectorTrajectory.clockPath
        parameters controller phase₀ 0)
  have hbase :=
    p.fourthRootGauge_mul_jacobiBlochPath_T1_eq_quadraticMomentSeries
      d ha (hclocks.kappa_ne_zero hω) t
  rw [hclocks.quadraticOmega_eq,
    hclocks.quadraticClockRatio_eq] at hbase
  calc
    (p.fourthRootGauge d t * (p.jacobiBlochPath t).T1) *
          (c *
            HGAS.Analysis.realFrequencyExponential
              (-(CanonicalFixedDetectorTrajectory.omegaFrequency
                    parameters controller j) *
                (1 -
                  CanonicalFixedDetectorTrajectory.numberFrequency
                      parameters I controller j /
                    CanonicalFixedDetectorTrajectory.omegaFrequency
                      parameters controller j)) t) =
        c *
          (HGAS.Analysis.realFrequencyExponential
              (-(CanonicalFixedDetectorTrajectory.omegaFrequency
                    parameters controller j) *
                (1 -
                  CanonicalFixedDetectorTrajectory.numberFrequency
                      parameters I controller j /
                    CanonicalFixedDetectorTrajectory.omegaFrequency
                      parameters controller j)) t *
            (p.fourthRootGauge d t *
              (p.jacobiBlochPath t).T1)) := by ring
    _ =
        c *
          quadraticMomentSeries
            (p.gaugedBlochCoefficient d)
            (CanonicalFixedDetectorTrajectory.omegaFrequency
              parameters controller j)
            (CanonicalFixedDetectorTrajectory.numberFrequency
                parameters I controller j /
              CanonicalFixedDetectorTrajectory.omegaFrequency
                parameters controller j)
            p.a0.re (-1) t := by
      rw [hbase]
      rw [quadraticMomentSeries_minus_character]
    _ =
        quadraticMomentSeries
          (fun k => c * p.gaugedBlochCoefficient d k)
          (CanonicalFixedDetectorTrajectory.omegaFrequency
            parameters controller j)
          (CanonicalFixedDetectorTrajectory.numberFrequency
              parameters I controller j /
            CanonicalFixedDetectorTrajectory.omegaFrequency
              parameters controller j)
          p.a0.re (-1) t :=
      const_mul_quadraticMomentSeries
        _ _ _ _ _ _ _

/-! ## Evaluation of the three literal polynomial codes -/

theorem evalPair_jacobiMeanCode_eq_quadraticMomentSeries
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → Circle)
    (j : Fin vars)
    (p : AffineBlochParameters) (d : ℂ)
    (hclocks :
      MatchesDetectorClocksRealPi p
        (CanonicalFixedDetectorTrajectory.omegaFrequency
          parameters controller j)
        (CanonicalFixedDetectorTrajectory.numberFrequency
          parameters I controller j))
    (ha : p.a0.im = 0)
    (hω :
      CanonicalFixedDetectorTrajectory.omegaFrequency
        parameters controller j ≠ 0)
    (t : ℝ)
    (z : FixedDetectorPolynomialCode.State eqs vars)
    (hmatch :
      MatchesCompiledGaugedBlochPhaseAt
        parameters controller phase₀ j p d t z) :
    evalPair (FixedDetectorMomentCode.jacobiMeanCode j)
        (FixedDetectorPolynomialCode.point z) =
      quadraticMomentSeries
          (p.gaugedBlochCoefficient d)
          (CanonicalFixedDetectorTrajectory.omegaFrequency
            parameters controller j)
          (CanonicalFixedDetectorTrajectory.numberFrequency
              parameters I controller j /
            CanonicalFixedDetectorTrajectory.omegaFrequency
              parameters controller j)
          p.a0.re 0 t -
        1 := by
  rw [FixedDetectorMomentCode.evalPair_jacobiMeanCode,
    hmatch.output_eq]
  rw [p.fourthRootGauge_mul_jacobiBlochPath_T1_eq_quadraticMomentSeries
    d ha (hclocks.kappa_ne_zero hω)]
  rw [hclocks.quadraticOmega_eq,
    hclocks.quadraticClockRatio_eq]

theorem evalPair_jacobiPlusMeanCode_eq_quadraticMomentSeries_phase
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → Circle)
    (j : Fin vars)
    (p : AffineBlochParameters) (d : ℂ)
    (hclocks :
      MatchesDetectorClocksRealPi p
        (CanonicalFixedDetectorTrajectory.omegaFrequency
          parameters controller j)
        (CanonicalFixedDetectorTrajectory.numberFrequency
          parameters I controller j))
    (ha : p.a0.im = 0)
    (hω :
      CanonicalFixedDetectorTrajectory.omegaFrequency
        parameters controller j ≠ 0)
    (t : ℝ)
    (z : FixedDetectorPolynomialCode.State eqs vars)
    (hmatch :
      MatchesCompiledGaugedBlochPhaseAt
        parameters controller phase₀ j p d t z) :
    let c :=
      characterValue
        (FixedDetectorMomentCode.jacobiPlusExponent I j)
        (CanonicalFixedDetectorTrajectory.clockPath
          parameters controller phase₀ 0)
    evalPair (FixedDetectorMomentCode.jacobiPlusMeanCode I j)
        (FixedDetectorPolynomialCode.point z) =
      quadraticMomentSeries
          (fun k => c * p.gaugedBlochCoefficient d k)
          (CanonicalFixedDetectorTrajectory.omegaFrequency
            parameters controller j)
          (CanonicalFixedDetectorTrajectory.numberFrequency
              parameters I controller j /
            CanonicalFixedDetectorTrajectory.omegaFrequency
              parameters controller j)
          p.a0.re 1 t -
        (1 / 256 : ℚ) := by
  dsimp only
  rw [FixedDetectorMomentCode.evalPair_jacobiPlusMeanCode,
    hmatch.output_eq, hmatch.controllers_eq]
  rw [jacobiPlusCharacter_mul_gaugedBlochOutput_eq_series_phase
    parameters I controller phase₀ j p d hclocks ha hω t]

theorem evalPair_jacobiMinusMeanCode_eq_quadraticMomentSeries_phase
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → Circle)
    (j : Fin vars)
    (p : AffineBlochParameters) (d : ℂ)
    (hclocks :
      MatchesDetectorClocksRealPi p
        (CanonicalFixedDetectorTrajectory.omegaFrequency
          parameters controller j)
        (CanonicalFixedDetectorTrajectory.numberFrequency
          parameters I controller j))
    (ha : p.a0.im = 0)
    (hω :
      CanonicalFixedDetectorTrajectory.omegaFrequency
        parameters controller j ≠ 0)
    (t : ℝ)
    (z : FixedDetectorPolynomialCode.State eqs vars)
    (hmatch :
      MatchesCompiledGaugedBlochPhaseAt
        parameters controller phase₀ j p d t z) :
    let c :=
      characterValue
        (FixedDetectorMomentCode.jacobiMinusExponent I j)
        (CanonicalFixedDetectorTrajectory.clockPath
          parameters controller phase₀ 0)
    evalPair (FixedDetectorMomentCode.jacobiMinusMeanCode I j)
        (FixedDetectorPolynomialCode.point z) =
      quadraticMomentSeries
          (fun k => c * p.gaugedBlochCoefficient d k)
          (CanonicalFixedDetectorTrajectory.omegaFrequency
            parameters controller j)
          (CanonicalFixedDetectorTrajectory.numberFrequency
              parameters I controller j /
            CanonicalFixedDetectorTrajectory.omegaFrequency
              parameters controller j)
          p.a0.re (-1) t -
        (1 / 256 : ℚ) := by
  dsimp only
  rw [FixedDetectorMomentCode.evalPair_jacobiMinusMeanCode,
    hmatch.output_eq, hmatch.controllers_eq]
  rw [jacobiMinusCharacter_mul_gaugedBlochOutput_eq_series_phase
    parameters I controller phase₀ j p d hclocks ha hω t]

end FixedDetectorOrdinaryTimeMomentSeries

end

end HGAS
