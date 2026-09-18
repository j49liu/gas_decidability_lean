import HGAS.Arithmetic.CorrectedFixedDetectorMomentCode
import HGAS.Arithmetic.FixedDetectorOrdinaryTimeMomentSeries
import Mathlib.Tactic

/-!
# Corrected ordinary-time Jacobi moment series

The classified gauged Bloch series is unchanged by the selector
zero-mode correction.  Only the constant subtracted from the two twisted
rows changes from the unconditional `1/256` to
`CorrectedJacobiSelectorCentering.selectorCenter I j`.
-/

namespace HGAS

open Modular
open Clocks
open Clocks.ControllerPhaseProductCharacterCode

noncomputable section

namespace CorrectedFixedDetectorOrdinaryTimeMomentSeries

open FixedDetectorOrdinaryTimeBlochCrosswalk
open FixedDetectorOrdinaryTimeMomentSeries

variable {eqs vars : ℕ}

/-- Corrected `(1,1)` row with arbitrary initial clock phase. -/
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
    evalPair (CorrectedFixedDetectorMomentCode.jacobiPlusMeanCode I j)
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
        CorrectedJacobiSelectorCentering.selectorCenter I j := by
  dsimp only
  rw [CorrectedFixedDetectorMomentCode.evalPair_jacobiPlusMeanCode,
    hmatch.output_eq, hmatch.controllers_eq]
  rw [jacobiPlusCharacter_mul_gaugedBlochOutput_eq_series_phase
    parameters I controller phase₀ j p d hclocks ha hω t]

/-- Corrected `(1,-1)` row with arbitrary initial clock phase. -/
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
    evalPair (CorrectedFixedDetectorMomentCode.jacobiMinusMeanCode I j)
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
        CorrectedJacobiSelectorCentering.selectorCenter I j := by
  dsimp only
  rw [CorrectedFixedDetectorMomentCode.evalPair_jacobiMinusMeanCode,
    hmatch.output_eq, hmatch.controllers_eq]
  rw [jacobiMinusCharacter_mul_gaugedBlochOutput_eq_series_phase
    parameters I controller phase₀ j p d hclocks ha hω t]

end CorrectedFixedDetectorOrdinaryTimeMomentSeries

end

end HGAS
