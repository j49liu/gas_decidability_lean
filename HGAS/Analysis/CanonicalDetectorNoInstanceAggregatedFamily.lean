import HGAS.Analysis.CanonicalSelectorMomentAggregatedFamilies
import HGAS.Arithmetic.CanonicalFixedDetectorFundamentalPhase
import HGAS.Arithmetic.CorrectedCanonicalFixedDetectorMomentFourierCrosswalk
import Mathlib.Tactic

/-!
# The supported detector Fourier family on a no-instance

The seven selector moments are centered by construction.  The final
arithmetic detector is different: its constant coefficient is precisely
the weighted sum of integer solutions of the input DQL system.  Thus, on
a no-instance, the *unmodified* detector series is already centered.

This file packages that observation in the same reusable
`RawCenteredFamily` interface used for the selector moments.  It also
records:

* absolute and radical-height-weighted summability at the literal
  compiler parameters `lambda = 1/256` and `eta = 1/2`;
* collection of repeated flattened exponents and removal of zero
  coefficients; and
* exact transport from the arithmetic fourth-power phase torus to the
  fundamental physical clock torus.

No coefficient is changed in this construction.  The only hypothesis is
that the DQL instance has no integer solution.
-/

noncomputable section

open Function

namespace HGAS.Analysis.CanonicalDetectorNoInstanceAggregatedFamily

open HGAS
open HGAS.Clocks
open HGAS.Analysis.CanonicalSelectorMomentAggregatedFamilies

variable {eqs vars : ℕ}

/-- The literal theta parameter represented by the fourth-root gauge. -/
abbrev thetaParameter : ℝ := 1 / 256

/-- The literal Poisson parameter represented by the reciprocal blocks. -/
abbrev poissonParameter : ℝ := 1 / 2

/-- On a DQL no-instance, every raw detector term with zero exponent is
absent: such an index would itself contain an integer solution. -/
theorem aggregate_detectorCoefficient_zero_of_not_solvable
    (I : DQLSystem eqs vars)
    (hnot : ¬ I.Solvable) :
    aggregateFourierCoefficient
        (detectorCoefficient thetaParameter poissonParameter)
        (detectorExponent I) 0 = 0 := by
  classical
  rw [aggregateFourierCoefficient_eq_tsum_ite]
  have hterms :
      (fun p : DetectorIndex vars ↦
        if detectorExponent I p = 0 then
          detectorCoefficient thetaParameter poissonParameter p
        else 0) =
      fun _ ↦ 0 := by
    funext p
    have hp : detectorExponent I p ≠ 0 := by
      intro hzero
      have hsatisfies :
          I.Satisfies p.1 ∧
            p.2 = fun j ↦ p.1 j ^ 2 :=
        (detectorExponent_eq_zero_iff I p.1 p.2).1 hzero
      exact hnot ⟨p.1, hsatisfies.1⟩
    simp [hp]
  rw [hterms]
  simp

/-- Raw centered detector family at the exact compiler normalization.
The family depends on the proof that the instance is unsolvable only
through its zero-mode certificate. -/
def detector
    (I : DQLSystem eqs vars)
    (hnot : ¬ I.Solvable) :
    RawCenteredFamily eqs vars where
  Index := DetectorIndex vars
  coefficient :=
    detectorCoefficient thetaParameter poissonParameter
  exponent := detectorExponent I
  zeroMode :=
    aggregate_detectorCoefficient_zero_of_not_solvable I hnot
  summable_height := by
    intro radicand heightPower
    exact
      summable_norm_detectorCoefficient_mul_radicalHeight_pow_automatic
        (lambda := thetaParameter)
        (eta := poissonParameter)
        (q := (1 / 2 : ℝ))
        (by norm_num [thetaParameter])
        (by norm_num [thetaParameter])
        (by norm_num [poissonParameter])
        (by norm_num [poissonParameter])
        (by norm_num)
        (by norm_num)
        radicand I heightPower

/-- Before support aggregation, the flattened detector series on the
fundamental clock path is exactly the original expanded detector on the
arithmetic fourth-power phase path. -/
theorem torusFourierSeries_flat_detector_fundamentalPhasePath
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (I : DQLSystem eqs vars)
    (t : ℝ) :
    torusFourierSeries
        (detectorCoefficient thetaParameter poissonParameter)
        (fun p ↦
          DetectorCharacterCode.flattenCharacter
            (detectorExponent I p))
        (CanonicalFixedDetectorFundamentalPhase.fundamentalPhasePath
          parameters controller t) =
      expandedDetector thetaParameter poissonParameter I
        (CanonicalFixedDetectorFourierCrosswalk.detectorPhasePath
          parameters controller t) := by
  unfold torusFourierSeries expandedDetector
  apply tsum_congr
  intro p
  unfold torusSeriesTerm
  rw [
    CanonicalFixedDetectorFundamentalPhase.mFourier_flattenCharacter_fundamentalPhasePath]

/-- The canonical supported no-instance family represents the literal
expanded detector along the fundamental physical clock orbit. -/
theorem torusFourierSeries_supported_detector_fundamentalPhasePath
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (I : DQLSystem eqs vars)
    (hnot : ¬ I.Solvable)
    (t : ℝ) :
    torusFourierSeries
        (detector I hnot).supportedCoefficient
        (detector I hnot).supportedExponent
        (CanonicalFixedDetectorFundamentalPhase.fundamentalPhasePath
          parameters controller t) =
      expandedDetector thetaParameter poissonParameter I
        (CanonicalFixedDetectorFourierCrosswalk.detectorPhasePath
          parameters controller t) := by
  rw [(detector I hnot).torusFourierSeries_supported
    (fun _ : Fin (vars + eqs) ↦ 2)]
  exact
    torusFourierSeries_flat_detector_fundamentalPhasePath
      parameters controller I t

/-- Consequently the supported family is exactly the complex detector
coordinate stored by the canonical polynomial state. -/
theorem evalPair_detectorCode_canonical_eq_supportedSeries
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (I : DQLSystem eqs vars)
    (hnot : ¬ I.Solvable)
    (t : ℝ) :
    ControllerPhaseProductCharacterCode.evalPair
        (FixedDetectorPolynomialCode.detectorCode
          (eqs := eqs) (vars := vars))
        (FixedDetectorPolynomialCode.point
          (CorrectedCanonicalFixedDetectorMomentFourierCrosswalk.canonicalState
            parameters I controller t)) =
      torusFourierSeries
        (detector I hnot).supportedCoefficient
        (detector I hnot).supportedExponent
        (CanonicalFixedDetectorFundamentalPhase.fundamentalPhasePath
          parameters controller t) := by
  unfold
    CorrectedCanonicalFixedDetectorMomentFourierCrosswalk.canonicalState
  rw [
    CanonicalFixedDetectorFourierCrosswalk.evalPair_detectorCode_canonical_eq_expandedDetector]
  exact
    (torusFourierSeries_supported_detector_fundamentalPhasePath
      parameters controller I hnot t).symm

end HGAS.Analysis.CanonicalDetectorNoInstanceAggregatedFamily
