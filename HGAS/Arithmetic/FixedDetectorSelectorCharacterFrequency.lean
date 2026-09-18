import HGAS.Arithmetic.FixedDetectorMomentCode
import HGAS.Arithmetic.FixedDetectorPrivateFrequency
import Mathlib.Tactic

/-!
# Frequencies of the two private selector characters

The corrected detector uses two twists from the private phase clock of a
column:

* the inverse private character in the first `Y` moment; and
* the exponent `-2` in the `p₂` root moment.

Because the private character itself is the fourth power of the
fundamental phase, their frequencies are respectively `-ω_j` and
`-ω_j/2`.  This file records those two finite-sum identities independently
of any trajectory.
-/

namespace HGAS.FixedDetectorSelectorCharacterFrequency

open HGAS
open HGAS.Clocks
open ControllerPhaseProductCharacterCode

noncomputable section

variable {eqs vars : ℕ}

/-- The first-harmonic selector character has the negative private
frequency. -/
theorem characterFrequency_unaryFirstHarmonicExponent
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (j : Fin vars) :
    LockedControllerPhaseTrajectory.characterFrequency
        parameters controller
        (FixedDetectorMomentCode.unaryFirstHarmonicExponent j) =
      -CanonicalFixedDetectorTrajectory.omegaFrequency
        parameters controller j := by
  rw [
    HGAS.CanonicalFixedDetectorFourierCrosswalk.omegaFrequency_eq_characterFrequency]
  unfold
    LockedControllerPhaseTrajectory.characterFrequency
    FixedDetectorMomentCode.unaryFirstHarmonicExponent
    FixedDetectorMomentCode.privateExponent
  simp only [Int.cast_neg]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The root-half selector character has half the negative private
frequency. -/
theorem characterFrequency_rootHalfExponent
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (j : Fin vars) :
    LockedControllerPhaseTrajectory.characterFrequency
        parameters controller
        (FixedDetectorMomentCode.rootHalfExponent j) =
      -CanonicalFixedDetectorTrajectory.omegaFrequency
          parameters controller j / 2 := by
  have hprivate :=
    HGAS.FixedDetectorPrivateFrequency.omegaFrequency_eq_four_mul_privateAngularVelocity
        parameters controller j
  unfold LockedControllerPhaseTrajectory.characterFrequency
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp [FixedDetectorMomentCode.rootHalfExponent,
    HGAS.FixedDetectorPrivateFrequency.privateClockIndex] at *
  linarith

end

end HGAS.FixedDetectorSelectorCharacterFrequency
