import HGAS.Arithmetic.CorrectedFixedDetectorDriftCode
import HGAS.Arithmetic.FixedDetectorTrajectoryCrosswalk
import Mathlib.Tactic

/-!
# The zero-radius obstruction in the final detector oscillator

The fixed detector appends a complex oscillator `R` and multiplies the
arithmetic detector by `R`.  In the present all-affine compiler, the two
real coordinates of `R` are not constrained to lie on the unit circle.
Consequently `R = 0` is an invariant state of the oscillator.

This file records the obstruction at exactly the interfaces used by the
corrected detector:

* replacing `R` by zero leaves the base state, validity energy, and every
  corrected selector moment unchanged;
* it makes the arithmetic detector identically zero;
* the replacement commutes with the complete polynomial vector field; and
* every base integral curve therefore lifts to a complete integral curve
  with identically zero detector.

No dynamical or measure-theoretic hypothesis is used.  These are literal
identities of the emitted polynomial system.
-/

namespace HGAS.CorrectedFixedDetectorRHSZeroObstruction

open HGAS
open HGAS.Clocks

noncomputable section

variable {eqs vars : ℕ}

/-- Replace only the final RHS oscillator by its affine origin. -/
def eraseRHS
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    FixedDetectorPolynomialCode.State eqs vars where
  base := z.base
  rhs := Controller.phaseOrigin

@[simp]
theorem eraseRHS_base
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    (eraseRHS z).base = z.base :=
  rfl

@[simp]
theorem eraseRHS_rhs
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    (eraseRHS z).rhs = Controller.phaseOrigin :=
  rfl

/-- The validity sum of squares cannot detect the radius of the appended
RHS oscillator. -/
@[simp]
theorem validityEnergyValue_eraseRHS
    (I : DQLSystem eqs vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    CorrectedFixedDetectorDriftCode.validityEnergyValue I (eraseRHS z) =
      CorrectedFixedDetectorDriftCode.validityEnergyValue I z :=
  rfl

/-- None of the seven corrected complex selector moments can detect the
radius of the appended RHS oscillator. -/
@[simp]
theorem localMomentValue_eraseRHS
    (I : DQLSystem eqs vars)
    (j : Fin vars)
    (r : Fin CorrectedFixedDetectorMomentCode.localMomentCount)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    CorrectedFixedDetectorMomentCode.localMomentValue I j (eraseRHS z) r =
      CorrectedFixedDetectorMomentCode.localMomentValue I j z r := by
  fin_cases r <;>
    rfl

@[simp]
theorem momentValue_eraseRHS
    (I : DQLSystem eqs vars)
    (k : Fin (CorrectedFixedDetectorMomentCode.momentCount vars))
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    CorrectedFixedDetectorMomentCode.momentValue I (eraseRHS z) k =
      CorrectedFixedDetectorMomentCode.momentValue I z k := by
  simp [CorrectedFixedDetectorMomentCode.momentValue]

@[simp]
theorem scalarMomentValue_eraseRHS
    (I : DQLSystem eqs vars)
    (k : Fin (CorrectedFixedDetectorMomentCode.scalarMomentCount vars))
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    CorrectedFixedDetectorMomentCode.scalarMomentValue I (eraseRHS z) k =
      CorrectedFixedDetectorMomentCode.scalarMomentValue I z k := by
  simp [CorrectedFixedDetectorMomentCode.scalarMomentValue]

/-- At oscillator radius zero, the complete arithmetic detector is zero,
independently of the DQL instance and of every base coordinate. -/
@[simp]
theorem detectorValue_eraseRHS
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    CorrectedFixedDetectorDriftCode.detectorValue (eraseRHS z) = 0 := by
  change
    (0 : ℂ) *
        ∏ j : Fin vars,
          ((z.base.base.gauge j *
              (z.base.base.source.linked j).jacobi.T1) *
            (((3 / 4 : ℝ) : ℂ) *
              z.base.reciprocal
                (DetectorPoissonReciprocalCode.positiveIndex j) *
              z.base.reciprocal
                (DetectorPoissonReciprocalCode.negativeIndex j))) =
      0
  simp

@[simp]
theorem detectorDriftValue_eraseRHS
    (I : DQLSystem eqs vars)
    (b : Fin 2)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    CorrectedFixedDetectorDriftCode.driftValue I (eraseRHS z)
        (CorrectedFixedDetectorDriftCode.detectorIndex b) =
      0 := by
  fin_cases b <;>
    simp [CorrectedFixedDetectorDriftCode.driftValue,
      CorrectedFixedDetectorDriftCode.detectorIndex,
      FixedDetectorDriftCode.detectorIndex]

/-- The zero replacement commutes with the complete semantic polynomial
vector field.  Thus the zero-radius stratum is invariant, not merely a
pointwise zero set of the observable. -/
@[simp]
theorem vectorField_eraseRHS
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    FixedDetectorPolynomialCode.vectorField parameters I (eraseRHS z) =
      eraseRHS
        (FixedDetectorPolynomialCode.vectorField parameters I z) := by
  apply FixedDetectorPolynomialCode.State.ext
  · rfl
  · ext <;>
      simp [eraseRHS, FixedDetectorPolynomialCode.vectorField,
        Clocks.RHSOscillatorPolynomialCode.oscillatorField,
        Controller.phaseOrigin, Controller.phaseField]

/-- The identically zero phase is a solution of the appended oscillator
over an arbitrary base path and arbitrary time-dependent frequency read
from that path. -/
theorem phaseOrigin_isOscillatorTrajectory
    {n q : ℕ}
    (a : Fin q → RationalCode)
    (ν : Fin q → PolynomialCode n)
    (x : ℝ → Fin n → ℝ) :
    Clocks.RHSOscillatorPolynomialCode.IsOscillatorTrajectory
      a ν x (fun _ ↦ (Controller.phaseOrigin :
        Controller.PhaseState ℝ)) where
  c t := by
    simpa [Clocks.RHSOscillatorPolynomialCode.oscillatorField,
      Controller.phaseOrigin, Controller.phaseField] using
      (hasDerivAt_const t (0 : ℝ))
  d t := by
    simpa [Clocks.RHSOscillatorPolynomialCode.oscillatorField,
      Controller.phaseOrigin, Controller.phaseField] using
      (hasDerivAt_const t (0 : ℝ))

/-- Adjoin the zero RHS oscillator to a Poisson-completed detector base
path. -/
def zeroRHSExtension
    (z : ℝ → DetectorPoissonReciprocalCode.State eqs vars)
    (t : ℝ) :
    FixedDetectorPolynomialCode.State eqs vars where
  base := z t
  rhs := Controller.phaseOrigin

@[simp]
theorem zeroRHSExtension_base
    (z : ℝ → DetectorPoissonReciprocalCode.State eqs vars)
    (t : ℝ) :
    (zeroRHSExtension z t).base = z t :=
  rfl

@[simp]
theorem zeroRHSExtension_rhs
    (z : ℝ → DetectorPoissonReciprocalCode.State eqs vars)
    (t : ℝ) :
    (zeroRHSExtension z t).rhs =
      (Controller.phaseOrigin : Controller.PhaseState ℝ) :=
  rfl

/-- Every integral curve of the detector base has a complete
fixed-detector lift on the invariant stratum `R = 0`. -/
theorem zeroRHSExtension_point_isIntegralCurve
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (z : ℝ → DetectorPoissonReciprocalCode.State eqs vars)
    (hbase :
      IsIntegralCurve
        (fun t ↦ DetectorPoissonReciprocalCode.point (z t))
        (fun _ x ↦
          PolynomialFieldCode.realize
            (DetectorPoissonReciprocalCode.fieldCode parameters I) x)) :
    IsIntegralCurve
      (fun t ↦
        FixedDetectorPolynomialCode.point (zeroRHSExtension z t))
      (fun _ x ↦
        PolynomialFieldCode.realize
          (FixedDetectorPolynomialCode.fieldCode parameters I) x) := by
  apply FixedDetectorPolynomialCode.point_isIntegralCurve
      parameters I (zeroRHSExtension z)
  · simpa only [zeroRHSExtension_base] using hbase
  · simpa only [zeroRHSExtension_base, zeroRHSExtension_rhs] using
      (phaseOrigin_isOscillatorTrajectory
        (FixedDetectorPolynomialCode.rhsWeightCode I)
        (FixedDetectorPolynomialCode.equationFrequencyCode parameters)
        (fun t ↦ DetectorPoissonReciprocalCode.point (z t)))

/-- Along the preceding complete trajectory the complex arithmetic
detector vanishes at every time. -/
@[simp]
theorem detectorValue_zeroRHSExtension
    (z : ℝ → DetectorPoissonReciprocalCode.State eqs vars)
    (t : ℝ) :
    CorrectedFixedDetectorDriftCode.detectorValue
        (zeroRHSExtension z t) =
      0 := by
  change
    (0 : ℂ) *
        ∏ j : Fin vars,
          (((z t).base.gauge j *
              ((z t).base.source.linked j).jacobi.T1) *
            (((3 / 4 : ℝ) : ℂ) *
              (z t).reciprocal
                (DetectorPoissonReciprocalCode.positiveIndex j) *
              (z t).reciprocal
                (DetectorPoissonReciprocalCode.negativeIndex j))) =
      0
  simp

end

end HGAS.CorrectedFixedDetectorRHSZeroObstruction
