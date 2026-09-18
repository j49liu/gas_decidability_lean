import HGAS.Arithmetic.CanonicalFixedDetectorFourierCrosswalk
import HGAS.Clocks.ObservedTimeChangedControllerPhaseHaar
import HGAS.Analysis.TorusCohomologicalPrimitive
import Mathlib.Tactic

/-!
# Fundamental clock phase of the canonical fixed detector

`CanonicalFixedDetectorFourierCrosswalk.detectorPhasePath` uses the
arithmetic fourth-power clocks indexed by
`DetectorPhase eqs vars = Fin vars ⊕ Fin eqs`.  The polynomial compiler,
however, literally stores the fundamental circles indexed by
`Fin (vars + eqs)`.  This file records the exact relation.

The fundamental phase rotates in turns with frequency

```text
  angularVelocity / (2π).
```

Flattening an arithmetic character reindexes it and multiplies it by
four.  Its value on the fundamental phase is therefore exactly its value
on the fourth-power detector phase.  For prime controller parameters,
the frequency vector is the common scale `1/(2π)` times a signed
prime-square-root vector.
-/

noncomputable section

namespace HGAS.CanonicalFixedDetectorFundamentalPhase

open HGAS
open HGAS.Clocks

variable {eqs vars : ℕ}

/-- Fundamental physical clock frequencies, measured in turns rather
than radians. -/
def turnsFrequency
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ) :
    Fin (vars + eqs) → ℝ :=
  fun i ↦
    LockedControllerPhaseTrajectory.angularVelocity
      parameters controller i / (2 * Real.pi)

/-- Fundamental all-one phase orbit as an additive torus translation
from zero. -/
def fundamentalPhasePath
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ) :
    UnitAddTorus (Fin (vars + eqs)) :=
  RadicalClock.torusDisplacement
    (turnsFrequency parameters controller) t

@[simp]
theorem fundamentalPhasePath_apply
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ) (i : Fin (vars + eqs)) :
    fundamentalPhasePath parameters controller t i =
      ((LockedControllerPhaseTrajectory.angularVelocity
          parameters controller i * t / (2 * Real.pi) : ℝ) :
        UnitAddCircle) := by
  unfold fundamentalPhasePath RadicalClock.torusDisplacement
    turnsFrequency
  congr 1
  ring

/-- The path is the translation flow orbit of zero. -/
theorem fundamentalPhasePath_eq_flow_zero
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ) :
    fundamentalPhasePath parameters controller t =
      RadicalClock.torusTranslationFlow
        (turnsFrequency parameters controller) t 0 := by
  simp [fundamentalPhasePath,
    RadicalClock.torusTranslationFlow_apply]

/-- A flattened arithmetic character on the fundamental phase is the
same character on the fourth-power detector phase. -/
theorem mFourier_flattenCharacter_fundamentalPhasePath
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (a : DetectorPhase eqs vars → ℤ)
    (t : ℝ) :
    UnitAddTorus.mFourier
        (DetectorCharacterCode.flattenCharacter a)
        (fundamentalPhasePath parameters controller t) =
      UnitAddTorus.mFourier a
        (CanonicalFixedDetectorFourierCrosswalk.detectorPhasePath
          parameters controller t) := by
  rw [CanonicalFixedDetectorFourierCrosswalk.mFourier_detectorPhasePath]
  unfold fundamentalPhasePath
  rw [RadicalClock.mFourier_torusDisplacement]
  have hpair :
      RadicalClock.frequencyPairing
          (DetectorCharacterCode.flattenCharacter a)
          (turnsFrequency parameters controller) =
        LockedControllerPhaseTrajectory.characterFrequency
            parameters controller
            (DetectorCharacterCode.flattenCharacter a) /
          (2 * Real.pi) := by
    unfold RadicalClock.frequencyPairing turnsFrequency
      LockedControllerPhaseTrajectory.characterFrequency
    calc
      (∑ i,
          (DetectorCharacterCode.flattenCharacter a i : ℝ) *
            (LockedControllerPhaseTrajectory.angularVelocity
                parameters controller i /
              (2 * Real.pi))) =
          ∑ i,
            ((DetectorCharacterCode.flattenCharacter a i : ℝ) *
                LockedControllerPhaseTrajectory.angularVelocity
                  parameters controller i) /
              (2 * Real.pi) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ =
          (∑ i,
              (DetectorCharacterCode.flattenCharacter a i : ℝ) *
                LockedControllerPhaseTrajectory.angularVelocity
                  parameters controller i) /
            (2 * Real.pi) := by
        rw [Finset.sum_div]
  rw [hpair]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

/-- Every literal fundamental physical-clock character is its additive
torus Fourier character on `fundamentalPhasePath`.  Unlike the preceding
theorem, this statement permits exponents not divisible by four (notably
the `ζ⁻²` twist in the `p₂` selector). -/
theorem characterValue_onePhase_eq_mFourier_fundamental
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (a : Fin (vars + eqs) → ℤ)
    (t : ℝ) :
    ControllerPhaseProductCharacterCode.characterValue a
        (CanonicalFixedDetectorTrajectory.clockPath
          parameters controller
          LockedControllerPhaseTrajectory.onePhase t) =
      UnitAddTorus.mFourier a
        (fundamentalPhasePath parameters controller t) := by
  unfold CanonicalFixedDetectorTrajectory.clockPath
  rw [LockedControllerPhaseTrajectory.characterValue_onePhase]
  unfold fundamentalPhasePath
  rw [RadicalClock.mFourier_torusDisplacement]
  have hpair :
      RadicalClock.frequencyPairing a
          (turnsFrequency parameters controller) =
        LockedControllerPhaseTrajectory.characterFrequency
            parameters controller a /
          (2 * Real.pi) := by
    unfold RadicalClock.frequencyPairing turnsFrequency
      LockedControllerPhaseTrajectory.characterFrequency
    calc
      (∑ i,
          (a i : ℝ) *
            (LockedControllerPhaseTrajectory.angularVelocity
                parameters controller i /
              (2 * Real.pi))) =
          ∑ i,
            ((a i : ℝ) *
                LockedControllerPhaseTrajectory.angularVelocity
                  parameters controller i) /
              (2 * Real.pi) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ =
          (∑ i,
              (a i : ℝ) *
                LockedControllerPhaseTrajectory.angularVelocity
                  parameters controller i) /
            (2 * Real.pi) := by
        rw [Finset.sum_div]
  rw [hpair]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

/-- The preceding character identity transports an arbitrary raw Fourier
series term by term. -/
theorem torusFourierSeries_flatten_fundamentalPhasePath
    {ι : Type*}
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (coefficient : ι → ℂ)
    (exponent : ι → DetectorPhase eqs vars → ℤ)
    (t : ℝ) :
    Analysis.torusFourierSeries coefficient
        (fun i ↦ DetectorCharacterCode.flattenCharacter (exponent i))
        (fundamentalPhasePath parameters controller t) =
      Analysis.torusFourierSeries coefficient exponent
        (CanonicalFixedDetectorFourierCrosswalk.detectorPhasePath
          parameters controller t) := by
  unfold Analysis.torusFourierSeries Analysis.torusSeriesTerm
  apply tsum_congr
  intro i
  rw [mFourier_flattenCharacter_fundamentalPhasePath]

/-- Exact character derivative on the fundamental translation orbit. -/
theorem mFourier_fundamentalPhasePath_hasDerivAt
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (a : Fin (vars + eqs) → ℤ)
    (t : ℝ) :
    HasDerivAt
      (fun s ↦
        UnitAddTorus.mFourier a
          (fundamentalPhasePath parameters controller s))
      (Analysis.torusAngularFrequency a
          (turnsFrequency parameters controller) *
        UnitAddTorus.mFourier a
          (fundamentalPhasePath parameters controller t)) t := by
  simpa only [fundamentalPhasePath_eq_flow_zero] using
    (Analysis.mFourier_torusTranslationFlow_hasDerivAt
      a (turnsFrequency parameters controller)
      (0 : UnitAddTorus (Fin (vars + eqs))) t)

/-- Prime rational codes decode the angular velocity to the literal
locked-controller frequency. -/
theorem angularVelocity_primeClockCodes
    (p : Fin (vars + eqs) → ℕ)
    (controller :
      Fin (vars + eqs) → Controller.ControllerState ℝ)
    (i : Fin (vars + eqs)) :
    LockedControllerPhaseTrajectory.angularVelocity
        (ObservedTimeChangedControllerPhaseHaar.primeClockCodes p)
        controller i =
      Controller.lockedFrequency (p i : ℝ) (controller i) := by
  simp [LockedControllerPhaseTrajectory.angularVelocity,
    Controller.lockedFrequency,
    ObservedTimeChangedControllerPhaseHaar.decode_primeClockCodes]

/-- If the locked controller frequencies are the signed radical vector,
then the fundamental turns frequencies are exactly the standard common
rescaling used by the small-divisor theorem. -/
theorem turnsFrequency_primeClockCodes_eq_scaledRadical
    (p : Fin (vars + eqs) → ℕ)
    (controller :
      Fin (vars + eqs) → Controller.ControllerState ℝ)
    (sign : Fin (vars + eqs) → ℤ)
    (hfrequency :
      (fun i ↦ Controller.lockedFrequency
        (p i : ℝ) (controller i)) =
        RadicalIndependence.signedPrimeSqrtFrequency p sign) :
    turnsFrequency
        (ObservedTimeChangedControllerPhaseHaar.primeClockCodes p)
        controller =
      ScaledRadicalClock.scaledSignedPrimeSqrtFrequency
        (1 / (2 * Real.pi)) p sign := by
  funext i
  rw [turnsFrequency, angularVelocity_primeClockCodes]
  have hi := congrFun hfrequency i
  rw [hi]
  unfold ScaledRadicalClock.scaledSignedPrimeSqrtFrequency
  ring

end HGAS.CanonicalFixedDetectorFundamentalPhase
