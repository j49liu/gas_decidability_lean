import HGAS.Arithmetic.NormalizedCorrectedEffectiveCompilerInput
import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorSelectedFactorization
import HGAS.Clocks.ScaledRadicalClock
import Mathlib.Tactic

/-!
# Nonresonance of the effective selected detector phase

The effective compiler assigns a distinct prime radicand to every
fundamental controller.  Validity normalization puts every selected
controller on its unit circle, while controller locking makes it an
equilibrium.  Hence its signed angular velocity is one of the two square
roots of that prime.

This file transfers that fact through the fourth-power clock convention
and the reindexing from `Fin (vars + eqs)` to
`DetectorPhase eqs vars`.  The resulting actual detector frequency has
no nontrivial integer character.  This is the exact hypothesis required
by arbitrary-horizon Fourier Cesàro convergence.
-/

namespace
  HGAS.NormalizedCorrectedEffectiveSelectedDetectorPhase

open HGAS
open HGAS.Clocks
open NormalizedCorrectedEffectiveCompilerInput
open NormalizedCorrectedFixedDetectorTwoSidedValidityOrbit
open NormalizedCorrectedFixedDetectorBidirectionalValidityOrbit
open NormalizedCorrectedFixedDetectorTwoSidedStructuredOrbit
open NormalizedCorrectedFixedDetectorTwoSidedControllerLocking
open NormalizedCorrectedFixedDetectorColumnTrajectory
open NormalizedCorrectedFixedDetectorSelectedFactorization
open CanonicalFixedDetectorFundamentalPhase
open
  NormalizedCorrectedFixedDetectorTwoSidedStructuredOrbit.SelectedTwoSidedValidityOrbit
open
  NormalizedCorrectedFixedDetectorTwoSidedControllerLocking.SelectedTwoSidedValidityOrbit
open
  NormalizedCorrectedFixedDetectorColumnTrajectory.SelectedTwoSidedValidityOrbit
open
  NormalizedCorrectedFixedDetectorSelectedFactorization.SelectedBidirectionalValidityOrbit

noncomputable section

variable {eqs vars : ℕ}
variable (D : DQLSystem eqs vars)

/-- Prime radicand in arithmetic detector-phase indexing. -/
def detectorPrimeRadicand
    (_D : DQLSystem eqs vars)
    (phase : DetectorPhase eqs vars) : ℕ :=
  primeRadicand (vars + eqs) (finSumFinEquiv phase)

theorem detectorPrimeRadicand_prime :
    ∀ phase, (detectorPrimeRadicand D phase).Prime := by
  intro phase
  exact primeRadicand_prime (vars + eqs) (finSumFinEquiv phase)

theorem detectorPrimeRadicand_injective :
    Function.Injective (detectorPrimeRadicand D) := by
  exact
    (primeRadicand_injective (vars + eqs)).comp
      finSumFinEquiv.injective

namespace SelectedBidirectionalValidityOrbit

variable
  (O :
    SelectedBidirectionalValidityOrbit
      (NormalizedCorrectedEffectiveCompilerInput.compilerInput D))

private abbrev B :=
  O.toSelectedTwoSidedValidityOrbit

/-- The effective selected controllers have unit radius and are locked
at the prime-controller equilibria. -/
theorem exists_fundamentalControllerSign :
    ∃ sign : Fin (vars + eqs) → ℤ,
      (∀ i, sign i = 1 ∨ sign i = -1) ∧
      (fun i ↦
        Controller.lockedFrequency
          (primeRadicand (vars + eqs) i : ℝ)
          (initialController (B D O) i)) =
        RadicalIndependence.signedPrimeSqrtFrequency
          (primeRadicand (vars + eqs)) sign := by
  have hscale :
      0 <
        (RationalCode.decode
          (NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
            (compilerInput D)) : ℝ) :=
    compilerInput_accumulatorScale_pos D
  have hp :
      ∀ i,
        (1 : ℝ) <
          (RationalCode.decode
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
              (compilerInput D) i) : ℝ) := by
    simpa only [compilerInput_parameters] using
      controllerParameters_gt_one eqs vars
  have hunit :
      ∀ i,
        Controller.controllerRadiusSq
          (initialController (B D O) i) = 1 := by
    intro i
    have h :=
      (clockRadii_one_physicalTime (B D O) hscale 0).1 i
    exact h
  have hequilibrium :
      ∀ i,
        Controller.IsControllerEquilibrium
          (primeRadicand (vars + eqs) i : ℝ)
          (initialController (B D O) i) := by
    intro i
    have h :=
      controller_equilibrium_at_zero (B D O) hscale hp i
    simpa only [compilerInput_parameters, controllerParameters,
      ObservedTimeChangedControllerPhaseHaar.decode_primeClockCodes] using h
  exact
    RadicalClock.exists_signs_for_primeControllerEquilibria
      (primeRadicand (vars + eqs))
      (initialController (B D O)) hunit hequilibrium

/-- **Signed-radical form of the actual detector frequency.**  The common
scale is `2/π`: `1/(2π)` converts radians to turns and the arithmetic
clock is the fourth power of the fundamental phase. -/
theorem exists_sign_physicalDetectorTurnsFrequency :
    ∃ sign : DetectorPhase eqs vars → ℤ,
      (∀ phase, sign phase = 1 ∨ sign phase = -1) ∧
      physicalDetectorTurnsFrequency O =
        ScaledRadicalClock.scaledSignedPrimeSqrtFrequency
          (2 / Real.pi) (detectorPrimeRadicand D) sign := by
  obtain ⟨fundamentalSign, hfundamentalSign, hfrequency⟩ :=
    exists_fundamentalControllerSign D O
  let sign : DetectorPhase eqs vars → ℤ :=
    fun phase ↦ fundamentalSign (finSumFinEquiv phase)
  refine ⟨sign, ?_, ?_⟩
  · intro phase
    exact hfundamentalSign (finSumFinEquiv phase)
  · funext phase
    have hi :=
      congrFun hfrequency (finSumFinEquiv phase)
    unfold physicalDetectorTurnsFrequency
      physicalFundamentalTurnsFrequency
      ScaledRadicalClock.scaledSignedPrimeSqrtFrequency
      detectorPrimeRadicand
    change
      4 *
          (LockedControllerPhaseTrajectory.angularVelocity
              (ObservedTimeChangedControllerPhaseHaar.primeClockCodes
                (primeRadicand (vars + eqs)))
              (initialController (B D O))
              (finSumFinEquiv phase) /
            (2 * Real.pi)) =
        2 / Real.pi *
          RadicalIndependence.signedPrimeSqrtFrequency
            (fun phase ↦
              primeRadicand (vars + eqs) (finSumFinEquiv phase))
            sign phase
    rw [angularVelocity_primeClockCodes]
    rw [hi]
    simp only [RadicalIndependence.signedPrimeSqrtFrequency, sign]
    ring

/-- **No-resonance endpoint for the selected effective detector.** -/
theorem physicalDetectorTurnsFrequency_hasNoCharacter :
    RadicalIndependence.HasNoNontrivialIntegerCharacter
      (physicalDetectorTurnsFrequency O) := by
  obtain ⟨sign, hsign, hfrequency⟩ :=
    exists_sign_physicalDetectorTurnsFrequency D O
  rw [hfrequency]
  exact
    ScaledRadicalClock.scaledSignedPrimeSqrtFrequency_hasNoCharacter
      (2 / Real.pi)
      (by positivity)
      (detectorPrimeRadicand D)
      (detectorPrimeRadicand_prime D)
      (detectorPrimeRadicand_injective D)
      sign hsign

end SelectedBidirectionalValidityOrbit

end

end HGAS.NormalizedCorrectedEffectiveSelectedDetectorPhase
