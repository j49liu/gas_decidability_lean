import HGAS.Analysis.AutonomousC1ODEUniqueness
import HGAS.Arithmetic.CanonicalFixedDetectorFourierCrosswalk
import HGAS.Arithmetic.DetectorPoissonReciprocalSemantics
import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorSelectedPhysicalPhase
import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorTwoSidedCompleteStructure
import Mathlib.Tactic

/-!
# Factorization of the detector on a selected normalized orbit

This file isolates all parts of the selected-orbit detector crosswalk that
do not depend on the three Jacobi moment normalizations.

* The right-hand-side oscillator is classified by uniqueness for its
  constant complex linear ODE.  It is a fixed nonzero twist times the
  right-hand-side Fourier character at the actual physical phase.
* Vanishing of the compiled reciprocal residuals identifies the two
  stored Poisson variables with the exact reciprocal graphs.
* Consequently, once each actual theta output is identified with its
  Gaussian theta series at the actual phase, the whole literal detector
  is the same fixed twist times the factorized Fourier detector.

The twist is unavoidable: the validity equations impose unit radius on
the final oscillator but do not choose its initial angle.  Its
nonvanishing is exactly what is needed in the invariant-average
contradiction.
-/

namespace HGAS.NormalizedCorrectedFixedDetectorSelectedFactorization

open HGAS
open HGAS.Clocks
open HGAS.Modular
open Complex
open scoped BigOperators
open Clocks.ControllerPhaseProductCharacterCode
open NormalizedCorrectedFixedDetectorTwoSidedValidityOrbit
open NormalizedCorrectedFixedDetectorBidirectionalValidityOrbit
open NormalizedCorrectedFixedDetectorTwoSidedStructuredOrbit
open NormalizedCorrectedFixedDetectorTwoSidedCompleteStructure
open NormalizedCorrectedFixedDetectorTwoSidedControllerLocking
open NormalizedCorrectedFixedDetectorSelectedPhysicalPhase
open
  NormalizedCorrectedFixedDetectorTwoSidedStructuredOrbit.SelectedTwoSidedValidityOrbit
open
  NormalizedCorrectedFixedDetectorTwoSidedCompleteStructure.SelectedTwoSidedValidityOrbit
open
  NormalizedCorrectedFixedDetectorTwoSidedControllerLocking.SelectedTwoSidedValidityOrbit
open
  NormalizedCorrectedFixedDetectorSelectedPhysicalPhase.SelectedBidirectionalValidityOrbit
open
  NormalizedCorrectedFixedDetectorColumnCharacters.SelectedBidirectionalValidityOrbit

noncomputable section

variable {eqs vars : ℕ}
variable
  {u :
    NormalizedCorrectedFixedDetectorCompactSourceCode.CompilerInput
      eqs vars}

namespace SelectedBidirectionalValidityOrbit

variable (O : SelectedBidirectionalValidityOrbit u)

private abbrev B : SelectedTwoSidedValidityOrbit u :=
  O.toSelectedTwoSidedValidityOrbit

private abbrev parameters
    (_O : SelectedBidirectionalValidityOrbit u) :
    Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → RationalCode :=
  NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u

private abbrev I
    (_O : SelectedBidirectionalValidityOrbit u) :
    DQLSystem eqs vars :=
  NormalizedCorrectedFixedDetectorCompactSourceCode.system u

private abbrev controller :
    Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
      Controller.ControllerState ℝ :=
  NormalizedCorrectedFixedDetectorColumnTrajectory.SelectedTwoSidedValidityOrbit.initialController
    (B O)

/-- Initial unit phases of all selected physical clocks. -/
def physicalClockInitialPhase
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ)) :
    Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → Circle :=
  LockedControllerPhaseCompleteCurve.initialPhase
    (clockPoint (B O))
    (fun i ↦ (clockPoint_onClockCircles (B O) hscale 0 i).2)

/-- Fundamental clock frequencies in turns per unit physical time. -/
def physicalFundamentalTurnsFrequency
    (i : Fin (FixedDetectorPolynomialCode.clockCount eqs vars)) : ℝ :=
  LockedControllerPhaseTrajectory.angularVelocity
      (parameters O) (controller O) i /
    (2 * Real.pi)

/-- Arithmetic detector frequencies in turns per unit physical time.
The factor four is the compiler's fourth-root clock convention. -/
def physicalDetectorTurnsFrequency
    (phase : DetectorPhase eqs vars) : ℝ :=
  4 *
    physicalFundamentalTurnsFrequency O (finSumFinEquiv phase)

/-- The final real oscillator, read as one complex number. -/
def physicalRHSComplex (t : ℝ) : ℂ :=
  PhaseClockFlow.phaseStateComplex ((B O).physicalState t).rhs

/-- Package the initial physical RHS pair as a genuine circle point. -/
def physicalRHSInitialCircle
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ)) : Circle :=
  CircleRealCoordinates.circle
    ⟨![((B O).physicalState 0).rhs.c,
        ((B O).physicalState 0).rhs.d], by
      simpa [Controller.phaseRadiusSq] using
        rhsRadius_one_physicalTime (B O) hscale 0⟩

@[simp]
theorem physicalRHSInitialCircle_coe
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ)) :
    (physicalRHSInitialCircle O hscale : ℂ) =
      physicalRHSComplex O 0 := by
  apply Complex.ext <;>
    simp [physicalRHSInitialCircle, physicalRHSComplex,
      PhaseClockFlow.phaseStateComplex,
      CircleRealCoordinates.circle]

/-- The actual initial value of the flattened RHS clock character. -/
def physicalRHSCharacterInitial : ℂ :=
  characterValue
    (DetectorCharacterCode.flattenCharacter
      (DetectorCharacterCode.rhsCharacter (I O)))
    (physicalControllers O 0)

/-- The constant phase mismatch between the independent terminal
oscillator and the product of fundamental clocks. -/
def physicalRHSTwist
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ)) : ℂ :=
  (physicalRHSInitialCircle O hscale : ℂ) *
    (physicalRHSCharacterInitial O)⁻¹

/-- The initial RHS character is a unit and therefore nonzero. -/
theorem physicalRHSCharacterInitial_ne_zero
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ)) :
    physicalRHSCharacterInitial O ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [show ‖physicalRHSCharacterInitial O‖ = 1 by
    exact norm_characterValue_eq_one
      _ _ (physicalControllers_onPhaseCircles O hscale 0)]
  norm_num

/-- The RHS twist is nonzero. -/
theorem physicalRHSTwist_ne_zero
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ)) :
    physicalRHSTwist O hscale ≠ 0 := by
  exact mul_ne_zero
    (Circle.coe_ne_zero (physicalRHSInitialCircle O hscale))
    (inv_ne_zero (physicalRHSCharacterInitial_ne_zero O hscale))

/-- The actual physical controllers and phases are exactly the explicit
locked state family through their selected initial data. -/
theorem physicalControllers_eq_lockedStateFamily
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (hp :
      ∀ i,
        (1 : ℝ) <
          (RationalCode.decode
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
              u i) : ℝ))
    (t : ℝ) :
    physicalControllers O t =
      LockedControllerPhaseTrajectory.stateFamily
        (parameters O) (controller O)
        (physicalClockInitialPhase O hscale) t := by
  have hlocked :=
    clockState_eq_lockedStateFamily O hscale hp t
  have hrecovered :=
    clockState_eq_recoveredControllers O t
  have hinitialController :
      LockedControllerPhaseCompleteCurve.initialController
          (clockPoint (B O)) =
        controller O := by
    funext i
    simp only [
      LockedControllerPhaseCompleteCurve.initialController,
      clockPoint,
      ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint,
      ControllerPhaseProductPolynomialCode.state_point,
      controller]
    rfl
  calc
    physicalControllers O t =
        ControllerPhaseProductPolynomialCode.state
          (clockPoint (B O) t) := by
      exact hrecovered.symm
    _ =
        LockedControllerPhaseTrajectory.stateFamily
          (parameters O)
          (LockedControllerPhaseCompleteCurve.initialController
            (clockPoint (B O)))
          (physicalClockInitialPhase O hscale) t := by
      exact hlocked
    _ = _ := by rw [hinitialController]

/-- Each multiplicative phase circle is its initial selected circle
rotated by the locked physical angular velocity. -/
theorem physicalPhaseCircle_eq_rotation
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (hp :
      ∀ i,
        (1 : ℝ) <
          (RationalCode.decode
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
              u i) : ℝ))
    (t : ℝ)
    (i : Fin (FixedDetectorPolynomialCode.clockCount eqs vars)) :
    ControllerPhaseProductTorusObservation.phaseCircle
        (physicalControllers O)
        (fun s k ↦ physicalControllers_phaseRadiusSq O hscale s k)
        t i =
      PhaseClockFlow.phaseRotationFlow
        (LockedControllerPhaseTrajectory.angularVelocity
          (parameters O) (controller O) i)
        t
        (ControllerPhaseProductTorusObservation.phaseCircle
          (physicalControllers O)
          (fun s k ↦ physicalControllers_phaseRadiusSq O hscale s k)
          0 i) := by
  let z := physicalControllers O
  let hz :
      ∀ s i, Controller.phaseRadiusSq (z s i).phase = 1 :=
    fun s k ↦ physicalControllers_phaseRadiusSq O hscale s k
  let phase₀ := physicalClockInitialPhase O hscale
  let omega :=
    LockedControllerPhaseTrajectory.angularVelocity
      (parameters O) (controller O) i
  have hstate (s : ℝ) :
      phaseValue (z s) i =
        (PhaseClockFlow.phaseRotationFlow omega s (phase₀ i) : ℂ) := by
    have h :=
      congrArg (fun q ↦ phaseValue q i)
        (physicalControllers_eq_lockedStateFamily O hscale hp s)
    simpa only [z, phase₀, omega,
      LockedControllerPhaseTrajectory.phaseValue_stateFamily] using h
  have hinitial :
      ControllerPhaseProductTorusObservation.phaseCircle
          z hz 0 i =
        phase₀ i := by
    apply Circle.ext
    rw [
      ControllerPhaseProductTorusObservation.phaseCircle_coe]
    change phaseValue (z 0) i = (phase₀ i : ℂ)
    rw [hstate 0]
    simp
  apply Circle.ext
  rw [ControllerPhaseProductTorusObservation.phaseCircle_coe]
  change
    phaseValue (z t) i =
      (PhaseClockFlow.phaseRotationFlow omega t
        (ControllerPhaseProductTorusObservation.phaseCircle
          z hz 0 i) : ℂ)
  rw [hinitial]
  exact hstate t

/-- The actual fundamental additive phase is an exact torus translation
through its noncanonical selected initial phase. -/
theorem physicalFundamentalPhase_eq_translation
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (hp :
      ∀ i,
        (1 : ℝ) <
          (RationalCode.decode
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
              u i) : ℝ))
    (t : ℝ) :
    physicalFundamentalPhase O hscale t =
      RadicalClock.torusTranslationFlow
        (physicalFundamentalTurnsFrequency O) t
        (physicalFundamentalPhase O hscale 0) := by
  funext i
  apply PhaseClockFlow.unitAddCircleHomeomorph.injective
  have hsemi :=
    PhaseClockFlow.unitAddCircleHomeomorph_semiconj
      (LockedControllerPhaseTrajectory.angularVelocity
        (parameters O) (controller O) i)
      t
      (physicalFundamentalPhase O hscale 0 i)
  rw [RadicalClock.torusTranslationFlow_apply]
  change
    PhaseClockFlow.unitAddCircleHomeomorph
        (physicalFundamentalPhase O hscale t i) =
      PhaseClockFlow.unitAddCircleHomeomorph
        (PhaseClockFlow.turnTranslationFlow
          (physicalFundamentalTurnsFrequency O i) t
          (physicalFundamentalPhase O hscale 0 i))
  rw [show
      physicalFundamentalTurnsFrequency O i =
        PhaseClockFlow.radiansToTurnsFrequency
          (LockedControllerPhaseTrajectory.angularVelocity
            (parameters O) (controller O) i) by
    rfl]
  rw [hsemi]
  unfold physicalFundamentalPhase
    ControllerPhaseProductTorusObservation.phase
  simp only [
    PhaseClockFlow.unitAddCircleHomeomorph.apply_symm_apply]
  exact physicalPhaseCircle_eq_rotation O hscale hp t i

/-- **Exact selected detector phase flow.**  The arithmetic fourth-power
phase follows a literal torus translation through its actual initial
phase. -/
theorem physicalDetectorPhase_eq_translation
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (hp :
      ∀ i,
        (1 : ℝ) <
          (RationalCode.decode
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
              u i) : ℝ))
    (t : ℝ) :
    physicalDetectorPhase O hscale t =
      RadicalClock.torusTranslationFlow
        (physicalDetectorTurnsFrequency O) t
        (physicalDetectorPhase O hscale 0) := by
  funext phase
  unfold physicalDetectorPhase
  rw [show
      physicalFundamentalPhase O hscale t
          (finSumFinEquiv phase) =
        RadicalClock.torusTranslationFlow
          (physicalFundamentalTurnsFrequency O) t
          (physicalFundamentalPhase O hscale 0)
          (finSumFinEquiv phase) by
    exact congrFun
      (physicalFundamentalPhase_eq_translation O hscale hp t)
      (finSumFinEquiv phase)]
  unfold RadicalClock.torusTranslationFlow
    RadicalClock.torusDisplacement
    physicalDetectorTurnsFrequency
  simp only [Pi.add_apply]
  rw [zsmul_add]
  congr 1
  rw [← QuotientAddGroup.mk_zsmul]
  congr 1
  unfold physicalFundamentalTurnsFrequency
  ring

/-- Along the selected orbit, the frequency read by the terminal
oscillator is the constant frequency determined by the locked initial
controllers. -/
theorem physicalWeightedFrequency_eq_rhsFrequency
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (hp :
      ∀ i,
        (1 : ℝ) <
          (RationalCode.decode
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
              u i) : ℝ))
    (t : ℝ) :
    RHSOscillatorPolynomialCode.weightedFrequency
        (FixedDetectorPolynomialCode.rhsWeightCode (I O))
        (FixedDetectorPolynomialCode.equationFrequencyCode
          (parameters O))
        (DetectorPoissonReciprocalCode.point
          ((B O).physicalState t).base) =
      CanonicalFixedDetectorTrajectory.rhsFrequency
        (parameters O) (I O) (controller O) := by
  rw [FixedDetectorPolynomialCode.weightedFrequency_eq]
  unfold CanonicalFixedDetectorTrajectory.rhsFrequency
  apply Finset.sum_congr rfl
  intro row _
  congr 1
  have hlocked :=
    clockState_eq_lockedStateFamily O hscale hp t
  have hrecovered :=
    clockState_eq_recoveredControllers O t
  have hinitialController :
      LockedControllerPhaseCompleteCurve.initialController
          (clockPoint (B O)) =
        controller O := by
    funext i
    simp only [
      LockedControllerPhaseCompleteCurve.initialController,
      clockPoint,
      ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint,
      ControllerPhaseProductPolynomialCode.state_point,
      controller]
    rfl
  have hcontrollers :
      ((B O).physicalState t).base.base.source.controllers =
        LockedControllerPhaseTrajectory.stateFamily
          (parameters O) (controller O)
          (LockedControllerPhaseCompleteCurve.initialPhase
            (clockPoint (B O))
            (fun i ↦
              (clockPoint_onClockCircles (B O) hscale 0 i).2))
          t := by
    calc
      ((B O).physicalState t).base.base.source.controllers =
          ControllerPhaseProductPolynomialCode.state
            (clockPoint (B O) t) := by
        simpa only [
          recoveredState_physicalPoint]
          using hrecovered.symm
      _ = _ := hlocked
        |>.trans (by
          rw [hinitialController])
  rw [hcontrollers]
  exact
    LockedControllerPhaseTrajectory.frequencyValue_stateFamily
      (parameters O) (controller O) _
      (FixedDetectorPolynomialCode.equationBasisExponent row) t

/-- The selected physical RHS solves a constant scalar complex ODE. -/
theorem physicalRHSComplex_hasDerivAt
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (hp :
      ∀ i,
        (1 : ℝ) <
          (RationalCode.decode
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
              u i) : ℝ))
    (t : ℝ) :
    HasDerivAt (physicalRHSComplex O)
      (((-4 *
          CanonicalFixedDetectorTrajectory.rhsFrequency
            (parameters O) (I O) (controller O) : ℝ) : ℂ) *
        Complex.I * physicalRHSComplex O t) t := by
  have hstructured :=
    physicalPoint_isStructuredTrajectory (B O)
  have hc := hstructured.rhs.c t
  have hd := hstructured.rhs.d t
  have hfrequency :
      RHSOscillatorPolynomialCode.weightedFrequency
          (FixedDetectorPolynomialCode.rhsWeightCode (I O))
          (FixedDetectorPolynomialCode.equationFrequencyCode
            (parameters O))
          (DetectorPoissonReciprocalCode.point
            (FixedDetectorReverseTrajectoryCrosswalk.recoveredState
              (B O).physicalPoint t).base) =
        CanonicalFixedDetectorTrajectory.rhsFrequency
          (parameters O) (I O) (controller O) := by
    simpa only [recoveredState_physicalPoint]
      using physicalWeightedFrequency_eq_rhsFrequency O hscale hp t
  rw [RHSOscillatorPolynomialCode.oscillatorField, hfrequency] at hc hd
  have hcomplex :
      HasDerivAt (physicalRHSComplex O)
        (PhaseClockFlow.phaseStateComplex
          (Controller.phaseField
            (-4 *
              CanonicalFixedDetectorTrajectory.rhsFrequency
                (parameters O) (I O) (controller O))
            ((B O).physicalState t).rhs)) t := by
    apply HGAS.HasDerivAt.complex_of_re_im
    · simpa [physicalRHSComplex, PhaseClockFlow.phaseStateComplex] using hc
    · simpa [physicalRHSComplex, PhaseClockFlow.phaseStateComplex] using hd
  simpa [PhaseClockFlow.phaseStateComplex_phaseField,
    physicalRHSComplex] using hcomplex

/-- The explicit circle rotation through the selected initial RHS value
solves the same scalar complex ODE. -/
theorem explicitPhysicalRHS_hasDerivAt
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (t : ℝ) :
    HasDerivAt
      (fun s : ℝ ↦
        (PhaseClockFlow.phaseRotationFlow
          (-4 *
            CanonicalFixedDetectorTrajectory.rhsFrequency
              (parameters O) (I O) (controller O))
          s (physicalRHSInitialCircle O hscale) : ℂ))
      (((-4 *
          CanonicalFixedDetectorTrajectory.rhsFrequency
            (parameters O) (I O) (controller O) : ℝ) : ℂ) *
        Complex.I *
        (PhaseClockFlow.phaseRotationFlow
          (-4 *
            CanonicalFixedDetectorTrajectory.rhsFrequency
              (parameters O) (I O) (controller O))
          t (physicalRHSInitialCircle O hscale) : ℂ)) t := by
  exact
    PhaseClockFlow.hasDerivAt_phaseRotationFlow_coe
      (-4 *
        CanonicalFixedDetectorTrajectory.rhsFrequency
          (parameters O) (I O) (controller O))
      t (physicalRHSInitialCircle O hscale)

/-- ODE uniqueness identifies the actual terminal oscillator with the
explicit rotation through its actual initial point. -/
theorem physicalRHSComplex_eq_rotation
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (hp :
      ∀ i,
        (1 : ℝ) <
          (RationalCode.decode
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
              u i) : ℝ))
    (t : ℝ) :
    physicalRHSComplex O t =
      (PhaseClockFlow.phaseRotationFlow
        (-4 *
          CanonicalFixedDetectorTrajectory.rhsFrequency
            (parameters O) (I O) (controller O))
        t (physicalRHSInitialCircle O hscale) : ℂ) := by
  let Y : ℂ → ℂ :=
    fun z ↦
      (((-4 *
          CanonicalFixedDetectorTrajectory.rhsFrequency
            (parameters O) (I O) (controller O) : ℝ) : ℂ) *
        Complex.I) * z
  have hY : ContDiff ℝ 1 Y := by
    fun_prop
  have heq :
      physicalRHSComplex O =
        fun s : ℝ ↦
          (PhaseClockFlow.phaseRotationFlow
            (-4 *
              CanonicalFixedDetectorTrajectory.rhsFrequency
                (parameters O) (I O) (controller O))
            s (physicalRHSInitialCircle O hscale) : ℂ) := by
    apply
      HGAS.Analysis.autonomousC1_ode_solution_unique
        (t₀ := 0) hY
    · intro s
      exact physicalRHSComplex_hasDerivAt O hscale hp s
    · intro s
      exact explicitPhysicalRHS_hasDerivAt O hscale s
    · simpa only [Y, PhaseClockFlow.phaseRotationFlow_apply, mul_zero,
        Circle.exp_zero, one_mul] using
        (physicalRHSInitialCircle_coe O hscale).symm
  exact congrFun heq t

/-- Closed exponential formula for the actual terminal oscillator. -/
theorem physicalRHSComplex_eq_initial_mul_exponential
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (hp :
      ∀ i,
        (1 : ℝ) <
          (RationalCode.decode
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
              u i) : ℝ))
    (t : ℝ) :
    physicalRHSComplex O t =
      (physicalRHSInitialCircle O hscale : ℂ) *
        HGAS.Analysis.realFrequencyExponential
          (-4 *
            CanonicalFixedDetectorTrajectory.rhsFrequency
              (parameters O) (I O) (controller O)) t := by
  rw [physicalRHSComplex_eq_rotation O hscale hp t]
  unfold HGAS.Analysis.realFrequencyExponential
  simp only [PhaseClockFlow.phaseRotationFlow_apply, Circle.coe_mul,
    Circle.coe_exp]
  rw [mul_comm]
  congr 1
  congr 1
  push_cast
  ring

/-- The flattened RHS clock character has the same exponential factor. -/
theorem physicalRHSCharacter_eq_initial_mul_exponential
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (hp :
      ∀ i,
        (1 : ℝ) <
          (RationalCode.decode
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
              u i) : ℝ))
    (t : ℝ) :
    characterValue
        (DetectorCharacterCode.flattenCharacter
          (DetectorCharacterCode.rhsCharacter (I O)))
        (physicalControllers O t) =
      physicalRHSCharacterInitial O *
        HGAS.Analysis.realFrequencyExponential
          (-4 *
            CanonicalFixedDetectorTrajectory.rhsFrequency
              (parameters O) (I O) (controller O)) t := by
  unfold physicalControllers physicalRHSCharacterInitial
  rw [
    characterValue_physical_eq_initial_mul_exponential O hscale hp]
  rw [
    CanonicalFixedDetectorFourierCrosswalk.rhsCharacterFrequency_eq]
  rfl

/-- **RHS twist theorem.**  The actual unit terminal oscillator is a fixed
nonzero twist times the RHS Fourier character at the actual detector
phase. -/
theorem physicalRHSComplex_eq_twist_mul_mFourier
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (hp :
      ∀ i,
        (1 : ℝ) <
          (RationalCode.decode
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
              u i) : ℝ))
    (t : ℝ) :
    physicalRHSComplex O t =
      physicalRHSTwist O hscale *
        UnitAddTorus.mFourier
          (DetectorCharacterCode.rhsCharacter (I O))
          (physicalDetectorPhase O hscale t) := by
  rw [mFourier_physicalDetectorPhase O hscale]
  rw [physicalRHSCharacter_eq_initial_mul_exponential O hscale hp t]
  rw [physicalRHSComplex_eq_initial_mul_exponential O hscale hp t]
  unfold physicalRHSTwist
  field_simp [physicalRHSCharacterInitial_ne_zero O hscale]

/-! ## The two Poisson reciprocal graphs -/

/-- Every selected physical reciprocal graph residual vanishes. -/
theorem physicalReciprocalGraphResidual_zero
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (t : ℝ)
    (k : Fin (DetectorPoissonReciprocalCode.reciprocalCount vars)) :
    DetectorPoissonReciprocalCode.reciprocalGraphResidual
        (I O) ((B O).physicalState t).base k = 0 := by
  apply
    (DetectorPoissonReciprocalCode.forall_eval_residualCode_eq_zero_iff_graphResidual
      (I O) ((B O).physicalState t).base).1
  intro r
  have h :=
    (validityResiduals_zero_physicalTime (B O) hscale t).2.2 r
  simpa only [recoveredState_physicalPoint]
    using h

/-- The two stored reciprocal coordinates give the exact Poisson Fourier
series at the actual detector phase. -/
theorem physicalPoissonFactor_eq_poissonSeries
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (t : ℝ) (j : Fin vars) :
    (((3 / 4 : ℝ) : ℂ) *
        ((B O).physicalState t).base.reciprocal
          (DetectorPoissonReciprocalCode.positiveIndex j) *
        ((B O).physicalState t).base.reciprocal
          (DetectorPoissonReciprocalCode.negativeIndex j)) =
      ∑' s : ℤ,
        DetectorFactorizedFourier.poissonTerm
          (1 / 2 : ℝ) (I O) j s
          (physicalDetectorPhase O hscale t) := by
  let z := ((B O).physicalState t).base
  have hz :
      OnPhaseCircles z.base.source.controllers := by
    simpa only [z, physicalControllers] using
      physicalControllers_onPhaseCircles O hscale t
  have hpositive :=
    DetectorPoissonReciprocalCode.positiveReciprocal_eq_inv
      (I O) z j hz
      (physicalReciprocalGraphResidual_zero O hscale t
        (DetectorPoissonReciprocalCode.positiveIndex j))
  have hnegative :=
    DetectorPoissonReciprocalCode.negativeReciprocal_eq_inv
      (I O) z j hz
      (physicalReciprocalGraphResidual_zero O hscale t
        (DetectorPoissonReciprocalCode.negativeIndex j))
  rw [show
      ((B O).physicalState t).base.reciprocal
          (DetectorPoissonReciprocalCode.positiveIndex j) =
        z.reciprocal
          (DetectorPoissonReciprocalCode.positiveIndex j) by rfl,
    show
      ((B O).physicalState t).base.reciprocal
          (DetectorPoissonReciprocalCode.negativeIndex j) =
        z.reciprocal
          (DetectorPoissonReciprocalCode.negativeIndex j) by rfl,
    hpositive, hnegative]
  rw [CanonicalFixedDetectorFourierCrosswalk.tsum_poissonTerm
    (by norm_num) (by norm_num)]
  rw [poissonCharacterValue_eq_mFourier O hscale j t]
  rw [div_eq_mul_inv]
  norm_num
  rw [mul_assoc, ← mul_inv_rev]
  congr 2
  all_goals ring

/-! ## Final detector factorization -/

/-- Multiplying the assumed theta identities with the proved Poisson
identities gives the detector product before the terminal oscillator. -/
theorem physicalDetectorProduct_eq_factorizedProduct
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (t : ℝ)
    (htheta :
      ∀ j : Fin vars,
        ((B O).physicalState t).base.base.gauge j *
            (((B O).physicalState t).base.base.source.linked j).jacobi.T1 =
          ∑' n : ℤ,
            DetectorFactorizedFourier.thetaTerm
              (1 / 256 : ℝ) (I O) j n
              (physicalDetectorPhase O hscale t)) :
    (∏ j : Fin vars,
        ((((B O).physicalState t).base.base.gauge j *
            (((B O).physicalState t).base.base.source.linked j).jacobi.T1) *
          (((3 / 4 : ℝ) : ℂ) *
            ((B O).physicalState t).base.reciprocal
              (DetectorPoissonReciprocalCode.positiveIndex j) *
            ((B O).physicalState t).base.reciprocal
              (DetectorPoissonReciprocalCode.negativeIndex j)))) =
      (∏ j : Fin vars,
        ∑' n : ℤ,
          DetectorFactorizedFourier.thetaTerm
            (1 / 256 : ℝ) (I O) j n
            (physicalDetectorPhase O hscale t)) *
      (∏ j : Fin vars,
        ∑' s : ℤ,
          DetectorFactorizedFourier.poissonTerm
            (1 / 2 : ℝ) (I O) j s
            (physicalDetectorPhase O hscale t)) := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [htheta j, physicalPoissonFactor_eq_poissonSeries O hscale t j]

/-- **Selected-orbit detector factorization.**  If every actual theta
output is the canonical Gaussian theta series at the actual physical
phase, then the literal normalized detector value is the fixed nonzero
RHS twist times the factorized Fourier detector. -/
theorem detectorValue_eq_twist_mul_factorizedDetector
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (hp :
      ∀ i,
        (1 : ℝ) <
          (RationalCode.decode
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
              u i) : ℝ))
    (t : ℝ)
    (ht : 0 ≤ t)
    (htheta :
      ∀ j : Fin vars,
        ((B O).physicalState t).base.base.gauge j *
            (((B O).physicalState t).base.base.source.linked j).jacobi.T1 =
          ∑' n : ℤ,
            DetectorFactorizedFourier.thetaTerm
              (1 / 256 : ℝ) (I O) j n
              (physicalDetectorPhase O hscale t)) :
    NormalizedCorrectedFixedDetectorDriftCode.detectorValue
        ((B O).physicalState t) =
      physicalRHSTwist O hscale *
        DetectorFactorizedFourier.factorizedDetector
          (1 / 256 : ℝ) (1 / 2 : ℝ) (I O)
          (physicalDetectorPhase O hscale t) := by
  have _ := ht
  unfold NormalizedCorrectedFixedDetectorDriftCode.detectorValue
    CorrectedFixedDetectorDriftCode.detectorValue
    FixedDetectorDriftCode.detectorValue
  have hrhs :
      (⟨((B O).physicalState t).rhs.c,
          ((B O).physicalState t).rhs.d⟩ : ℂ) =
        physicalRHSComplex O t := by
    apply Complex.ext <;>
      simp [physicalRHSComplex, PhaseClockFlow.phaseStateComplex]
  rw [hrhs]
  rw [physicalRHSComplex_eq_twist_mul_mFourier O hscale hp t]
  rw [physicalDetectorProduct_eq_factorizedProduct O hscale t htheta]
  unfold DetectorFactorizedFourier.factorizedDetector
  ring

/-- Expanded-series form of the same endpoint. -/
theorem detectorValue_eq_twist_mul_expandedDetector
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (hp :
      ∀ i,
        (1 : ℝ) <
          (RationalCode.decode
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
              u i) : ℝ))
    (t : ℝ)
    (ht : 0 ≤ t)
    (htheta :
      ∀ j : Fin vars,
        ((B O).physicalState t).base.base.gauge j *
            (((B O).physicalState t).base.base.source.linked j).jacobi.T1 =
          ∑' n : ℤ,
            DetectorFactorizedFourier.thetaTerm
              (1 / 256 : ℝ) (I O) j n
              (physicalDetectorPhase O hscale t)) :
    NormalizedCorrectedFixedDetectorDriftCode.detectorValue
        ((B O).physicalState t) =
      physicalRHSTwist O hscale *
        expandedDetector
          (1 / 256 : ℝ) (1 / 2 : ℝ) (I O)
          (physicalDetectorPhase O hscale t) := by
  rw [detectorValue_eq_twist_mul_factorizedDetector
    O hscale hp t ht htheta]
  rw [DetectorFactorizedFourier.factorizedDetector_eq_expandedDetector
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)]

end SelectedBidirectionalValidityOrbit

end

end HGAS.NormalizedCorrectedFixedDetectorSelectedFactorization
