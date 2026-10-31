import Stability.Selection.OrdinaryTimeDetectorProjection
import Stability.Selection.OrdinaryTimeThetaTarget
import HGAS.Clocks.LockedControllerPhaseCompleteCurve

/-!
# Clock characters and phases of the concrete source

The polynomial source, forward recurrence, and zero validity determine
the actual locked clock path. Every character retains its initial phase.
The fourth-power phase observation agrees with the detector Fourier
characters, including negative exponents. These are the clock and phase
identities used in Section 8, Theorem `thm:selector`.
-/

noncomputable section

namespace Stability.Selection

open HGAS HGAS.Modular HGAS.Clocks Filter MeasureTheory Topology
open HGAS.FixedDetectorReverseTrajectoryCrosswalk
open HGAS.Clocks.ControllerPhaseProductCharacterCode
open HGAS.CanonicalDetectorThetaQuadraticGeometric

variable {eqs vars : ℕ}

theorem detector_initialController_equilibrium
    (parameters : Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → RationalCode)
    (hp : ∀ i, (1 : ℝ) < (parameters i).decode) (I : DQLSystem eqs vars)
    {x : ℝ → Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ}
    (hx : IsIntegralCurve x (fun _ y ↦ PolynomialFieldCode.realize
      (FixedDetectorPolynomialCode.fieldCode parameters I) y))
    (hrec : ForwardRecurrentAt x 0)
    (hvalid : ∀ t, NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue I
      (recoveredState x t) = 0)
    (i : Fin (FixedDetectorPolynomialCode.clockCount eqs vars)) :
    Controller.IsControllerEquilibrium ((parameters i).decode : ℝ)
      (detectorInitialController x i) := by
  have hs := isStructuredTrajectory_of_isIntegralCurve parameters I x hx
  have h := RecurrentNormalizedControllerProduct.controller_equilibrium_at_zero
    parameters hp (detectorClockPoint x) (detectorClockPoint_onClockCircles I hvalid)
    ⟨rfl, fun t _ ↦ (hs.controllers t).hasDerivWithinAt⟩
    (detectorClockPoint_forwardRecurrentAt hrec) i
  simpa only [detectorClockPoint, detectorInitialController,
    ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint,
    ControllerPhaseProductPolynomialCode.state_point] using h

theorem detector_omega_ne_zero
    (parameters : Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → RationalCode)
    (hp : ∀ i, (1 : ℝ) < (parameters i).decode) (I : DQLSystem eqs vars)
    {x : ℝ → Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ}
    (hx : IsIntegralCurve x (fun _ y ↦ PolynomialFieldCode.realize
      (FixedDetectorPolynomialCode.fieldCode parameters I) y))
    (hrec : ForwardRecurrentAt x 0)
    (hvalid : ∀ t, NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue I
      (recoveredState x t) = 0) (j : Fin vars) :
    CanonicalFixedDetectorTrajectory.omegaFrequency
      parameters (detectorInitialController x) j ≠ 0 := by
  apply FixedDetectorPrivateFrequency.omegaFrequency_ne_zero_of_unit_equilibrium
    parameters (detectorInitialController x) j (hp _)
  · exact ((NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue_eq_zero_iff
      I (recoveredState x 0)).mp (hvalid 0)).2.1 _
  · exact detector_initialController_equilibrium parameters hp I hx hrec hvalid _

/-- All integral clock characters evolve with the literal controller
frequency, through their actual initial values. -/
theorem detector_character_eq_initial_mul_exponential
    (parameters : Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → RationalCode)
    (hp : ∀ i, (1 : ℝ) < (parameters i).decode) (I : DQLSystem eqs vars)
    {x : ℝ → Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ}
    (hx : IsIntegralCurve x (fun _ y ↦ PolynomialFieldCode.realize
      (FixedDetectorPolynomialCode.fieldCode parameters I) y))
    (hrec : ForwardRecurrentAt x 0)
    (hvalid : ∀ t, NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue I
      (recoveredState x t) = 0)
    (a : Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → ℤ) (t : ℝ) :
    characterValue a (recoveredState x t).base.base.source.controllers =
      characterValue a (recoveredState x 0).base.base.source.controllers *
        HGAS.Analysis.realFrequencyExponential
          (LockedControllerPhaseTrajectory.characterFrequency
            parameters (detectorInitialController x) a) t := by
  let c := detectorClockPoint x
  have hs := isStructuredTrajectory_of_isIntegralCurve parameters I x hx
  have hphase := fun i ↦ (detectorClockPoint_onClockCircles I hvalid 0 i).2
  have hinitial : LockedControllerPhaseCompleteCurve.initialController c =
      detectorInitialController x := by
    funext i
    simp only [LockedControllerPhaseCompleteCurve.initialController, c,
      detectorClockPoint, detectorInitialController,
      ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint,
      ControllerPhaseProductPolynomialCode.state_point]
  have hstate (u : ℝ) := LockedControllerPhaseCompleteCurve.state_curve_eq_stateFamily
    parameters c hs.controllers hphase
    (by simpa only [hinitial] using
      detector_initialController_equilibrium parameters hp I hx hrec hvalid) u
  have hchar :=
    LockedControllerPhaseTrajectory.characterValue_stateFamily_eq_initial_mul_exponential
      parameters (LockedControllerPhaseCompleteCurve.initialController c)
      (LockedControllerPhaseCompleteCurve.initialPhase c hphase) a t
  rw [← hstate t, LockedControllerPhaseCompleteCurve.stateFamily_initial_eq] at hchar
  simpa only [hinitial, c, detectorClockPoint,
    ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint,
    ControllerPhaseProductPolynomialCode.state_point] using hchar

/-- The actual fourth-power detector phase, extracted from unit phase
pairs. This definition applies to any family of states. -/
def detectorPhaseOfUnitControllers
    {X : Type*}
    (z : X → ControllerPhaseProductPolynomialCode.StateFamily
      (FixedDetectorPolynomialCode.clockCount eqs vars) ℝ)
    (hphase : ∀ t i, Controller.phaseRadiusSq (z t i).phase = 1)
    (t : X) : UnitAddTorus (DetectorPhase eqs vars) :=
  fun coordinate ↦ (4 : ℤ) •
    ControllerPhaseProductTorusObservation.phase z hphase t (finSumFinEquiv coordinate)

/-- Fourier characters of the extracted phase are exactly the compiled
signed-power characters, without any canonical initial-phase assumption. -/
theorem mFourier_detectorPhaseOfUnitControllers
    {X : Type*}
    (z : X → ControllerPhaseProductPolynomialCode.StateFamily
      (FixedDetectorPolynomialCode.clockCount eqs vars) ℝ)
    (hphase : ∀ t i, Controller.phaseRadiusSq (z t i).phase = 1)
    (t : X) (a : DetectorPhase eqs vars → ℤ) :
    UnitAddTorus.mFourier a (detectorPhaseOfUnitControllers z hphase t) =
      characterValue (DetectorCharacterCode.flattenCharacter a) (z t) := by
  rw [← ControllerPhaseProductTorusObservation.mFourier_phase z hphase t]
  classical
  unfold UnitAddTorus.mFourier detectorPhaseOfUnitControllers
    DetectorCharacterCode.flattenCharacter
  simp only [ContinuousMap.coe_mk]
  rw [← finSumFinEquiv.prod_comp]
  apply Finset.prod_congr rfl
  intro i _
  rw [fourier_apply, fourier_apply, mul_zsmul]
  simp only [finSumFinEquiv.symm_apply_apply, smul_smul]
  rw [mul_comm]

/-- The fourth-power phase extracted from the actual normalized source. -/
def detectorPhase (I : DQLSystem eqs vars)
    (x : ℝ → Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (hvalid : ∀ t, NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue I
      (recoveredState x t) = 0) (t : ℝ) : UnitAddTorus (DetectorPhase eqs vars) :=
  detectorPhaseOfUnitControllers (fun s ↦ (recoveredState x s).base.base.source.controllers)
    (fun s i ↦ ((NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue_eq_zero_iff
      I (recoveredState x s)).mp (hvalid s)).2.2.1 i) t

theorem mFourier_detectorPhase (I : DQLSystem eqs vars)
    (x : ℝ → Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (hvalid : ∀ t, NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue I
      (recoveredState x t) = 0) (t : ℝ) (a : DetectorPhase eqs vars → ℤ) :
    UnitAddTorus.mFourier a (detectorPhase I x hvalid t) =
      characterValue (DetectorCharacterCode.flattenCharacter a)
        (recoveredState x t).base.base.source.controllers :=
  mFourier_detectorPhaseOfUnitControllers _ _ t a

/-- The compiled character frequency equals its angular frequency on the
fourth-power detector torus. -/
theorem detector_characterFrequency_eq_torusRealFrequency
    (parameters : Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → RationalCode)
    (controller : Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
      Controller.ControllerState ℝ)
    (a : DetectorPhase eqs vars → ℤ) :
    LockedControllerPhaseTrajectory.characterFrequency parameters controller
      (DetectorCharacterCode.flattenCharacter a) =
      HGAS.Analysis.torusRealFrequency (fun _ : Unit ↦ a)
        (controllerDetectorTurnsFrequency parameters controller) () := by
  rw [CanonicalFixedDetectorFourierCrosswalk.flattenedCharacterFrequency_eq]
  unfold HGAS.Analysis.torusRealFrequency RadicalClock.frequencyPairing
    controllerDetectorTurnsFrequency
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  field_simp [Real.pi_ne_zero]

/-- The actual extracted phase follows the detector torus translation
through its actual initial point, for all real times. -/
theorem detectorPhase_eq_translation
    (parameters : Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → RationalCode)
    (hp : ∀ i, (1 : ℝ) < (parameters i).decode) (I : DQLSystem eqs vars)
    {x : ℝ → Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ}
    (hx : IsIntegralCurve x (fun _ y ↦ PolynomialFieldCode.realize
      (FixedDetectorPolynomialCode.fieldCode parameters I) y))
    (hrec : ForwardRecurrentAt x 0)
    (hvalid : ∀ t, NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue I
      (recoveredState x t) = 0) (t : ℝ) :
    detectorPhase I x hvalid t = RadicalClock.torusTranslationFlow
      (controllerDetectorTurnsFrequency parameters (detectorInitialController x)) t
      (detectorPhase I x hvalid 0) := by
  have hchar (a : DetectorPhase eqs vars → ℤ) :
      UnitAddTorus.mFourier a (detectorPhase I x hvalid t) =
        UnitAddTorus.mFourier a (RadicalClock.torusTranslationFlow
          (controllerDetectorTurnsFrequency parameters (detectorInitialController x)) t
          (detectorPhase I x hvalid 0)) := by
    rw [mFourier_detectorPhase,
      detector_character_eq_initial_mul_exponential parameters hp I hx hrec hvalid,
      detector_characterFrequency_eq_torusRealFrequency,
      RadicalClock.torusTranslationFlow_apply, RadicalClock.mFourier_add_point,
      RadicalClock.mFourier_torusDisplacement, mFourier_detectorPhase]
    congr 1
    unfold HGAS.Analysis.realFrequencyExponential HGAS.Analysis.torusRealFrequency
    congr 1
    push_cast
    ring
  classical
  funext i
  have hi := hchar (Pi.single i 1)
  rw [UnitAddTorus.mFourier_single, UnitAddTorus.mFourier_single,
    fourier_one, fourier_one, Subtype.coe_inj] at hi
  exact AddCircle.injective_toCircle one_ne_zero hi

/-- The actual gauge component obeys the required physical gauge clock. -/
theorem detector_gauge_hasDerivAt
    (parameters : Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → RationalCode)
    (hp : ∀ i, (1 : ℝ) < (parameters i).decode) (I : DQLSystem eqs vars)
    {x : ℝ → Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ}
    (hx : IsIntegralCurve x (fun _ y ↦ PolynomialFieldCode.realize
      (FixedDetectorPolynomialCode.fieldCode parameters I) y))
    (hrec : ForwardRecurrentAt x 0)
    (hvalid : ∀ t, NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue I
      (recoveredState x t) = 0) (j : Fin vars) (t : ℝ) :
    HasDerivAt (fun s ↦ (recoveredState x s).base.base.gauge j)
      ((((CanonicalFixedDetectorTrajectory.omegaFrequency
        parameters (detectorInitialController x) j +
        2 * CanonicalFixedDetectorTrajectory.numberFrequency
          parameters I (detectorInitialController x) j) / 4 : ℝ) : ℂ) *
        Complex.I * (recoveredState x t).base.base.gauge j) t := by
  have h := (isStructuredTrajectory_of_isIntegralCurve parameters I x hx).gauge j t
  have hlock := detector_controller_eq_initial parameters hp I hx hrec hvalid t
  have hfreq : frequencyValue parameters (DetectorJacobiGaugeData.gaugeExponents I j)
      (recoveredState x t).base.base.source.controllers =
      CanonicalFixedDetectorTrajectory.omegaFrequency parameters (detectorInitialController x) j +
        2 * CanonicalFixedDetectorTrajectory.numberFrequency
          parameters I (detectorInitialController x) j := by
    rw [DetectorJacobiGaugeData.gaugeFrequencyValue_eq_private_add_two_linear]
    unfold ControllerPhaseProductLinearFrequencyCode.value
      CanonicalFixedDetectorTrajectory.omegaFrequency
      CanonicalFixedDetectorTrajectory.numberFrequency
    simp_rw [hlock]
  simpa only [ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.vectorField,
    hfreq, mul_comm Complex.I] using h

end Stability.Selection
