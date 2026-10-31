import Stability.Selection.OrdinaryTimeSourceFlow
import HGAS.Arithmetic.NormalizedCorrectedCanonicalDriftFourierCrosswalk

/-!
# Prime-clock dynamics on the literal source graph

The chosen normalized positive controller has angular frequency `√p`.
At zero phase the literal graph is exactly the canonical detector path,
so the arithmetic Fourier identity applies to its actual scalar tests.
-/

noncomputable section

namespace Stability.Selection

open HGAS HGAS.Analysis HGAS.Modular HGAS.Clocks
open CanonicalFixedDetectorTrajectory CanonicalFixedDetectorFundamentalPhase
open ObservedTimeChangedControllerPhaseHaar
open HGAS.NormalizedCorrectedCanonicalFixedDetectorGraph

variable {eqs vars : ℕ}

/-- Positivity fixes the sign of the square-root angular clock. -/
theorem positiveController_lockedFrequency (p : ℝ) (hp : 1 < p) :
    Controller.lockedFrequency p (ExplicitPositiveControllerEquilibrium.state p) =
      Real.sqrt p := by
  have hr : 0 ≤ (ExplicitPositiveControllerEquilibrium.state p).r := by
    unfold ExplicitPositiveControllerEquilibrium.state
    rw [ControllerFlow.circleControllerState_r]
    unfold ExplicitPositiveControllerEquilibrium.circle
    rw [ControllerFlow.coe_normalizeToCircle]
    simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, ExplicitPositiveControllerEquilibrium.eigenvector]
    positivity
  have hl := (Controller.isControllerEquilibrium_iff_lock_of_unit p _
    (ExplicitPositiveControllerEquilibrium.state_radiusSq p)).mp
      (ExplicitPositiveControllerEquilibrium.state_isControllerEquilibrium p hp)
  have hs := Controller.lockedFrequency_sq_of_lock p _ hl
  have hf : 0 ≤ Controller.lockedFrequency p
      (ExplicitPositiveControllerEquilibrium.state p) :=
    mul_nonneg (zero_lt_one.trans hp).le hr
  nlinarith [Real.sq_sqrt (zero_lt_one.trans hp).le, Real.sqrt_nonneg p]

theorem positivePrimeController_turnsFrequency
    (p : Fin (vars + eqs) → ℕ) (hp : ∀ i, (p i).Prime) :
    turnsFrequency (primeClockCodes p)
      (fun i ↦ ExplicitPositiveControllerEquilibrium.state (p i : ℝ)) =
      ScaledRadicalClock.scaledSignedPrimeSqrtFrequency
        (1 / (2 * Real.pi)) p (fun _ ↦ 1) := by
  apply turnsFrequency_primeClockCodes_eq_scaledRadical
  funext i
  rw [positiveController_lockedFrequency _ (by exact_mod_cast (hp i).one_lt)]
  simp [RadicalIndependence.signedPrimeSqrtFrequency]

/-- The actual positive-prime source graph is an all-real integral curve
through each torus point. -/
theorem positivePrimeSourceGraph_isIntegralCurve
    (I : DQLSystem eqs vars) (p : Fin (vars + eqs) → ℕ)
    (hp : ∀ i, (p i).Prime) (x : UnitAddTorus (Fin (vars + eqs))) :
    IsIntegralCurve (fun t ↦ intendedSourceGraph I
      (fun i ↦ ExplicitPositiveControllerEquilibrium.state (p i : ℝ))
      (RadicalClock.torusTranslationFlow
        (ScaledRadicalClock.scaledSignedPrimeSqrtFrequency
          (1 / (2 * Real.pi)) p (fun _ ↦ 1)) t x))
      (fun _ y ↦ PolynomialFieldCode.realize
        (FixedDetectorPolynomialCode.fieldCode (primeClockCodes p) I) y) := by
  rw [← positivePrimeController_turnsFrequency p hp]
  apply intendedSourceGraph_isIntegralCurve
  intro i
  rw [decode_primeClockCodes]
  exact ExplicitPositiveControllerEquilibrium.state_isControllerEquilibrium _
    (by exact_mod_cast (hp i).one_lt)

/-- Every point of the literal source graph passes the algebraic validity
tests. This is independent of solvability and of the chosen clock rates. -/
theorem intendedSourceStateGraph_validityEnergy_zero
    (I : DQLSystem eqs vars)
    (controller : Fin (vars + eqs) → Controller.ControllerState ℝ)
    (hcontroller : ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (x : UnitAddTorus (Fin (vars + eqs))) :
    NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue I
      (intendedSourceStateGraph I controller x) = 0 := by
  obtain ⟨v, rfl⟩ : ∃ v : Fin (vars + eqs) → ℝ, (fun i ↦ (v i : UnitAddCircle)) = x := by
    choose v hv using fun i ↦ QuotientAddGroup.mk_surjective (x i)
    exact ⟨v, funext hv⟩
  let parameters : Fin (vars + eqs) → RationalCode := fun _ ↦ RationalCode.zero
  have he := intendedSourceStateGraph_flow_eq_canonical parameters I controller v 0
  simp only [Flow.map_zero, id_eq] at he
  rw [he]
  apply fixedDetectorPath_normalizedValidityEnergyValue_eq_zero _ _ _ _ _ _ _ hcontroller
  intro j t
  rw [← sourceEllipticParameter_flow, ← fundamentalThetaParameter_flow]
  have ht := halfPeriodThetaGraph_eq_jacobiTheta1 I j
    (fun i ↦ v i + t * turnsFrequency parameters controller i)
  change halfPeriodThetaGraph I j _ = _ at ht
  intro hz
  exact left_ne_zero_of_mul_eq_one (thetaReciprocalGraph_identity I j _) (ht.trans hz)

/-- Zero fundamental phase gives exactly the previous canonical path,
including the initial RHS oscillator and gauge. -/
theorem intendedSourceStateGraph_zeroOrbit
    (parameters : Fin (vars + eqs) → RationalCode) (I : DQLSystem eqs vars)
    (controller : Fin (vars + eqs) → Controller.ControllerState ℝ) (t : ℝ) :
    intendedSourceStateGraph I controller
      (RadicalClock.torusTranslationFlow (turnsFrequency parameters controller) t 0) =
      CorrectedCanonicalFixedDetectorMomentFourierCrosswalk.canonicalState
        parameters I controller t := by
  have h := intendedSourceStateGraph_flow_eq_canonical parameters I controller (fun _ ↦ 0) t
  have hcircle : sourceCharacterCircle
      (DetectorCharacterCode.flattenCharacter (DetectorCharacterCode.rhsCharacter I))
      (fun _ ↦ ((0 : ℝ) : UnitAddCircle)) = 1 := by
    apply Circle.coe_injective
    simp [sourceCharacterCircle, UnitAddTorus.mFourier]
  rw [hcircle] at h
  change intendedSourceStateGraph I controller
    (RadicalClock.torusTranslationFlow (turnsFrequency parameters controller) t 0) = _ at h
  simpa [CorrectedCanonicalFixedDetectorMomentFourierCrosswalk.canonicalState,
    sourceEllipticParameter, fundamentalThetaParameter,
    CanonicalFixedDetectorChart.halfPeriodInitialElliptic,
    LockedControllerPhaseTrajectory.onePhase] using h

/-- The exact normalized scalar drift on the literal zero-phase graph
is the proved no-instance Fourier family, in physical time. -/
theorem intendedSourceGraph_zeroOrbit_drift_eq_fourier
    (parameters : Fin (vars + eqs) → RationalCode) (I : DQLSystem eqs vars)
    (controller : Fin (vars + eqs) → Controller.ControllerState ℝ)
    (hcontroller : ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (hnot : ¬ I.Solvable) (t : ℝ) :
    NormalizedCorrectedFixedDetectorDriftCode.driftValue I
      (intendedSourceStateGraph I controller
        (RadicalClock.torusTranslationFlow (turnsFrequency parameters controller) t 0)) =
      realTorusFourierVector
        (NormalizedCorrectedCanonicalDriftFourierFamily.Index I hnot)
        (NormalizedCorrectedCanonicalDriftFourierFamily.coefficient I hnot)
        (NormalizedCorrectedCanonicalDriftFourierFamily.exponent I hnot)
        (RadicalClock.torusTranslationFlow (turnsFrequency parameters controller) t 0) := by
  rw [intendedSourceStateGraph_zeroOrbit,
    NormalizedCorrectedCanonicalDriftFourierCrosswalk.canonical_driftValue_eq_realTorusFourierVector
      parameters I controller hcontroller hnot,
    fundamentalPhasePath_eq_flow_zero]

end Stability.Selection
