import Stability.Selection.OrdinaryTimeDetectorTheta
import Stability.Selection.OrdinaryTimeDetectorMoments
import HGAS.Arithmetic.NormalizedCorrectedEffectiveColumnFrequencyIrrational

/-!
# Nonresonance of the actual prime-controller frequencies

Distinct prime parameters and forward recurrence force signed prime
square-root frequencies. Thus each nonzero linear column has irrational
linear/private frequency ratio, as required by the theta selector.
See Section 8, Theorem `thm:selector`, and its clock nonresonance step.
-/

noncomputable section

namespace Stability.Selection

open HGAS HGAS.Modular HGAS.Clocks Filter MeasureTheory Topology
open HGAS.FixedDetectorReverseTrajectoryCrosswalk
open HGAS.CanonicalDetectorThetaQuadraticGeometric
open HGAS.Clocks.ObservedTimeChangedControllerPhaseHaar

variable {eqs vars : ℕ}

/-- Nonresonance is a conclusion from the concrete prime-clock ODE and
forward recurrence, not an assumption on a selected measure. -/
theorem detector_primeFrequency_hasNoCharacter
    (p : Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (I : DQLSystem eqs vars)
    {x : ℝ → Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ}
    (hx : IsIntegralCurve x (fun _ y ↦ PolynomialFieldCode.realize
      (FixedDetectorPolynomialCode.fieldCode (primeClockCodes p) I) y))
    (hrec : ForwardRecurrentAt x 0)
    (hvalid : ∀ t, NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue I
      (recoveredState x t) = 0) :
    RadicalIndependence.HasNoNontrivialIntegerCharacter
      (controllerDetectorTurnsFrequency (primeClockCodes p) (detectorInitialController x)) := by
  have hunit : ∀ i, Controller.controllerRadiusSq (detectorInitialController x i) = 1 :=
    ((NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue_eq_zero_iff
      I (recoveredState x 0)).mp (hvalid 0)).2.1
  have heq : ∀ i, Controller.IsControllerEquilibrium (p i : ℝ)
      (detectorInitialController x i) := by
    simpa only [decode_primeClockCodes] using
      detector_initialController_equilibrium (primeClockCodes p) (primeClockCodes_gt_one p hp)
        I hx hrec hvalid
  obtain ⟨sign, hsign, hfrequency⟩ :=
    RadicalClock.exists_signs_for_primeControllerEquilibria
      p (detectorInitialController x) hunit heq
  have hfreq :
      controllerDetectorTurnsFrequency (primeClockCodes p) (detectorInitialController x) =
      ScaledRadicalClock.scaledSignedPrimeSqrtFrequency (2 / Real.pi)
        (fun coordinate : DetectorPhase eqs vars ↦ p (finSumFinEquiv coordinate))
        (fun coordinate ↦ sign (finSumFinEquiv coordinate)) := by
    funext coordinate
    unfold controllerDetectorTurnsFrequency ScaledRadicalClock.scaledSignedPrimeSqrtFrequency
    rw [CanonicalFixedDetectorFundamentalPhase.angularVelocity_primeClockCodes,
      congrFun hfrequency (finSumFinEquiv coordinate)]
    simp only [RadicalIndependence.signedPrimeSqrtFrequency]
    ring
  rw [hfreq]
  exact ScaledRadicalClock.scaledSignedPrimeSqrtFrequency_hasNoCharacter
    (2 / Real.pi) (by positivity) (fun coordinate ↦ p (finSumFinEquiv coordinate))
    (fun coordinate ↦ hp (finSumFinEquiv coordinate))
    (hinj.comp finSumFinEquiv.injective) _ (fun coordinate ↦ hsign (finSumFinEquiv coordinate))

/-- Every syntactically nonzero linear column has irrational actual
linear/private clock ratio. Both clocks retain their selected signs. -/
theorem detector_primeColumn_ratio_irrational
    (p : Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (I : DQLSystem eqs vars) (hcolumns : DQLNonzeroLinearAugmentation.HasNonzeroLinearColumn I)
    {x : ℝ → Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ}
    (hx : IsIntegralCurve x (fun _ y ↦ PolynomialFieldCode.realize
      (FixedDetectorPolynomialCode.fieldCode (primeClockCodes p) I) y))
    (hrec : ForwardRecurrentAt x 0)
    (hvalid : ∀ t, NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue I
      (recoveredState x t) = 0) (j : Fin vars) :
    Irrational (CanonicalFixedDetectorTrajectory.numberFrequency
        (primeClockCodes p) I (detectorInitialController x) j /
      CanonicalFixedDetectorTrajectory.omegaFrequency
        (primeClockCodes p) (detectorInitialController x) j) := by
  let frequency :=
    controllerDetectorTurnsFrequency (primeClockCodes p) (detectorInitialController x)
  have hratio :=
    NormalizedCorrectedEffectiveColumnFrequencyIrrational.linear_div_private_pairing_irrational
      I hcolumns frequency (detector_primeFrequency_hasNoCharacter p hp hinj I hx hrec hvalid) j
  rw [← privateAngularFrequency_controllerDetectorTurnsFrequency,
    ← linearAngularFrequency_controllerDetectorTurnsFrequency]
  have hcancel : linearAngularFrequency I j frequency / privateAngularFrequency j frequency =
      (∑ coordinate : DetectorPhase eqs vars,
        (DetectorCharacterCode.linearCharacter I j coordinate : ℝ) * frequency coordinate) /
      (∑ coordinate : DetectorPhase eqs vars,
        (DetectorCharacterCode.privateCharacter j coordinate : ℝ) * frequency coordinate) := by
    unfold linearAngularFrequency privateAngularFrequency
      HGAS.Analysis.torusRealFrequency RadicalClock.frequencyPairing
    field_simp [Real.pi_ne_zero]
  change Irrational (linearAngularFrequency I j frequency / privateAngularFrequency j frequency)
  rw [hcancel]
  exact hratio

/-- The concrete theta-output selector with the arithmetic ratio
hypothesis discharged by distinct prime parameters and nonzero columns. -/
theorem detector_primeThetaOutput_eq_thetaSum
    (p : Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (I : DQLSystem eqs vars) (hcolumns : DQLNonzeroLinearAugmentation.HasNonzeroLinearColumn I)
    {x : ℝ → Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ}
    (hx : IsIntegralCurve x (fun _ y ↦ PolynomialFieldCode.realize
      (FixedDetectorPolynomialCode.fieldCode (primeClockCodes p) I) y))
    (hrec : ForwardRecurrentAt x 0)
    (hvalid : ∀ t, NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue I
      (recoveredState x t) = 0) (j : Fin vars)
    {μ : ℝ} (hμ : 1 ≤ μ) (B : ℝ)
    (hgrowth : ∀ᶠ H : ℝ in atTop,
      H⁻¹ * (∫ t in (0 : ℝ)..H, (Real.sqrt (HGAS.normSq (x t))) ^ μ) ≤ B)
    (hmeans : ∀ r : Fin FixedDetectorMomentCode.localMomentCount,
      Tendsto (HGAS.Analysis.cesaroMeanAt (fun t ↦
        ControllerPhaseProductCharacterCode.evalPair
          (FixedDetectorMomentCode.localMomentCode I j r) (x t))) atTop (𝓝 0)) :
    ∀ t, (recoveredState x t).base.base.gauge j *
        ((recoveredState x t).base.base.source.linked j).jacobi.T1 =
      ∑' n : ℤ, DetectorFactorizedFourier.thetaTerm (1 / 256 : ℝ) I j n
        (detectorPhase I x hvalid t) :=
  detector_thetaOutput_eq_thetaSum (primeClockCodes p) (primeClockCodes_gt_one p hp) I
    hx hrec hvalid j (detector_primeColumn_ratio_irrational p hp hinj I hcolumns hx hrec hvalid j)
    hμ B hgrowth hmeans

/-- Scalar-code version of the concrete theta selector. Its analytic
inputs are exactly forward recurrence, zero validity, full forward means
of the real polynomial test coordinates, and bounded Euclidean growth.
The prime and nonzero-column data are the source's arithmetic parameters.
-/
theorem detector_primeThetaOutput_eq_thetaSum_of_scalarMeans
    (p : Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (I : DQLSystem eqs vars) (hcolumns : DQLNonzeroLinearAugmentation.HasNonzeroLinearColumn I)
    {x : ℝ → Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ}
    (hx : IsIntegralCurve x (fun _ y ↦ PolynomialFieldCode.realize
      (FixedDetectorPolynomialCode.fieldCode (primeClockCodes p) I) y))
    (hrec : ForwardRecurrentAt x 0)
    (hvalid : ∀ t, NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue I
      (recoveredState x t) = 0)
    {μ : ℝ} (hμ : 1 ≤ μ) (B : ℝ)
    (hgrowth : ∀ᶠ H : ℝ in atTop,
      H⁻¹ * (∫ t in (0 : ℝ)..H, (Real.sqrt (HGAS.normSq (x t))) ^ μ) ≤ B)
    (hmeans : ∀ k : Fin (FixedDetectorMomentCode.scalarMomentCount vars),
      Tendsto (fun H : ℝ ↦ H⁻¹ * ∫ t in (0 : ℝ)..H,
        MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) (x t)
          (PolynomialCode.decode (FixedDetectorMomentCode.scalarMomentCode I k))) atTop (𝓝 0)) :
    ∀ j t, (recoveredState x t).base.base.gauge j *
        ((recoveredState x t).base.base.source.linked j).jacobi.T1 =
      ∑' n : ℤ, DetectorFactorizedFourier.thetaTerm (1 / 256 : ℝ) I j n
        (detectorPhase I x hvalid t) := by
  intro j
  exact detector_primeThetaOutput_eq_thetaSum p hp hinj I hcolumns hx hrec hvalid j hμ B hgrowth
    (detector_complexMeans_of_scalarMeans I hx.continuous hmeans j)

end Stability.Selection
