import Stability.Selection.OrdinaryTimeDetectorFactorization
import HGAS.Arithmetic.DetectorFourierCesaroArbitraryHorizon

/-!
# Arithmetic averages on the actual source trajectory

The actual polynomial detector has a full real-horizon forward mean:
its unit RHS phase factor times the arithmetic Fourier constant. Hence,
on any source trajectory satisfying the selector hypotheses, the detector
mean is zero exactly when the DQL system has no integer solution.

This is the exclusion direction of Section 8, Corollary `cor:yes`.
It does not assert existence of an intended trajectory in the converse
direction, or extract a complete trajectory from a compact invariant measure.
-/

noncomputable section

namespace Stability.Selection

open HGAS HGAS.Modular HGAS.Clocks Filter MeasureTheory Topology
open HGAS.FixedDetectorReverseTrajectoryCrosswalk
open HGAS.CanonicalDetectorThetaQuadraticGeometric
open HGAS.Clocks.ControllerPhaseProductCharacterCode
open HGAS.Clocks.ObservedTimeChangedControllerPhaseHaar

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

variable {eqs vars : ℕ}

/-- The arithmetic constant term vanishes exactly in the unsolvable case. -/
theorem detector_integral_eq_zero_iff_not_solvable (I : DQLSystem eqs vars) :
    (∫ phase : UnitAddTorus (DetectorPhase eqs vars),
      expandedDetector (1 / 256 : ℝ) (1 / 2 : ℝ) I phase) = 0 ↔ ¬ I.Solvable := by
  constructor
  · intro hzero hsol
    exact (integral_expandedDetector_ne_zero_of_solvable
      (lambda := 1 / 256) (eta := 1 / 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) I hsol) hzero
  · intro hnot
    rw [integral_expandedDetector_eq_ofReal_selectedPairSum
      (lambda := 1 / 256) (eta := 1 / 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    have hweight : selectedPairWeight (1 / 256 : ℝ) (1 / 2 : ℝ) I = fun _ ↦ 0 := by
      funext p
      have hnotSat : ¬ I.Satisfies p.1 := fun h ↦ hnot ⟨p.1, h⟩
      simp [selectedPairWeight, hnotSat]
    rw [hweight]
    simp

/-- The arbitrary-sequence Fourier theorem yields the full real-horizon
limit; no distinguished subsequence is selected. -/
theorem detector_translation_forwardMean_tendsto
    (I : DQLSystem eqs vars) (frequency : DetectorPhase eqs vars → ℝ)
    (hfrequency : RadicalIndependence.HasNoNontrivialIntegerCharacter frequency)
    (phase₀ : UnitAddTorus (DetectorPhase eqs vars)) :
    Tendsto (HGAS.Analysis.cesaroMeanAt (fun t ↦
      expandedDetector (1 / 256 : ℝ) (1 / 2 : ℝ) I
        (RadicalClock.torusTranslationFlow frequency t phase₀))) atTop
      (𝓝 (∫ phase : UnitAddTorus (DetectorPhase eqs vars),
        expandedDetector (1 / 256 : ℝ) (1 / 2 : ℝ) I phase)) := by
  apply Filter.tendsto_iff_seq_tendsto.mpr
  intro T hT
  exact cesaroMeanAt_expandedDetector_translation_tendsto_integral
    (lambda := 1 / 256) (eta := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) I frequency hfrequency phase₀ hT

/-- Complex zero mean is equivalent to zero mean of both real polynomial
test coordinates, at the same full real horizons. -/
theorem forwardMean_zero_iff_components {f : ℝ → ℂ} (hf : Continuous f) :
    Tendsto (HGAS.Analysis.cesaroMeanAt f) atTop (𝓝 0) ↔
      Tendsto (fun H : ℝ ↦ H⁻¹ * ∫ t in (0 : ℝ)..H, (f t).re) atTop (𝓝 0) ∧
      Tendsto (fun H : ℝ ↦ H⁻¹ * ∫ t in (0 : ℝ)..H, (f t).im) atTop (𝓝 0) := by
  constructor
  · intro h
    constructor
    · simpa [Function.comp_def, forwardMean_eq_components hf] using
        (Complex.continuous_re.tendsto 0).comp h
    · simpa [Function.comp_def, forwardMean_eq_components hf] using
        (Complex.continuous_im.tendsto 0).comp h
  · rintro ⟨hre, him⟩
    exact tendsto_forwardMean_zero_of_components hf hre him

variable (p : Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → ℕ)
variable (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
variable (I : DQLSystem eqs vars)
variable (hcolumns : DQLNonzeroLinearAugmentation.HasNonzeroLinearColumn I)
variable {x : ℝ → Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ}
variable (hx : IsIntegralCurve x (fun _ y ↦ PolynomialFieldCode.realize
  (FixedDetectorPolynomialCode.fieldCode (primeClockCodes p) I) y))
variable (hrec : ForwardRecurrentAt x 0)
variable (hvalid : ∀ t, NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue I
  (recoveredState x t) = 0)
variable {μ : ℝ} (hμ : 1 ≤ μ) (B : ℝ)
variable (hgrowth : ∀ᶠ H : ℝ in atTop,
  H⁻¹ * (∫ t in (0 : ℝ)..H, (Real.sqrt (HGAS.normSq (x t))) ^ μ) ≤ B)
variable (hmeans : ∀ k : Fin (FixedDetectorMomentCode.scalarMomentCount vars),
  Tendsto (fun H : ℝ ↦ H⁻¹ * ∫ t in (0 : ℝ)..H,
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) (x t)
      (PolynomialCode.decode (FixedDetectorMomentCode.scalarMomentCode I k))) atTop (𝓝 0))

include p hp hinj hcolumns hx hrec hvalid hμ B hgrowth hmeans

/-- The literal polynomial detector equals its Fourier expression on the
actual phase trajectory. No theta identities are assumed here. -/
theorem detector_prime_value_eq_phaseFactor_mul_expanded (t : ℝ) :
    evalPair (FixedDetectorPolynomialCode.detectorCode (eqs := eqs) (vars := vars)) (x t) =
      detectorRHSPhaseFactor I x hvalid *
        expandedDetector (1 / 256 : ℝ) (1 / 2 : ℝ) I (detectorPhase I x hvalid t) := by
  have hsemantic := FixedDetectorDriftCode.evalPair_detectorCode_eq_detectorValue
    (recoveredState x t)
  rw [point_recoveredState] at hsemantic
  rw [hsemantic]
  exact detector_value_eq_phaseFactor_mul_expanded
    (primeClockCodes p) (primeClockCodes_gt_one p hp) I hx hrec hvalid
    (detector_primeThetaOutput_eq_thetaSum_of_scalarMeans
      p hp hinj I hcolumns hx hrec hvalid hμ B hgrowth hmeans) t

/-- Full real-horizon forward average of the actual polynomial detector. -/
theorem detector_prime_forwardMean_tendsto :
    Tendsto (HGAS.Analysis.cesaroMeanAt (fun t ↦
      evalPair (FixedDetectorPolynomialCode.detectorCode (eqs := eqs) (vars := vars)) (x t)))
      atTop (𝓝 (detectorRHSPhaseFactor I x hvalid *
        ∫ phase : UnitAddTorus (DetectorPhase eqs vars),
          expandedDetector (1 / 256 : ℝ) (1 / 2 : ℝ) I phase)) := by
  have hlimit := detector_translation_forwardMean_tendsto I
    (controllerDetectorTurnsFrequency (primeClockCodes p) (detectorInitialController x))
    (detector_primeFrequency_hasNoCharacter p hp hinj I hx hrec hvalid)
    (detectorPhase I x hvalid 0)
  have heq (t : ℝ) :
      evalPair (FixedDetectorPolynomialCode.detectorCode (eqs := eqs) (vars := vars)) (x t) =
        detectorRHSPhaseFactor I x hvalid * expandedDetector (1 / 256 : ℝ) (1 / 2 : ℝ) I
          (RadicalClock.torusTranslationFlow
            (controllerDetectorTurnsFrequency (primeClockCodes p) (detectorInitialController x))
            t (detectorPhase I x hvalid 0)) := by
    rw [detector_prime_value_eq_phaseFactor_mul_expanded
      p hp hinj I hcolumns hx hrec hvalid hμ B hgrowth hmeans t,
      detectorPhase_eq_translation
        (primeClockCodes p) (primeClockCodes_gt_one p hp) I hx hrec hvalid t]
  have hlinear (c : ℂ) (f : ℝ → ℂ) :
      HGAS.Analysis.cesaroMeanAt (fun t ↦ c * f t) =
        fun H ↦ c * HGAS.Analysis.cesaroMeanAt f H := by
    funext H
    exact cesaroMeanAt_const_mul c f H
  simp_rw [heq]
  rw [hlinear]
  exact hlimit.const_mul (detectorRHSPhaseFactor I x hvalid)

/-- Conditional on the literal selector hypotheses, the detector has
zero forward mean exactly when the integer system is unsolvable.
This equivalence concerns a given source trajectory, not its existence. -/
theorem detector_prime_forwardMean_zero_iff_not_solvable :
    Tendsto (HGAS.Analysis.cesaroMeanAt (fun t ↦
      evalPair (FixedDetectorPolynomialCode.detectorCode (eqs := eqs) (vars := vars)) (x t)))
      atTop (𝓝 0) ↔ ¬ I.Solvable := by
  have hlimit := detector_prime_forwardMean_tendsto p hp hinj I hcolumns
    hx hrec hvalid hμ B hgrowth hmeans
  have hphase : detectorRHSPhaseFactor I x hvalid ≠ 0 := by
    intro hzero
    have hnorm := norm_detectorRHSPhaseFactor I hvalid
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm
  constructor
  · intro hzero
    have hc := tendsto_nhds_unique hlimit hzero
    exact (detector_integral_eq_zero_iff_not_solvable I).mp
      ((mul_eq_zero.mp hc).resolve_left hphase)
  · intro hnot
    simpa only [(detector_integral_eq_zero_iff_not_solvable I).mpr hnot, mul_zero] using hlimit

/-- The two literal scalar detector-code means vanish exactly in the
unsolvable case, on any trajectory satisfying the selector hypotheses.
This is the real-polynomial test interface used by the source system. -/
theorem detector_prime_scalarMeans_zero_iff_not_solvable :
    (Tendsto (fun H : ℝ ↦ H⁻¹ * ∫ t in (0 : ℝ)..H,
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) (x t)
        (PolynomialCode.decode
          (FixedDetectorPolynomialCode.detectorCode (eqs := eqs) (vars := vars)).1))
      atTop (𝓝 0) ∧
    Tendsto (fun H : ℝ ↦ H⁻¹ * ∫ t in (0 : ℝ)..H,
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) (x t)
        (PolynomialCode.decode
          (FixedDetectorPolynomialCode.detectorCode (eqs := eqs) (vars := vars)).2))
      atTop (𝓝 0)) ↔ ¬ I.Solvable := by
  exact (forwardMean_zero_iff_components
    (continuous_evalPair_comp FixedDetectorPolynomialCode.detectorCode hx.continuous)).symm.trans
    (detector_prime_forwardMean_zero_iff_not_solvable
      p hp hinj I hcolumns hx hrec hvalid hμ B hgrowth hmeans)

end Stability.Selection
