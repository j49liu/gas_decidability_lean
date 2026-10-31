import Stability.Selection.OrdinaryTimePrimeClocks
import HGAS.Arithmetic.DetectorPoissonReciprocalSemantics

/-!
# Factorization of the actual polynomial detector

Pointwise validity selects the two reciprocal graphs. The actual RHS
oscillator follows its controller character with a constant unit phase
factor. Together with the theta-output identities, these give the literal
detector factorization for all real times (Section 8, Theorem `thm:selector`).
-/

noncomputable section

namespace Stability.Selection

open HGAS HGAS.Modular HGAS.Clocks Filter MeasureTheory Topology
open scoped BigOperators
open HGAS.FixedDetectorReverseTrajectoryCrosswalk
open HGAS.Clocks.ControllerPhaseProductCharacterCode
open HGAS.CanonicalDetectorThetaQuadraticGeometric
open HGAS.NormalizedCorrectedFixedDetectorNormalizationConsequences

variable {eqs vars : ℕ}

theorem detector_reciprocalGraphResidual_zero
    (I : DQLSystem eqs vars)
    {x : ℝ → Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ}
    (hvalid : ∀ t, NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue I
      (recoveredState x t) = 0) (t : ℝ)
    (k : Fin (DetectorPoissonReciprocalCode.reciprocalCount vars)) :
    DetectorPoissonReciprocalCode.reciprocalGraphResidual I (recoveredState x t).base k = 0 := by
  apply (DetectorPoissonReciprocalCode.forall_eval_residualCode_eq_zero_iff_graphResidual
    I (recoveredState x t).base).mp
  exact ((NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue_eq_zero_iff
    I (recoveredState x t)).mp (hvalid t)).1.2.2

/-- The actual stored reciprocals are the two literal inverse factors. -/
theorem detector_reciprocals_eq_inv
    (I : DQLSystem eqs vars)
    {x : ℝ → Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ}
    (hvalid : ∀ t, NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue I
      (recoveredState x t) = 0) (t : ℝ) (j : Fin vars) :
    (recoveredState x t).base.reciprocal (DetectorPoissonReciprocalCode.positiveIndex j) =
      (1 - (1 / 2 : ℂ) * DetectorPoissonReciprocalCode.poissonCharacterValue
        I (recoveredState x t).base j)⁻¹ ∧
    (recoveredState x t).base.reciprocal (DetectorPoissonReciprocalCode.negativeIndex j) =
      (1 - (1 / 2 : ℂ) * (DetectorPoissonReciprocalCode.poissonCharacterValue
        I (recoveredState x t).base j)⁻¹)⁻¹ := by
  have hunit := onPhaseCircles_of_validityEnergyValue_eq_zero I _ (hvalid t)
  have hpos := DetectorPoissonReciprocalCode.positiveReciprocal_eq_inv I _ j hunit
    (detector_reciprocalGraphResidual_zero I hvalid t _)
  have hneg := DetectorPoissonReciprocalCode.negativeReciprocal_eq_inv I _ j hunit
    (detector_reciprocalGraphResidual_zero I hvalid t _)
  constructor <;> norm_num at hpos hneg ⊢ <;> assumption

theorem detector_poissonFactor_eq_poissonSeries
    (I : DQLSystem eqs vars)
    {x : ℝ → Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ}
    (hvalid : ∀ t, NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue I
      (recoveredState x t) = 0) (t : ℝ) (j : Fin vars) :
    (3 / 4 : ℂ) *
        (recoveredState x t).base.reciprocal (DetectorPoissonReciprocalCode.positiveIndex j) *
        (recoveredState x t).base.reciprocal (DetectorPoissonReciprocalCode.negativeIndex j) =
      ∑' s : ℤ, DetectorFactorizedFourier.poissonTerm (1 / 2 : ℝ) I j s
        (detectorPhase I x hvalid t) := by
  obtain ⟨hpos, hneg⟩ := detector_reciprocals_eq_inv I hvalid t j
  rw [hpos, hneg, CanonicalFixedDetectorFourierCrosswalk.tsum_poissonTerm
    (by norm_num) (by norm_num)]
  have hcharacter : DetectorPoissonReciprocalCode.poissonCharacterValue
      I (recoveredState x t).base j =
      UnitAddTorus.mFourier (DetectorCharacterCode.poissonArgumentCharacter I j)
        (detectorPhase I x hvalid t) := (mFourier_detectorPhase I x hvalid t _).symm
  rw [hcharacter, div_eq_mul_inv]
  norm_num
  rw [mul_assoc, ← mul_inv_rev]
  congr 2
  all_goals ring

/-- The RHS oscillator read as a complex number. -/
def detectorRHS
    (x : ℝ → Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ) (t : ℝ) : ℂ :=
  PhaseClockFlow.phaseStateComplex (recoveredState x t).rhs

/-- Initial phase factor between the actual oscillator and the required
RHS torus character. It need not equal the initial oscillator itself. -/
def detectorRHSPhaseFactor (I : DQLSystem eqs vars)
    (x : ℝ → Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (hvalid : ∀ t, NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue I
      (recoveredState x t) = 0) : ℂ :=
  detectorRHS x 0 /
    UnitAddTorus.mFourier (DetectorCharacterCode.rhsCharacter I) (detectorPhase I x hvalid 0)

theorem norm_detectorRHSPhaseFactor
    (I : DQLSystem eqs vars)
    {x : ℝ → Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ}
    (hvalid : ∀ t, NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue I
      (recoveredState x t) = 0) : ‖detectorRHSPhaseFactor I x hvalid‖ = 1 := by
  have hradius := ((NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue_eq_zero_iff
    I (recoveredState x 0)).mp (hvalid 0)).2.2.2
  have hsq : ‖detectorRHS x 0‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simpa [detectorRHS, PhaseClockFlow.phaseStateComplex, Controller.phaseRadiusSq, pow_two]
      using hradius
  have hrhs : ‖detectorRHS x 0‖ = 1 := by nlinarith [norm_nonneg (detectorRHS x 0)]
  rw [detectorRHSPhaseFactor, norm_div, HGAS.Analysis.norm_mFourier_apply, hrhs, div_one]

variable (parameters : Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → RationalCode)
variable (hp : ∀ i, (1 : ℝ) < (parameters i).decode) (I : DQLSystem eqs vars)
variable {x : ℝ → Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ}
variable (hx : IsIntegralCurve x (fun _ y ↦ PolynomialFieldCode.realize
  (FixedDetectorPolynomialCode.fieldCode parameters I) y))
variable (hrec : ForwardRecurrentAt x 0)
variable (hvalid : ∀ t, NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue I
  (recoveredState x t) = 0)

include parameters hp hx hrec hvalid

theorem detector_rhs_hasDerivAt (t : ℝ) :
    HasDerivAt (detectorRHS x)
      (((-4 * CanonicalFixedDetectorTrajectory.rhsFrequency
          parameters I (detectorInitialController x) : ℝ) : ℂ) *
        Complex.I * detectorRHS x t) t := by
  have hlock := detector_controller_eq_initial parameters hp I hx hrec hvalid t
  have hfreq : RHSOscillatorPolynomialCode.weightedFrequency
      (FixedDetectorPolynomialCode.rhsWeightCode I)
      (FixedDetectorPolynomialCode.equationFrequencyCode parameters)
      (DetectorPoissonReciprocalCode.point (recoveredState x t).base) =
      CanonicalFixedDetectorTrajectory.rhsFrequency parameters I (detectorInitialController x) := by
    rw [FixedDetectorPolynomialCode.weightedFrequency_eq]
    unfold CanonicalFixedDetectorTrajectory.rhsFrequency
    apply Finset.sum_congr rfl
    intro row _
    congr 1
    unfold frequencyValue LockedControllerPhaseTrajectory.characterFrequency
      LockedControllerPhaseTrajectory.angularVelocity
    apply Finset.sum_congr rfl
    intro i _
    rw [hlock i]
    ring
  have hs := isStructuredTrajectory_of_isIntegralCurve parameters I x hx
  have hc := hs.rhs.c t
  have hd := hs.rhs.d t
  rw [RHSOscillatorPolynomialCode.oscillatorField, hfreq] at hc hd
  have hcomplex : HasDerivAt (detectorRHS x)
      (PhaseClockFlow.phaseStateComplex (Controller.phaseField
        (-4 * CanonicalFixedDetectorTrajectory.rhsFrequency
          parameters I (detectorInitialController x))
        (recoveredState x t).rhs)) t := by
    apply HGAS.HasDerivAt.complex_of_re_im
    · simpa [detectorRHS, PhaseClockFlow.phaseStateComplex] using hc
    · simpa [detectorRHS, PhaseClockFlow.phaseStateComplex] using hd
  simpa only [PhaseClockFlow.phaseStateComplex_phaseField, detectorRHS] using hcomplex

theorem detector_rhs_eq_phaseFactor_mul_character (t : ℝ) :
    detectorRHS x t = detectorRHSPhaseFactor I x hvalid *
      UnitAddTorus.mFourier (DetectorCharacterCode.rhsCharacter I)
        (detectorPhase I x hvalid t) := by
  have heq := eq_initial_mul_frequency_of_hasDerivAt (detectorRHS x)
    (-4 * CanonicalFixedDetectorTrajectory.rhsFrequency parameters I (detectorInitialController x))
    (detector_rhs_hasDerivAt parameters hp I hx hrec hvalid) t
  have hne : UnitAddTorus.mFourier (DetectorCharacterCode.rhsCharacter I)
      (detectorPhase I x hvalid 0) ≠ 0 := by
    intro hzero
    have hnorm := HGAS.Analysis.norm_mFourier_apply
      (DetectorCharacterCode.rhsCharacter I) (detectorPhase I x hvalid 0)
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm
  rw [heq, mFourier_detectorPhase,
    detector_character_eq_initial_mul_exponential parameters hp I hx hrec hvalid,
    CanonicalFixedDetectorFourierCrosswalk.rhsCharacterFrequency_eq]
  unfold detectorRHSPhaseFactor
  rw [← mFourier_detectorPhase I x hvalid 0]
  field_simp

/-- Actual theta and reciprocal outputs assemble into the Fourier
detector with the actual unit RHS phase factor, at every real time. -/
theorem detector_value_eq_phaseFactor_mul_expanded
    (htheta : ∀ j t, (recoveredState x t).base.base.gauge j *
      ((recoveredState x t).base.base.source.linked j).jacobi.T1 =
      ∑' n : ℤ, DetectorFactorizedFourier.thetaTerm (1 / 256 : ℝ) I j n
        (detectorPhase I x hvalid t)) (t : ℝ) :
    FixedDetectorDriftCode.detectorValue (recoveredState x t) =
      detectorRHSPhaseFactor I x hvalid *
        expandedDetector (1 / 256 : ℝ) (1 / 2 : ℝ) I (detectorPhase I x hvalid t) := by
  have hproduct :
      (∏ j : Fin vars,
        ((recoveredState x t).base.base.gauge j *
            ((recoveredState x t).base.base.source.linked j).jacobi.T1) *
          ((3 / 4 : ℂ) *
            (recoveredState x t).base.reciprocal (DetectorPoissonReciprocalCode.positiveIndex j) *
            (recoveredState x t).base.reciprocal (DetectorPoissonReciprocalCode.negativeIndex j))) =
      (∏ j : Fin vars, ∑' n : ℤ, DetectorFactorizedFourier.thetaTerm (1 / 256 : ℝ)
        I j n (detectorPhase I x hvalid t)) *
      (∏ j : Fin vars, ∑' s : ℤ, DetectorFactorizedFourier.poissonTerm (1 / 2 : ℝ)
        I j s (detectorPhase I x hvalid t)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    rw [htheta j t, detector_poissonFactor_eq_poissonSeries I hvalid t j]
  rw [← DetectorFactorizedFourier.factorizedDetector_eq_expandedDetector
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  unfold FixedDetectorDriftCode.detectorValue
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat]
  have hrhs : (⟨(recoveredState x t).rhs.c, (recoveredState x t).rhs.d⟩ : ℂ) =
      detectorRHS x t := by
    apply Complex.ext <;> simp [detectorRHS, PhaseClockFlow.phaseStateComplex]
  rw [hrhs, detector_rhs_eq_phaseFactor_mul_character parameters hp I hx hrec hvalid, hproduct]
  unfold DetectorFactorizedFourier.factorizedDetector
  ring

end Stability.Selection
