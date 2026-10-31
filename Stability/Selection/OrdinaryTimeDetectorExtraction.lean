import Stability.Selection.OrdinaryTimeBasePhysicalOrbit
import Stability.Selection.OrdinaryTimeSourceEquivalence

/-!
# Extracting an actual detector trajectory from its compact base measure

An ergodic invariant probability for the literal compact base field, with
full mass off the equator and zero compact test means, gives a complete
source trajectory passing all tests. Its Euclidean growth exponent is the
actual even denominator-clearing exponent. No selected orbit, recurrence,
genericity, or physical-time means are added to the measure assumptions.

This implements Section 9, Lemma `lem:selectedorbit`, and its arithmetic
exclusion consequence. The compact reward and accumulator conclusion are
separate assertions.
-/

noncomputable section

namespace Stability.Selection

open HGAS HGAS.Dynamics HGAS.CompactAccumulatorPipelineCode
open HGAS.CompactAccumulatorPipelineCode.AllAffineCompactSourceChart (layout)
open HGAS.CompactAccumulatorPipelineCode.AllAffineCompactBaseChartTrajectory (finiteInterior)
open HGAS.NormalizedCorrectedFixedDetectorCompactSourceCode
  (sourceDegreeBound clearingExponent sourceFieldCode sourceDriftCode)
open HGAS.Clocks.ObservedTimeChangedControllerPhaseHaar
open Filter Topology MeasureTheory

variable {eqs vars : ℕ}

/-- The canonical compact flow of the actual source field, before adding
the accumulator sphere. -/
def detectorCompactBaseFlow
    (parameters : Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars) :
    Flow ℝ (BaseSpace (layout (FixedDetectorPolynomialCode.dimension eqs vars))) :=
  baseFlow (layout (FixedDetectorPolynomialCode.dimension eqs vars))
    (sourceDegreeBound I) (clearingExponent I) (sourceFieldCode parameters I)

/-- The literal clearing exponent meets the source selector's lower
threshold on its real growth exponent. -/
theorem detector_clearingExponent_ge_one (I : DQLSystem eqs vars) :
    (1 : ℝ) ≤ (clearingExponent I : ℝ) := by
  have hfield : 9 ≤ FixedDetectorPolynomialCode.fieldDegree I := Nat.le_max_left _ _
  have hdegree :=
    NormalizedCorrectedFixedDetectorCompactSourceCode.fieldDegree_le_sourceDegreeBound I
  have hn : 1 ≤ clearingExponent I := by unfold clearingExponent; omega
  exact_mod_cast hn

/-- The exact compact-base measure assumptions supply the actual complete
source trajectory, pointwise validity, forward recurrence, all full-horizon
test means, and a growth bound at the clearing exponent. -/
theorem exists_detector_trajectory_of_ergodic_compactBase_zero
    (parameters : Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (ν : InvariantProbabilityMeasure (detectorCompactBaseFlow parameters I))
    (hν : IsErgodicInvariantProbability (detectorCompactBaseFlow parameters I) ν.measure)
    (hfull : (ν.measure : Measure (BaseSpace
      (layout (FixedDetectorPolynomialCode.dimension eqs vars)))) finiteInterior = 1)
    (hzero : ∀ q : Fin (NormalizedCorrectedFixedDetectorDriftCode.driftCount vars),
      (∫ b, baseDriftBCF (layout (FixedDetectorPolynomialCode.dimension eqs vars))
        (clearingExponent I) RationalCode.one (sourceDriftCode I) b q
        ∂(ν.measure : Measure (BaseSpace
          (layout (FixedDetectorPolynomialCode.dimension eqs vars))))) = 0) :
    ∃ x : ℝ → Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ,
      IsIntegralCurve x (fun _ y ↦ PolynomialFieldCode.realize
        (FixedDetectorPolynomialCode.fieldCode parameters I) y) ∧
      ForwardRecurrentAt x 0 ∧
      (∀ t, NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue I
        (FixedDetectorReverseTrajectoryCrosswalk.recoveredState x t) = 0) ∧
      (∃ B : ℝ, ∀ H : ℝ, 1 ≤ H →
        H⁻¹ * (∫ t in (0 : ℝ)..H,
          (Real.sqrt (normSq (x t))) ^ (clearingExponent I : ℝ)) ≤ B) ∧
      ∀ q : Fin (NormalizedCorrectedFixedDetectorDriftCode.driftCount vars),
        Tendsto (fun H : ℝ ↦ H⁻¹ * ∫ t in (0 : ℝ)..H,
          MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) (x t)
            (PolynomialCode.decode (NormalizedCorrectedFixedDetectorDriftCode.driftCode I q)))
          atTop (𝓝 0) := by
  let hP := NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode_termsDegreeLE
    parameters I
  let hh :=
    NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode_termsAffineBlockDegreeLE I
  have hnonneg (x : Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ) :
      0 ≤ MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode (sourceDriftCode I
          (NormalizedCorrectedFixedDetectorDriftCode.validityIndex vars))) := by
    have heq := NormalizedCorrectedFixedDetectorDriftCode.eval_driftCode_validityIndex I
      (FixedDetectorPolynomialCode.state x)
    rw [FixedDetectorPolynomialCode.point_state] at heq
    rw [show sourceDriftCode I = NormalizedCorrectedFixedDetectorDriftCode.driftCode I from rfl,
      heq]
    exact NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue_nonneg I _
  obtain ⟨O⟩ := exists_ordinaryTimeBaseOrbit (sourceDegreeBound I) (sourceDegreeBound I)
    (sourceFieldCode parameters I) hP RationalCode.one (by simp) (sourceDriftCode I) hh
    (NormalizedCorrectedFixedDetectorDriftCode.validityIndex vars) hnonneg ν hν hfull hzero
  refine ⟨O.physicalCurve, O.physicalCurve_isIntegralCurve
    (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode_termsAffineBlockDegreeLE
      parameters I), O.physicalCurve_forwardRecurrentAt, ?_, ?_, ?_⟩
  · intro t
    have hz := O.physicalCurve_zeroCoordinate (by simp) hh t
    have heq := NormalizedCorrectedFixedDetectorDriftCode.eval_driftCode_validityIndex I
      (FixedDetectorPolynomialCode.state (O.physicalCurve t))
    rw [FixedDetectorPolynomialCode.point_state] at heq
    exact heq.symm.trans hz
  · simpa only [clearingExponent, Nat.cast_mul, Nat.cast_ofNat] using
      O.physicalCurve_growth_all_horizons
  · exact O.physicalCurve_testMean_zero (by simp) hh

/-- A solvable arithmetic instance admits no ergodic finite-base
probability with zero mean for every compact test. -/
theorem not_solvable_of_ergodic_compactBase_zero
    (p : Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (I : DQLSystem eqs vars) (hcolumns : DQLNonzeroLinearAugmentation.HasNonzeroLinearColumn I)
    (ν : InvariantProbabilityMeasure (detectorCompactBaseFlow (primeClockCodes p) I))
    (hν : IsErgodicInvariantProbability
      (detectorCompactBaseFlow (primeClockCodes p) I) ν.measure)
    (hfull : (ν.measure : Measure (BaseSpace
      (layout (FixedDetectorPolynomialCode.dimension eqs vars)))) finiteInterior = 1)
    (hzero : ∀ q : Fin (NormalizedCorrectedFixedDetectorDriftCode.driftCount vars),
      (∫ b, baseDriftBCF (layout (FixedDetectorPolynomialCode.dimension eqs vars))
        (clearingExponent I) RationalCode.one (sourceDriftCode I) b q
        ∂(ν.measure : Measure (BaseSpace
          (layout (FixedDetectorPolynomialCode.dimension eqs vars))))) = 0) :
    ¬ I.Solvable := by
  apply (exists_prime_source_trajectory_iff_not_solvable p hp hinj I hcolumns
    (clearingExponent I) (detector_clearingExponent_ge_one I)).mp
  obtain ⟨x, hx, hrec, hvalid, ⟨B, hgrowth⟩, hmeans⟩ :=
    exists_detector_trajectory_of_ergodic_compactBase_zero
      (primeClockCodes p) I ν hν hfull hzero
  exact ⟨x, hx, hrec, hvalid, ⟨B, Filter.eventually_atTop.2 ⟨1, hgrowth⟩⟩, hmeans⟩

end Stability.Selection
