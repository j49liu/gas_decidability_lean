import Stability.Selection.OrdinaryTimePrimeExistence
import Stability.Selection.OrdinaryTimeDetectorAverage

/-!
# Arithmetic equivalence for complete ordinary-time source trajectories

For distinct prime clocks and nonzero linear columns, an unsolvable DQL
instance is equivalent to existence of a complete, pointwise-valid,
forward-recurrent source trajectory with bounded forward growth moment
and zero averages for every actual scalar test. The converse constructs
a uniformly bounded trajectory on the canonical orbit closure.

This is the source-level equivalence in Section 8, Corollary `cor:yes`.
It does not include extraction of a source trajectory from a compact
invariant measure in Section 9.
-/

noncomputable section

namespace Stability.Selection

open HGAS HGAS.Clocks Filter Topology MeasureTheory
open HGAS.Clocks.ObservedTimeChangedControllerPhaseHaar
open HGAS.NormalizedCorrectedEffectiveColumnFrequencyIrrational

variable {eqs vars : ℕ}

/-- With nonzero linear columns, all literal selector codes have the
printed centering constants; conditional compiler centering disappears. -/
theorem selector_scalarCode_eq_of_nonzero_columns
    (I : DQLSystem eqs vars) (hcolumns : DQLNonzeroLinearAugmentation.HasNonzeroLinearColumn I)
    (k : Fin (FixedDetectorMomentCode.scalarMomentCount vars)) :
    CorrectedFixedDetectorMomentCode.scalarMomentCode I k =
      FixedDetectorMomentCode.scalarMomentCode I k := by
  have hcenter (j : Fin vars) : CorrectedJacobiSelectorCentering.selectorCenter I j = 1 / 256 :=
    CorrectedJacobiSelectorCentering.selectorCenter_eq_of_linearCharacter_ne_zero I j
      (linearCharacter_ne_zero_of_hasNonzeroLinearColumn I hcolumns j)
  have hlocal (j : Fin vars) : CorrectedFixedDetectorMomentCode.localMomentCode I j =
      FixedDetectorMomentCode.localMomentCode I j := by
    funext r
    fin_cases r <;>
      simp [CorrectedFixedDetectorMomentCode.localMomentCode,
        FixedDetectorMomentCode.localMomentCode,
        CorrectedFixedDetectorMomentCode.jacobiPlusMeanCode,
        CorrectedFixedDetectorMomentCode.jacobiMinusMeanCode,
        FixedDetectorMomentCode.jacobiPlusMeanCode,
        FixedDetectorMomentCode.jacobiMinusMeanCode, hcenter]
  simp only [CorrectedFixedDetectorMomentCode.scalarMomentCode,
    FixedDetectorMomentCode.scalarMomentCode, CorrectedFixedDetectorMomentCode.momentCode,
    FixedDetectorMomentCode.momentCode, hlocal]

/-- Full source-level existence equivalence. Validity is imposed
pointwise, completeness means all real time, and the only recurrence
assumption is forward recurrence. Every mean uses the full real horizon.
The growth bound may be eventual; the constructed converse satisfies it
at every positive horizon. -/
theorem exists_prime_source_trajectory_iff_not_solvable
    (p : Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (I : DQLSystem eqs vars) (hcolumns : DQLNonzeroLinearAugmentation.HasNonzeroLinearColumn I)
    (μ : ℝ) (hμ : 1 ≤ μ) :
    (∃ x : ℝ → Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ,
      IsIntegralCurve x (fun _ y ↦ PolynomialFieldCode.realize
        (FixedDetectorPolynomialCode.fieldCode (primeClockCodes p) I) y) ∧
      ForwardRecurrentAt x 0 ∧
      (∀ t, NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue I
        (FixedDetectorReverseTrajectoryCrosswalk.recoveredState x t) = 0) ∧
      (∃ B : ℝ, ∀ᶠ H : ℝ in atTop,
        H⁻¹ * (∫ t in (0 : ℝ)..H, (Real.sqrt (normSq (x t))) ^ μ) ≤ B) ∧
      ∀ q : Fin (NormalizedCorrectedFixedDetectorDriftCode.driftCount vars),
        Tendsto (fun H : ℝ ↦ H⁻¹ * ∫ t in (0 : ℝ)..H,
          MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) (x t)
            (PolynomialCode.decode (NormalizedCorrectedFixedDetectorDriftCode.driftCode I q)))
          atTop (𝓝 0)) ↔ ¬ I.Solvable := by
  constructor
  · rintro ⟨x, hx, hrec, hvalid, ⟨B, hgrowth⟩, hmeans⟩
    have hselector (k : Fin (FixedDetectorMomentCode.scalarMomentCount vars)) :
        Tendsto (fun H : ℝ ↦ H⁻¹ * ∫ t in (0 : ℝ)..H,
          MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) (x t)
            (PolynomialCode.decode (FixedDetectorMomentCode.scalarMomentCode I k)))
          atTop (𝓝 0) := by
      simpa only [NormalizedCorrectedFixedDetectorDriftCode.driftCode,
        NormalizedCorrectedFixedDetectorDriftCode.momentIndex,
        CorrectedFixedDetectorDriftCode.momentIndex, FixedDetectorDriftCode.momentIndex,
        Equiv.symm_apply_apply, selector_scalarCode_eq_of_nonzero_columns I hcolumns] using
          hmeans (NormalizedCorrectedFixedDetectorDriftCode.momentIndex k)
    apply (detector_prime_scalarMeans_zero_iff_not_solvable
      p hp hinj I hcolumns hx hrec hvalid hμ B hgrowth hselector).mp
    constructor
    · simpa [NormalizedCorrectedFixedDetectorDriftCode.driftCode,
        NormalizedCorrectedFixedDetectorDriftCode.detectorIndex,
        CorrectedFixedDetectorDriftCode.detectorIndex, FixedDetectorDriftCode.detectorIndex] using
          hmeans (NormalizedCorrectedFixedDetectorDriftCode.detectorIndex 0)
    · simpa [NormalizedCorrectedFixedDetectorDriftCode.driftCode,
        NormalizedCorrectedFixedDetectorDriftCode.detectorIndex,
        CorrectedFixedDetectorDriftCode.detectorIndex, FixedDetectorDriftCode.detectorIndex] using
          hmeans (NormalizedCorrectedFixedDetectorDriftCode.detectorIndex 1)
  · intro hnot
    obtain ⟨x, hx, hrec, hvalid, hbound, hmeans⟩ :=
      exists_prime_source_trajectory_of_not_solvable p hp hinj I hnot
    refine ⟨x, hx, hrec, hvalid,
      ⟨(Real.sqrt (CanonicalFixedDetectorRawOrbitBound.canonicalRawNormSqBound eqs vars)) ^ μ,
        ?_⟩, hmeans⟩
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
    exact forwardGrowth_le_of_normSq_le hx.continuous hbound (by linarith) hH

end Stability.Selection
