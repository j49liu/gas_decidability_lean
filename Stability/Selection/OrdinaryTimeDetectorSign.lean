import Stability.Selection.OrdinaryTimeDetectorGap
import Stability.Selection.OrdinaryTimeDetectorInvariantGraph

/-!
# The exact compact reward sign and homogeneous wrapper

The two quantitative branches concern the same raw least-integer gain
code, margin, compact polynomial field, and reward. Their composition gives
the Section 9 sign theorem and the faithful homogeneous-field certificate.
-/

noncomputable section

namespace Stability.Selection

open HGAS HGAS.Dynamics HGAS.CompactAccumulatorPipelineCode
open HGAS.NormalizedCorrectedFixedDetectorCompactSourceCode
open HGAS.Clocks.ObservedTimeChangedControllerPhaseHaar

variable {eqs vars : ℕ}

local instance : Nonempty (DetectorCompactSpace eqs vars) := by
  simpa [NormalizedCorrectedFixedDetectorCompactSourceCode.layout] using
    nonempty_sourceProductSphere_oneBlockAllAffine
      (sourceDimension eqs vars) (driftDimension vars)

/-- Solvable instances have the printed negative margin. -/
theorem detector_maximum_le_neg_margin_of_solvable
    (I : DQLSystem eqs vars) (hcolumns : DQLNonzeroLinearAugmentation.HasNonzeroLinearColumn I)
    (p : Fin (vars + eqs) → ℕ) (hp : ∀ i, (p i).Prime) (hinjective : Function.Injective p)
    (hsolv : I.Solvable) :
    maximalInvariantAverage (DetectorInvariantGraph.flow I p)
      (DetectorInvariantGraph.reward eqs vars) ≤ -(detectorGraphMargin eqs vars : ℝ) :=
  detectorGraphGain_maximum_le_neg_margin I hcolumns p hp hinjective hsolv

/-- Unsolvable instances have the printed positive lower bound. This
branch does not need the nonzero-column condition. -/
theorem detector_maximum_ge_graph_weight_of_not_solvable
    (I : DQLSystem eqs vars) (hnot : ¬ I.Solvable)
    (p : Fin (vars + eqs) → ℕ) (hp : ∀ i, (p i).Prime) (hinjective : Function.Injective p) :
    5 * (graphWeightBudget (sourceGraphSizeBudget eqs vars) : ℝ) / 4 ≤
      maximalInvariantAverage (DetectorInvariantGraph.flow I p)
        (DetectorInvariantGraph.reward eqs vars) := by
  obtain ⟨μ, _, hμ⟩ := DetectorInvariantGraph.exists_probability I hnot p hp hinjective
  exact le_maximalInvariantAverage_of_invariantProbability _ _ μ hμ

/-- Strict negativity of the actual maximal invariant reward is exactly
arithmetic solvability, with the least-integer gain throughout. -/
theorem detector_maximum_neg_iff_solvable
    (I : DQLSystem eqs vars) (hcolumns : DQLNonzeroLinearAugmentation.HasNonzeroLinearColumn I)
    (p : Fin (vars + eqs) → ℕ) (hp : ∀ i, (p i).Prime) (hinjective : Function.Injective p) :
    maximalInvariantAverage (DetectorInvariantGraph.flow I p)
      (DetectorInvariantGraph.reward eqs vars) < 0 ↔ I.Solvable := by
  have hε : (0 : ℝ) < detectorGraphMargin eqs vars := by
    exact_mod_cast detectorGraphMargin_pos eqs vars
  have hw : (0 : ℝ) < (graphWeightBudget (sourceGraphSizeBudget eqs vars) : ℝ) := by
    exact_mod_cast graphWeightBudget_pos (sourceGraphSizeBudget eqs vars)
  exact maximalInvariantAverage_neg_iff_of_two_sided_gap _ _ I.Solvable hε
    (show (0 : ℝ) < 5 * (graphWeightBudget (sourceGraphSizeBudget eqs vars) : ℝ) / 4 by
      positivity)
    (detector_maximum_le_neg_margin_of_solvable I hcolumns p hp hinjective)
    (fun hnot ↦ detector_maximum_ge_graph_weight_of_not_solvable I hnot p hp hinjective)

/-- The literal input to the preserved compact polynomial compiler,
with the new raw least-integer gain and stated margin. -/
def detectorCompilerInput (I : DQLSystem eqs vars) (p : Fin (vars + eqs) → ℕ) :
    NormalizedCorrectedFixedDetectorCompactSourceCode.CompilerInput eqs vars :=
  (((primeClockCodes p, I), DetectorInvariantGraph.gainCode I p),
    DetectorInvariantGraph.marginCode eqs vars)

/-- Both exact quantitative branches form the compiler's semantic gap. -/
def detectorAccumulatorGap
    (I : DQLSystem eqs vars) (hcolumns : DQLNonzeroLinearAugmentation.HasNonzeroLinearColumn I)
    (p : Fin (vars + eqs) → ℕ) (hp : ∀ i, (p i).Prime) (hinjective : Function.Injective p) :
    CanonicalCompactAccumulatorGap I layout (sourceDegreeBound I) (clearingExponent I)
      (DetectorInvariantGraph.gainCode I p) (sourceFieldCode (primeClockCodes p) I)
      (sourceFieldCode_termsDegreeLE (primeClockCodes p) I)
      (sourceDriftCode I) (sourceDriftCode_termsDegreeLE I)
      (DetectorInvariantGraph.marginCode eqs vars) (baseCompactTangency (primeClockCodes p) I) where
  epsilon_pos := by
    change (0 : ℝ) < (RationalCode.encode (detectorGraphMargin eqs vars)).decode
    rw [RationalCode.decode_encode]
    exact_mod_cast detectorGraphMargin_pos eqs vars
  delta := 5 * (graphWeightBudget (sourceGraphSizeBudget eqs vars) : ℝ) / 4
  delta_pos := by
    have hw : (0 : ℝ) < (graphWeightBudget (sourceGraphSizeBudget eqs vars) : ℝ) := by
      exact_mod_cast graphWeightBudget_pos (sourceGraphSizeBudget eqs vars)
    positivity
  nonzero_mean := by
    intro hsolv μ hμ hpos
    apply detectorConditionalBase_nonzero_mean I hcolumns p hp hinjective _ _ _ hsolv μ hμ hpos
    rw [DetectorInvariantGraph.decode_gainCode]
    exact_mod_cast (detectorGraphGain_pos I p).ne'
  finite_graph := by
    intro hnot
    obtain ⟨μ, _, hμ⟩ := DetectorInvariantGraph.exists_probability I hnot p hp hinjective
    exact ⟨μ, hμ⟩

/-- Faithful certificate for the actual compact source, not for a
definitionally different gain chosen by an alternate construction. -/
def detectorSignCertificate
    (I : DQLSystem eqs vars) (hcolumns : DQLNonzeroLinearAugmentation.HasNonzeroLinearColumn I)
    (p : Fin (vars + eqs) → ℕ) (hp : ∀ i, (p i).Prime) (hinjective : Function.Injective p) :
    Compiler.CompactSignSourceCertificate
      (sourceBlock (m := driftDimension vars) (layout (eqs := eqs) (vars := vars))) I :=
  (detectorAccumulatorGap I hcolumns p hp hinjective).toCompactSignSourceCertificate I
    layout (sourceDegreeBound I) (clearingExponent I) (DetectorInvariantGraph.gainCode I p)
    (sourceFieldCode (primeClockCodes p) I) (sourceFieldCode_termsDegreeLE (primeClockCodes p) I)
    (sourceDriftCode I) (sourceDriftCode_termsDegreeLE I)
    (DetectorInvariantGraph.marginCode eqs vars)
    (baseCompactTangency (primeClockCodes p) I)

/-- The source pair is literally the existing compiler applied to the
stated raw input. The preserved alternative-gain compiler is unchanged. -/
theorem detectorSignCertificate_source_eq
    (I : DQLSystem eqs vars) (hcolumns : DQLNonzeroLinearAugmentation.HasNonzeroLinearColumn I)
    (p : Fin (vars + eqs) → ℕ) (hp : ∀ i, (p i).Prime) (hinjective : Function.Injective p) :
    NormalizedCorrectedFixedDetectorCompactSourceCode.compile (detectorCompilerInput I p) =
      ((detectorSignCertificate I hcolumns p hp hinjective).fieldCode,
        (detectorSignCertificate I hcolumns p hp hinjective).rewardCode) := rfl

/-- The actual homogeneous wrapper using the least-integer detector gain
is globally asymptotically stable exactly on solvable instances. -/
theorem detectorFinalField_gas_iff_solvable
    (I : DQLSystem eqs vars) (hcolumns : DQLNonzeroLinearAugmentation.HasNonzeroLinearColumn I)
    (p : Fin (vars + eqs) → ℕ) (hp : ∀ i, (p i).Prime) (hinjective : Function.Injective p) :
    GloballyAsymptoticallyStable (PolynomialFieldCode.realize
      (detectorSignCertificate I hcolumns p hp hinjective).finalFieldCode) 0 ↔ I.Solvable :=
  (detectorSignCertificate I hcolumns p hp hinjective).finalField_gas_iff_solvable

end Stability.Selection
