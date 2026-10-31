import Stability.Selection.OrdinaryTimeConditionalBase
import HGAS.Arithmetic.NormalizedCorrectedEffectiveGapFromCanonicalTheta

/-!
# An effective compact accumulator gap from ordinary-time selection

The yes-instance obstruction uses the actual conditional base measure
and the forward ordinary-time extraction theorem. The no-instance graph
uses the published effective primitive budget and gain. That gain and
reward margin need not equal the least-integer choices in Section 9;
this theorem does not identify them or assert the full printed torus graph.
-/

noncomputable section

namespace Stability.Selection

open HGAS HGAS.Dynamics HGAS.CompactAccumulatorPipelineCode
open HGAS.NormalizedCorrectedFixedDetectorCompactSourceCode
open HGAS.NormalizedCorrectedEffectiveCompilerInput
open MeasureTheory

variable {eqs vars : ℕ}

local instance : Nonempty (UnitSpherePolynomialWrapper.SourceProductSphere
    (sourceBlock (m := driftDimension vars) (layout (eqs := eqs) (vars := vars)))) := by
  simpa [NormalizedCorrectedFixedDetectorCompactSourceCode.layout] using
    nonempty_sourceProductSphere_oneBlockAllAffine
      (sourceDimension eqs vars) (driftDimension vars)

/-- The complete effective gap certificate, with no selected-theta or
bidirectional-recurrence premise. The nonzero-column hypothesis is the
arithmetic augmentation condition used by ordinary-time selection. -/
def effectiveDetectorAccumulatorGap (I : DQLSystem eqs vars)
    (hcolumns : DQLNonzeroLinearAugmentation.HasNonzeroLinearColumn I) :
    NormalizedCorrectedEffectiveGapFromCanonicalTheta.Gap I where
  epsilon_pos := by
    simpa using decode_rewardMarginCode_pos eqs vars
  delta := explicitFiniteGraphDelta
    (NormalizedCorrectedEffectiveNoInstanceFiniteGraph.centralLower eqs vars)
  delta_pos := explicitFiniteGraphDelta_pos
    NormalizedCorrectedCanonicalFixedDetectorCentralChart.canonicalCentralWeightSqLowerBound_pos
  nonzero_mean := by
    intro hsolv μ hμ hpos
    by_contra! hzero
    let ν := conditionalBaseProbability
      (layout (eqs := eqs) (vars := vars))
      (sourceDegreeBound I) (clearingExponent I) (accumulatorScale (compilerInput I))
      (sourceFieldCode (parameters (compilerInput I)) I)
      (sourceFieldCode_termsDegreeLE (parameters (compilerInput I)) I)
      (sourceDriftCode I) (sourceDriftCode_termsDegreeLE I)
      (rewardMargin (compilerInput I))
      (baseCompactTangency (parameters (compilerInput I)) I) μ hpos
    have hν := ordinaryConditionalBase_ergodic
      (sourceDegreeBound I) (clearingExponent I) (accumulatorScale (compilerInput I))
      (sourceFieldCode (parameters (compilerInput I)) I)
      (sourceFieldCode_termsDegreeLE (parameters (compilerInput I)) I)
      (sourceDriftCode I) (sourceDriftCode_termsDegreeLE I)
      (rewardMargin (compilerInput I))
      (baseCompactTangency (parameters (compilerInput I)) I) μ hpos hμ
    have hfull := ordinaryConditionalBase_finiteInterior_full
      (sourceDegreeBound I) (clearingExponent I) (accumulatorScale (compilerInput I))
      (sourceFieldCode (parameters (compilerInput I)) I)
      (sourceFieldCode_termsDegreeLE (parameters (compilerInput I)) I)
      (sourceDriftCode I) (sourceDriftCode_termsDegreeLE I)
      (rewardMargin (compilerInput I))
      (baseCompactTangency (parameters (compilerInput I)) I) μ hpos
    apply not_solvable_of_ergodic_compactBase_zero
      (primeRadicand (vars + eqs)) (primeRadicand_prime _) (primeRadicand_injective _)
      I hcolumns ν hν hfull _ hsolv
    intro q
    exact compactBase_mean_zero_of_scaled
      (clearingExponent I) (accumulatorScale (compilerInput I))
      (compilerInput_accumulatorScale_pos I).ne' (sourceDriftCode I)
      (ν.measure : Measure (BaseSpace (layout (eqs := eqs) (vars := vars)))) q (hzero q)
  finite_graph := NormalizedCorrectedEffectiveNoInstanceFiniteGraph.finite_graph I

/-- The faithful compact-sign certificate for the literal effective
compiler output. Its data do not add any dynamical hypotheses. -/
def effectiveDetectorSignCertificate (I : DQLSystem eqs vars)
    (hcolumns : DQLNonzeroLinearAugmentation.HasNonzeroLinearColumn I) :
    Compiler.CompactSignSourceCertificate
      (sourceBlock (m := driftDimension vars) (layout (eqs := eqs) (vars := vars))) I :=
  (effectiveDetectorAccumulatorGap I hcolumns).toCompactSignSourceCertificate I
    layout (sourceDegreeBound I) (clearingExponent I) (accumulatorScale (compilerInput I))
    (sourceFieldCode (parameters (compilerInput I)) I)
    (sourceFieldCode_termsDegreeLE (parameters (compilerInput I)) I)
    (sourceDriftCode I) (sourceDriftCode_termsDegreeLE I)
    (rewardMargin (compilerInput I))
    (baseCompactTangency (parameters (compilerInput I)) I)

/-- The certificate's field and reward are definitionally the actual
compiled rational polynomial pair. -/
theorem effectiveDetectorSignCertificate_source_eq (I : DQLSystem eqs vars)
    (hcolumns : DQLNonzeroLinearAugmentation.HasNonzeroLinearColumn I) :
    NormalizedCorrectedFixedDetectorCompactSourceCode.compile (compilerInput I) =
      ((effectiveDetectorSignCertificate I hcolumns).fieldCode,
        (effectiveDetectorSignCertificate I hcolumns).rewardCode) := rfl

/-- The homogeneous polynomial wrapper of the effective source is GAS
exactly on solvable instances. This uses the effective alternative gain,
not an asserted equality with the manuscript's least-integer choice. -/
theorem effectiveDetectorFinalField_gas_iff_solvable (I : DQLSystem eqs vars)
    (hcolumns : DQLNonzeroLinearAugmentation.HasNonzeroLinearColumn I) :
    GloballyAsymptoticallyStable (PolynomialFieldCode.realize
      (effectiveDetectorSignCertificate I hcolumns).finalFieldCode) 0 ↔ I.Solvable :=
  (effectiveDetectorSignCertificate I hcolumns).finalField_gas_iff_solvable

end Stability.Selection
