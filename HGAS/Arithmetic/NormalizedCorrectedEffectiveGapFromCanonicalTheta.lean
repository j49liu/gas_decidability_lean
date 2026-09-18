import HGAS.Arithmetic.NormalizedCorrectedEffectiveNoInstanceFiniteGraph
import HGAS.Arithmetic.NormalizedCorrectedEffectiveNonzeroMeanFromTheta
import HGAS.Compiler.CompactAccumulatorPipelineGapCertificate
import HGAS.Compiler.CompactAccumulatorPipelineNonempty
import Mathlib.Tactic

/-!
# The effective semantic gap from canonical theta outputs

The normalized compact compiler needs exactly two instance-dependent
measure statements:

* a solvable instance cannot have all conditional drift means equal to
  zero; and
* a nonsolvable instance has an invariant finite graph with positive
  reward.

The second statement is unconditional and was proved by the canonical
orbit-closure Fourier model.  The first follows from the selected-orbit
argument once every selected detector column has its canonical theta
output.  This module joins those independent branches at the narrow
`CanonicalCompactAccumulatorGap` interface.
-/

noncomputable section

open Function MeasureTheory
open scoped BoundedContinuousFunction

namespace HGAS.NormalizedCorrectedEffectiveGapFromCanonicalTheta

open HGAS
open HGAS.CompactAccumulatorPipelineCode
open HGAS.NormalizedCorrectedCanonicalFixedDetectorCentralChart
open HGAS.NormalizedCorrectedEffectiveSelectedDetectorAverage
open HGAS.NormalizedCorrectedFixedDetectorBidirectionalValidityOrbit
open HGAS.NormalizedCorrectedFixedDetectorCompactSourceCode

variable {eqs vars : ℕ}

private abbrev compilerInput
    (I : DQLSystem eqs vars) :=
  NormalizedCorrectedEffectiveCompilerInput.compilerInput I

local instance sourceProductSphere_nonempty :
    Nonempty
      (UnitSpherePolynomialWrapper.SourceProductSphere
        (sourceBlock
          (m :=
            NormalizedCorrectedFixedDetectorCompactSourceCode.driftDimension
              vars)
          (NormalizedCorrectedFixedDetectorCompactSourceCode.layout
            (eqs := eqs) (vars := vars)))) := by
  simpa [
    NormalizedCorrectedFixedDetectorCompactSourceCode.layout] using
      (nonempty_sourceProductSphere_oneBlockAllAffine
        (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDimension
          eqs vars)
        (NormalizedCorrectedFixedDetectorCompactSourceCode.driftDimension
          vars))

/-- Exact semantic gap type for one effective normalized compiler
instance. -/
abbrev Gap (I : DQLSystem eqs vars) :=
  CanonicalCompactAccumulatorGap
    I
    NormalizedCorrectedFixedDetectorCompactSourceCode.layout
    (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDegreeBound I)
    (NormalizedCorrectedFixedDetectorCompactSourceCode.clearingExponent I)
    (NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
      (compilerInput I))
    (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode
      (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
        (compilerInput I))
      I)
    (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode_termsDegreeLE
      (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
        (compilerInput I))
      I)
    (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode I)
    (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode_termsDegreeLE
      I)
    (NormalizedCorrectedFixedDetectorCompactSourceCode.rewardMargin
      (compilerInput I))
    (NormalizedCorrectedFixedDetectorCompactSourceCode.baseCompactTangency
      (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
        (compilerInput I))
      I)

/-- Canonical theta outputs on all selected recurrent validity orbits
complete the two-field semantic gap certificate. -/
def gapOfCanonicalThetaOutputs
    (I : DQLSystem eqs vars)
    (hcanonical :
      ∀ O :
          SelectedBidirectionalValidityOrbit (compilerInput I),
        HasCanonicalThetaOutputs I O) :
    Gap I where
  epsilon_pos := by
    simpa [compilerInput] using
      NormalizedCorrectedEffectiveCompilerInput.decode_rewardMarginCode_pos
        eqs vars
  delta :=
    NormalizedCorrectedFixedDetectorCompactSourceCode.explicitFiniteGraphDelta
      (NormalizedCorrectedEffectiveNoInstanceFiniteGraph.centralLower
        eqs vars)
  delta_pos := by
    exact
      explicitFiniteGraphDelta_pos
        canonicalCentralWeightSqLowerBound_pos
  nonzero_mean := by
    intro hsolvable μ hμ hpos
    by_contra hall
    push Not at hall
    apply
      HGAS.NormalizedCorrectedEffectiveNonzeroMeanFromTheta.not_conditionalBaseDriftZero_of_solvable
        I hcanonical hsolvable μ hμ hpos
    intro i
    exact hall i
  finite_graph :=
    NormalizedCorrectedEffectiveNoInstanceFiniteGraph.finite_graph I

end HGAS.NormalizedCorrectedEffectiveGapFromCanonicalTheta
