import HGAS.Arithmetic.NormalizedCorrectedAugmentedFamilyFromGap
import HGAS.Arithmetic.NormalizedCorrectedEffectiveGapFromCanonicalTheta
import Mathlib.Tactic

/-!
# The repaired fixed universal family from its theta theorem

This module is the final narrow join before the end-to-end reduction.
It converts a canonical-theta theorem for every selected recurrent orbit
of every augmented universal instance into the complete computable
fixed-dimension, fixed-degree compact-sign source family.
-/

namespace HGAS.NormalizedCorrectedAugmentedFamilyFromTheta

open HGAS
open NormalizedCorrectedEffectiveSelectedDetectorAverage
open NormalizedCorrectedFixedDetectorBidirectionalValidityOrbit

noncomputable section

private abbrev system (input : ℕ) :=
  UniversalHalting.augmentedUniversalHaltingFixedDQL input

private abbrev compilerInput (input : ℕ) :=
  NormalizedCorrectedEffectiveCompilerInput.compilerInput (system input)

/-- Pointwise theta correctness on the repaired universal family. -/
def HasCanonicalThetaOutputsForUniversalFamily : Prop :=
  ∀ input : ℕ,
    ∀ O : SelectedBidirectionalValidityOrbit (compilerInput input),
      HasCanonicalThetaOutputs (system input) O

/-- Convert the universal theta theorem into the exact semantic gap
family. -/
def gapsOfCanonicalThetaOutputs
    (hcanonical : HasCanonicalThetaOutputsForUniversalFamily) :
    ∀ input : ℕ,
      NormalizedCorrectedAugmentedFamilyFromGap.Gap input :=
  fun input ↦
    NormalizedCorrectedEffectiveGapFromCanonicalTheta.gapOfCanonicalThetaOutputs
      (system input) (hcanonical input)

/-- The complete executable compact-sign source family, conditional only
on the all-orbit theta theorem. -/
def familyOfCanonicalThetaOutputs
    (hcanonical : HasCanonicalThetaOutputsForUniversalFamily) :
    Compiler.FixedUniversalDQLCompactSignSourceFamily
      NormalizedCorrectedAugmentedFamilyFromGap.system
      NormalizedCorrectedAugmentedUniversalResources.sourceBlock
      NormalizedCorrectedAugmentedUniversalResources.wrapperDegree :=
  NormalizedCorrectedAugmentedFamilyFromGap.familyOfGaps
    (gapsOfCanonicalThetaOutputs hcanonical)

end

end HGAS.NormalizedCorrectedAugmentedFamilyFromTheta
