import HGAS.Arithmetic.NormalizedCorrectedAugmentedUniversalResources
import HGAS.Compiler.CompactAccumulatorPipelineGapCertificate
import HGAS.Compiler.FixedUniversalDQLCompactSignSourceFamily
import Mathlib.Tactic

/-!
# Fixed repaired universal family from semantic gap certificates

This is the effectivity firewall for the linearly nondegenerate universal
DQL family.  Once one supplies the semantic yes/no gap certificate for
each augmented instance, the definitions below package the literal
normalized-corrected compiler output into one computable family with a
single source dimension and a single odd homogeneous degree.
-/

namespace HGAS.NormalizedCorrectedAugmentedFamilyFromGap

open HGAS

noncomputable section

abbrev system (input : ℕ) :
    DQLSystem
      NormalizedCorrectedAugmentedUniversalResources.equationCount
      NormalizedCorrectedAugmentedUniversalResources.variableCount :=
  UniversalHalting.augmentedUniversalHaltingFixedDQL input

abbrev compilerInput (input : ℕ) :
    NormalizedCorrectedFixedDetectorCompactSourceCode.CompilerInput
      NormalizedCorrectedAugmentedUniversalResources.equationCount
      NormalizedCorrectedAugmentedUniversalResources.variableCount :=
  NormalizedCorrectedEffectiveCompilerInput.compilerInput (system input)

local instance pipelineSourceProductSphere_nonempty :
    Nonempty
      (UnitSpherePolynomialWrapper.SourceProductSphere
        (CompactAccumulatorPipelineCode.sourceBlock
          (m :=
            NormalizedCorrectedFixedDetectorCompactSourceCode.driftDimension
              NormalizedCorrectedAugmentedUniversalResources.variableCount)
          (NormalizedCorrectedFixedDetectorCompactSourceCode.layout
            (eqs :=
              NormalizedCorrectedAugmentedUniversalResources.equationCount)
            (vars :=
              NormalizedCorrectedAugmentedUniversalResources.variableCount)))) := by
  simpa only [
    NormalizedCorrectedAugmentedUniversalResources.sourceBlock] using
      NormalizedCorrectedAugmentedUniversalResources.sourceProductSphere_nonempty

/-- Exact semantic residue required for one repaired compiler instance. -/
abbrev Gap (input : ℕ) :=
  CompactAccumulatorPipelineCode.CanonicalCompactAccumulatorGap
    (system input)
    NormalizedCorrectedFixedDetectorCompactSourceCode.layout
    (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDegreeBound
      (system input))
    (NormalizedCorrectedFixedDetectorCompactSourceCode.clearingExponent
      (system input))
    (NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
      (compilerInput input))
    (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode
      (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
        (compilerInput input))
      (system input))
    (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode_termsDegreeLE
      (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
        (compilerInput input))
      (system input))
    (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode
      (system input))
    (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode_termsDegreeLE
      (system input))
    (NormalizedCorrectedFixedDetectorCompactSourceCode.rewardMargin
      (compilerInput input))
    (NormalizedCorrectedFixedDetectorCompactSourceCode.baseCompactTangency
      (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
        (compilerInput input))
      (system input))

/-- Convert one repaired semantic gap to the exact compact-sign source
certificate. -/
def certificateOfGap
    (input : ℕ) (G : Gap input) :
    Compiler.CompactSignSourceCertificate
      NormalizedCorrectedAugmentedUniversalResources.sourceBlock
      (system input) :=
  G.toCompactSignSourceCertificate
      (system input)
      NormalizedCorrectedFixedDetectorCompactSourceCode.layout
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDegreeBound
        (system input))
      (NormalizedCorrectedFixedDetectorCompactSourceCode.clearingExponent
        (system input))
      (NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
        (compilerInput input))
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode
        (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
          (compilerInput input))
        (system input))
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode_termsDegreeLE
        (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
          (compilerInput input))
        (system input))
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode
        (system input))
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode_termsDegreeLE
        (system input))
      (NormalizedCorrectedFixedDetectorCompactSourceCode.rewardMargin
        (compilerInput input))
      (NormalizedCorrectedFixedDetectorCompactSourceCode.baseCompactTangency
        (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
          (compilerInput input))
        (system input))

theorem certificateOfGap_degree
    (input : ℕ) (G : Gap input) :
    (certificateOfGap input G).degree =
      NormalizedCorrectedAugmentedUniversalResources.wrapperDegree := by
  change
    CompactAccumulatorPipelineCode.wrapperDegree
        (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDegreeBound
          (system input))
        NormalizedCorrectedFixedDetectorCompactSourceCode.affineBlockCount
        (NormalizedCorrectedFixedDetectorCompactSourceCode.clearingExponent
          (system input)) =
      NormalizedCorrectedAugmentedUniversalResources.wrapperDegree
  exact
    NormalizedCorrectedAugmentedUniversalResources.instance_wrapperDegree_eq
      input

theorem sourceCode_eq_certificateOfGap
    (input : ℕ) (G : Gap input) :
    NormalizedCorrectedAugmentedUniversalResources.sourceCode input =
      ((certificateOfGap input G).fieldCode,
        (certificateOfGap input G).rewardCode) := by
  rfl

/-- A family of repaired semantic gaps yields the complete fixed universal
compact-sign source family. -/
def familyOfGaps
    (G : ∀ input : ℕ, Gap input) :
    Compiler.FixedUniversalDQLCompactSignSourceFamily
      system
      NormalizedCorrectedAugmentedUniversalResources.sourceBlock
      NormalizedCorrectedAugmentedUniversalResources.wrapperDegree :=
  Compiler.FixedUniversalDQLCompactSignSourceFamily.ofComputableSourceCodes
    (fun input ↦
      UniversalHalting.augmentedUniversalHaltingFixedDQL_solvable_iff
        input)
    NormalizedCorrectedAugmentedUniversalResources.wrapperDegree
    NormalizedCorrectedAugmentedUniversalResources.wrapperDegree_ge_three
    NormalizedCorrectedAugmentedUniversalResources.wrapperDegree_odd
    (fun input ↦ certificateOfGap input (G input))
    (fun input ↦ certificateOfGap_degree input (G input))
    NormalizedCorrectedAugmentedUniversalResources.sourceCode
    NormalizedCorrectedAugmentedUniversalResources.sourceCode_computable
    (fun input ↦ sourceCode_eq_certificateOfGap input (G input))

end

end HGAS.NormalizedCorrectedAugmentedFamilyFromGap
