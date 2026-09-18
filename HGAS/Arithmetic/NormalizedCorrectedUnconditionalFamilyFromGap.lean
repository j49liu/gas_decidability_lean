import HGAS.Arithmetic.NormalizedCorrectedUnconditionalCompactResources
import HGAS.Compiler.CompactAccumulatorPipelineGapCertificate
import HGAS.Compiler.UnconditionalFixedCompactSignReduction
import Mathlib.Tactic

/-!
# Assembling the fixed universal family from semantic gap certificates

## Legacy unaugmented route

This module lies outside the public endpoint import closure.  It packages
the older unaugmented universal system conditionally on a family of
semantic gap certificates; the completed theorem does not obtain those
certificates through this route.  The live construction first applies the
nonzero-column augmentation and is assembled in
`NormalizedCorrectedAugmentedEffectiveFamily`.

This module is the final effectivity firewall.  Its only input is one
`CanonicalCompactAccumulatorGap` for each unary universal-halting
instance.  From those semantic certificates it constructs the single
fixed-dimension, fixed-degree, computable compact-sign source family
consumed by the recursion-theoretic reduction.

All code emitted by the family is the literal normalized corrected
compiler output; the semantic certificate cannot silently refer to a
different polynomial field.
-/

namespace HGAS.NormalizedCorrectedUnconditionalFamilyFromGap

open HGAS

noncomputable section

abbrev system (input : ℕ) :
    DQLSystem
      NormalizedCorrectedUnconditionalCompactResources.equationCount
      NormalizedCorrectedUnconditionalCompactResources.variableCount :=
  UniversalHalting.unconditionalUniversalHaltingFixedDQL input

abbrev compilerInput (input : ℕ) :
    NormalizedCorrectedFixedDetectorCompactSourceCode.CompilerInput
      NormalizedCorrectedUnconditionalCompactResources.equationCount
      NormalizedCorrectedUnconditionalCompactResources.variableCount :=
  NormalizedCorrectedEffectiveCompilerInput.compilerInput (system input)

local instance pipelineSourceProductSphere_nonempty :
    Nonempty
      (UnitSpherePolynomialWrapper.SourceProductSphere
        (CompactAccumulatorPipelineCode.sourceBlock
          (m :=
            NormalizedCorrectedFixedDetectorCompactSourceCode.driftDimension
              NormalizedCorrectedUnconditionalCompactResources.variableCount)
          (NormalizedCorrectedFixedDetectorCompactSourceCode.layout
            (eqs :=
              NormalizedCorrectedUnconditionalCompactResources.equationCount)
            (vars :=
              NormalizedCorrectedUnconditionalCompactResources.variableCount)))) := by
  simpa only [
    NormalizedCorrectedUnconditionalCompactResources.sourceBlock] using
      NormalizedCorrectedUnconditionalCompactResources.sourceProductSphere_nonempty

/-- Exact semantic residue required for one normalized corrected compiler
instance. -/
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

/-- Convert one semantic gap to the exact compact-sign source certificate
at the fixed source block assignment. -/
def certificateOfGap
    (input : ℕ) (G : Gap input) :
    Compiler.CompactSignSourceCertificate
      NormalizedCorrectedUnconditionalCompactResources.sourceBlock
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
      NormalizedCorrectedUnconditionalCompactResources.wrapperDegree := by
  change
    CompactAccumulatorPipelineCode.wrapperDegree
        (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDegreeBound
          (system input))
        NormalizedCorrectedFixedDetectorCompactSourceCode.affineBlockCount
        (NormalizedCorrectedFixedDetectorCompactSourceCode.clearingExponent
          (system input)) =
      NormalizedCorrectedUnconditionalCompactResources.wrapperDegree
  exact
    NormalizedCorrectedUnconditionalCompactResources.instance_wrapperDegree_eq
      input

/-- The executable source pair is literally the field/reward pair named
by the semantic certificate. -/
theorem sourceCode_eq_certificateOfGap
    (input : ℕ) (G : Gap input) :
    NormalizedCorrectedUnconditionalCompactResources.sourceCode input =
      ((certificateOfGap input G).fieldCode,
        (certificateOfGap input G).rewardCode) := by
  rfl

/-- A family of semantic gaps produces the complete fixed universal
compact-sign source family. -/
def familyOfGaps
    (G : ∀ input : ℕ, Gap input) :
    Compiler.FixedUniversalCompactSignSourceFamily
      NormalizedCorrectedUnconditionalCompactResources.sourceBlock
      NormalizedCorrectedUnconditionalCompactResources.wrapperDegree :=
  Compiler.FixedUniversalCompactSignSourceFamily.ofComputableSourceCodes
    NormalizedCorrectedUnconditionalCompactResources.wrapperDegree
    NormalizedCorrectedUnconditionalCompactResources.wrapperDegree_ge_three
    NormalizedCorrectedUnconditionalCompactResources.wrapperDegree_odd
    (fun input ↦ certificateOfGap input (G input))
    (fun input ↦ certificateOfGap_degree input (G input))
    NormalizedCorrectedUnconditionalCompactResources.sourceCode
    NormalizedCorrectedUnconditionalCompactResources.sourceCode_computable
    (fun input ↦ sourceCode_eq_certificateOfGap input (G input))

end

end HGAS.NormalizedCorrectedUnconditionalFamilyFromGap
