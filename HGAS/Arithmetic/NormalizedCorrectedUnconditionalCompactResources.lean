import HGAS.Arithmetic.NormalizedCorrectedEffectiveCompilerInput
import HGAS.Arithmetic.NormalizedCorrectedUnconditionalFixedDetectorDegree
import HGAS.Compiler.CompactAccumulatorPipelineCertificate
import HGAS.Compiler.CompactAccumulatorPipelineNonempty
import Mathlib.Tactic

/-!
# Fixed finite resources of the normalized corrected universal compiler

This file freezes all purely syntactic resources of the final
universal-halting family:

* one source dimension;
* one two-block product-of-spheres layout;
* one odd compact-sign wrapper degree; and
* one computable source field/reward code map.

No semantic orbit or invariant-measure argument occurs here.  That
separation is useful both for the final reduction and for auditing its
effectivity.
-/

namespace HGAS.NormalizedCorrectedUnconditionalCompactResources

open HGAS

noncomputable section

abbrev equationCount : ℕ :=
  UniversalHalting.unconditionalFixedDQLEquationCount

abbrev variableCount : ℕ :=
  UniversalHalting.unconditionalFixedDQLVariableCount

/-- Dimension of the compact polynomial source before the last
homogeneous sign wrapper. -/
abbrev compactSourceDimension : ℕ :=
  NormalizedCorrectedFixedDetectorCompactSourceCode.finalDimension
    equationCount variableCount

/-- The compact source has one centrally compactified affine sphere and
one accumulator sphere. -/
abbrev sourceSphereCount : ℕ := 2

/-- The fixed block assignment of the compact source. -/
def sourceBlock :
    Fin compactSourceDimension → Fin sourceSphereCount :=
  CompactAccumulatorPipelineCode.sourceBlock
    (m :=
      NormalizedCorrectedFixedDetectorCompactSourceCode.driftDimension
        variableCount)
    (NormalizedCorrectedFixedDetectorCompactSourceCode.layout
      (eqs := equationCount) (vars := variableCount))

/-- The fixed source product of spheres is inhabited. -/
instance sourceProductSphere_nonempty :
    Nonempty
      (UnitSpherePolynomialWrapper.SourceProductSphere sourceBlock) := by
  simpa only [sourceBlock,
    NormalizedCorrectedFixedDetectorCompactSourceCode.layout,
    NormalizedCorrectedFixedDetectorCompactSourceCode.finalDimension,
    NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDimension,
    NormalizedCorrectedFixedDetectorCompactSourceCode.affineBlockCount,
    NormalizedCorrectedFixedDetectorCompactSourceCode.compactBlockCount]
    using
      CompactAccumulatorPipelineCode.nonempty_sourceProductSphere_oneBlockAllAffine
          (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDimension
            equationCount variableCount)
          (NormalizedCorrectedFixedDetectorCompactSourceCode.driftDimension
            variableCount)

/-- One fixed odd degree for the compact-sign source certificate. -/
noncomputable abbrev wrapperDegree : ℕ :=
  CompactAccumulatorPipelineCode.wrapperDegree
    UniversalHalting.unconditionalNormalizedCorrectedDetectorSourceDegree
    NormalizedCorrectedFixedDetectorCompactSourceCode.affineBlockCount
    UniversalHalting.unconditionalNormalizedCorrectedDetectorClearingExponent

theorem wrapperDegree_ge_three :
    3 ≤ wrapperDegree :=
  CompactAccumulatorPipelineCode.wrapperDegree_ge_three _ _ _

theorem wrapperDegree_odd :
    wrapperDegree % 2 = 1 :=
  CompactAccumulatorPipelineCode.wrapperDegree_odd _ _ _

/-- Each encoded universal instance has exactly the same semantic wrapper
degree. -/
theorem instance_wrapperDegree_eq (input : ℕ) :
    CompactAccumulatorPipelineCode.wrapperDegree
        (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDegreeBound
          (UniversalHalting.unconditionalUniversalHaltingFixedDQL input))
        NormalizedCorrectedFixedDetectorCompactSourceCode.affineBlockCount
        (NormalizedCorrectedFixedDetectorCompactSourceCode.clearingExponent
          (UniversalHalting.unconditionalUniversalHaltingFixedDQL input)) =
      wrapperDegree := by
  rw [
    UniversalHalting.unconditionalUniversalHaltingFixedDQL_normalizedCorrected_sourceDegreeBound_eq,
    UniversalHalting.unconditionalUniversalHaltingFixedDQL_normalizedCorrected_clearingExponent_eq]

/-- Executable compact source field/reward syntax for a unary universal
halting input. -/
def sourceCode (input : ℕ) :
    PolynomialFieldCode compactSourceDimension ×
      PolynomialCode compactSourceDimension :=
  NormalizedCorrectedFixedDetectorCompactSourceCode.compile
    (NormalizedCorrectedEffectiveCompilerInput.compilerInput
      (UniversalHalting.unconditionalUniversalHaltingFixedDQL input))

/-- The complete fixed-resource source compiler is computable. -/
theorem sourceCode_computable :
    Computable sourceCode :=
  NormalizedCorrectedEffectiveCompilerInput.compiledSourceCode_computable.comp
      UniversalHalting.unconditionalUniversalHaltingFixedDQL_computable

end

end HGAS.NormalizedCorrectedUnconditionalCompactResources
