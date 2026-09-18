import HGAS.Arithmetic.DQLNonzeroLinearAugmentation
import HGAS.Arithmetic.FixedTemplateDetectorDegree
import HGAS.Arithmetic.NormalizedCorrectedEffectiveCompilerInput
import HGAS.Arithmetic.UnconditionalFixedDetectorDegree
import HGAS.Compiler.CompactAccumulatorPipelineCertificate
import HGAS.Compiler.CompactAccumulatorPipelineNonempty
import Mathlib.Tactic

/-!
# Fixed resources for the linearly nondegenerate universal DQL family

The normalized three-moment detector needs every DQL variable to occur
linearly somewhere.  `DQLNonzeroLinearAugmentation` enforces that condition
by duplicating every variable and appending `x_j-y_j=0`.  This file applies
that preprocessing to the once-and-for-all universal-halting DQL family
and freezes all resulting compiler resources.

Nothing semantic is lost:

* augmented solvability is exactly old solvability;
* every augmented linear column is nonzero;
* the augmented specialization map is computable; and
* its dimensions and all detector degrees are independent of the input.
-/

namespace HGAS

namespace DQLNonzeroLinearAugmentation

open FixedTemplateDetectorDegree

variable {eqs vars : ℕ} {I J : DQLSystem eqs vars}

/-- Augmentation preserves equality of the quadratic and linear character
tables. -/
theorem sameCharacterData_augment
    (h : SameCharacterData I J) :
    SameCharacterData (augment I) (augment J) := by
  constructor
  · funext row j
    cases hrow : finSumFinEquiv.symm row with
    | inl r =>
        cases hj : finSumFinEquiv.symm j with
        | inl k =>
            simpa [augment, hrow, hj] using
              congrFun (congrFun h.quadratic r) k
        | inr k =>
            simp [augment, hrow, hj]
    | inr r =>
        cases hj : finSumFinEquiv.symm j <;>
          simp [augment, hrow, hj]
  · funext row j
    cases hrow : finSumFinEquiv.symm row with
    | inl r =>
        cases hj : finSumFinEquiv.symm j with
        | inl k =>
            simpa [augment, hrow, hj] using
              congrFun (congrFun h.linear r) k
        | inr k =>
            simp [augment, hrow, hj]
    | inr r =>
        cases hj : finSumFinEquiv.symm j <;>
          simp [augment, hrow, hj]

end DQLNonzeroLinearAugmentation

namespace UniversalHalting

open DQLNonzeroLinearAugmentation
open FixedTemplateDetectorDegree

noncomputable section

/-- Fixed row count after appending one equality row per old variable. -/
abbrev augmentedFixedDQLEquationCount : ℕ :=
  unconditionalFixedDQLEquationCount +
    unconditionalFixedDQLVariableCount

/-- Fixed variable count after duplicating every old variable. -/
abbrev augmentedFixedDQLVariableCount : ℕ :=
  unconditionalFixedDQLVariableCount +
    unconditionalFixedDQLVariableCount

/-- The linearly nondegenerate universal-halting DQL family. -/
def augmentedUniversalHaltingFixedDQL (input : ℕ) :
    DQLSystem augmentedFixedDQLEquationCount
      augmentedFixedDQLVariableCount :=
  augment (unconditionalUniversalHaltingFixedDQL input)

/-- The repaired DQL family still has exact universal-halting semantics. -/
theorem augmentedUniversalHaltingFixedDQL_solvable_iff
    (input : ℕ) :
    (augmentedUniversalHaltingFixedDQL input).Solvable ↔
      Predicate input := by
  rw [augmentedUniversalHaltingFixedDQL, augment_solvable_iff,
    unconditionalUniversalHaltingFixedDQL_solvable_iff]

/-- Every variable in every repaired instance has a nonzero linear
coefficient. -/
theorem augmentedUniversalHaltingFixedDQL_hasNonzeroLinearColumn
    (input : ℕ) :
    HasNonzeroLinearColumn
      (augmentedUniversalHaltingFixedDQL input) :=
  augment_hasNonzeroLinearColumn _

/-- The repaired fixed-target specialization remains computable. -/
theorem augmentedUniversalHaltingFixedDQL_computable :
    Computable augmentedUniversalHaltingFixedDQL :=
  augment_computable.comp
    unconditionalUniversalHaltingFixedDQL_computable

/-- Canonical augmented reference used only to name the common finite
degree constants. -/
def augmentedReferenceDQL :
    DQLSystem augmentedFixedDQLEquationCount
      augmentedFixedDQLVariableCount :=
  augment unconditionalReferenceDQL

/-- All repaired universal instances have the same detector character
tables as the repaired reference instance. -/
theorem augmentedUniversalHaltingFixedDQL_sameCharacterData
    (input : ℕ) :
    SameCharacterData
      (augmentedUniversalHaltingFixedDQL input)
      augmentedReferenceDQL := by
  apply sameCharacterData_augment
  exact
    fixedTemplateDQL_sameCharacterData
      unconditionalUniversalPolynomial (unaryVector input)
        (fun _ ↦ 0)

/-- One input-independent normalized affine-source degree. -/
abbrev augmentedNormalizedCorrectedDetectorSourceDegree : ℕ :=
  NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDegreeBound
    augmentedReferenceDQL

/-- One input-independent normalized clearing exponent. -/
abbrev augmentedNormalizedCorrectedDetectorClearingExponent : ℕ :=
  NormalizedCorrectedFixedDetectorCompactSourceCode.clearingExponent
    augmentedReferenceDQL

/-- One input-independent complete normalized compiler degree. -/
abbrev augmentedNormalizedCorrectedDetectorCompilerDegree : ℕ :=
  NormalizedCorrectedFixedDetectorCompactSourceCode.compilerDegree
    augmentedReferenceDQL

theorem
    augmentedUniversalHaltingFixedDQL_normalizedCorrected_sourceDegreeBound_eq
    (input : ℕ) :
    NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDegreeBound
        (augmentedUniversalHaltingFixedDQL input) =
      augmentedNormalizedCorrectedDetectorSourceDegree :=
  SameCharacterData.sourceDegreeBound_eq
    (augmentedUniversalHaltingFixedDQL_sameCharacterData input)

theorem
    augmentedUniversalHaltingFixedDQL_normalizedCorrected_clearingExponent_eq
    (input : ℕ) :
    NormalizedCorrectedFixedDetectorCompactSourceCode.clearingExponent
        (augmentedUniversalHaltingFixedDQL input) =
      augmentedNormalizedCorrectedDetectorClearingExponent :=
  SameCharacterData.clearingExponent_eq
    (augmentedUniversalHaltingFixedDQL_sameCharacterData input)

theorem
    augmentedUniversalHaltingFixedDQL_normalizedCorrected_compilerDegree_eq
    (input : ℕ) :
    NormalizedCorrectedFixedDetectorCompactSourceCode.compilerDegree
        (augmentedUniversalHaltingFixedDQL input) =
      augmentedNormalizedCorrectedDetectorCompilerDegree :=
  SameCharacterData.compilerDegree_eq
    (augmentedUniversalHaltingFixedDQL_sameCharacterData input)

end

end UniversalHalting

namespace NormalizedCorrectedAugmentedUniversalResources

open DQLNonzeroLinearAugmentation

noncomputable section

abbrev equationCount : ℕ :=
  UniversalHalting.augmentedFixedDQLEquationCount

abbrev variableCount : ℕ :=
  UniversalHalting.augmentedFixedDQLVariableCount

/-- Dimension of the compact source before the homogeneous sign wrapper. -/
abbrev compactSourceDimension : ℕ :=
  NormalizedCorrectedFixedDetectorCompactSourceCode.finalDimension
    equationCount variableCount

abbrev sourceSphereCount : ℕ := 2

/-- Fixed two-block product-of-spheres assignment. -/
def sourceBlock :
    Fin compactSourceDimension → Fin sourceSphereCount :=
  CompactAccumulatorPipelineCode.sourceBlock
    (m :=
      NormalizedCorrectedFixedDetectorCompactSourceCode.driftDimension
        variableCount)
    (NormalizedCorrectedFixedDetectorCompactSourceCode.layout
      (eqs := equationCount) (vars := variableCount))

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

/-- Fixed odd homogeneous wrapper degree for the repaired family. -/
abbrev wrapperDegree : ℕ :=
  CompactAccumulatorPipelineCode.wrapperDegree
    UniversalHalting.augmentedNormalizedCorrectedDetectorSourceDegree
    NormalizedCorrectedFixedDetectorCompactSourceCode.affineBlockCount
    UniversalHalting.augmentedNormalizedCorrectedDetectorClearingExponent

theorem wrapperDegree_ge_three :
    3 ≤ wrapperDegree :=
  CompactAccumulatorPipelineCode.wrapperDegree_ge_three _ _ _

theorem wrapperDegree_odd :
    wrapperDegree % 2 = 1 :=
  CompactAccumulatorPipelineCode.wrapperDegree_odd _ _ _

theorem instance_wrapperDegree_eq (input : ℕ) :
    CompactAccumulatorPipelineCode.wrapperDegree
        (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDegreeBound
          (UniversalHalting.augmentedUniversalHaltingFixedDQL input))
        NormalizedCorrectedFixedDetectorCompactSourceCode.affineBlockCount
        (NormalizedCorrectedFixedDetectorCompactSourceCode.clearingExponent
          (UniversalHalting.augmentedUniversalHaltingFixedDQL input)) =
      wrapperDegree := by
  rw [
    UniversalHalting.augmentedUniversalHaltingFixedDQL_normalizedCorrected_sourceDegreeBound_eq,
    UniversalHalting.augmentedUniversalHaltingFixedDQL_normalizedCorrected_clearingExponent_eq]

/-- Executable compact source syntax for the repaired universal family. -/
def sourceCode (input : ℕ) :
    PolynomialFieldCode compactSourceDimension ×
      PolynomialCode compactSourceDimension :=
  NormalizedCorrectedFixedDetectorCompactSourceCode.compile
    (NormalizedCorrectedEffectiveCompilerInput.compilerInput
      (UniversalHalting.augmentedUniversalHaltingFixedDQL input))

theorem sourceCode_computable :
    Computable sourceCode :=
  NormalizedCorrectedEffectiveCompilerInput.compiledSourceCode_computable.comp
    UniversalHalting.augmentedUniversalHaltingFixedDQL_computable

end

end NormalizedCorrectedAugmentedUniversalResources

end HGAS
