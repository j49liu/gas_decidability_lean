import HGAS.Arithmetic.UnconditionalMRDP
import HGAS.Arithmetic.FixedRepresentationDQL

/-!
# Unconditional fixed-resource DQL completeness

This module specializes the previously parameterized fixed-template DQL
pipeline to the proved primitive-recursive MRDP closure theorem.  It
therefore exhibits fixed, classically selected natural numbers `E` and
`V` such that solvability of `DQLSystem E V` is `Σ⁰₁`-complete.
-/

namespace HGAS

namespace UniversalHalting

/-- Fixed equation count of the chosen universal DQL template. -/
noncomputable abbrev unconditionalFixedDQLEquationCount : ℕ :=
  fixedUniversalDQLEquationCount
    binaryPrimitiveRecursiveRelationsAreDiophantine

/-- Fixed variable count of the chosen universal DQL template. -/
noncomputable abbrev unconditionalFixedDQLVariableCount : ℕ :=
  fixedUniversalDQLVariableCount
    binaryPrimitiveRecursiveRelationsAreDiophantine

/-- Computable specialization into one fixed DQL type. -/
noncomputable def unconditionalUniversalHaltingFixedDQL
    (input : ℕ) :
    DQLSystem unconditionalFixedDQLEquationCount
      unconditionalFixedDQLVariableCount :=
  universalHaltingFixedDQL
    binaryPrimitiveRecursiveRelationsAreDiophantine input

/-- Exact universal-halting semantics. -/
theorem unconditionalUniversalHaltingFixedDQL_solvable_iff
    (input : ℕ) :
    (unconditionalUniversalHaltingFixedDQL input).Solvable ↔
      Predicate input :=
  universalHaltingFixedDQL_solvable_iff
    binaryPrimitiveRecursiveRelationsAreDiophantine input

/-- The fixed-target specialization map is computable. -/
theorem unconditionalUniversalHaltingFixedDQL_computable :
    Computable unconditionalUniversalHaltingFixedDQL :=
  universalHaltingFixedDQL_computable
    binaryPrimitiveRecursiveRelationsAreDiophantine

/-- Universal halting many-one reduces to the single fixed DQL type. -/
theorem predicate_manyOneReducible_unconditionalFixedDQL :
    Predicate ≤₀
      (DQLSystem.Solvable :
        DQLSystem unconditionalFixedDQLEquationCount
          unconditionalFixedDQLVariableCount → Prop) :=
  predicate_manyOneReducible_fixedDQL
    binaryPrimitiveRecursiveRelationsAreDiophantine

/-- Solvability on one fixed DQL type is `Σ⁰₁`-complete. -/
theorem unconditionalFixedDQLSolvability_sigmaOneComplete :
    SigmaOneComplete
      (DQLSystem.Solvable :
        DQLSystem unconditionalFixedDQLEquationCount
          unconditionalFixedDQLVariableCount → Prop) :=
  fixedDQLSolvability_sigmaOneComplete
    binaryPrimitiveRecursiveRelationsAreDiophantine

/-- In particular, fixed-resource DQL solvability is undecidable. -/
theorem unconditionalFixedDQLSolvability_not_computable :
    ¬ComputablePred
      (DQLSystem.Solvable :
        DQLSystem unconditionalFixedDQLEquationCount
          unconditionalFixedDQLVariableCount → Prop) :=
  unconditionalFixedDQLSolvability_sigmaOneComplete.not_computable

end UniversalHalting

end HGAS
