import HGAS.Arithmetic.PrimitiveRecursiveDiophantine
import HGAS.Arithmetic.UniversalHaltingDiophantineGap

/-!
# The unconditional primitive-recursive MRDP interface

Earlier modules deliberately parameterized the universal-halting
reduction by

```
BinaryPrimitiveRecursiveRelationsAreDiophantine.
```

The sparse bounded-universal construction and the radix-trace induction
now prove that proposition.  This short module connects the completed
proof to the existing universal-halting and fixed-polynomial pipeline.

No assumption, axiom, placeholder, or opaque external DPRM theorem occurs
in this file.
-/

namespace HGAS

namespace UniversalHalting

/-- The formerly isolated closure specification is now a theorem. -/
theorem binaryPrimitiveRecursiveRelationsAreDiophantine :
    BinaryPrimitiveRecursiveRelationsAreDiophantine := by
  intro relation hrelation
  exact
    PrimitiveRecursiveDiophantine.binaryPrimrecRel_dioph
      relation hrelation

/-- The literal bounded universal-machine trace relation is
Diophantine, unconditionally. -/
theorem boundedTraceSet_dioph_unconditional :
    Dioph BoundedTraceSet :=
  boundedTraceSet_dioph
    binaryPrimitiveRecursiveRelationsAreDiophantine

/-- Universal halting is a unary Diophantine set. -/
theorem unarySet_dioph_unconditional :
    Dioph UnarySet :=
  unarySet_dioph_of_boundedTraceSet_dioph
    boundedTraceSet_dioph_unconditional

/-- A fixed finite sparse integer polynomial representing universal
halting.  Noncomputability here is only the harmless choice of one
finite-support representative from a proof in `Prop`; the represented
set and the polynomial are fixed once and for all. -/
noncomputable def unconditionalUniversalHaltingRepresentation :
    FiniteDiophantineRepresentation 1 UnarySet :=
  universalHaltingRepresentationOfPrimitiveRecursiveClosure
    binaryPrimitiveRecursiveRelationsAreDiophantine

/-- Exact semantics of the fixed universal-halting polynomial. -/
theorem unconditionalUniversalHaltingRepresentation_spec
    (parameters : Fin 1 → ℕ) :
    parameters ∈ UnarySet ↔
      ∃ witnesses :
          Fin unconditionalUniversalHaltingRepresentation.witnessCount →
            ℕ,
        IntegerPolynomialCode.eval
            unconditionalUniversalHaltingRepresentation.polynomial
            (Fin.addCases parameters witnesses) = 0 :=
  unconditionalUniversalHaltingRepresentation.represents parameters

/-- Solvability of the fixed universal polynomial is not computable. -/
theorem unconditionalUniversalHaltingPolynomialSolvability_not_computable :
    ¬ComputablePred
      (fun parameters : Fin 1 → ℕ =>
        ∃ witnesses :
            Fin
              unconditionalUniversalHaltingRepresentation.witnessCount →
                ℕ,
          IntegerPolynomialCode.eval
              unconditionalUniversalHaltingRepresentation.polynomial
              (Fin.addCases parameters witnesses) = 0) := by
  simpa [unconditionalUniversalHaltingRepresentation] using
    universalHaltingPolynomialSolvability_not_computable
      binaryPrimitiveRecursiveRelationsAreDiophantine

/-- The literal DQL instance produced from the fixed universal polynomial
after substituting one program/input code. -/
noncomputable def unconditionalUniversalHaltingDQL
    (input : ℕ) :=
  universalHaltingDQL
    binaryPrimitiveRecursiveRelationsAreDiophantine input

/-- Exact correctness of the unconditional DQL reduction. -/
theorem unconditionalUniversalHaltingDQL_solvable_iff
    (input : ℕ) :
    (unconditionalUniversalHaltingDQL input).Solvable ↔
      Predicate input := by
  exact
    universalHaltingDQL_solvable_iff
      binaryPrimitiveRecursiveRelationsAreDiophantine input

/-- Solvability in this fixed one-parameter DQL family is undecidable. -/
theorem unconditionalUniversalHaltingDQLSolvability_not_computable :
    ¬ComputablePred
      (fun input =>
        (unconditionalUniversalHaltingDQL input).Solvable) := by
  simpa [unconditionalUniversalHaltingDQL] using
    universalHaltingDQLSolvability_not_computable
      binaryPrimitiveRecursiveRelationsAreDiophantine

end UniversalHalting

end HGAS
