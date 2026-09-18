import HGAS.Arithmetic.ExecutableMRDPBoundary
import HGAS.Arithmetic.FiniteDiophantineExtraction
import HGAS.Arithmetic.FiniteRepresentationDQL
import HGAS.Arithmetic.RadixSequenceCode
import Mathlib.Tactic

/-!
# The exact remaining Diophantine theorem for universal halting

The earlier boundary was phrased as a polynomial certificate tailored to
`Nat.Partrec.Code.evaln`.  The finite-support extraction theorem lets us
replace that tailored assumption by one standard semantic closure theorem:

> every primitive-recursive binary relation on natural numbers is
> Diophantine.

This file proves, without assumptions, that this single statement produces
a finite polynomial representation of universal halting.  It bypasses the
older bounded-trace certificate interface: Mathlib's existential closure
first absorbs the resource bound, and finite-support extraction is then
applied directly to the unary universal set.  Thus all
interpreter-specific, finite-variable, and sparse-compilation bookkeeping
is now discharged.

The proposition `BinaryPrimitiveRecursiveRelationsAreDiophantine` is not
postulated.  It is a named specification of the theorem still
absent from Mathlib.  Proving it is the primitive-recursion/bounded-
universal-quantifier part of DPRM.  `RadixSequenceCode` supplies the
elementary finite-sequence code needed in a future direct proof.
-/

namespace HGAS

namespace UniversalHalting

/-- The two-coordinate set corresponding to the bounded trace relation. -/
def BoundedTraceSet : Set (Fin 2 → ℕ) :=
  {input | BoundedTrace (input 0) (input 1)}

/-- The precise semantic primitive-recursion closure theorem needed here.

It is stated only for binary natural-number relations because that is the
smallest form sufficient for `BoundedTrace`. -/
def BinaryPrimitiveRecursiveRelationsAreDiophantine : Prop :=
  ∀ relation : ℕ → ℕ → Prop,
    PrimrecRel relation →
      Dioph
        {input : Fin 2 → ℕ |
          relation (input 0) (input 1)}

/-- The generic semantic closure theorem applies directly to the literal
bounded interpreter already proved primitive recursive. -/
theorem boundedTraceSet_dioph
    (closure :
      BinaryPrimitiveRecursiveRelationsAreDiophantine) :
    Dioph BoundedTraceSet := by
  simpa [BoundedTraceSet] using
    closure BoundedTrace boundedTrace_primrecRel

/-- Split the two trace coordinates into a unary parameter and a unary
existential bound. -/
def splitTraceIndex : Fin 2 → Fin 1 ⊕ Fin 1 :=
  (finSumFinEquiv : (Fin 1 ⊕ Fin 1) ≃ Fin 2).symm

/-- Existentially quantifying the bound in a Diophantine bounded-trace
relation gives the unary universal halting set. -/
theorem unarySet_dioph_of_boundedTraceSet_dioph
    (htrace : Dioph BoundedTraceSet) :
    Dioph UnarySet := by
  have hsplit :
      Dioph
        {assignment : (Fin 1 ⊕ Fin 1) → ℕ |
          assignment ∘ splitTraceIndex ∈ BoundedTraceSet} :=
    Dioph.reindex_dioph (Fin 1 ⊕ Fin 1)
      splitTraceIndex htrace
  have hexists :
      Dioph
        {parameters : Fin 1 → ℕ |
          ∃ bound : Fin 1 → ℕ,
            Sum.elim parameters bound ∘ splitTraceIndex ∈
              BoundedTraceSet} :=
    Dioph.ex_dioph hsplit
  refine hexists.ext fun parameters => ?_
  change
    (∃ bound : Fin 1 → ℕ,
      BoundedTrace
        ((Sum.elim parameters bound ∘ splitTraceIndex) 0)
        ((Sum.elim parameters bound ∘ splitTraceIndex) 1)) ↔
      Predicate (parameters 0)
  rw [predicate_iff_exists_bound]
  constructor
  · rintro ⟨bound, hbound⟩
    exact ⟨bound 0, by
      simpa [splitTraceIndex] using hbound⟩
  · rintro ⟨bound, hbound⟩
    refine ⟨fun _ => bound, ?_⟩
    simpa [splitTraceIndex] using hbound

/-- Under the same one theorem, universal halting has a finite sparse
Diophantine representation. -/
noncomputable def universalHaltingRepresentationOfPrimitiveRecursiveClosure
    (closure :
      BinaryPrimitiveRecursiveRelationsAreDiophantine) :
    FiniteDiophantineRepresentation 1 UnarySet :=
  finiteDiophantineRepresentationOfDioph
    (unarySet_dioph_of_boundedTraceSet_dioph
      (boundedTraceSet_dioph closure))

/-- Hence the represented parameterized zero problem is noncomputable.
No additional effectiveness assumption is needed: the chosen universal
polynomial is fixed once and for all. -/
theorem universalHaltingPolynomialSolvability_not_computable
    (closure :
      BinaryPrimitiveRecursiveRelationsAreDiophantine) :
    ¬ComputablePred
      (fun parameters : Fin 1 → ℕ =>
        ∃ witnesses :
            Fin
              (universalHaltingRepresentationOfPrimitiveRecursiveClosure
                closure).witnessCount → ℕ,
          IntegerPolynomialCode.eval
              (universalHaltingRepresentationOfPrimitiveRecursiveClosure
                closure).polynomial
              (Fin.addCases parameters witnesses) = 0) := by
  intro hcomputable
  apply unarySet_not_computable
  exact ComputablePred.of_eq hcomputable fun parameters =>
    ((universalHaltingRepresentationOfPrimitiveRecursiveClosure
      closure).represents parameters).symm

/-- The literal DQL instance obtained by substituting one universal-machine
input into the fixed universal polynomial. -/
noncomputable def universalHaltingDQL
    (closure :
      BinaryPrimitiveRecursiveRelationsAreDiophantine)
    (input : ℕ) :=
  (universalHaltingRepresentationOfPrimitiveRecursiveClosure closure)
    |>.specializedDQL (unaryVector input)

/-- The specialized DQL system is solvable exactly when the encoded
universal program halts. -/
theorem universalHaltingDQL_solvable_iff
    (closure :
      BinaryPrimitiveRecursiveRelationsAreDiophantine)
    (input : ℕ) :
    (universalHaltingDQL closure input).Solvable ↔
      Predicate input := by
  rw [universalHaltingDQL,
    FiniteDiophantineRepresentation.specializedDQL_solvable_iff]
  rfl

/-- Therefore the solvability predicate of this fixed one-parameter DQL
family is not computable. -/
theorem universalHaltingDQLSolvability_not_computable
    (closure :
      BinaryPrimitiveRecursiveRelationsAreDiophantine) :
    ¬ComputablePred
      (fun input => (universalHaltingDQL closure input).Solvable) := by
  intro hcomputable
  exact predicate_not_computable
    (ComputablePred.of_eq hcomputable fun input =>
      universalHaltingDQL_solvable_iff closure input)

end UniversalHalting

end HGAS
