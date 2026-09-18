import HGAS.Arithmetic.FixedTemplatePolynomialDQL

/-!
# Fixed-resource DQL systems from finite Diophantine representations

This file packages the fixed-template compiler at the level used by the
universal-halting reduction.  A finite Diophantine representation contains
one fixed sparse polynomial.  Consequently both DQL dimensions below are
literal constants attached to that representation; varying the represented
parameter tuple changes only coefficients and right-hand sides.

The final section applies the construction to the finite universal
Diophantine representation obtained from the explicitly isolated DPRM
closure statement.  It gives a computable many-one reduction into one
fixed type `DQLSystem E V`, and proves that solvability on that type is
`Σ⁰₁`-complete.
-/

namespace HGAS

namespace FiniteDiophantineRepresentation

open FixedTemplatePolynomialDQL

variable {m : ℕ} {set : Set (Fin m → ℕ)}

/-- Fixed equation count associated with one finite representation. -/
abbrev fixedDQLEquationCount
    (representation : FiniteDiophantineRepresentation m set) : ℕ :=
  templateEquationCount representation.polynomial

/-- Fixed variable count associated with one finite representation. -/
abbrev fixedDQLVariableCount
    (representation : FiniteDiophantineRepresentation m set) : ℕ :=
  templateVariableCount representation.polynomial

/-- Compile the fixed representing polynomial at a parameter tuple,
without changing either DQL dimension. -/
def fixedDQL
    (representation : FiniteDiophantineRepresentation m set)
    (parameters : Fin m → ℕ) :
    DQLSystem (fixedDQLEquationCount representation)
      (fixedDQLVariableCount representation) :=
  fixedTemplateDQL representation.polynomial parameters

/-- Exact represented-set semantics of the fixed-resource compiler. -/
theorem fixedDQL_solvable_iff
    (representation : FiniteDiophantineRepresentation m set)
    (parameters : Fin m → ℕ) :
    (representation.fixedDQL parameters).Solvable ↔
      parameters ∈ set := by
  rw [fixedDQL,
    FixedTemplatePolynomialDQL.fixedTemplateDQL_solvable_iff]
  exact (representation.represents parameters).symm

/-- Parameter specialization into the fixed DQL type is computable. -/
theorem fixedDQL_computable
    (representation : FiniteDiophantineRepresentation m set) :
    Computable representation.fixedDQL :=
  FixedTemplatePolynomialDQL.fixedTemplateDQL_computable
    representation.polynomial

/-- Every finite representation supplies a computable many-one reduction
from represented-set membership into solvability on one fixed DQL type. -/
theorem manyOneReducible_fixedDQL
    (representation : FiniteDiophantineRepresentation m set) :
    (fun parameters => parameters ∈ set) ≤₀
      (DQLSystem.Solvable :
        DQLSystem (fixedDQLEquationCount representation)
          (fixedDQLVariableCount representation) → Prop) := by
  exact
    ⟨representation.fixedDQL, representation.fixedDQL_computable,
      fun parameters =>
        (representation.fixedDQL_solvable_iff parameters).symm⟩

end FiniteDiophantineRepresentation

namespace UniversalHalting

open FixedTemplatePolynomialDQL

/-- The chosen finite universal representation, named locally to keep all
resource formulas readable. -/
noncomputable abbrev fixedUniversalRepresentation
    (closure : BinaryPrimitiveRecursiveRelationsAreDiophantine) :
    FiniteDiophantineRepresentation 1 UnarySet :=
  universalHaltingRepresentationOfPrimitiveRecursiveClosure closure

/-- The equation count, fixed once the DPRM closure witness and the
resulting universal polynomial have been chosen. -/
noncomputable abbrev fixedUniversalDQLEquationCount
    (closure : BinaryPrimitiveRecursiveRelationsAreDiophantine) : ℕ :=
  (fixedUniversalRepresentation closure).fixedDQLEquationCount

/-- The variable count, fixed once the universal polynomial has
been chosen. -/
noncomputable abbrev fixedUniversalDQLVariableCount
    (closure : BinaryPrimitiveRecursiveRelationsAreDiophantine) : ℕ :=
  (fixedUniversalRepresentation closure).fixedDQLVariableCount

/-- Computable specialization of universal halting into one fixed DQL
type.  The codomain dimensions do not depend on `input`. -/
noncomputable def universalHaltingFixedDQL
    (closure : BinaryPrimitiveRecursiveRelationsAreDiophantine)
    (input : ℕ) :
    DQLSystem (fixedUniversalDQLEquationCount closure)
      (fixedUniversalDQLVariableCount closure) :=
  (fixedUniversalRepresentation closure).fixedDQL (unaryVector input)

/-- The fixed-type instance is solvable exactly on universal-halting
inputs. -/
theorem universalHaltingFixedDQL_solvable_iff
    (closure : BinaryPrimitiveRecursiveRelationsAreDiophantine)
    (input : ℕ) :
    (universalHaltingFixedDQL closure input).Solvable ↔
      Predicate input := by
  rw [universalHaltingFixedDQL,
    FiniteDiophantineRepresentation.fixedDQL_solvable_iff]
  rfl

/-- Although its target type contains the nonconstructively extracted
universal polynomial, the specialization function itself is computable:
that polynomial is fixed data, and only the unary input varies. -/
theorem universalHaltingFixedDQL_computable
    (closure : BinaryPrimitiveRecursiveRelationsAreDiophantine) :
    Computable (universalHaltingFixedDQL closure) := by
  exact
    (fixedUniversalRepresentation closure).fixedDQL_computable.comp
      unaryVector_primrec.to_comp

/-- Universal halting computably many-one reduces to solvability of DQL
systems with these two fixed dimensions. -/
theorem predicate_manyOneReducible_fixedDQL
    (closure : BinaryPrimitiveRecursiveRelationsAreDiophantine) :
    Predicate ≤₀
      (DQLSystem.Solvable :
        DQLSystem (fixedUniversalDQLEquationCount closure)
          (fixedUniversalDQLVariableCount closure) → Prop) := by
  exact
    ⟨universalHaltingFixedDQL closure,
      universalHaltingFixedDQL_computable closure,
      fun input =>
        (universalHaltingFixedDQL_solvable_iff closure input).symm⟩

/-- Solvability on a single fixed DQL type is `Σ⁰₁`-complete,
conditional only on the named primitive-recursive Diophantine closure
theorem. -/
theorem fixedDQLSolvability_sigmaOneComplete
    (closure : BinaryPrimitiveRecursiveRelationsAreDiophantine) :
    SigmaOneComplete
      (DQLSystem.Solvable :
        DQLSystem (fixedUniversalDQLEquationCount closure)
          (fixedUniversalDQLVariableCount closure) → Prop) := by
  constructor
  · exact
      DQLSystem.solvable_re
        (fixedUniversalDQLEquationCount closure)
        (fixedUniversalDQLVariableCount closure)
  · intro predicate hpredicate
    exact
      (re_manyOneReducible_predicate hpredicate).trans
        (predicate_manyOneReducible_fixedDQL closure)

/-- Hence solvability on that one fixed DQL type is not computable. -/
theorem fixedDQLSolvability_not_computable
    (closure : BinaryPrimitiveRecursiveRelationsAreDiophantine) :
    ¬ComputablePred
      (DQLSystem.Solvable :
        DQLSystem (fixedUniversalDQLEquationCount closure)
          (fixedUniversalDQLVariableCount closure) → Prop) :=
  (fixedDQLSolvability_sigmaOneComplete closure).not_computable

end UniversalHalting

end HGAS
