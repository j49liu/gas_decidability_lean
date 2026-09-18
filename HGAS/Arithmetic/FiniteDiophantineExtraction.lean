import HGAS.Arithmetic.MathlibDiophBridge
import Mathlib.Tactic

/-!
# Noncomputable extraction of finitely many Diophantine witnesses

Mathlib's definition

```
Dioph S := ∃ β p, ∀ v, v ∈ S ↔ ∃ t : β → ℕ, p (Sum.elim v t) = 0
```

allows an arbitrary witness-index type `β`.  This is harmless
mathematically: a polynomial expression mentions only finitely many
variables.  The present file proves that observation carefully.

Starting from a proof that a set on `Fin m` is Diophantine, we:

1. recover a finite expression tree from its `IsPoly` derivation;
2. collect the finitely many witness indices occurring in that tree;
3. reindex precisely those witnesses by a finite type;
4. compile the resulting finite polynomial to the sparse executable code
   used by `FiniteDiophantineRepresentation`.

The construction is deliberately `noncomputable`.  A proof of `Dioph`
lives in `Prop`, and hence cannot serve as an executable compiler input.
For the lower-bound argument this distinction is useful: once one proves
the *single fixed* universal predicate Diophantine, this file is enough to
obtain a fixed finite polynomial.  The missing theorem is therefore
reduced to the semantic DPRM closure step, rather than finite-support
bookkeeping.
-/

namespace HGAS

open scoped BigOperators

/-! ## Polynomial syntax on an arbitrary index type -/

/-- A finite expression for a Mathlib-style integer polynomial on an
arbitrary variable-index type. -/
inductive IndexedPolynomialExpression (ι : Type*) where
  | projection (i : ι)
  | constant (value : ℤ)
  | sub (left right : IndexedPolynomialExpression ι)
  | mul (left right : IndexedPolynomialExpression ι)

namespace IndexedPolynomialExpression

variable {ι : Type*}

/-- Evaluation of an indexed polynomial expression. -/
def eval (assignment : ι → ℕ) :
    IndexedPolynomialExpression ι → ℤ
  | .projection i => assignment i
  | .constant value => value
  | .sub left right => eval assignment left - eval assignment right
  | .mul left right => eval assignment left * eval assignment right

/-- Interpret explicit syntax as Mathlib's extensional polynomial. -/
def toMathlibPoly :
    IndexedPolynomialExpression ι → Poly ι
  | .projection i => Poly.proj i
  | .constant value => Poly.const value
  | .sub left right => left.toMathlibPoly - right.toMathlibPoly
  | .mul left right => left.toMathlibPoly * right.toMathlibPoly

@[simp]
theorem toMathlibPoly_apply
    (expression : IndexedPolynomialExpression ι)
    (assignment : ι → ℕ) :
    expression.toMathlibPoly assignment =
      expression.eval assignment := by
  induction expression with
  | projection i => rfl
  | constant value => rfl
  | sub left right ihLeft ihRight =>
      simp [toMathlibPoly, eval, ihLeft, ihRight]
  | mul left right ihLeft ihRight =>
      simp [toMathlibPoly, eval, ihLeft, ihRight]

/-- Structural completeness of the explicit syntax for `IsPoly`.
The result is existential because the derivation and result both live in
`Prop`. -/
theorem exists_of_isPoly
    {function : (ι → ℕ) → ℤ} (hfunction : IsPoly function) :
    ∃ expression : IndexedPolynomialExpression ι,
      ∀ assignment, expression.eval assignment =
        function assignment := by
  induction hfunction with
  | proj i =>
      exact ⟨.projection i, fun _ => rfl⟩
  | const value =>
      exact ⟨.constant value, fun _ => rfl⟩
  | sub hleft hright ihLeft ihRight =>
      obtain ⟨left, hleft⟩ := ihLeft
      obtain ⟨right, hright⟩ := ihRight
      exact ⟨.sub left right, fun assignment => by
        simp only [eval]
        rw [hleft, hright]⟩
  | mul hleft hright ihLeft ihRight =>
      obtain ⟨left, hleft⟩ := ihLeft
      obtain ⟨right, hright⟩ := ihRight
      exact ⟨.mul left right, fun assignment => by
        simp only [eval]
        rw [hleft, hright]⟩

/-! ## Collecting and reindexing witness variables -/

variable {m : ℕ} {β : Type*} [DecidableEq β]

/-- The finite set of right-summand (witness) variables actually
mentioned by an expression. -/
noncomputable def witnessSupport :
    IndexedPolynomialExpression (Fin m ⊕ β) → Finset β
  | .projection (.inl _) => ∅
  | .projection (.inr witness) => {witness}
  | .constant _ => ∅
  | .sub left right =>
      left.witnessSupport ∪ right.witnessSupport
  | .mul left right =>
      left.witnessSupport ∪ right.witnessSupport

/-- Reindex an expression into any finite witness support containing all
of the witnesses that it uses. -/
noncomputable def reindexWitnessesInto
    (support : Finset β) :
    (expression : IndexedPolynomialExpression (Fin m ⊕ β)) →
      expression.witnessSupport ⊆ support →
      IndexedPolynomialExpression
        (Fin m ⊕ Fin (Fintype.card ↥support))
  | .projection (.inl parameter), _ =>
      .projection (.inl parameter)
  | .projection (.inr witness), hsupport =>
      .projection (.inr
        (Fintype.equivFin ↥support
          ⟨witness, by
            apply hsupport
            simp [witnessSupport]⟩))
  | .constant value, _ =>
      .constant value
  | .sub left right, hsupport =>
      .sub
        (reindexWitnessesInto support left
          (Finset.Subset.trans Finset.subset_union_left hsupport))
        (reindexWitnessesInto support right
          (Finset.Subset.trans Finset.subset_union_right hsupport))
  | .mul left right, hsupport =>
      .mul
        (reindexWitnessesInto support left
          (Finset.Subset.trans Finset.subset_union_left hsupport))
        (reindexWitnessesInto support right
          (Finset.Subset.trans Finset.subset_union_right hsupport))

/-- Restrict an arbitrary witness assignment to a finite support. -/
noncomputable def compressWitnesses
    (support : Finset β) (witnesses : β → ℕ) :
    Fin (Fintype.card ↥support) → ℕ :=
  fun index =>
    witnesses ((Fintype.equivFin ↥support).symm index).1

/-- Extend a finite witness assignment by zero away from its support. -/
noncomputable def expandWitnesses
    (support : Finset β)
    (witnesses : Fin (Fintype.card ↥support) → ℕ) :
    β → ℕ :=
  fun witness =>
    if hwitness : witness ∈ support then
      witnesses (Fintype.equivFin ↥support ⟨witness, hwitness⟩)
    else
      0

/-- Reindexing preserves evaluation when an original assignment is
restricted to the finite support. -/
theorem eval_reindexWitnessesInto_compress
    (support : Finset β)
    (expression : IndexedPolynomialExpression (Fin m ⊕ β))
    (hsupport : expression.witnessSupport ⊆ support)
    (parameters : Fin m → ℕ) (witnesses : β → ℕ) :
    (reindexWitnessesInto support expression hsupport).eval
        (Sum.elim parameters (compressWitnesses support witnesses)) =
      expression.eval (Sum.elim parameters witnesses) := by
  induction expression with
  | projection index =>
      cases index with
      | inl parameter =>
          rfl
      | inr witness =>
          have hwitness : witness ∈ support := by
            apply hsupport
            simp [witnessSupport]
          simp only [reindexWitnessesInto, eval, Sum.elim_inr,
            compressWitnesses]
          rw [Equiv.symm_apply_apply]
  | constant value =>
      rfl
  | sub left right ihLeft ihRight =>
      simp only [reindexWitnessesInto, eval]
      rw [ihLeft, ihRight]
  | mul left right ihLeft ihRight =>
      simp only [reindexWitnessesInto, eval]
      rw [ihLeft, ihRight]

/-- Conversely, reindexing preserves evaluation after a finite
assignment is extended by zero away from the support. -/
theorem eval_reindexWitnessesInto_expand
    (support : Finset β)
    (expression : IndexedPolynomialExpression (Fin m ⊕ β))
    (hsupport : expression.witnessSupport ⊆ support)
    (parameters : Fin m → ℕ)
    (witnesses : Fin (Fintype.card ↥support) → ℕ) :
    (reindexWitnessesInto support expression hsupport).eval
        (Sum.elim parameters witnesses) =
      expression.eval
        (Sum.elim parameters
          (expandWitnesses support witnesses)) := by
  induction expression with
  | projection index =>
      cases index with
      | inl parameter =>
          rfl
      | inr witness =>
          have hwitness : witness ∈ support := by
            apply hsupport
            simp [witnessSupport]
          simp [reindexWitnessesInto, eval, expandWitnesses,
            hwitness]
  | constant value =>
      rfl
  | sub left right ihLeft ihRight =>
      simp only [reindexWitnessesInto, eval]
      rw [ihLeft, ihRight]
  | mul left right ihLeft ihRight =>
      simp only [reindexWitnessesInto, eval]
      rw [ihLeft, ihRight]

/-- Reindex an expression by exactly the witnesses occurring in it. -/
noncomputable def reindexWitnesses
    (expression : IndexedPolynomialExpression (Fin m ⊕ β)) :
    IndexedPolynomialExpression
      (Fin m ⊕ Fin
        (Fintype.card ↥expression.witnessSupport)) :=
  reindexWitnessesInto expression.witnessSupport expression
    Finset.Subset.rfl

end IndexedPolynomialExpression

/-! ## From Mathlib `Dioph` to finite sparse code -/

/-- Every Mathlib-Diophantine set on a finite parameter tuple admits a
finite sparse-polynomial representation.

This is an existence theorem, not an effective compiler: the proof of
`Dioph set` is eliminated only into another proposition. -/
theorem exists_finiteDiophantineRepresentation_of_dioph
    {m : ℕ} {set : Set (Fin m → ℕ)}
    (hset : Dioph set) :
    Nonempty (FiniteDiophantineRepresentation m set) := by
  obtain ⟨β, polynomial, hpolynomial⟩ := hset
  letI : DecidableEq β := Classical.decEq β
  obtain ⟨expression, hexpression⟩ :=
    IndexedPolynomialExpression.exists_of_isPoly
      polynomial.isPoly
  let support := expression.witnessSupport
  let witnessCount := Fintype.card ↥support
  let finiteExpression :
      IndexedPolynomialExpression
        (Fin m ⊕ Fin witnessCount) :=
    IndexedPolynomialExpression.reindexWitnessesInto
      support expression Finset.Subset.rfl
  let finitePolynomial : Poly (Fin m ⊕ Fin witnessCount) :=
    finiteExpression.toMathlibPoly
  have hcorrect :
      ∀ parameters, parameters ∈ set ↔
        ∃ witnesses : Fin witnessCount → ℕ,
          finitePolynomial
            (Sum.elim parameters witnesses) = 0 := by
    intro parameters
    rw [hpolynomial parameters]
    constructor
    · rintro ⟨witnesses, hwitnesses⟩
      refine ⟨IndexedPolynomialExpression.compressWitnesses
        support witnesses, ?_⟩
      simp only [finitePolynomial,
        IndexedPolynomialExpression.toMathlibPoly_apply]
      rw [
        IndexedPolynomialExpression.eval_reindexWitnessesInto_compress]
      rw [hexpression]
      exact hwitnesses
    · rintro ⟨witnesses, hwitnesses⟩
      refine ⟨IndexedPolynomialExpression.expandWitnesses
        support witnesses, ?_⟩
      rw [← hexpression]
      rw [←
        IndexedPolynomialExpression.eval_reindexWitnessesInto_expand
          support expression Finset.Subset.rfl parameters witnesses]
      simpa [finitePolynomial] using hwitnesses
  exact ⟨FiniteDiophantineRepresentation.ofMathlibPoly
    witnessCount finitePolynomial hcorrect⟩

/-- A chosen finite representation of a Mathlib-Diophantine set.
Noncomputability is unavoidable because the input is a proof in `Prop`. -/
noncomputable def finiteDiophantineRepresentationOfDioph
    {m : ℕ} {set : Set (Fin m → ℕ)}
    (hset : Dioph set) :
    FiniteDiophantineRepresentation m set :=
  (Classical.choice
    (exists_finiteDiophantineRepresentation_of_dioph hset))

end HGAS
