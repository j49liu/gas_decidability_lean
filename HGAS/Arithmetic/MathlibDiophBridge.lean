import HGAS.Arithmetic.PolynomialGateCompiler
import Mathlib.NumberTheory.Dioph
import Mathlib.Tactic

/-!
# Bridging Mathlib Diophantine polynomials to executable sparse code

Mathlib's `Mathlib.NumberTheory.Dioph` develops Diophantine sets using the
type

```
Poly α = { f : (α → ℕ) → ℤ // IsPoly f }.
```

This is an elegant extensional interface: two polynomials are equal when
they have the same evaluation function.  It is not, however, an executable
polynomial syntax.  The only record of how the function was assembled is a
proof of `IsPoly f`, and that proof lies in `Prop`; Lean erases it and
forbids eliminating it into a syntax tree in `Type`.

This file makes the boundary precise and supplies both sides of it:

* `DiophPolynomialExpression` is explicit syntax whose four constructors
  mirror `IsPoly`.
* `DiophPolynomialExpression.compile` is an executable structural compiler
  from that syntax to `IntegerPolynomialCode`.
* `IntegerPolynomialCode.toMathlibPoly` gives the executable semantic map
  in the other direction for every sparse code, with exact evaluation.
* `exists_diophPolynomialExpression_of_isPoly` is the constructive,
  axiom-free structural completeness theorem for an `IsPoly` derivation.
  Its result is existential because both premise and conclusion live in
  `Prop`.
* `integerPolynomialCodeOfMathlibPoly` chooses a sparse code for an
  extensional Mathlib `Poly`.  This final convenience definition is
  deliberately marked `noncomputable`; all semantic correctness results
  remain exact.
* `FiniteDiophantineRepresentation` records the concrete output that a
  genuinely effective finite-variable MRDP construction must provide:
  a natural number of witness variables, a finite sparse integer
  polynomial, and its representation theorem.

Nothing here asserts an effective MRDP theorem.  In particular, Mathlib's
proposition `Dioph` quantifies over an arbitrary witness type and an
extensional `Poly`; those data do not by themselves supply a finite,
computably obtainable polynomial code.  The final section isolates the
additional interface needed by a later effective construction.
-/

namespace HGAS

open scoped BigOperators

namespace ExponentCode

/-- The exponent vector of the variable `X_i`: exponent one at `i` and
zero at every other coordinate. -/
def basis {n : ℕ} (i : Fin n) : ExponentCode n :=
  fun j => if j = i then 1 else 0

/-- The monomial with zero exponent vector is the constant one. -/
@[simp]
theorem evalMonomial_zero {n : ℕ} (x : Fin n → ℕ) :
    NaturalPolynomialCode.evalMonomial
      (zero : ExponentCode n) x = 1 := by
  simp [NaturalPolynomialCode.evalMonomial, zero]

/-- Evaluating the basis monomial at `x` selects the corresponding
coordinate of `x`. -/
@[simp]
theorem evalMonomial_basis {n : ℕ} (i : Fin n)
    (x : Fin n → ℕ) :
    NaturalPolynomialCode.evalMonomial (basis i) x = x i := by
  rw [NaturalPolynomialCode.evalMonomial, List.prod_ofFn]
  rw [Finset.prod_eq_single i]
  · simp [basis]
  · intro j _hj hji
    simp [basis, hji]
  · simp

/-- Adding exponent vectors corresponds to multiplying their monomials. -/
@[simp]
theorem evalMonomial_add {n : ℕ}
    (a b : ExponentCode n) (x : Fin n → ℕ) :
    NaturalPolynomialCode.evalMonomial (add a b) x =
      NaturalPolynomialCode.evalMonomial a x *
        NaturalPolynomialCode.evalMonomial b x := by
  simp only [NaturalPolynomialCode.evalMonomial, add, List.prod_ofFn,
    pow_add, Finset.prod_mul_distrib]

end ExponentCode

namespace IntegerPolynomialCode

/-- Sparse code for a constant integer polynomial. -/
def constant {n : ℕ} (z : ℤ) : IntegerPolynomialCode n :=
  [(ExponentCode.zero, SignedMagnitudeCode.encode z)]

/-- Sparse code for the `i`th coordinate projection. -/
def projection {n : ℕ} (i : Fin n) : IntegerPolynomialCode n :=
  [(ExponentCode.basis i, SignedMagnitudeCode.encode 1)]

/-- Negate every coefficient of a sparse integer polynomial. -/
def neg {n : ℕ} (p : IntegerPolynomialCode n) :
    IntegerPolynomialCode n :=
  p.map fun t => (t.1, SignedMagnitudeCode.neg t.2)

/-- Add sparse polynomials by concatenating their term lists.  Repeated
monomials are allowed by `IntegerPolynomialCode`, so normalization is not
needed for correctness. -/
def add {n : ℕ} (p q : IntegerPolynomialCode n) :
    IntegerPolynomialCode n :=
  p ++ q

/-- Subtraction of sparse integer polynomials. -/
def sub {n : ℕ} (p q : IntegerPolynomialCode n) :
    IntegerPolynomialCode n :=
  add p (neg q)

/-- Multiply two sparse terms by adding exponent vectors and multiplying
signed coefficients. -/
def mulTerm {n : ℕ}
    (a b : ExponentCode n × SignedMagnitudeCode) :
    ExponentCode n × SignedMagnitudeCode :=
  (ExponentCode.add a.1 b.1,
    SignedMagnitudeCode.mul a.2 b.2)

/-- Distributive product of two sparse integer polynomials. -/
def mul {n : ℕ} (p q : IntegerPolynomialCode n) :
    IntegerPolynomialCode n :=
  p.flatMap fun a => q.map (mulTerm a)

/-- Evaluation of the sparse constant code is its integer value. -/
@[simp]
theorem eval_constant {n : ℕ} (z : ℤ) (x : Fin n → ℕ) :
    eval (constant z) x = z := by
  simp [constant, eval, ExponentCode.evalMonomial_zero]

/-- Evaluation of a sparse projection code selects one input. -/
@[simp]
theorem eval_projection {n : ℕ} (i : Fin n) (x : Fin n → ℕ) :
    eval (projection i) x = x i := by
  simp [projection, eval, ExponentCode.evalMonomial_basis]

/-- Coefficientwise sparse negation has the expected semantics. -/
@[simp]
theorem eval_neg {n : ℕ} (p : IntegerPolynomialCode n)
    (x : Fin n → ℕ) :
    eval (neg p) x = -eval p x := by
  induction p with
  | nil => simp [neg, eval]
  | cons t p ih =>
      rw [show neg (t :: p) =
          (t.1, SignedMagnitudeCode.neg t.2) :: neg p by rfl]
      rw [eval_cons, SignedMagnitudeCode.decode_neg, ih, eval_cons]
      ring

/-- Concatenation of term lists adds their evaluations. -/
@[simp]
theorem eval_add {n : ℕ} (p q : IntegerPolynomialCode n)
    (x : Fin n → ℕ) :
    eval (add p q) x = eval p x + eval q x := by
  simp [add, eval, List.map_append]

/-- Sparse subtraction has the expected semantics. -/
@[simp]
theorem eval_sub {n : ℕ} (p q : IntegerPolynomialCode n)
    (x : Fin n → ℕ) :
    eval (sub p q) x = eval p x - eval q x := by
  rw [sub, eval_add, eval_neg]
  ring

private theorem eval_map_mulTerm {n : ℕ}
    (a : ExponentCode n × SignedMagnitudeCode)
    (q : IntegerPolynomialCode n) (x : Fin n → ℕ) :
    eval (q.map (mulTerm a)) x =
      (SignedMagnitudeCode.decode a.2 *
        (NaturalPolynomialCode.evalMonomial a.1 x : ℤ)) *
        eval q x := by
  induction q with
  | nil => simp [eval]
  | cons b q ih =>
      simp only [List.map_cons, eval_cons, mulTerm,
        SignedMagnitudeCode.decode_mul,
        ExponentCode.evalMonomial_add, ih]
      push_cast
      ring

/-- The distributive sparse product has the expected semantics. -/
@[simp]
theorem eval_mul {n : ℕ} (p q : IntegerPolynomialCode n)
    (x : Fin n → ℕ) :
    eval (mul p q) x = eval p x * eval q x := by
  induction p with
  | nil => simp [mul, eval]
  | cons a p ih =>
      rw [show mul (a :: p) q =
          add (q.map (mulTerm a)) (mul p q) by rfl]
      rw [eval_add, eval_map_mulTerm, ih, eval_cons]
      ring

/-! ### The semantic map from sparse codes to Mathlib polynomials -/

variable {n : ℕ}

/-- The Mathlib polynomial represented by one exponent vector with
coefficient one. -/
def monomialMathlibPoly (e : ExponentCode n) : Poly (Fin n) :=
  (List.ofFn fun i => (Poly.proj i) ^ e i).prod

private theorem listProd_apply (polynomials : List (Poly (Fin n)))
    (x : Fin n → ℕ) :
    polynomials.prod x = (polynomials.map fun p => p x).prod := by
  induction polynomials with
  | nil => rfl
  | cons p polynomials ih =>
      simp [ih]

private theorem polyPow_apply (p : Poly (Fin n)) (k : ℕ)
    (x : Fin n → ℕ) :
    (p ^ k) x = p x ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      simp [pow_succ, ih]

/-- Evaluation of the Mathlib monomial agrees with the executable
natural-number monomial evaluator. -/
@[simp]
theorem monomialMathlibPoly_apply (e : ExponentCode n)
    (x : Fin n → ℕ) :
    monomialMathlibPoly e x =
      NaturalPolynomialCode.evalMonomial e x := by
  rw [monomialMathlibPoly, listProd_apply]
  unfold NaturalPolynomialCode.evalMonomial
  have hterms :
      (List.ofFn fun i => ((Poly.proj i) ^ e i) x) =
        List.ofFn fun i => ((x i : ℤ) ^ e i) := by
    apply congrArg List.ofFn
    funext i
    rw [polyPow_apply, Poly.proj_apply]
  rw [List.map_ofFn, Function.comp_def, hterms]
  push_cast
  simp [List.map_ofFn, Function.comp_def]

/-- Interpret every sparse integer polynomial code as a Mathlib
function-based polynomial.  Unlike the converse map below, this direction
is ordinary structural recursion and is executable. -/
def toMathlibPoly : IntegerPolynomialCode n → Poly (Fin n)
  | [] => 0
  | term :: polynomial =>
      Poly.const (SignedMagnitudeCode.decode term.2) *
          monomialMathlibPoly term.1 +
        toMathlibPoly polynomial

/-- The semantic interpretation of sparse code is exactly its direct
integer evaluator. -/
@[simp]
theorem toMathlibPoly_apply (p : IntegerPolynomialCode n)
    (x : Fin n → ℕ) :
    toMathlibPoly p x = eval p x := by
  induction p with
  | nil => simp [toMathlibPoly]
  | cons term polynomial ih =>
      simp [toMathlibPoly, ih, eval_cons]

end IntegerPolynomialCode

/-! ## An executable syntax matching `IsPoly` -/

/-- A finite syntax tree for integer polynomials on `n` natural-number
variables.  Its constructors deliberately mirror the constructors of
Mathlib's `IsPoly`. -/
inductive DiophPolynomialExpression (n : ℕ) where
  | projection (i : Fin n)
  | constant (z : ℤ)
  | sub (left right : DiophPolynomialExpression n)
  | mul (left right : DiophPolynomialExpression n)
deriving DecidableEq, Repr

namespace DiophPolynomialExpression

variable {n : ℕ}

/-- Direct evaluation of an explicit polynomial expression. -/
def eval (x : Fin n → ℕ) : DiophPolynomialExpression n → ℤ
  | .projection i => x i
  | .constant z => z
  | .sub left right => eval x left - eval x right
  | .mul left right => eval x left * eval x right

/-- Executable compilation of a polynomial expression into sparse integer
polynomial code. -/
def compile : DiophPolynomialExpression n → IntegerPolynomialCode n
  | .projection i => IntegerPolynomialCode.projection i
  | .constant z => IntegerPolynomialCode.constant z
  | .sub left right =>
      IntegerPolynomialCode.sub (compile left) (compile right)
  | .mul left right =>
      IntegerPolynomialCode.mul (compile left) (compile right)

/-- Sparse compilation preserves evaluation exactly. -/
@[simp]
theorem eval_compile (expression : DiophPolynomialExpression n)
    (x : Fin n → ℕ) :
    IntegerPolynomialCode.eval expression.compile x =
      expression.eval x := by
  induction expression with
  | projection i => simp [compile, eval]
  | constant z => simp [compile, eval]
  | sub left right ihLeft ihRight =>
      simp [compile, eval, ihLeft, ihRight]
  | mul left right ihLeft ihRight =>
      simp [compile, eval, ihLeft, ihRight]

/-- Regard an explicit expression as Mathlib's extensional polynomial
object. -/
def toMathlibPoly :
    DiophPolynomialExpression n → Poly (Fin n)
  | .projection i => Poly.proj i
  | .constant z => Poly.const z
  | .sub left right => left.toMathlibPoly - right.toMathlibPoly
  | .mul left right => left.toMathlibPoly * right.toMathlibPoly

@[simp]
theorem toMathlibPoly_apply
    (expression : DiophPolynomialExpression n) (x : Fin n → ℕ) :
    expression.toMathlibPoly x = expression.eval x := by
  induction expression with
  | projection i => simp [toMathlibPoly, eval]
  | constant z => simp [toMathlibPoly, eval]
  | sub left right ihLeft ihRight =>
      simp [toMathlibPoly, eval, ihLeft, ihRight]
  | mul left right ihLeft ihRight =>
      simp [toMathlibPoly, eval, ihLeft, ihRight]

/-- The two semantic interpretations of the explicit syntax agree. -/
theorem compile_toMathlibPoly_eval
    (expression : DiophPolynomialExpression n) (x : Fin n → ℕ) :
    IntegerPolynomialCode.eval expression.compile x =
      expression.toMathlibPoly x := by
  rw [eval_compile, toMathlibPoly_apply]

end DiophPolynomialExpression

/-! ## Structural completeness for Mathlib's function-based polynomials -/

/-- Every derivation of Mathlib's `IsPoly` proposition has an extensionally
equal explicit syntax tree.

This theorem is intentionally existential.  The input derivation is a proof
in `Prop`, so Lean erases it during code generation and does not permit the
proof itself to be used as executable data. -/
theorem exists_diophPolynomialExpression_of_isPoly {n : ℕ}
    {f : (Fin n → ℕ) → ℤ} (hf : IsPoly f) :
    ∃ expression : DiophPolynomialExpression n,
      ∀ x, expression.eval x = f x := by
  induction hf with
  | proj i =>
      exact ⟨.projection i, fun _ => rfl⟩
  | const z =>
      exact ⟨.constant z, fun _ => rfl⟩
  | sub hf hg ihf ihg =>
      obtain ⟨left, hleft⟩ := ihf
      obtain ⟨right, hright⟩ := ihg
      exact ⟨.sub left right, fun x =>
        congrArg₂ (· - ·) (hleft x) (hright x)⟩
  | mul hf hg ihf ihg =>
      obtain ⟨left, hleft⟩ := ihf
      obtain ⟨right, hright⟩ := ihg
      exact ⟨.mul left right, fun x =>
        congrArg₂ (· * ·) (hleft x) (hright x)⟩

/-- Every finite-variable Mathlib polynomial admits extensionally equal
sparse integer polynomial code. -/
theorem exists_integerPolynomialCode_of_mathlibPoly {n : ℕ}
    (p : Poly (Fin n)) :
    ∃ code : IntegerPolynomialCode n,
      ∀ x, IntegerPolynomialCode.eval code x = p x := by
  obtain ⟨expression, hexpression⟩ :=
    exists_diophPolynomialExpression_of_isPoly p.isPoly
  exact ⟨expression.compile, fun x => by
    rw [DiophPolynomialExpression.eval_compile, hexpression]⟩

/-- A chosen sparse representation of a Mathlib polynomial.

This definition is noncomputable because it chooses a witness from
`exists_integerPolynomialCode_of_mathlibPoly`.  By contrast,
`DiophPolynomialExpression.compile` above is an ordinary executable
structural recursion. -/
noncomputable def integerPolynomialCodeOfMathlibPoly {n : ℕ}
    (p : Poly (Fin n)) : IntegerPolynomialCode n :=
  Classical.choose (exists_integerPolynomialCode_of_mathlibPoly p)

/-- The chosen sparse representation has exactly the same evaluation
function as its source polynomial. -/
@[simp]
theorem eval_integerPolynomialCodeOfMathlibPoly {n : ℕ}
    (p : Poly (Fin n)) (x : Fin n → ℕ) :
    IntegerPolynomialCode.eval (integerPolynomialCodeOfMathlibPoly p) x =
      p x :=
  Classical.choose_spec (exists_integerPolynomialCode_of_mathlibPoly p) x

/-- Converting a Mathlib polynomial to chosen sparse code and interpreting
that code back in Mathlib is extensionally the identity. -/
@[simp]
theorem toMathlibPoly_integerPolynomialCodeOfMathlibPoly {n : ℕ}
    (p : Poly (Fin n)) :
    IntegerPolynomialCode.toMathlibPoly
      (integerPolynomialCodeOfMathlibPoly p) = p := by
  ext x
  simp

/-- The converse round trip need not reproduce the same sparse term list
(zero terms and repeated monomials make the syntax noncanonical), but it
does reproduce exactly the same evaluation function. -/
@[simp]
theorem eval_integerPolynomialCodeOf_toMathlibPoly {n : ℕ}
    (code : IntegerPolynomialCode n) (x : Fin n → ℕ) :
    IntegerPolynomialCode.eval
        (integerPolynomialCodeOfMathlibPoly
          (IntegerPolynomialCode.toMathlibPoly code)) x =
      IntegerPolynomialCode.eval code x := by
  simp

/-- Passing from a finite-variable Mathlib polynomial to the chosen sparse
code preserves the existence of a natural-number zero. -/
theorem exists_zero_iff_integerPolynomialCodeOfMathlibPoly {n : ℕ}
    (p : Poly (Fin n)) :
    (∃ x : Fin n → ℕ, p x = 0) ↔
      ∃ x : Fin n → ℕ,
        IntegerPolynomialCode.eval
          (integerPolynomialCodeOfMathlibPoly p) x = 0 := by
  simp

/-! ## Flattening a finite parameter/witness split -/

/-- Flatten a polynomial whose variables are separated into parameters and
witnesses into a sparse code indexed by one finite type. -/
noncomputable def splitIntegerPolynomialCodeOfMathlibPoly {m k : ℕ}
    (p : Poly (Fin m ⊕ Fin k)) : IntegerPolynomialCode (m + k) :=
  integerPolynomialCodeOfMathlibPoly (p.map finSumFinEquiv)

/-- Exact evaluation formula for the flattened finite-variable code. -/
@[simp]
theorem eval_splitIntegerPolynomialCodeOfMathlibPoly {m k : ℕ}
    (p : Poly (Fin m ⊕ Fin k)) (parameters : Fin m → ℕ)
    (witnesses : Fin k → ℕ) :
    IntegerPolynomialCode.eval
        (splitIntegerPolynomialCodeOfMathlibPoly p)
        (Fin.addCases parameters witnesses) =
      p (Sum.elim parameters witnesses) := by
  rw [splitIntegerPolynomialCodeOfMathlibPoly,
    eval_integerPolynomialCodeOfMathlibPoly, Poly.map_apply]
  congr 1
  funext i
  cases i with
  | inl i => simp
  | inr i => simp

/-- Flattening preserves pointwise existential solvability in the witness
variables. -/
theorem exists_witness_zero_iff_splitIntegerPolynomialCodeOfMathlibPoly
    {m k : ℕ} (p : Poly (Fin m ⊕ Fin k))
    (parameters : Fin m → ℕ) :
    (∃ witnesses : Fin k → ℕ,
        p (Sum.elim parameters witnesses) = 0) ↔
      ∃ witnesses : Fin k → ℕ,
        IntegerPolynomialCode.eval
          (splitIntegerPolynomialCodeOfMathlibPoly p)
          (Fin.addCases parameters witnesses) = 0 := by
  simp

/-! ## The data an effective finite-variable MRDP compiler must return -/

/-- Fully explicit finite-variable Diophantine data for a set of
`m`-tuples.  Unlike Mathlib's proposition `Dioph`, both the number of
witness variables and the polynomial are concrete finite data.

For a *uniform effective* MRDP result, one still has to give a computable
map from the chosen source-program code to the first two fields of this
structure and prove `represents` uniformly.  A theorem merely asserting
that this structure is inhabited for each recursively enumerable set does
not by itself provide the many-one reduction needed for undecidability. -/
structure FiniteDiophantineRepresentation
    (m : ℕ) (set : Set (Fin m → ℕ)) where
  witnessCount : ℕ
  polynomial : IntegerPolynomialCode (m + witnessCount)
  represents :
    ∀ parameters, parameters ∈ set ↔
      ∃ witnesses : Fin witnessCount → ℕ,
        IntegerPolynomialCode.eval polynomial
          (Fin.addCases parameters witnesses) = 0

namespace FiniteDiophantineRepresentation

variable {m : ℕ} {set : Set (Fin m → ℕ)}

/-- The representation directly yields the expected zero-solvability
equivalence. -/
theorem mem_iff_exists_zero
    (representation : FiniteDiophantineRepresentation m set)
    (parameters : Fin m → ℕ) :
    parameters ∈ set ↔
      ∃ witnesses : Fin representation.witnessCount → ℕ,
        IntegerPolynomialCode.eval representation.polynomial
          (Fin.addCases parameters witnesses) = 0 :=
  representation.represents parameters

/-- A finite-variable Mathlib polynomial and its semantic correctness
statement determine explicit finite Diophantine data, with a deliberately
noncomputable choice of sparse representation. -/
noncomputable def ofMathlibPoly (k : ℕ)
    (p : Poly (Fin m ⊕ Fin k))
    (correct :
      ∀ parameters, parameters ∈ set ↔
        ∃ witnesses : Fin k → ℕ,
          p (Sum.elim parameters witnesses) = 0) :
    FiniteDiophantineRepresentation m set where
  witnessCount := k
  polynomial := splitIntegerPolynomialCodeOfMathlibPoly p
  represents parameters :=
    (correct parameters).trans
      (exists_witness_zero_iff_splitIntegerPolynomialCodeOfMathlibPoly
        p parameters)

end FiniteDiophantineRepresentation

end HGAS
