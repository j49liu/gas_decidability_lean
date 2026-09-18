import HGAS.Arithmetic.MathlibDiophBridge
import Mathlib.Computability.Reduce
import Mathlib.Tactic

/-!
# An executable universal-halting trace and the effective MRDP boundary

This file uses Mathlib's `Nat.Partrec.Code` as a concrete universal
programming language.  A natural input encodes a pair `(program,input)`.
The bounded interpreter `Nat.Partrec.Code.evaln` is then used as a literal,
terminating trace checker.

The following parts are complete and executable:

* `DiophantineArithmeticExpression` is arithmetic syntax including
  variable exponentiation.  Its graph is proved Diophantine using
  `Dioph.pow_dioph`.
* `UniversalHalting.boundedHalts` is a Boolean bounded evaluator, and
  `boundedTrace_primrecRel` proves that its propositional relation is
  primitive recursive.
* `UniversalHalting.predicate_iff_exists_bound` identifies unbounded
  halting with the existence of a successful finite bound.
* `UniversalHalting.re_manyOneReducible_predicate` proves that this unary
  natural-number predicate is recursively-enumerable complete under
  computable many-one reductions.
* `BoundedTracePolynomialCertificate.toUniversalHaltingRepresentation`
  is the exact, choice-free last compiler step: any explicit polynomial
  representation of the bounded trace relation becomes a
  `FiniteDiophantineRepresentation` of universal halting.

The file intentionally does **not** manufacture the missing
`BoundedTracePolynomialCertificate`.  Mathlib proves that exponentiation
is Diophantine, but currently has no theorem turning an arbitrary
primitive-recursive derivation (such as `primrec_evaln`) into finite
polynomial syntax.  Doing so requires the remaining sequence-coding and
bounded-universal-quantifier part of effective MRDP.  Keeping this as a
data structure, instead of an assumption or opaque proposition, records
exactly what that future construction must compute.
-/

namespace HGAS

open Encodable Denumerable
open Part

/-! ## Executable positive arithmetic syntax with exponentiation -/

/-- Arithmetic expressions whose Mathlib graphs are Diophantine using its
closure library and `Dioph.pow_dioph`. -/
inductive DiophantineArithmeticExpression (n : ℕ) where
  | projection (i : Fin n)
  | constant (value : ℕ)
  | add (left right : DiophantineArithmeticExpression n)
  | mul (left right : DiophantineArithmeticExpression n)
  | sub (left right : DiophantineArithmeticExpression n)
  | mod (left right : DiophantineArithmeticExpression n)
  | div (left right : DiophantineArithmeticExpression n)
  | pow (base exponent : DiophantineArithmeticExpression n)
deriving DecidableEq, Repr

namespace DiophantineArithmeticExpression

variable {n : ℕ}

/-- Executable evaluation of a positive Diophantine arithmetic
expression.  Subtraction is truncated natural subtraction. -/
def eval (input : Fin n → ℕ) :
    DiophantineArithmeticExpression n → ℕ
  | .projection i => input i
  | .constant value => value
  | .add lhs rhs =>
      DiophantineArithmeticExpression.eval input lhs +
        DiophantineArithmeticExpression.eval input rhs
  | .mul lhs rhs =>
      DiophantineArithmeticExpression.eval input lhs *
        DiophantineArithmeticExpression.eval input rhs
  | .sub lhs rhs =>
      DiophantineArithmeticExpression.eval input lhs -
        DiophantineArithmeticExpression.eval input rhs
  | .mod lhs rhs =>
      DiophantineArithmeticExpression.eval input lhs %
        DiophantineArithmeticExpression.eval input rhs
  | .div lhs rhs =>
      DiophantineArithmeticExpression.eval input lhs /
        DiophantineArithmeticExpression.eval input rhs
  | .pow base exponent =>
      DiophantineArithmeticExpression.eval input base ^
        DiophantineArithmeticExpression.eval input exponent

/-- Every expression in the explicit syntax has a Diophantine graph.
The power case is exactly the deep theorem `Dioph.pow_dioph`. -/
theorem eval_diophFn (expression : DiophantineArithmeticExpression n) :
    Dioph.DiophFn fun input => expression.eval input := by
  induction expression with
  | projection i =>
      simpa [eval] using Dioph.proj_dioph i
  | constant value =>
      simpa [eval] using
        (Dioph.const_dioph (α := Fin n) value)
  | add left right ihLeft ihRight =>
      simpa [eval] using Dioph.add_dioph ihLeft ihRight
  | mul left right ihLeft ihRight =>
      simpa [eval] using Dioph.mul_dioph ihLeft ihRight
  | sub left right ihLeft ihRight =>
      simpa [eval] using Dioph.sub_dioph ihLeft ihRight
  | mod left right ihLeft ihRight =>
      simpa [eval] using Dioph.mod_dioph ihLeft ihRight
  | div left right ihLeft ihRight =>
      simpa [eval] using Dioph.div_dioph ihLeft ihRight
  | pow base exponent ihBase ihExponent =>
      simpa [eval] using Dioph.pow_dioph ihBase ihExponent

end DiophantineArithmeticExpression

/-- Positive formulas formed from Diophantine-function comparisons,
conjunction, and disjunction. -/
inductive PositiveDiophantineFormula (n : ℕ) where
  | eq (left right : DiophantineArithmeticExpression n)
  | le (left right : DiophantineArithmeticExpression n)
  | lt (left right : DiophantineArithmeticExpression n)
  | dvd (left right : DiophantineArithmeticExpression n)
  | and (left right : PositiveDiophantineFormula n)
  | or (left right : PositiveDiophantineFormula n)
deriving DecidableEq, Repr

namespace PositiveDiophantineFormula

variable {n : ℕ}

/-- Executable semantics of a positive formula. -/
def Holds (input : Fin n → ℕ) :
    PositiveDiophantineFormula n → Prop
  | .eq lhs rhs => lhs.eval input = rhs.eval input
  | .le lhs rhs => lhs.eval input ≤ rhs.eval input
  | .lt lhs rhs => lhs.eval input < rhs.eval input
  | .dvd lhs rhs => lhs.eval input ∣ rhs.eval input
  | .and lhs rhs => lhs.Holds input ∧ rhs.Holds input
  | .or lhs rhs => lhs.Holds input ∨ rhs.Holds input

/-- Executable Boolean checker for a positive formula. -/
def holdsBool (input : Fin n → ℕ) :
    PositiveDiophantineFormula n → Bool
  | .eq lhs rhs => lhs.eval input == rhs.eval input
  | .le lhs rhs => decide (lhs.eval input ≤ rhs.eval input)
  | .lt lhs rhs => decide (lhs.eval input < rhs.eval input)
  | .dvd lhs rhs => decide (lhs.eval input ∣ rhs.eval input)
  | .and lhs rhs => holdsBool input lhs && holdsBool input rhs
  | .or lhs rhs => holdsBool input lhs || holdsBool input rhs

/-- The Boolean checker agrees with the propositional semantics. -/
@[simp]
theorem holdsBool_eq_true_iff (formula : PositiveDiophantineFormula n)
    (input : Fin n → ℕ) :
    formula.holdsBool input = true ↔ formula.Holds input := by
  induction formula with
  | eq left right =>
      simp [holdsBool, Holds]
  | le left right =>
      simp [holdsBool, Holds]
  | lt left right =>
      simp [holdsBool, Holds]
  | dvd left right =>
      simp [holdsBool, Holds]
  | and left right ihLeft ihRight =>
      simp [holdsBool, Holds, ihLeft, ihRight]
  | or left right ihLeft ihRight =>
      simp [holdsBool, Holds, ihLeft, ihRight]

/-- Every positive formula denotes a Mathlib Diophantine set. -/
theorem holds_dioph (formula : PositiveDiophantineFormula n) :
    Dioph {input | formula.Holds input} := by
  induction formula with
  | eq left right =>
      simpa [Holds] using
        Dioph.eq_dioph left.eval_diophFn right.eval_diophFn
  | le left right =>
      simpa [Holds] using
        Dioph.le_dioph left.eval_diophFn right.eval_diophFn
  | lt left right =>
      simpa [Holds] using
        Dioph.lt_dioph left.eval_diophFn right.eval_diophFn
  | dvd left right =>
      simpa [Holds] using
        Dioph.dvd_dioph left.eval_diophFn right.eval_diophFn
  | and left right ihLeft ihRight =>
      simpa [Holds, Set.inter_def] using Dioph.inter ihLeft ihRight
  | or left right ihLeft ihRight =>
      simpa [Holds, Set.union_def] using Dioph.union ihLeft ihRight

end PositiveDiophantineFormula

namespace UniversalHalting

open Nat.Partrec (Code)
open Nat.Partrec.Code

/-! ## The Matiyasevic ingredient already present in Mathlib -/

/-- Mathlib proves that variable-base, variable-exponent natural
exponentiation has a Diophantine graph. -/
theorem naturalPow_diophFn :
    Dioph.DiophFn fun v : Fin 2 → ℕ =>
      v 0 ^ v 1 :=
  Dioph.pow_dioph (Dioph.proj_dioph (0 : Fin 2))
    (Dioph.proj_dioph (1 : Fin 2))

/-- Decode the program component of a paired natural input. -/
def program (input : ℕ) : Code :=
  ofNat Code input.unpair.1

/-- Decode the data component of a paired natural input. -/
def data (input : ℕ) : ℕ :=
  input.unpair.2

/-- Canonically encode one universal-machine instance. -/
def encodeInstance (program : Code) (input : ℕ) : ℕ :=
  Nat.pair (encode program) input

@[simp]
theorem program_encodeInstance (source : Code) (input : ℕ) :
    program (encodeInstance source input) = source := by
  simp [program, encodeInstance]

@[simp]
theorem data_encodeInstance (source : Code) (input : ℕ) :
    data (encodeInstance source input) = input := by
  simp [data, encodeInstance]

/-- Instance encoding is primitive recursive in both arguments. -/
theorem encodeInstance_primrec₂ : Primrec₂ encodeInstance :=
  Primrec₂.natPair.comp₂
    (Primrec.encode.comp₂ Primrec₂.left) Primrec₂.right

/-- Universal partial evaluation on the paired input `(program,data)`. -/
def partialEval (input : ℕ) : Part ℕ :=
  eval (program input) (data input)

/-- The unary universal halting predicate on natural-number codes. -/
def Predicate (input : ℕ) : Prop :=
  (partialEval input).Dom

/-- The bounded evaluator is an executable finite computation trace
checker. -/
def boundedEval (input bound : ℕ) : Option ℕ :=
  evaln bound (program input) (data input)

/-- Boolean bounded-halting checker. -/
def boundedHalts (input bound : ℕ) : Bool :=
  (boundedEval input bound).isSome

/-- Propositional form of the finite trace checker. -/
def BoundedTrace (input bound : ℕ) : Prop :=
  boundedHalts input bound = true

instance boundedTraceDecidable (input bound : ℕ) :
    Decidable (BoundedTrace input bound) :=
  by
    unfold BoundedTrace
    infer_instance

theorem program_primrec : Primrec program := by
  exact (Primrec.ofNat Code).comp
    (Primrec.fst.comp Primrec.unpair)

theorem data_primrec : Primrec data :=
  Primrec.snd.comp Primrec.unpair

theorem boundedEval_primrec :
    Primrec fun pair : ℕ × ℕ => boundedEval pair.1 pair.2 := by
  exact primrec_evaln.comp
    ((Primrec.snd.pair (program_primrec.comp Primrec.fst)).pair
      (data_primrec.comp Primrec.fst))

theorem boundedHalts_primrec :
    Primrec fun pair : ℕ × ℕ => boundedHalts pair.1 pair.2 :=
  Primrec.option_isSome.comp boundedEval_primrec

theorem boundedHalts_primrec₂ : Primrec₂ boundedHalts :=
  boundedHalts_primrec

theorem boundedTrace_primrecRel : PrimrecRel BoundedTrace := by
  refine ⟨inferInstance, ?_⟩
  simpa [BoundedTrace] using boundedHalts_primrec

theorem boundedHalts_eq_true_iff (input bound : ℕ) :
    boundedHalts input bound = true ↔
      ∃ output, output ∈ boundedEval input bound := by
  simpa [boundedHalts, Option.mem_def] using
    (Option.isSome_iff_exists (x := boundedEval input bound))

/-- Increasing the resource bound preserves a successful finite trace. -/
theorem boundedTrace_mono {input smaller larger : ℕ}
    (hbound : smaller ≤ larger) :
    BoundedTrace input smaller → BoundedTrace input larger := by
  intro htrace
  obtain ⟨output, houtput⟩ :=
    (boundedHalts_eq_true_iff input smaller).1 htrace
  apply (boundedHalts_eq_true_iff input larger).2
  exact ⟨output, evaln_mono hbound houtput⟩

theorem predicate_iff_exists_bound (input : ℕ) :
    Predicate input ↔ ∃ bound, BoundedTrace input bound := by
  rw [Predicate, partialEval, Part.dom_iff_mem]
  constructor
  · rintro ⟨output, houtput⟩
    rw [evaln_complete] at houtput
    obtain ⟨bound, hbound⟩ := houtput
    exact ⟨bound, (boundedHalts_eq_true_iff input bound).2
      ⟨output, hbound⟩⟩
  · rintro ⟨bound, hbound⟩
    obtain ⟨output, houtput⟩ :=
      (boundedHalts_eq_true_iff input bound).1 hbound
    exact ⟨output, evaln_sound houtput⟩

/-- Every successful bounded trace is sound for unbounded evaluation. -/
theorem boundedTrace_sound {input bound : ℕ}
    (htrace : BoundedTrace input bound) :
    Predicate input :=
  (predicate_iff_exists_bound input).2 ⟨bound, htrace⟩

theorem partialEval_partrec : Partrec partialEval :=
  eval_part.comp program_primrec.to_comp data_primrec.to_comp

theorem predicate_re : REPred Predicate :=
  partialEval_partrec.dom_re

/-- Every recursively enumerable predicate many-one reduces to the unary
universal halting predicate. -/
theorem re_manyOneReducible_predicate {α : Type*} [Primcodable α]
    {p : α → Prop} (hp : REPred p) :
    p ≤₀ Predicate := by
  unfold REPred Partrec at hp
  obtain ⟨code, hcode⟩ := exists_code.mp hp
  let reduction (a : α) : ℕ := encodeInstance code (encode a)
  refine ⟨reduction, ?_, ?_⟩
  · exact (encodeInstance_primrec₂.comp
      (Primrec.const code) Primrec.encode).to_comp
  · intro a
    change p a ↔ (partialEval (reduction a)).Dom
    rw [show partialEval (reduction a) =
        Part.bind (decode (α := α) (encode a))
          (fun a => (Part.assert (p a) fun _ => Part.some ()).map encode) by
      simp only [reduction, partialEval, program_encodeInstance,
        data_encodeInstance]
      rw [hcode]]
    simp only [Encodable.encodek, Part.coe_some, Part.bind_some]
    change p a ↔ ∃ _ : p a, True
    simp

/-- Standard natural-number formulation of recursive-enumerability
completeness. -/
theorem predicate_re_complete :
    REPred Predicate ∧
      ∀ {p : ℕ → Prop}, REPred p → p ≤₀ Predicate :=
  ⟨predicate_re, fun hp => re_manyOneReducible_predicate hp⟩

/-- The universal predicate is not computable. -/
theorem predicate_not_computable : ¬ComputablePred Predicate := by
  intro h
  have reduction :=
    re_manyOneReducible_predicate (ComputablePred.halting_problem_re 0)
  exact ComputablePred.halting_problem 0
    (ComputablePred.computable_of_manyOneReducible reduction h)

/-- Unary-vector form expected by `FiniteDiophantineRepresentation`. -/
def UnarySet : Set (Fin 1 → ℕ) :=
  {parameters | Predicate (parameters 0)}

/-- Package one natural number as a one-coordinate vector. -/
def unaryVector (input : ℕ) : Fin 1 → ℕ :=
  fun _ => input

/-- Read the unique coordinate of a unary vector. -/
def unaryValue (parameters : Fin 1 → ℕ) : ℕ :=
  parameters 0

@[simp]
theorem unaryValue_unaryVector (input : ℕ) :
    unaryValue (unaryVector input) = input :=
  rfl

theorem unaryVector_primrec : Primrec unaryVector := by
  change Primrec (fun input : ℕ => fun _ : Fin 1 => input)
  rw [Primrec.fin_curry]
  exact Primrec.fst

theorem unaryValue_primrec : Primrec unaryValue :=
  Primrec.fin_app.comp Primrec.id (Primrec.const 0)

/-- Natural and one-coordinate presentations of universal halting have
the same computable many-one degree. -/
theorem predicate_manyOneEquiv_unarySet :
    ManyOneEquiv Predicate (fun parameters => parameters ∈ UnarySet) := by
  constructor
  · exact ⟨unaryVector, unaryVector_primrec.to_comp, fun _ => Iff.rfl⟩
  · exact ⟨unaryValue, unaryValue_primrec.to_comp, fun _ => Iff.rfl⟩

/-- The one-coordinate presentation is itself recursively enumerable. -/
theorem unarySet_re :
    REPred (fun parameters => parameters ∈ UnarySet) :=
  (partialEval_partrec.comp unaryValue_primrec.to_comp).dom_re

/-- Every recursively enumerable predicate reduces to the one-coordinate
presentation used by the polynomial interface. -/
theorem re_manyOneReducible_unarySet {α : Type*} [Primcodable α]
    {p : α → Prop} (hp : REPred p) :
    p ≤₀ (fun parameters => parameters ∈ UnarySet) :=
  (re_manyOneReducible_predicate hp).trans
    predicate_manyOneEquiv_unarySet.1

/-- The one-coordinate universal set is not computable. -/
theorem unarySet_not_computable :
    ¬ComputablePred (fun parameters => parameters ∈ UnarySet) := by
  intro h
  exact predicate_not_computable
    (ComputablePred.computable_of_manyOneReducible
      predicate_manyOneEquiv_unarySet.1 h)

/-- Assignment layout used by a finite polynomial certificate for the
bounded trace predicate: input, bound, then auxiliary variables. -/
def traceAssignment {auxiliaryCount : ℕ}
    (input bound : ℕ) (auxiliary : Fin auxiliaryCount → ℕ) :
    Fin (1 + (1 + auxiliaryCount)) → ℕ :=
  Fin.addCases (fun _ => input)
    (Fin.addCases (fun _ => bound) auxiliary)

/-- Exact missing certificate at the effective MRDP boundary. -/
structure BoundedTracePolynomialCertificate where
  auxiliaryCount : ℕ
  polynomial :
    IntegerPolynomialCode (1 + (1 + auxiliaryCount))
  represents :
    ∀ input bound,
      BoundedTrace input bound ↔
        ∃ auxiliary : Fin auxiliaryCount → ℕ,
          IntegerPolynomialCode.eval polynomial
            (traceAssignment input bound auxiliary) = 0

namespace BoundedTracePolynomialCertificate

/-- A polynomial certificate for the decidable bounded evaluator yields,
without any further choice, a finite polynomial representation of the
unbounded universal halting set.  The computation bound becomes the first
existential witness. -/
def toUniversalHaltingRepresentation
    (certificate : BoundedTracePolynomialCertificate) :
    FiniteDiophantineRepresentation 1 UnarySet where
  witnessCount := 1 + certificate.auxiliaryCount
  polynomial := certificate.polynomial
  represents parameters := by
    change Predicate (parameters 0) ↔
      ∃ witnesses : Fin (1 + certificate.auxiliaryCount) → ℕ,
        IntegerPolynomialCode.eval certificate.polynomial
          (Fin.addCases parameters witnesses) = 0
    constructor
    · intro hhalts
      obtain ⟨bound, hbound⟩ :=
        (predicate_iff_exists_bound (parameters 0)).1 hhalts
      obtain ⟨auxiliary, hauxiliary⟩ :=
        (certificate.represents (parameters 0) bound).1 hbound
      let witnesses : Fin (1 + certificate.auxiliaryCount) → ℕ :=
        Fin.addCases (fun _ => bound) auxiliary
      refine ⟨witnesses, ?_⟩
      have hparameters : parameters = fun _ => parameters 0 := by
        funext i
        fin_cases i
        rfl
      rw [hparameters]
      exact hauxiliary
    · rintro ⟨witnesses, hwitnesses⟩
      let bound : ℕ :=
        witnesses (Fin.castAdd certificate.auxiliaryCount 0)
      let auxiliary : Fin certificate.auxiliaryCount → ℕ :=
        fun i => witnesses (Fin.natAdd 1 i)
      have hwitnesses_split :
          witnesses = Fin.addCases (fun _ => bound) auxiliary := by
        funext i
        induction i using Fin.addCases with
        | left i =>
            fin_cases i
            simp [bound]
        | right i =>
            simp [auxiliary]
      apply (predicate_iff_exists_bound (parameters 0)).2
      refine ⟨bound,
        (certificate.represents (parameters 0) bound).2
          ⟨auxiliary, ?_⟩⟩
      have hparameters : parameters = fun _ => parameters 0 := by
        funext i
        fin_cases i
        rfl
      rw [hparameters, hwitnesses_split] at hwitnesses
      exact hwitnesses

/-- Consequently, the parameterized natural-zero problem for the
certificate polynomial cannot be computable. -/
theorem representedSolvability_not_computable
    (certificate : BoundedTracePolynomialCertificate) :
    ¬ComputablePred
      (fun parameters : Fin 1 → ℕ =>
        ∃ witnesses : Fin (1 + certificate.auxiliaryCount) → ℕ,
          IntegerPolynomialCode.eval certificate.polynomial
            (Fin.addCases parameters witnesses) = 0) := by
  intro hcomputable
  apply unarySet_not_computable
  exact ComputablePred.of_eq hcomputable fun parameters =>
    (certificate.toUniversalHaltingRepresentation.represents
      parameters).symm

end BoundedTracePolynomialCertificate

end UniversalHalting

end HGAS
