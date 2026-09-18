import HGAS.Arithmetic.FourSquareAugmentation
import HGAS.Foundation.FinitePolynomialCode
import Mathlib.Computability.Partrec
import Mathlib.Computability.Primrec.List
import Mathlib.Tactic

/-!
# Sparse polynomial equations as arithmetic circuits

This file supplies the executable source-to-circuit part of the
Diophantine reduction.  It is deliberately split into three reusable
layers.

1. `NaturalArithmeticExpression` is a tiny expression language containing
   variables, zero, one, addition, and multiplication.
2. `ArithmeticGateCode` is a finite-register, natural-number code for the
   four gate relations used in `GateDQLCompiler`.
3. Sparse natural and integer polynomials are expanded into expressions by
   monomial powering.  An integer equation is represented as equality of
   its nonnegative and nonpositive parts, so no subtraction gate is needed.

The expression compiler allocates registers from left to right.  Every
generated instruction writes exactly one fresh register and reads only
older registers.  This simple invariant has two consequences: every input
assignment has a canonical extension satisfying the generated program, and
every satisfying register assignment gives the intended expression value.

The final theorem composes this compiler with
`GateDQLCompiler.compileNaturalCircuit`.  Thus its statement concerns a
literal diagonal--quadratic--linear system, not merely an informal circuit.
-/

namespace HGAS

/-! ## Sparse natural and integer polynomial syntax -/

/-- A sparse polynomial with natural coefficients.  Repeated monomials and
zero coefficients are allowed. -/
abbrev NaturalPolynomialCode (n : ℕ) :=
  List (ExponentCode n × ℕ)

/-- A sparse polynomial with signed integer coefficients. -/
abbrev IntegerPolynomialCode (n : ℕ) :=
  List (ExponentCode n × SignedMagnitudeCode)

namespace NaturalPolynomialCode

variable {n : ℕ}

/-- Evaluation of one monomial at a natural-number point. -/
def evalMonomial (e : ExponentCode n) (x : Fin n → ℕ) : ℕ :=
  (List.ofFn fun i ↦ x i ^ e i).prod

/-- Direct executable evaluation of a sparse natural polynomial. -/
def eval (p : NaturalPolynomialCode n) (x : Fin n → ℕ) : ℕ :=
  (p.map fun t ↦ t.2 * evalMonomial t.1 x).sum

@[simp]
theorem eval_nil (x : Fin n → ℕ) :
    eval ([] : NaturalPolynomialCode n) x = 0 := rfl

@[simp]
theorem eval_cons (t : ExponentCode n × ℕ)
    (p : NaturalPolynomialCode n) (x : Fin n → ℕ) :
    eval (t :: p) x = t.2 * evalMonomial t.1 x + eval p x := rfl

end NaturalPolynomialCode

namespace IntegerPolynomialCode

variable {n : ℕ}

/-- Direct executable evaluation of a sparse integer polynomial at a
natural-number point. -/
def eval (p : IntegerPolynomialCode n) (x : Fin n → ℕ) : ℤ :=
  (p.map fun t ↦
    SignedMagnitudeCode.decode t.2 *
      (NaturalPolynomialCode.evalMonomial t.1 x : ℤ)).sum

/-- Terms with nonnegative sign, with negatively signed terms assigned
coefficient zero. -/
def positivePart (p : IntegerPolynomialCode n) :
    NaturalPolynomialCode n :=
  p.map fun t ↦ (t.1, if t.2.1 then 0 else t.2.2)

/-- Absolute values of negatively signed terms, with nonnegative terms
assigned coefficient zero. -/
def negativePart (p : IntegerPolynomialCode n) :
    NaturalPolynomialCode n :=
  p.map fun t ↦ (t.1, if t.2.1 then t.2.2 else 0)

@[simp]
theorem eval_nil (x : Fin n → ℕ) :
    eval ([] : IntegerPolynomialCode n) x = 0 := rfl

@[simp]
theorem eval_cons (t : ExponentCode n × SignedMagnitudeCode)
    (p : IntegerPolynomialCode n) (x : Fin n → ℕ) :
    eval (t :: p) x =
      SignedMagnitudeCode.decode t.2 *
        (NaturalPolynomialCode.evalMonomial t.1 x : ℤ) +
      eval p x := rfl

/-- Splitting coefficients by sign is arithmetically exact. -/
theorem positivePart_sub_negativePart (p : IntegerPolynomialCode n)
    (x : Fin n → ℕ) :
    (NaturalPolynomialCode.eval (positivePart p) x : ℤ) -
        NaturalPolynomialCode.eval (negativePart p) x =
      eval p x := by
  induction p with
  | nil =>
      simp [positivePart, negativePart]
  | cons t p ih =>
      rcases t with ⟨e, ⟨sign, magnitude⟩⟩
      cases sign <;>
        simp only [positivePart, negativePart, List.map_cons,
          NaturalPolynomialCode.eval_cons, eval_cons,
          SignedMagnitudeCode.decode, Bool.false_eq_true,
          ↓reduceIte] at ih ⊢ <;>
        push_cast at ih ⊢ <;>
        linear_combination ih

/-- An integer polynomial vanishes exactly when its positive and negative
natural parts agree. -/
theorem positivePart_eq_negativePart_iff
    (p : IntegerPolynomialCode n) (x : Fin n → ℕ) :
    NaturalPolynomialCode.eval (positivePart p) x =
        NaturalPolynomialCode.eval (negativePart p) x ↔
      eval p x = 0 := by
  have hsplit := positivePart_sub_negativePart p x
  omega

end IntegerPolynomialCode

/-! ## A reusable natural arithmetic expression language -/

/-- Expressions computed by the four arithmetic gates. -/
inductive NaturalArithmeticExpression (n : ℕ) where
  | input (i : Fin n)
  | zero
  | one
  | add (left right : NaturalArithmeticExpression n)
  | mul (left right : NaturalArithmeticExpression n)
deriving DecidableEq, Repr

namespace NaturalArithmeticExpression

variable {n : ℕ}

/-- Evaluate an arithmetic expression over the natural numbers. -/
def eval (x : Fin n → ℕ) : NaturalArithmeticExpression n → ℕ
  | .input i => x i
  | .zero => 0
  | .one => 1
  | .add left right => eval x left + eval x right
  | .mul left right => eval x left * eval x right

/-- A natural-number literal, built in unary from zero, one, and addition.
The representation is intentionally elementary; later optimizations can
replace it by binary expansion without changing the compiler interface. -/
def numeral : ℕ → NaturalArithmeticExpression n
  | 0 => .zero
  | k + 1 => .add (numeral k) .one

@[simp]
theorem eval_numeral (x : Fin n → ℕ) (k : ℕ) :
    eval x (numeral k) = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp [numeral, eval, ih]

/-- Monomial powering in the expression language. -/
def power (base : NaturalArithmeticExpression n) :
    ℕ → NaturalArithmeticExpression n
  | 0 => .one
  | k + 1 => .mul (power base k) base

@[simp]
theorem eval_power (x : Fin n → ℕ)
    (base : NaturalArithmeticExpression n) (k : ℕ) :
    eval x (power base k) = eval x base ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp [power, eval, ih, pow_succ]

/-- Turn an exponent vector into the product of the corresponding powers
of the input variables. -/
def monomial (e : ExponentCode n) : NaturalArithmeticExpression n :=
  (List.ofFn fun i ↦ power (.input i) (e i)).foldr .mul .one

private theorem eval_foldr_mul (x : Fin n → ℕ)
    (expressions : List (NaturalArithmeticExpression n)) :
    eval x (expressions.foldr .mul .one) =
      (expressions.map (eval x)).prod := by
  induction expressions with
  | nil => rfl
  | cons expression expressions ih =>
      simp [eval, ih]

@[simp]
theorem eval_monomial (x : Fin n → ℕ) (e : ExponentCode n) :
    eval x (monomial e) = NaturalPolynomialCode.evalMonomial e x := by
  rw [monomial, eval_foldr_mul]
  unfold NaturalPolynomialCode.evalMonomial
  rw [← List.ofFn_comp']
  congr 1
  apply congrArg List.ofFn
  funext i
  simp [eval]

/-- Expand a sparse natural polynomial into additions of powered
monomials. -/
def ofPolynomial (p : NaturalPolynomialCode n) :
    NaturalArithmeticExpression n :=
  p.foldr
    (fun t acc ↦ .add (.mul (numeral t.2) (monomial t.1)) acc)
    .zero

@[simp]
theorem eval_ofPolynomial (x : Fin n → ℕ)
    (p : NaturalPolynomialCode n) :
    eval x (ofPolynomial p) = NaturalPolynomialCode.eval p x := by
  induction p with
  | nil => rfl
  | cons t p ih =>
      change
        eval x
            (.add (.mul (numeral t.2) (monomial t.1))
              (ofPolynomial p)) =
          t.2 * NaturalPolynomialCode.evalMonomial t.1 x +
            NaturalPolynomialCode.eval p x
      simp [eval, ih]

/-- Left-associated monomial expansion.  This has the same value as
`monomial`, but is convenient for a tail-recursive circuit builder. -/
def monomialForward (e : ExponentCode n) :
    NaturalArithmeticExpression n :=
  (List.ofFn fun i ↦ power (.input i) (e i)).foldl .mul .one

private theorem eval_foldl_mul (x : Fin n → ℕ)
    (expressions : List (NaturalArithmeticExpression n))
    (accumulator : NaturalArithmeticExpression n) :
    eval x (expressions.foldl .mul accumulator) =
      eval x accumulator * (expressions.map (eval x)).prod := by
  induction expressions generalizing accumulator with
  | nil =>
      simp
  | cons expression expressions ih =>
      rw [List.foldl_cons, ih]
      simp [eval, Nat.mul_assoc]

@[simp]
theorem eval_monomialForward (x : Fin n → ℕ) (e : ExponentCode n) :
    eval x (monomialForward e) =
      NaturalPolynomialCode.evalMonomial e x := by
  rw [monomialForward, eval_foldl_mul]
  simp only [eval]
  rw [one_mul]
  unfold NaturalPolynomialCode.evalMonomial
  rw [← List.ofFn_comp']
  congr 1
  apply congrArg List.ofFn
  funext i
  simp [eval]

/-- Left-associated sparse-polynomial expansion used by the effective
compiler. -/
def ofPolynomialForward (p : NaturalPolynomialCode n) :
    NaturalArithmeticExpression n :=
  p.foldl
    (fun acc t ↦ .add acc (.mul (numeral t.2) (monomialForward t.1)))
    .zero

private theorem eval_foldl_polynomial
    (x : Fin n → ℕ) (p : NaturalPolynomialCode n)
    (accumulator : NaturalArithmeticExpression n) :
    eval x
        (p.foldl
          (fun acc t ↦
            .add acc (.mul (numeral t.2) (monomialForward t.1)))
          accumulator) =
      eval x accumulator + NaturalPolynomialCode.eval p x := by
  induction p generalizing accumulator with
  | nil =>
      simp
  | cons t p ih =>
      rw [List.foldl_cons, ih]
      simp [eval, Nat.add_assoc]

@[simp]
theorem eval_ofPolynomialForward (x : Fin n → ℕ)
    (p : NaturalPolynomialCode n) :
    eval x (ofPolynomialForward p) =
      NaturalPolynomialCode.eval p x := by
  rw [ofPolynomialForward, eval_foldl_polynomial]
  simp [eval]

end NaturalArithmeticExpression

/-! ## Executable register-gate codes -/

/-- A primitive-codable raw arithmetic gate.

The fields are `(tag, x, y, z)`.  Tags `0`, `1`, `2`, and `3` denote,
respectively, `zero x`, `one x`, `add x y z`, and `mul x y z`.  Any
noncanonical tag is interpreted as multiplication, making decoding total.
-/
abbrev ArithmeticGateCode := ℕ × (ℕ × (ℕ × ℕ))

namespace ArithmeticGateCode

def tag (g : ArithmeticGateCode) : ℕ := g.1
def x (g : ArithmeticGateCode) : ℕ := g.2.1
def y (g : ArithmeticGateCode) : ℕ := g.2.2.1
def z (g : ArithmeticGateCode) : ℕ := g.2.2.2

def zero (out : ℕ) : ArithmeticGateCode := (0, out, 0, 0)
def one (out : ℕ) : ArithmeticGateCode := (1, out, 0, 0)
def add (left right out : ℕ) : ArithmeticGateCode :=
  (2, left, right, out)
def mul (left right out : ℕ) : ArithmeticGateCode :=
  (3, left, right, out)

/-- The register written by a gate. -/
def output (g : ArithmeticGateCode) : ℕ :=
  if tag g < 2 then x g else z g

/-- Natural-number semantics of a raw gate. -/
def Holds (g : ArithmeticGateCode) (value : ℕ → ℕ) : Prop :=
  match tag g with
  | 0 => value (x g) = 0
  | 1 => value (x g) = 1
  | 2 => value (x g) + value (y g) = value (z g)
  | _ => value (x g) * value (y g) = value (z g)

/-- A gate is ready at `next` when it writes register `next` and reads only
strictly older registers. -/
def ReadyAt (g : ArithmeticGateCode) (next : ℕ) : Prop :=
  output g = next ∧
    match tag g with
    | 0 => True
    | 1 => True
    | _ => x g < next ∧ y g < next

/-- Every register mentioned by the gate is below a common bound. -/
def BoundedBy (g : ArithmeticGateCode) (bound : ℕ) : Prop :=
  match tag g with
  | 0 => x g < bound
  | 1 => x g < bound
  | _ => x g < bound ∧ y g < bound ∧ z g < bound

/-- The value written by a gate when it is executed as an assignment. -/
def resultValue (g : ArithmeticGateCode) (value : ℕ → ℕ) : ℕ :=
  match tag g with
  | 0 => 0
  | 1 => 1
  | 2 => value (x g) + value (y g)
  | _ => value (x g) * value (y g)

/-- Execute one assignment gate by changing only its output register. -/
def execute (g : ArithmeticGateCode) (value : ℕ → ℕ) : ℕ → ℕ :=
  Function.update value (output g) (resultValue g value)

@[simp]
theorem output_zero (out : ℕ) : output (zero out) = out := by
  simp [output, zero, tag, x]

@[simp]
theorem output_one (out : ℕ) : output (one out) = out := by
  simp [output, one, tag, x]

@[simp]
theorem output_add (left right out : ℕ) :
    output (add left right out) = out := by
  simp [output, add, tag, z]

@[simp]
theorem output_mul (left right out : ℕ) :
    output (mul left right out) = out := by
  simp [output, mul, tag, z]

/-- Execution leaves every register strictly below the fresh output
unchanged. -/
theorem execute_eq_of_lt_output (g : ArithmeticGateCode)
    (value : ℕ → ℕ) {i : ℕ} (hi : i < output g) :
    execute g value i = value i := by
  simp [execute, Function.update, ne_of_lt hi]

/-- Executing a ready gate makes that gate true. -/
theorem holds_execute_of_readyAt (g : ArithmeticGateCode)
    (value : ℕ → ℕ) (next : ℕ) (hready : ReadyAt g next) :
    Holds g (execute g value) := by
  rcases hready with ⟨houtput, hreads⟩
  cases htag : tag g with
  | zero =>
      have hout' : output g = x g := by
        simp [output, htag]
      simp only [Holds, htag]
      change execute g value (x g) = 0
      rw [← hout']
      simp [execute, resultValue, htag]
  | succ k =>
      cases k with
      | zero =>
          have hout' : output g = x g := by
            simp [output, htag]
          simp only [Holds, htag]
          change execute g value (x g) = 1
          rw [← hout']
          simp [execute, resultValue, htag]
      | succ k =>
          have hreads' : x g < next ∧ y g < next := by
            simpa [htag] using hreads
          have hout : output g = z g := by
            simp [output, htag]
          cases k with
          | zero =>
              simp only [Holds, htag]
              change
                execute g value (x g) + execute g value (y g) =
                  execute g value (z g)
              rw [execute_eq_of_lt_output g value (by omega),
                execute_eq_of_lt_output g value (by omega), ← hout]
              simp [execute, resultValue, htag]
          | succ k =>
              simp only [Holds, htag]
              change
                execute g value (x g) * execute g value (y g) =
                  execute g value (z g)
              rw [execute_eq_of_lt_output g value (by omega),
                execute_eq_of_lt_output g value (by omega), ← hout]
              simp [execute, resultValue, htag]

/-- Readiness at `next` implies that all mentioned registers are below
`next + 1`. -/
theorem boundedBy_succ_of_readyAt (g : ArithmeticGateCode)
    (next : ℕ) (hready : ReadyAt g next) :
    BoundedBy g (next + 1) := by
  rcases hready with ⟨houtput, hreads⟩
  cases htag : tag g with
  | zero =>
      simp [BoundedBy, output, htag] at houtput ⊢
      omega
  | succ k =>
      cases k with
      | zero =>
          simp [BoundedBy, output, htag] at houtput ⊢
          omega
      | succ k =>
          have hreads' : x g < next ∧ y g < next := by
            simpa [htag] using hreads
          have hz : z g = next := by
            simpa [output, htag] using houtput
          cases k <;>
            simp only [BoundedBy, htag] <;>
            exact ⟨by omega, by omega, by omega⟩

/-- Increasing the register bound preserves boundedness. -/
theorem BoundedBy.mono (g : ArithmeticGateCode)
    {small large : ℕ} (hbound : BoundedBy g small)
    (hle : small ≤ large) :
    BoundedBy g large := by
  cases htag : tag g with
  | zero =>
      simpa [BoundedBy, htag] using
        (show x g < large from
          (show x g < small by
            simpa [BoundedBy, htag] using hbound).trans_le hle)
  | succ k =>
      cases k with
      | zero =>
          simpa [BoundedBy, htag] using
            (show x g < large from
              (show x g < small by
                simpa [BoundedBy, htag] using hbound).trans_le hle)
      | succ k =>
          have hparts : x g < small ∧ y g < small ∧ z g < small := by
            simpa [BoundedBy, htag] using hbound
          cases k <;>
            simp only [BoundedBy, htag] <;>
            exact ⟨hparts.1.trans_le hle,
              hparts.2.1.trans_le hle, hparts.2.2.trans_le hle⟩

/-- Gate truth depends only on the finitely many registers named by the
gate. -/
theorem holds_congr_of_boundedBy (g : ArithmeticGateCode)
    {bound : ℕ} (hbound : BoundedBy g bound)
    {left right : ℕ → ℕ}
    (hagrees : ∀ i, i < bound → left i = right i) :
    Holds g left ↔ Holds g right := by
  cases htag : tag g with
  | zero =>
      have hx : x g < bound := by
        simpa [BoundedBy, htag] using hbound
      simp [Holds, htag, hagrees (x g) hx]
  | succ k =>
      cases k with
      | zero =>
          have hx : x g < bound := by
            simpa [BoundedBy, htag] using hbound
          simp [Holds, htag, hagrees (x g) hx]
      | succ k =>
          have hparts : x g < bound ∧ y g < bound ∧ z g < bound := by
            simpa [BoundedBy, htag] using hbound
          cases k <;>
            simp [Holds, htag, hagrees (x g) hparts.1,
              hagrees (y g) hparts.2.1,
              hagrees (z g) hparts.2.2]

end ArithmeticGateCode

/-- Every gate in a raw circuit holds.  The membership formulation is
convenient for compositional compiler proofs. -/
def RawArithmeticCircuitHolds
    (gates : List ArithmeticGateCode) (value : ℕ → ℕ) : Prop :=
  ∀ g ∈ gates, ArithmeticGateCode.Holds g value

/-- A list of single-assignment gates occupying consecutive fresh
registers beginning at `start`. -/
def ForwardCircuitFrom : ℕ → List ArithmeticGateCode → Prop
  | _, [] => True
  | start, g :: gates =>
      ArithmeticGateCode.ReadyAt g start ∧
        ForwardCircuitFrom (start + 1) gates

@[simp]
theorem rawArithmeticCircuitHolds_nil (value : ℕ → ℕ) :
    RawArithmeticCircuitHolds [] value := by
  simp [RawArithmeticCircuitHolds]

@[simp]
theorem rawArithmeticCircuitHolds_cons
    (g : ArithmeticGateCode) (gates : List ArithmeticGateCode)
    (value : ℕ → ℕ) :
    RawArithmeticCircuitHolds (g :: gates) value ↔
      ArithmeticGateCode.Holds g value ∧
        RawArithmeticCircuitHolds gates value := by
  simp [RawArithmeticCircuitHolds]

@[simp]
theorem rawArithmeticCircuitHolds_append
    (left right : List ArithmeticGateCode) (value : ℕ → ℕ) :
    RawArithmeticCircuitHolds (left ++ right) value ↔
      RawArithmeticCircuitHolds left value ∧
        RawArithmeticCircuitHolds right value := by
  constructor
  · intro h
    constructor
    · intro g hg
      exact h g (List.mem_append_left right hg)
    · intro g hg
      exact h g (List.mem_append_right left hg)
  · rintro ⟨hleft, hright⟩ g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hleft g hg
    · exact hright g hg

/-- Forward circuits compose when the second fragment starts immediately
after the first. -/
theorem forwardCircuitFrom_append (start : ℕ)
    (left right : List ArithmeticGateCode) :
    ForwardCircuitFrom start (left ++ right) ↔
      ForwardCircuitFrom start left ∧
        ForwardCircuitFrom (start + left.length) right := by
  induction left generalizing start with
  | nil =>
      simp [ForwardCircuitFrom]
  | cons g left ih =>
      simp [ForwardCircuitFrom, ih, Nat.add_comm, Nat.add_left_comm,
        and_assoc]

/-- A forward circuit has a satisfying assignment extending any prescribed
values of the older registers. -/
theorem exists_rawArithmeticCircuitHolds_of_forward
    (gates : List ArithmeticGateCode) (start : ℕ)
    (base : ℕ → ℕ) (hforward : ForwardCircuitFrom start gates) :
    ∃ value : ℕ → ℕ,
      RawArithmeticCircuitHolds gates value ∧
        ∀ i, i < start → value i = base i := by
  induction gates generalizing start base with
  | nil =>
      exact ⟨base, rawArithmeticCircuitHolds_nil base, fun _ _ ↦ rfl⟩
  | cons g gates ih =>
      rcases hforward with ⟨hready, htail⟩
      let after := ArithmeticGateCode.execute g base
      obtain ⟨value, hvalue, hagrees⟩ :=
        ih (start + 1) after htail
      refine ⟨value, ?_, ?_⟩
      · rw [rawArithmeticCircuitHolds_cons]
        constructor
        · have hgateAfter :
              ArithmeticGateCode.Holds g after :=
            ArithmeticGateCode.holds_execute_of_readyAt
              g base start hready
          have hbound :
              ArithmeticGateCode.BoundedBy g (start + 1) :=
            ArithmeticGateCode.boundedBy_succ_of_readyAt
              g start hready
          exact
            (ArithmeticGateCode.holds_congr_of_boundedBy
              g hbound hagrees).mpr hgateAfter
        · exact hvalue
      · intro i hi
        calc
          value i = after i := hagrees i (by omega)
          _ = base i := by
            apply ArithmeticGateCode.execute_eq_of_lt_output
            rw [hready.1]
            exact hi

/-- Every gate in a forward circuit is bounded by the first unused
register after the whole circuit. -/
theorem forwardCircuitFrom_bounded
    (gates : List ArithmeticGateCode) (start : ℕ)
    (hforward : ForwardCircuitFrom start gates) :
    ∀ g ∈ gates,
      ArithmeticGateCode.BoundedBy g (start + gates.length) := by
  induction gates generalizing start with
  | nil =>
      simp
  | cons first gates ih =>
      rcases hforward with ⟨hfirst, htail⟩
      intro g hg
      rcases List.mem_cons.mp hg with hEq | hg
      · subst g
        have hbound :=
          ArithmeticGateCode.boundedBy_succ_of_readyAt
            first start hfirst
        have hmono : start + 1 ≤ start + (gates.length + 1) := by
          omega
        exact ArithmeticGateCode.BoundedBy.mono first hbound hmono
      · have htailBound := ih (start + 1) htail g hg
        simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using htailBound

/-! ## Realization as `ArithmeticGate` circuits -/

namespace ArithmeticGateCode

/-- Total conversion of a natural register number to a finite register.
The modulo is irrelevant for bounded codes, but makes the decoder total on
all raw data. -/
def finiteIndex (bound : ℕ) (hbound : 0 < bound) (i : ℕ) : Fin bound :=
  ⟨i % bound, Nat.mod_lt i hbound⟩

theorem finiteIndex_eq_of_lt (bound : ℕ) (hbound : 0 < bound)
    (i : ℕ) (hi : i < bound) :
    finiteIndex bound hbound i = ⟨i, hi⟩ := by
  apply Fin.ext
  simp [finiteIndex, Nat.mod_eq_of_lt hi]

/-- Decode a raw gate into the circuit syntax used by the DQL compiler. -/
def toArithmeticGate (bound : ℕ) (hbound : 0 < bound)
    (g : ArithmeticGateCode) : ArithmeticGate bound :=
  match tag g with
  | 0 => .zero (finiteIndex bound hbound (x g))
  | 1 => .one (finiteIndex bound hbound (x g))
  | 2 =>
      .add (finiteIndex bound hbound (x g))
        (finiteIndex bound hbound (y g))
        (finiteIndex bound hbound (z g))
  | _ =>
      .mul (finiteIndex bound hbound (x g))
        (finiteIndex bound hbound (y g))
        (finiteIndex bound hbound (z g))

/-- Extend a finite assignment to all natural register numbers.  Values
outside the finite register file are irrelevant and are set to zero. -/
def liftFiniteValue {bound : ℕ} (value : Fin bound → ℕ) : ℕ → ℕ :=
  fun i ↦ if hi : i < bound then value ⟨i, hi⟩ else 0

@[simp]
theorem liftFiniteValue_of_lt {bound : ℕ}
    (value : Fin bound → ℕ) {i : ℕ} (hi : i < bound) :
    liftFiniteValue value i = value ⟨i, hi⟩ := by
  simp [liftFiniteValue, hi]

/-- On a bounded raw gate, raw natural semantics and finite
`ArithmeticGate` semantics coincide exactly. -/
theorem toArithmeticGate_holds_iff
    {bound : ℕ} (hpositive : 0 < bound)
    (g : ArithmeticGateCode) (hbounded : BoundedBy g bound)
    (value : Fin bound → ℕ) :
    (toArithmeticGate bound hpositive g).Holds
        (fun i ↦ (value i : ℤ)) ↔
      Holds g (liftFiniteValue value) := by
  cases htag : tag g with
  | zero =>
      have hx : x g < bound := by
        simpa [BoundedBy, htag] using hbounded
      have hindex :=
        finiteIndex_eq_of_lt bound hpositive (x g) hx
      simp [toArithmeticGate, htag, ArithmeticGate.Holds, Holds,
        hindex, liftFiniteValue_of_lt value hx]
  | succ k =>
      cases k with
      | zero =>
          have hx : x g < bound := by
            simpa [BoundedBy, htag] using hbounded
          have hindex :=
            finiteIndex_eq_of_lt bound hpositive (x g) hx
          simp [toArithmeticGate, htag, ArithmeticGate.Holds, Holds,
            hindex, liftFiniteValue_of_lt value hx]
      | succ k =>
          have hparts : x g < bound ∧ y g < bound ∧ z g < bound := by
            simpa [BoundedBy, htag] using hbounded
          have hx :=
            finiteIndex_eq_of_lt bound hpositive (x g) hparts.1
          have hy :=
            finiteIndex_eq_of_lt bound hpositive (y g) hparts.2.1
          have hz :=
            finiteIndex_eq_of_lt bound hpositive (z g) hparts.2.2
          cases k <;>
            simp [toArithmeticGate, htag, ArithmeticGate.Holds, Holds,
              hx, hy, hz, liftFiniteValue_of_lt value hparts.1,
              liftFiniteValue_of_lt value hparts.2.1,
              liftFiniteValue_of_lt value hparts.2.2] <;>
            norm_cast

end ArithmeticGateCode

/-- Realize a list of raw gates in a finite register file. -/
def realizeArithmeticCircuit (bound : ℕ) (hbound : 0 < bound)
    (gates : List ArithmeticGateCode) :
    List (ArithmeticGate bound) :=
  gates.map (ArithmeticGateCode.toArithmeticGate bound hbound)

/-- Membership semantics and the index-based circuit semantics used by
`GateDQLCompiler` are equivalent. -/
theorem naturalCircuitHolds_iff_forall_mem
    {vars : ℕ} (gates : List (ArithmeticGate vars))
    (value : Fin vars → ℕ) :
    GateDQLCompiler.NaturalCircuitHolds gates value ↔
      ∀ g ∈ gates,
        g.Holds (fun i ↦ (value i : ℤ)) := by
  unfold GateDQLCompiler.NaturalCircuitHolds ArithmeticCircuitHolds
  let predicate : ArithmeticGate vars → Prop :=
    fun g ↦ g.Holds (fun i ↦ (value i : ℤ))
  change
    (∀ i : Fin gates.length, predicate (gates.get i)) ↔
      ∀ g ∈ gates, predicate g
  exact (@List.forall_mem_iff_get _ gates predicate).symm

/-- Correctness of finite realization for a list of bounded raw gates. -/
theorem naturalCircuitHolds_realize_iff
    {bound : ℕ} (hpositive : 0 < bound)
    (gates : List ArithmeticGateCode)
    (hbounded :
      ∀ g ∈ gates, ArithmeticGateCode.BoundedBy g bound)
    (value : Fin bound → ℕ) :
    GateDQLCompiler.NaturalCircuitHolds
        (realizeArithmeticCircuit bound hpositive gates) value ↔
      RawArithmeticCircuitHolds gates
        (ArithmeticGateCode.liftFiniteValue value) := by
  rw [naturalCircuitHolds_iff_forall_mem]
  unfold RawArithmeticCircuitHolds realizeArithmeticCircuit
  constructor
  · intro h g hg
    exact
      (ArithmeticGateCode.toArithmeticGate_holds_iff
        hpositive g (hbounded g hg) value).mp
          (h _ (List.mem_map.mpr ⟨g, hg, rfl⟩))
  · intro h gate hgate
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hgate
    exact
      (ArithmeticGateCode.toArithmeticGate_holds_iff
        hpositive g (hbounded g hg) value).mpr (h g hg)

/-! ## Compiling expressions to forward circuits -/

/-- A compiled expression fragment.  Its fresh-register interval starts at
an external parameter; `output` may also be one of the older input
registers when the expression is just a variable. -/
structure ArithmeticFragment where
  gates : List ArithmeticGateCode
  output : ℕ
deriving DecidableEq, Repr

namespace ArithmeticFragment

/-- The first unused register after a fragment. -/
def next (start : ℕ) (fragment : ArithmeticFragment) : ℕ :=
  start + fragment.gates.length

end ArithmeticFragment

namespace NaturalArithmeticExpression

/-- Compile an expression, allocating any new registers consecutively from
`start`.  Input variables retain register numbers `0, ..., n-1`. -/
def compileFrom (start : ℕ) :
    NaturalArithmeticExpression n → ArithmeticFragment
  | .input i => ⟨[], i.1⟩
  | .zero => ⟨[ArithmeticGateCode.zero start], start⟩
  | .one => ⟨[ArithmeticGateCode.one start], start⟩
  | .add left right =>
      let leftCode := compileFrom start left
      let rightStart := leftCode.next start
      let rightCode := compileFrom rightStart right
      let out := rightCode.next rightStart
      ⟨leftCode.gates ++ rightCode.gates ++
          [ArithmeticGateCode.add leftCode.output rightCode.output out],
        out⟩
  | .mul left right =>
      let leftCode := compileFrom start left
      let rightStart := leftCode.next start
      let rightCode := compileFrom rightStart right
      let out := rightCode.next rightStart
      ⟨leftCode.gates ++ rightCode.gates ++
          [ArithmeticGateCode.mul leftCode.output rightCode.output out],
        out⟩

/-- Every generated expression program is a forward circuit, and its
reported output is an existing register below the first unused register. -/
theorem compileFrom_forward (expression : NaturalArithmeticExpression n)
    (start : ℕ) (hinputs : n ≤ start) :
    ForwardCircuitFrom start (compileFrom start expression).gates ∧
      (compileFrom start expression).output <
        (compileFrom start expression).next start := by
  induction expression generalizing start with
  | input i =>
      constructor
      · simp [compileFrom, ForwardCircuitFrom]
      · simp only [compileFrom, ArithmeticFragment.next, List.length_nil,
          Nat.add_zero]
        exact lt_of_lt_of_le i.isLt hinputs
  | zero =>
      simp [compileFrom, ForwardCircuitFrom, ArithmeticGateCode.ReadyAt,
        ArithmeticGateCode.output, ArithmeticGateCode.zero,
        ArithmeticGateCode.tag, ArithmeticGateCode.x,
        ArithmeticFragment.next]
  | one =>
      simp [compileFrom, ForwardCircuitFrom, ArithmeticGateCode.ReadyAt,
        ArithmeticGateCode.output, ArithmeticGateCode.one,
        ArithmeticGateCode.tag, ArithmeticGateCode.x,
        ArithmeticFragment.next]
  | add left right leftIH rightIH =>
      let leftCode := compileFrom start left
      let rightStart := leftCode.next start
      let rightCode := compileFrom rightStart right
      let out := rightCode.next rightStart
      have hleft := leftIH start hinputs
      have hstart_le_rightStart : start ≤ rightStart := by
        simp [rightStart, ArithmeticFragment.next]
      have hright :=
        rightIH rightStart (hinputs.trans hstart_le_rightStart)
      change
        ForwardCircuitFrom start leftCode.gates ∧
          leftCode.output < leftCode.next start at hleft
      change
        ForwardCircuitFrom rightStart rightCode.gates ∧
          rightCode.output < rightCode.next rightStart at hright
      have hleftOut : leftCode.output < out := by
        exact hleft.2.trans_le (by
          simp [out, rightStart, ArithmeticFragment.next])
      have hrightOut : rightCode.output < out := hright.2
      change
        ForwardCircuitFrom start
            (leftCode.gates ++ rightCode.gates ++
              [ArithmeticGateCode.add
                leftCode.output rightCode.output out]) ∧
          out <
            start +
              (leftCode.gates ++ rightCode.gates ++
                [ArithmeticGateCode.add
                  leftCode.output rightCode.output out]).length
      constructor
      · rw [forwardCircuitFrom_append, forwardCircuitFrom_append]
        constructor
        · exact ⟨hleft.1, by
            simpa [rightStart, ArithmeticFragment.next] using hright.1⟩
        · have hprefix :
              start + (leftCode.gates ++ rightCode.gates).length =
                out := by
            simp [out, rightStart, ArithmeticFragment.next,
              Nat.add_assoc]
          rw [hprefix]
          simp [ForwardCircuitFrom, ArithmeticGateCode.ReadyAt,
            ArithmeticGateCode.add, ArithmeticGateCode.output,
            ArithmeticGateCode.tag, ArithmeticGateCode.x,
            ArithmeticGateCode.y, ArithmeticGateCode.z,
            hleftOut, hrightOut]
      · simp only [List.length_append, List.length_cons, List.length_nil]
        simp [out, rightStart, ArithmeticFragment.next]
        omega
  | mul left right leftIH rightIH =>
      let leftCode := compileFrom start left
      let rightStart := leftCode.next start
      let rightCode := compileFrom rightStart right
      let out := rightCode.next rightStart
      have hleft := leftIH start hinputs
      have hstart_le_rightStart : start ≤ rightStart := by
        simp [rightStart, ArithmeticFragment.next]
      have hright :=
        rightIH rightStart (hinputs.trans hstart_le_rightStart)
      change
        ForwardCircuitFrom start leftCode.gates ∧
          leftCode.output < leftCode.next start at hleft
      change
        ForwardCircuitFrom rightStart rightCode.gates ∧
          rightCode.output < rightCode.next rightStart at hright
      have hleftOut : leftCode.output < out := by
        exact hleft.2.trans_le (by
          simp [out, rightStart, ArithmeticFragment.next])
      have hrightOut : rightCode.output < out := hright.2
      change
        ForwardCircuitFrom start
            (leftCode.gates ++ rightCode.gates ++
              [ArithmeticGateCode.mul
                leftCode.output rightCode.output out]) ∧
          out <
            start +
              (leftCode.gates ++ rightCode.gates ++
                [ArithmeticGateCode.mul
                  leftCode.output rightCode.output out]).length
      constructor
      · rw [forwardCircuitFrom_append, forwardCircuitFrom_append]
        constructor
        · exact ⟨hleft.1, by
            simpa [rightStart, ArithmeticFragment.next] using hright.1⟩
        · have hprefix :
              start + (leftCode.gates ++ rightCode.gates).length =
                out := by
            simp [out, rightStart, ArithmeticFragment.next,
              Nat.add_assoc]
          rw [hprefix]
          simp [ForwardCircuitFrom, ArithmeticGateCode.ReadyAt,
            ArithmeticGateCode.mul, ArithmeticGateCode.output,
            ArithmeticGateCode.tag, ArithmeticGateCode.x,
            ArithmeticGateCode.y, ArithmeticGateCode.z,
            hleftOut, hrightOut]
      · simp only [List.length_append, List.length_cons, List.length_nil]
        simp [out, rightStart, ArithmeticFragment.next]
        omega

/-- Semantic soundness of the expression compiler: any assignment
satisfying its gates gives the exact value of the source expression in the
reported output register. -/
theorem compileFrom_output_eq_eval
    (expression : NaturalArithmeticExpression n) (start : ℕ)
    (value : ℕ → ℕ)
    (hvalue :
      RawArithmeticCircuitHolds
        (compileFrom start expression).gates value) :
    value (compileFrom start expression).output =
      eval (fun i ↦ value i.1) expression := by
  induction expression generalizing start with
  | input i =>
      rfl
  | zero =>
      exact hvalue (ArithmeticGateCode.zero start) (by simp [compileFrom])
  | one =>
      exact hvalue (ArithmeticGateCode.one start) (by simp [compileFrom])
  | add left right leftIH rightIH =>
      let leftCode := compileFrom start left
      let rightStart := leftCode.next start
      let rightCode := compileFrom rightStart right
      let out := rightCode.next rightStart
      change
        RawArithmeticCircuitHolds
          (leftCode.gates ++ rightCode.gates ++
            [ArithmeticGateCode.add
              leftCode.output rightCode.output out]) value at hvalue
      have hparts :=
        (rawArithmeticCircuitHolds_append
          (leftCode.gates ++ rightCode.gates)
          [ArithmeticGateCode.add
            leftCode.output rightCode.output out] value).mp hvalue
      have hprogram :=
        (rawArithmeticCircuitHolds_append
          leftCode.gates rightCode.gates value).mp hparts.1
      have hleft :
          RawArithmeticCircuitHolds leftCode.gates value :=
        hprogram.1
      have hright :
          RawArithmeticCircuitHolds rightCode.gates value :=
        hprogram.2
      have hgate :
          ArithmeticGateCode.Holds
            (ArithmeticGateCode.add
              leftCode.output rightCode.output out) value := by
        exact
          (rawArithmeticCircuitHolds_cons
            (ArithmeticGateCode.add
              leftCode.output rightCode.output out) [] value).mp
              hparts.2 |>.1
      change value out = eval (fun i ↦ value i.1) left +
        eval (fun i ↦ value i.1) right
      rw [← leftIH start hleft, ← rightIH rightStart hright]
      simpa [ArithmeticGateCode.Holds, ArithmeticGateCode.add,
        ArithmeticGateCode.tag, ArithmeticGateCode.x,
        ArithmeticGateCode.y, ArithmeticGateCode.z] using hgate.symm
  | mul left right leftIH rightIH =>
      let leftCode := compileFrom start left
      let rightStart := leftCode.next start
      let rightCode := compileFrom rightStart right
      let out := rightCode.next rightStart
      change
        RawArithmeticCircuitHolds
          (leftCode.gates ++ rightCode.gates ++
            [ArithmeticGateCode.mul
              leftCode.output rightCode.output out]) value at hvalue
      have hparts :=
        (rawArithmeticCircuitHolds_append
          (leftCode.gates ++ rightCode.gates)
          [ArithmeticGateCode.mul
            leftCode.output rightCode.output out] value).mp hvalue
      have hprogram :=
        (rawArithmeticCircuitHolds_append
          leftCode.gates rightCode.gates value).mp hparts.1
      have hleft :
          RawArithmeticCircuitHolds leftCode.gates value :=
        hprogram.1
      have hright :
          RawArithmeticCircuitHolds rightCode.gates value :=
        hprogram.2
      have hgate :
          ArithmeticGateCode.Holds
            (ArithmeticGateCode.mul
              leftCode.output rightCode.output out) value := by
        exact
          (rawArithmeticCircuitHolds_cons
            (ArithmeticGateCode.mul
              leftCode.output rightCode.output out) [] value).mp
              hparts.2 |>.1
      change value out = eval (fun i ↦ value i.1) left *
        eval (fun i ↦ value i.1) right
      rw [← leftIH start hleft, ← rightIH rightStart hright]
      simpa [ArithmeticGateCode.Holds, ArithmeticGateCode.mul,
        ArithmeticGateCode.tag, ArithmeticGateCode.x,
        ArithmeticGateCode.y, ArithmeticGateCode.z] using hgate.symm

end NaturalArithmeticExpression

/-! ## Equation circuits -/

namespace PolynomialGateCompiler

variable {n : ℕ}

/-- Extend a finite input tuple to a total register assignment. -/
def inputExtension (x : Fin n → ℕ) : ℕ → ℕ :=
  fun i ↦ if hi : i < n then x ⟨i, hi⟩ else 0

@[simp]
theorem inputExtension_apply (x : Fin n → ℕ) (i : Fin n) :
    inputExtension x i.1 = x i := by
  simp [inputExtension, i.isLt]

/-- The fragment computing the left side of an expression equation.  The
first fresh register `n` is reserved for a global zero. -/
def leftFragment (left : NaturalArithmeticExpression n) :
    ArithmeticFragment :=
  left.compileFrom (n + 1)

/-- First register available to the right-side fragment. -/
def rightStart (left : NaturalArithmeticExpression n) : ℕ :=
  (leftFragment left).next (n + 1)

/-- The fragment computing the right side of an expression equation. -/
def rightFragment (left right : NaturalArithmeticExpression n) :
    ArithmeticFragment :=
  right.compileFrom (rightStart left)

/-- Total number of finite circuit registers. -/
def expressionEquationVariableCount
    (left right : NaturalArithmeticExpression n) : ℕ :=
  (rightFragment left right).next (rightStart left)

/-- Forward, assignment-like part of the equation circuit. -/
def expressionEquationProgram
    (left right : NaturalArithmeticExpression n) :
    List ArithmeticGateCode :=
  ArithmeticGateCode.zero n ::
    ((leftFragment left).gates ++ (rightFragment left right).gates)

/-- The final relation `left + 0 = right`. -/
def expressionEquationGate
    (left right : NaturalArithmeticExpression n) :
    ArithmeticGateCode :=
  ArithmeticGateCode.add
    (leftFragment left).output n (rightFragment left right).output

/-- Complete raw code of an expression equation. -/
def expressionEquationGateCodes
    (left right : NaturalArithmeticExpression n) :
    List ArithmeticGateCode :=
  expressionEquationProgram left right ++
    [expressionEquationGate left right]

/-- Nondependent primitive-codable output of the source compiler: the
register count paired with its raw gate list. -/
def expressionEquationCode
    (left right : NaturalArithmeticExpression n) :
    ℕ × List ArithmeticGateCode :=
  (expressionEquationVariableCount left right,
    expressionEquationGateCodes left right)

theorem expressionEquationVariableCount_positive
    (left right : NaturalArithmeticExpression n) :
    0 < expressionEquationVariableCount left right := by
  simp [expressionEquationVariableCount, rightFragment,
    rightStart, leftFragment, ArithmeticFragment.next]

theorem expressionEquationProgram_length
    (left right : NaturalArithmeticExpression n) :
    n + (expressionEquationProgram left right).length =
      expressionEquationVariableCount left right := by
  simp [expressionEquationProgram, expressionEquationVariableCount,
    rightFragment, rightStart, leftFragment, ArithmeticFragment.next,
    Nat.add_assoc]
  omega

/-- The assignment part of an equation circuit is forward. -/
theorem expressionEquationProgram_forward
    (left right : NaturalArithmeticExpression n) :
    ForwardCircuitFrom n (expressionEquationProgram left right) := by
  have hleft :=
    NaturalArithmeticExpression.compileFrom_forward left (n + 1)
      (by omega)
  have hright :=
    NaturalArithmeticExpression.compileFrom_forward right
      (rightStart left) (by
        simp [rightStart, leftFragment, ArithmeticFragment.next]
        omega)
  change
    ArithmeticGateCode.ReadyAt (ArithmeticGateCode.zero n) n ∧
      ForwardCircuitFrom (n + 1)
        ((leftFragment left).gates ++
          (rightFragment left right).gates)
  constructor
  · simp [ArithmeticGateCode.ReadyAt, ArithmeticGateCode.zero,
      ArithmeticGateCode.output, ArithmeticGateCode.tag,
      ArithmeticGateCode.x]
  · rw [forwardCircuitFrom_append]
    constructor
    · exact hleft.1
    · simpa [rightStart, leftFragment, rightFragment,
        ArithmeticFragment.next] using hright.1

theorem leftFragment_output_lt_count
    (left right : NaturalArithmeticExpression n) :
    (leftFragment left).output <
      expressionEquationVariableCount left right := by
  have hleft :=
    NaturalArithmeticExpression.compileFrom_forward left (n + 1)
      (by omega)
  have hrightStart :
      rightStart left ≤ expressionEquationVariableCount left right := by
    simp [expressionEquationVariableCount, rightFragment,
      ArithmeticFragment.next]
  exact hleft.2.trans_le hrightStart

theorem rightFragment_output_lt_count
    (left right : NaturalArithmeticExpression n) :
    (rightFragment left right).output <
      expressionEquationVariableCount left right := by
  exact
    (NaturalArithmeticExpression.compileFrom_forward right
      (rightStart left) (by
        simp [rightStart, leftFragment, ArithmeticFragment.next]
        omega)).2

/-- All raw register references emitted by the compiler are in range. -/
theorem expressionEquationGateCodes_bounded
    (left right : NaturalArithmeticExpression n) :
    ∀ g ∈ expressionEquationGateCodes left right,
      ArithmeticGateCode.BoundedBy g
        (expressionEquationVariableCount left right) := by
  intro g hg
  rcases List.mem_append.mp hg with hprogram | hfinal
  · have hbound :=
      forwardCircuitFrom_bounded
        (expressionEquationProgram left right) n
        (expressionEquationProgram_forward left right) g hprogram
    rw [expressionEquationProgram_length] at hbound
    exact hbound
  · simp only [List.mem_singleton] at hfinal
    subst g
    have hn :
        n < expressionEquationVariableCount left right := by
      simp [expressionEquationVariableCount, rightFragment, rightStart,
        leftFragment, ArithmeticFragment.next]
      omega
    simpa [expressionEquationGate, ArithmeticGateCode.BoundedBy,
      ArithmeticGateCode.add, ArithmeticGateCode.tag,
      ArithmeticGateCode.x, ArithmeticGateCode.y,
      ArithmeticGateCode.z] using
      And.intro (leftFragment_output_lt_count left right)
        ⟨hn, rightFragment_output_lt_count left right⟩

/-- Exact raw-circuit semantics of an expression equation. -/
theorem expressionEquation_raw_solvable_iff
    (left right : NaturalArithmeticExpression n) :
    (∃ value : ℕ → ℕ,
        RawArithmeticCircuitHolds
          (expressionEquationGateCodes left right) value) ↔
      ∃ x : Fin n → ℕ,
        left.eval x = right.eval x := by
  constructor
  · rintro ⟨value, hvalue⟩
    have hparts :=
      (rawArithmeticCircuitHolds_append
        (expressionEquationProgram left right)
        [expressionEquationGate left right] value).mp hvalue
    have hprogram := hparts.1
    have htail :=
      (rawArithmeticCircuitHolds_cons
        (expressionEquationGate left right) [] value).mp hparts.2
    have hzero :
        value n = 0 := by
      exact hprogram (ArithmeticGateCode.zero n) (by
        simp [expressionEquationProgram])
    have hleft :
        RawArithmeticCircuitHolds
          (leftFragment left).gates value := by
      intro g hg
      exact hprogram g (by
        simp only [expressionEquationProgram, List.mem_cons,
          List.mem_append]
        exact Or.inr (Or.inl hg))
    have hright :
        RawArithmeticCircuitHolds
          (rightFragment left right).gates value := by
      intro g hg
      exact hprogram g (by
        simp only [expressionEquationProgram, List.mem_cons,
          List.mem_append]
        exact Or.inr (Or.inr hg))
    have hleftEval :=
      NaturalArithmeticExpression.compileFrom_output_eq_eval
        left (n + 1) value hleft
    have hrightEval :=
      NaturalArithmeticExpression.compileFrom_output_eq_eval
        right (rightStart left) value hright
    refine ⟨fun i ↦ value i.1, ?_⟩
    change
      NaturalArithmeticExpression.eval (fun i ↦ value i.1) left =
        NaturalArithmeticExpression.eval (fun i ↦ value i.1) right
    rw [← hleftEval, ← hrightEval]
    have hequation := htail.1
    simpa [expressionEquationGate, ArithmeticGateCode.Holds,
      ArithmeticGateCode.add, ArithmeticGateCode.tag,
      ArithmeticGateCode.x, ArithmeticGateCode.y,
      ArithmeticGateCode.z, hzero] using hequation
  · rintro ⟨x, hequation⟩
    obtain ⟨value, hprogram, hagrees⟩ :=
      exists_rawArithmeticCircuitHolds_of_forward
        (expressionEquationProgram left right) n
        (inputExtension x)
        (expressionEquationProgram_forward left right)
    have hinputs :
        (fun i : Fin n ↦ value i.1) = x := by
      funext i
      rw [hagrees i.1 i.isLt]
      exact inputExtension_apply x i
    have hzero :
        value n = 0 := by
      exact hprogram (ArithmeticGateCode.zero n) (by
        simp [expressionEquationProgram])
    have hleft :
        RawArithmeticCircuitHolds
          (leftFragment left).gates value := by
      intro g hg
      exact hprogram g (by
        simp only [expressionEquationProgram, List.mem_cons,
          List.mem_append]
        exact Or.inr (Or.inl hg))
    have hright :
        RawArithmeticCircuitHolds
          (rightFragment left right).gates value := by
      intro g hg
      exact hprogram g (by
        simp only [expressionEquationProgram, List.mem_cons,
          List.mem_append]
        exact Or.inr (Or.inr hg))
    have hleftEval :=
      NaturalArithmeticExpression.compileFrom_output_eq_eval
        left (n + 1) value hleft
    have hrightEval :=
      NaturalArithmeticExpression.compileFrom_output_eq_eval
        right (rightStart left) value hright
    change
      value (leftFragment left).output =
        NaturalArithmeticExpression.eval (fun i ↦ value i.1) left
      at hleftEval
    change
      value (rightFragment left right).output =
        NaturalArithmeticExpression.eval (fun i ↦ value i.1) right
      at hrightEval
    have hgate :
        ArithmeticGateCode.Holds
          (expressionEquationGate left right) value := by
      simp only [expressionEquationGate, ArithmeticGateCode.Holds,
        ArithmeticGateCode.add, ArithmeticGateCode.tag,
        ArithmeticGateCode.x, ArithmeticGateCode.y,
        ArithmeticGateCode.z]
      rw [hzero, add_zero, hleftEval, hrightEval, hinputs]
      exact hequation
    refine ⟨value, ?_⟩
    rw [expressionEquationGateCodes,
      rawArithmeticCircuitHolds_append]
    exact ⟨hprogram,
      (rawArithmeticCircuitHolds_cons
        (expressionEquationGate left right) [] value).mpr
          ⟨hgate, rawArithmeticCircuitHolds_nil value⟩⟩

/-- Actual finite arithmetic circuit for an expression equation. -/
def expressionEquationCircuit
    (left right : NaturalArithmeticExpression n) :
    List (ArithmeticGate (expressionEquationVariableCount left right)) :=
  realizeArithmeticCircuit
    (expressionEquationVariableCount left right)
    (expressionEquationVariableCount_positive left right)
    (expressionEquationGateCodes left right)

/-- Exact solvability specification of the finite arithmetic circuit. -/
theorem expressionEquationCircuit_solvable_iff
    (left right : NaturalArithmeticExpression n) :
    (∃ value :
        Fin (expressionEquationVariableCount left right) → ℕ,
        GateDQLCompiler.NaturalCircuitHolds
          (expressionEquationCircuit left right) value) ↔
      ∃ x : Fin n → ℕ, left.eval x = right.eval x := by
  let bound := expressionEquationVariableCount left right
  have hpositive : 0 < bound :=
    expressionEquationVariableCount_positive left right
  have hbounded :
      ∀ g ∈ expressionEquationGateCodes left right,
        ArithmeticGateCode.BoundedBy g bound :=
    expressionEquationGateCodes_bounded left right
  constructor
  · rintro ⟨value, hvalue⟩
    have hraw :
        RawArithmeticCircuitHolds
          (expressionEquationGateCodes left right)
          (ArithmeticGateCode.liftFiniteValue value) := by
      exact
        (naturalCircuitHolds_realize_iff
          hpositive (expressionEquationGateCodes left right)
          hbounded value).mp hvalue
    exact
      (expressionEquation_raw_solvable_iff left right).mp
        ⟨ArithmeticGateCode.liftFiniteValue value, hraw⟩
  · intro hsource
    obtain ⟨rawValue, hraw⟩ :=
      (expressionEquation_raw_solvable_iff left right).mpr hsource
    let value : Fin bound → ℕ := fun i ↦ rawValue i.1
    have hagrees :
        ∀ i, i < bound →
          ArithmeticGateCode.liftFiniteValue value i = rawValue i := by
      intro i hi
      simp [ArithmeticGateCode.liftFiniteValue, value, hi]
    have hlifted :
        RawArithmeticCircuitHolds
          (expressionEquationGateCodes left right)
          (ArithmeticGateCode.liftFiniteValue value) := by
      intro g hg
      exact
        (ArithmeticGateCode.holds_congr_of_boundedBy
          g (hbounded g hg) hagrees).mpr (hraw g hg)
    refine ⟨value, ?_⟩
    exact
      (naturalCircuitHolds_realize_iff
        hpositive (expressionEquationGateCodes left right)
        hbounded value).mpr hlifted

/-- Literal DQL system obtained by composing the polynomial circuit with
the already verified natural-circuit compiler. -/
def expressionEquationDQL
    (left right : NaturalArithmeticExpression n) :=
  GateDQLCompiler.compileNaturalCircuit
    (expressionEquationCircuit left right)

/-- End-to-end correctness for arbitrary natural arithmetic expressions. -/
theorem expressionEquationDQL_solvable_iff
    (left right : NaturalArithmeticExpression n) :
    (expressionEquationDQL left right).Solvable ↔
      ∃ x : Fin n → ℕ, left.eval x = right.eval x := by
  rw [expressionEquationDQL,
    GateDQLCompiler.compileNaturalCircuit_solvable_iff,
    expressionEquationCircuit_solvable_iff]

/-! ## Sparse polynomial specializations -/

/-- State of the tail-recursive sparse-polynomial compiler:
`(next, gates, output)`. -/
abbrev ArithmeticBuilder :=
  ℕ × (List ArithmeticGateCode × ℕ)

namespace ArithmeticBuilder

def next (builder : ArithmeticBuilder) : ℕ := builder.1
def gates (builder : ArithmeticBuilder) : List ArithmeticGateCode :=
  builder.2.1
def output (builder : ArithmeticBuilder) : ℕ := builder.2.2

def fragment (builder : ArithmeticBuilder) : ArithmeticFragment :=
  ⟨builder.gates, builder.output⟩

end ArithmeticBuilder

/-- Start a builder with one fresh zero register. -/
def startZeroBuilder (start : ℕ) : ArithmeticBuilder :=
  (start + 1, [ArithmeticGateCode.zero start], start)

/-- Start a builder with one fresh one register. -/
def startOneBuilder (start : ℕ) : ArithmeticBuilder :=
  (start + 1, [ArithmeticGateCode.one start], start)

/-- Append a fresh one and an addition.  Iterating this operation compiles
a unary natural literal. -/
def numeralBuilderStep (builder : ArithmeticBuilder) :
    ArithmeticBuilder :=
  let oneRegister := builder.next
  let out := oneRegister + 1
  (out + 1,
    builder.gates ++
      [ArithmeticGateCode.one oneRegister,
        ArithmeticGateCode.add builder.output oneRegister out],
    out)

/-- Direct tail-recursive compiler for a natural literal. -/
def compileNumeralBuilder (start : ℕ) : ℕ → ArithmeticBuilder
  | 0 => startZeroBuilder start
  | k + 1 => numeralBuilderStep (compileNumeralBuilder start k)

/-- Append one multiplication by a fixed input register. -/
def powerBuilderStep (input : ℕ) (builder : ArithmeticBuilder) :
    ArithmeticBuilder :=
  let out := builder.next
  (out + 1,
    builder.gates ++
      [ArithmeticGateCode.mul builder.output input out],
    out)

/-- Direct tail-recursive compiler for a power of one input register. -/
def compilePowerBuilder (start input : ℕ) : ℕ → ArithmeticBuilder
  | 0 => startOneBuilder start
  | k + 1 => powerBuilderStep input (compilePowerBuilder start input k)

/-- Join two consecutively allocated builders with a fresh multiplication
gate. -/
def appendMulBuilder (left right : ArithmeticBuilder) :
    ArithmeticBuilder :=
  let out := right.next
  (out + 1,
    left.gates ++ right.gates ++
      [ArithmeticGateCode.mul left.output right.output out],
    out)

/-- Join two consecutively allocated builders with a fresh addition
gate. -/
def appendAddBuilder (left right : ArithmeticBuilder) :
    ArithmeticBuilder :=
  let out := right.next
  (out + 1,
    left.gates ++ right.gates ++
      [ArithmeticGateCode.add left.output right.output out],
    out)

/-- Extend a partial monomial by one powered input. -/
def appendPoweredInput (builder : ArithmeticBuilder)
    (term : Fin n × ℕ) : ArithmeticBuilder :=
  appendMulBuilder builder
    (compilePowerBuilder builder.next term.1.1 term.2)

/-- Executable ordered list of the entries of an exponent vector. -/
def exponentEntries (e : ExponentCode n) : List (Fin n × ℕ) :=
  List.ofFn fun i ↦ (i, e i)

/-- Tail-recursive monomial compiler. -/
def compileMonomialBuilder (start : ℕ) (e : ExponentCode n) :
    ArithmeticBuilder :=
  (exponentEntries e).foldl appendPoweredInput
    (startOneBuilder start)

/-- Tail-recursive compiler for one coefficient times one monomial. -/
def compileNaturalTermBuilder (start : ℕ)
    (term : ExponentCode n × ℕ) : ArithmeticBuilder :=
  let coefficient := compileNumeralBuilder start term.2
  let monomial := compileMonomialBuilder coefficient.next term.1
  appendMulBuilder coefficient monomial

/-- Extend a partial polynomial sum by one sparse term. -/
def appendNaturalTerm (builder : ArithmeticBuilder)
    (term : ExponentCode n × ℕ) : ArithmeticBuilder :=
  appendAddBuilder builder
    (compileNaturalTermBuilder builder.next term)

/-- Tail-recursive sparse natural-polynomial compiler. -/
def compileNaturalPolynomialBuilder (start : ℕ)
    (p : NaturalPolynomialCode n) : ArithmeticBuilder :=
  p.foldl appendNaturalTerm (startZeroBuilder start)

/-- Direct primitive-data compiler for a natural polynomial equation.
Register `n` is zero, followed by the two polynomial programs and one
terminal equality gate. -/
def naturalPolynomialEquationCodeDirect
    (left right : NaturalPolynomialCode n) :
    ℕ × List ArithmeticGateCode :=
  let zeroBuilder := startZeroBuilder n
  let leftBuilder :=
    compileNaturalPolynomialBuilder zeroBuilder.next left
  let rightBuilder :=
    compileNaturalPolynomialBuilder leftBuilder.next right
  (rightBuilder.next,
    zeroBuilder.gates ++ leftBuilder.gates ++ rightBuilder.gates ++
      [ArithmeticGateCode.add leftBuilder.output n rightBuilder.output])

/-- A builder represents an expression when its three observable fields
are exactly those of `compileFrom`, including the absolute next-register
counter. -/
def BuilderRepresents (start : ℕ)
    (expression : NaturalArithmeticExpression n)
    (builder : ArithmeticBuilder) : Prop :=
  builder.next = (expression.compileFrom start).next start ∧
    builder.gates = (expression.compileFrom start).gates ∧
      builder.output = (expression.compileFrom start).output

@[simp]
theorem startZeroBuilder_represents {n : ℕ} (start : ℕ) :
    BuilderRepresents (n := n) start
      (.zero : NaturalArithmeticExpression n)
      (startZeroBuilder start) := by
  simp [BuilderRepresents, startZeroBuilder, ArithmeticBuilder.next,
    ArithmeticBuilder.gates, ArithmeticBuilder.output,
    NaturalArithmeticExpression.compileFrom, ArithmeticFragment.next]

@[simp]
theorem startOneBuilder_represents {n : ℕ} (start : ℕ) :
    BuilderRepresents (n := n) start
      (.one : NaturalArithmeticExpression n)
      (startOneBuilder start) := by
  simp [BuilderRepresents, startOneBuilder, ArithmeticBuilder.next,
    ArithmeticBuilder.gates, ArithmeticBuilder.output,
    NaturalArithmeticExpression.compileFrom, ArithmeticFragment.next]

/-- Correctness of the generic multiplication join. -/
theorem appendMulBuilder_represents
    (start : ℕ) (left right : NaturalArithmeticExpression n)
    (leftBuilder rightBuilder : ArithmeticBuilder)
    (hleft : BuilderRepresents start left leftBuilder)
    (hright :
      BuilderRepresents leftBuilder.next right rightBuilder) :
    BuilderRepresents start (.mul left right)
      (appendMulBuilder leftBuilder rightBuilder) := by
  rcases hleft with ⟨hleftNext, hleftGates, hleftOutput⟩
  rcases hright with ⟨hrightNext, hrightGates, hrightOutput⟩
  have hleftCount :
      leftBuilder.next = start + leftBuilder.gates.length := by
    rw [hleftNext, hleftGates]
    rfl
  have hrightCount :
      rightBuilder.next =
        leftBuilder.next + rightBuilder.gates.length := by
    rw [hrightNext, hrightGates]
    rfl
  simp only [BuilderRepresents, appendMulBuilder,
    ArithmeticBuilder.next, ArithmeticBuilder.gates,
    ArithmeticBuilder.output]
  simp only [NaturalArithmeticExpression.compileFrom]
  rw [← hleftGates, ← hleftOutput, ← hleftNext,
    ← hrightGates, ← hrightOutput, ← hrightNext]
  constructor
  · simp only [ArithmeticFragment.next, List.length_append,
      List.length_cons, List.length_nil]
    change
      rightBuilder.next + 1 =
        start + (leftBuilder.gates.length +
          rightBuilder.gates.length + 1)
    rw [hrightCount, hleftCount]
    omega
  · exact ⟨rfl, rfl⟩

/-- Correctness of the generic addition join. -/
theorem appendAddBuilder_represents
    (start : ℕ) (left right : NaturalArithmeticExpression n)
    (leftBuilder rightBuilder : ArithmeticBuilder)
    (hleft : BuilderRepresents start left leftBuilder)
    (hright :
      BuilderRepresents leftBuilder.next right rightBuilder) :
    BuilderRepresents start (.add left right)
      (appendAddBuilder leftBuilder rightBuilder) := by
  rcases hleft with ⟨hleftNext, hleftGates, hleftOutput⟩
  rcases hright with ⟨hrightNext, hrightGates, hrightOutput⟩
  have hleftCount :
      leftBuilder.next = start + leftBuilder.gates.length := by
    rw [hleftNext, hleftGates]
    rfl
  have hrightCount :
      rightBuilder.next =
        leftBuilder.next + rightBuilder.gates.length := by
    rw [hrightNext, hrightGates]
    rfl
  simp only [BuilderRepresents, appendAddBuilder,
    ArithmeticBuilder.next, ArithmeticBuilder.gates,
    ArithmeticBuilder.output]
  simp only [NaturalArithmeticExpression.compileFrom]
  rw [← hleftGates, ← hleftOutput, ← hleftNext,
    ← hrightGates, ← hrightOutput, ← hrightNext]
  constructor
  · simp only [ArithmeticFragment.next, List.length_append,
      List.length_cons, List.length_nil]
    change
      rightBuilder.next + 1 =
        start + (leftBuilder.gates.length +
          rightBuilder.gates.length + 1)
    rw [hrightCount, hleftCount]
    omega
  · exact ⟨rfl, rfl⟩

theorem compileNumeralBuilder_represents {n : ℕ} (start k : ℕ) :
    BuilderRepresents (n := n) start
      (NaturalArithmeticExpression.numeral (n := n) k)
      (compileNumeralBuilder start k) := by
  induction k with
  | zero =>
      exact startZeroBuilder_represents (n := n) start
  | succ k ih =>
      have hone :
          BuilderRepresents
            (compileNumeralBuilder start k).next
            (.one : NaturalArithmeticExpression n)
            (startOneBuilder (compileNumeralBuilder start k).next) :=
        startOneBuilder_represents (n := n) _
      have hadd :=
        appendAddBuilder_represents start
          (NaturalArithmeticExpression.numeral k) .one
          (compileNumeralBuilder start k)
          (startOneBuilder (compileNumeralBuilder start k).next)
          ih hone
      simpa [compileNumeralBuilder, numeralBuilderStep,
        appendAddBuilder, startOneBuilder,
        ArithmeticBuilder.next, ArithmeticBuilder.gates,
        ArithmeticBuilder.output,
        NaturalArithmeticExpression.numeral] using hadd

theorem compilePowerBuilder_represents
    (start : ℕ) (input : Fin n) (k : ℕ) :
    BuilderRepresents start
      (NaturalArithmeticExpression.power (.input input) k)
      (compilePowerBuilder start input.1 k) := by
  induction k with
  | zero =>
      exact startOneBuilder_represents start
  | succ k ih =>
      have hinput :
          BuilderRepresents
            (compilePowerBuilder start input.1 k).next
            (.input input : NaturalArithmeticExpression n)
            ((compilePowerBuilder start input.1 k).next,
              [], input.1) := by
        simp [BuilderRepresents, ArithmeticBuilder.next,
          ArithmeticBuilder.gates, ArithmeticBuilder.output,
          NaturalArithmeticExpression.compileFrom,
          ArithmeticFragment.next]
      have hmul :=
        appendMulBuilder_represents start
          (NaturalArithmeticExpression.power (.input input) k)
          (.input input)
          (compilePowerBuilder start input.1 k)
          ((compilePowerBuilder start input.1 k).next, [], input.1)
          ih hinput
      simpa [compilePowerBuilder, powerBuilderStep,
        appendMulBuilder, ArithmeticBuilder.next,
        ArithmeticBuilder.gates, ArithmeticBuilder.output,
        NaturalArithmeticExpression.power] using hmul

private theorem foldlMonomialBuilder_represents
    (terms : List (Fin n × ℕ)) (start : ℕ)
    (accumulator : NaturalArithmeticExpression n)
    (builder : ArithmeticBuilder)
    (hbuilder : BuilderRepresents start accumulator builder) :
    BuilderRepresents start
      (terms.foldl
        (fun acc term ↦
          .mul acc
            (NaturalArithmeticExpression.power
              (.input term.1) term.2))
        accumulator)
      (terms.foldl appendPoweredInput builder) := by
  induction terms generalizing accumulator builder with
  | nil =>
      exact hbuilder
  | cons term terms ih =>
      rw [List.foldl_cons, List.foldl_cons]
      apply ih
      apply appendMulBuilder_represents start accumulator
        (NaturalArithmeticExpression.power (.input term.1) term.2)
        builder
        (compilePowerBuilder builder.next term.1.1 term.2)
        hbuilder
      exact compilePowerBuilder_represents builder.next term.1 term.2

theorem compileMonomialBuilder_represents
    (start : ℕ) (e : ExponentCode n) :
    BuilderRepresents start
      (NaturalArithmeticExpression.monomialForward e)
      (compileMonomialBuilder start e) := by
  unfold NaturalArithmeticExpression.monomialForward
  unfold compileMonomialBuilder exponentEntries
  have hrep :=
    foldlMonomialBuilder_represents
      (List.ofFn fun i ↦ (i, e i)) start .one
      (startOneBuilder start)
      (startOneBuilder_represents (n := n) start)
  let toExpression : Fin n × ℕ → NaturalArithmeticExpression n :=
    fun term ↦
      NaturalArithmeticExpression.power
        (NaturalArithmeticExpression.input term.1) term.2
  have hfold :
      (List.ofFn fun i ↦ (i, e i)).foldl
          (fun acc term ↦
            NaturalArithmeticExpression.mul acc
              (toExpression term))
          (NaturalArithmeticExpression.one) =
        ((List.ofFn fun i ↦ (i, e i)).map toExpression).foldl
          NaturalArithmeticExpression.mul
          NaturalArithmeticExpression.one := by
    exact List.foldl_map.symm
  have hmap :
      (List.ofFn fun i ↦ (i, e i)).map toExpression =
        List.ofFn fun i ↦
          NaturalArithmeticExpression.power
            (NaturalArithmeticExpression.input i) (e i) := by
    exact
      (List.ofFn_comp'
        (fun i ↦ (i, e i)) toExpression).symm
  rw [hfold, hmap] at hrep
  exact hrep

theorem compileNaturalTermBuilder_represents
    (start : ℕ) (term : ExponentCode n × ℕ) :
    BuilderRepresents start
      (.mul (NaturalArithmeticExpression.numeral term.2)
        (NaturalArithmeticExpression.monomialForward term.1))
      (compileNaturalTermBuilder start term) := by
  apply appendMulBuilder_represents start
    (NaturalArithmeticExpression.numeral term.2)
    (NaturalArithmeticExpression.monomialForward term.1)
  · exact compileNumeralBuilder_represents start term.2
  · exact compileMonomialBuilder_represents
      (compileNumeralBuilder start term.2).next term.1

private theorem foldlPolynomialBuilder_represents
    (terms : NaturalPolynomialCode n) (start : ℕ)
    (accumulator : NaturalArithmeticExpression n)
    (builder : ArithmeticBuilder)
    (hbuilder : BuilderRepresents start accumulator builder) :
    BuilderRepresents start
      (terms.foldl
        (fun acc term ↦
          .add acc
            (.mul (NaturalArithmeticExpression.numeral term.2)
              (NaturalArithmeticExpression.monomialForward term.1)))
        accumulator)
      (terms.foldl appendNaturalTerm builder) := by
  induction terms generalizing accumulator builder with
  | nil =>
      exact hbuilder
  | cons term terms ih =>
      rw [List.foldl_cons, List.foldl_cons]
      apply ih
      apply appendAddBuilder_represents start accumulator
        (.mul (NaturalArithmeticExpression.numeral term.2)
          (NaturalArithmeticExpression.monomialForward term.1))
        builder
        (compileNaturalTermBuilder builder.next term)
        hbuilder
      exact compileNaturalTermBuilder_represents builder.next term

theorem compileNaturalPolynomialBuilder_represents
    (start : ℕ) (p : NaturalPolynomialCode n) :
    BuilderRepresents start
      (NaturalArithmeticExpression.ofPolynomialForward p)
      (compileNaturalPolynomialBuilder start p) := by
  unfold NaturalArithmeticExpression.ofPolynomialForward
  unfold compileNaturalPolynomialBuilder
  exact
    foldlPolynomialBuilder_represents p start .zero
      (startZeroBuilder start) (startZeroBuilder_represents start)

/-- Raw compiler code for a sparse natural polynomial equation. -/
def naturalPolynomialEquationCode
    (left right : NaturalPolynomialCode n) :
    ℕ × List ArithmeticGateCode :=
  expressionEquationCode
    (NaturalArithmeticExpression.ofPolynomialForward left)
    (NaturalArithmeticExpression.ofPolynomialForward right)

/-- The direct tail-recursive implementation is definitionally faithful to
the generic expression compiler. -/
theorem naturalPolynomialEquationCodeDirect_eq
    (left right : NaturalPolynomialCode n) :
    naturalPolynomialEquationCodeDirect left right =
      naturalPolynomialEquationCode left right := by
  let zeroBuilder := startZeroBuilder n
  let leftBuilder :=
    compileNaturalPolynomialBuilder zeroBuilder.next left
  let rightBuilder :=
    compileNaturalPolynomialBuilder leftBuilder.next right
  have hleft :=
    compileNaturalPolynomialBuilder_represents
      zeroBuilder.next left
  have hright :=
    compileNaturalPolynomialBuilder_represents
      leftBuilder.next right
  rcases hleft with ⟨hleftNext, hleftGates, hleftOutput⟩
  rcases hright with ⟨hrightNext, hrightGates, hrightOutput⟩
  let leftExpression :=
    NaturalArithmeticExpression.ofPolynomialForward left
  let rightExpression :=
    NaturalArithmeticExpression.ofPolynomialForward right
  have hzeroNext : zeroBuilder.next = n + 1 := by
    simp [zeroBuilder, startZeroBuilder, ArithmeticBuilder.next]
  have hzeroGates :
      zeroBuilder.gates = [ArithmeticGateCode.zero n] := by
    simp [zeroBuilder, startZeroBuilder, ArithmeticBuilder.gates]
  have hleftNext' :
      leftBuilder.next =
        (leftFragment leftExpression).next (n + 1) := by
    simpa [leftBuilder, leftExpression, leftFragment, hzeroNext] using
      hleftNext
  have hleftGates' :
      leftBuilder.gates = (leftFragment leftExpression).gates := by
    simpa [leftBuilder, leftExpression, leftFragment, hzeroNext] using
      hleftGates
  have hleftOutput' :
      leftBuilder.output = (leftFragment leftExpression).output := by
    simpa [leftBuilder, leftExpression, leftFragment, hzeroNext] using
      hleftOutput
  have hrightNext' :
      rightBuilder.next =
        (rightFragment leftExpression rightExpression).next
          (rightStart leftExpression) := by
    simpa [rightBuilder, rightExpression, rightFragment, rightStart,
      ← hleftNext'] using hrightNext
  have hrightGates' :
      rightBuilder.gates =
        (rightFragment leftExpression rightExpression).gates := by
    simpa [rightBuilder, rightExpression, rightFragment, rightStart,
      ← hleftNext'] using hrightGates
  have hrightOutput' :
      rightBuilder.output =
        (rightFragment leftExpression rightExpression).output := by
    simpa [rightBuilder, rightExpression, rightFragment, rightStart,
      ← hleftNext'] using hrightOutput
  change
    (rightBuilder.next,
      zeroBuilder.gates ++ leftBuilder.gates ++ rightBuilder.gates ++
        [ArithmeticGateCode.add leftBuilder.output n
          rightBuilder.output]) =
      expressionEquationCode leftExpression rightExpression
  unfold expressionEquationCode
  apply Prod.ext
  · exact hrightNext'
  · simp [expressionEquationGateCodes, expressionEquationProgram,
      expressionEquationGate, hzeroGates, hleftGates',
      hleftOutput', hrightGates', hrightOutput']

/-! ### Primitive-recursiveness of the raw compiler -/

namespace CompilerPrimrec

theorem gateZero : Primrec ArithmeticGateCode.zero := by
  exact Primrec.pair
    (Primrec.const 0)
    (Primrec.pair Primrec.id
      (Primrec.pair (Primrec.const 0) (Primrec.const 0)))

theorem gateOne : Primrec ArithmeticGateCode.one := by
  exact Primrec.pair
    (Primrec.const 1)
    (Primrec.pair Primrec.id
      (Primrec.pair (Primrec.const 0) (Primrec.const 0)))

theorem gateAdd :
    Primrec
      (fun p : ℕ × (ℕ × ℕ) ↦
        ArithmeticGateCode.add p.1 p.2.1 p.2.2) := by
  exact Primrec.pair
    (Primrec.const 2)
    (Primrec.pair Primrec.fst
      (Primrec.pair
        (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)))

theorem gateMul :
    Primrec
      (fun p : ℕ × (ℕ × ℕ) ↦
        ArithmeticGateCode.mul p.1 p.2.1 p.2.2) := by
  exact Primrec.pair
    (Primrec.const 3)
    (Primrec.pair Primrec.fst
      (Primrec.pair
        (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)))

theorem builderNext : Primrec ArithmeticBuilder.next :=
  Primrec.fst

theorem builderGates : Primrec ArithmeticBuilder.gates :=
  Primrec.fst.comp Primrec.snd

theorem builderOutput : Primrec ArithmeticBuilder.output :=
  Primrec.snd.comp Primrec.snd

private theorem singleton {α : Type*} [Primcodable α]
    {β : Type*} [Primcodable β] {f : α → β}
    (hf : Primrec f) :
    Primrec (fun a ↦ [f a]) :=
  Primrec.list_cons.comp hf (Primrec.const [])

theorem startZero : Primrec startZeroBuilder := by
  exact Primrec.pair
    (Primrec.succ)
    (Primrec.pair
      (singleton gateZero)
      Primrec.id)

theorem startOne : Primrec startOneBuilder := by
  exact Primrec.pair
    (Primrec.succ)
    (Primrec.pair
      (singleton gateOne)
      Primrec.id)

theorem numeralStep : Primrec numeralBuilderStep := by
  have honeRegister : Primrec ArithmeticBuilder.next :=
    builderNext
  have hout :
      Primrec (fun b : ArithmeticBuilder ↦ b.next + 1) :=
    Primrec.succ.comp builderNext
  have hnext :
      Primrec (fun b : ArithmeticBuilder ↦ b.next + 1 + 1) :=
    Primrec.succ.comp hout
  have honeGate :
      Primrec
        (fun b : ArithmeticBuilder ↦
          ArithmeticGateCode.one b.next) :=
    gateOne.comp builderNext
  have haddGate :
      Primrec
        (fun b : ArithmeticBuilder ↦
          ArithmeticGateCode.add b.output b.next (b.next + 1)) :=
    gateAdd.comp
      (Primrec.pair builderOutput
        (Primrec.pair builderNext hout))
  have hnewGates :
      Primrec
        (fun b : ArithmeticBuilder ↦
          b.gates ++
            [ArithmeticGateCode.one b.next,
              ArithmeticGateCode.add b.output b.next (b.next + 1)]) :=
    Primrec.list_append.comp builderGates
      (Primrec.list_cons.comp honeGate
        (singleton haddGate))
  exact
    (Primrec.pair hnext
      (Primrec.pair hnewGates hout)).of_eq fun _ ↦ rfl

theorem compileNumeral :
    Primrec₂ compileNumeralBuilder := by
  have hstep :
      Primrec₂
        (fun (_ : ℕ) (p : ℕ × ArithmeticBuilder) ↦
          numeralBuilderStep p.2) :=
    numeralStep.comp₂
      (Primrec.snd.comp₂ Primrec₂.right)
  exact
    (Primrec.nat_rec startZero hstep).of_eq fun start k ↦ by
      induction k with
      | zero => rfl
      | succ k ih =>
          simp only [compileNumeralBuilder]
          rw [ih]

theorem powerStep :
    Primrec₂ powerBuilderStep := by
  have hout :
      Primrec
        (fun p : ℕ × ArithmeticBuilder ↦ p.2.next) :=
    builderNext.comp Primrec.snd
  have hgate :
      Primrec
        (fun p : ℕ × ArithmeticBuilder ↦
          ArithmeticGateCode.mul p.2.output p.1 p.2.next) :=
    gateMul.comp
      (Primrec.pair
        (builderOutput.comp Primrec.snd)
        (Primrec.pair Primrec.fst
          (builderNext.comp Primrec.snd)))
  have hgates :
      Primrec
        (fun p : ℕ × ArithmeticBuilder ↦
          p.2.gates ++
            [ArithmeticGateCode.mul p.2.output p.1 p.2.next]) :=
    Primrec.list_append.comp
      (builderGates.comp Primrec.snd)
      (singleton hgate)
  exact
    (Primrec.pair
      (Primrec.succ.comp hout)
      (Primrec.pair hgates hout)).to₂.of_eq fun _ _ ↦ rfl

theorem compilePower :
    Primrec₂
      (fun p : ℕ × ℕ ↦
        compilePowerBuilder p.1 p.2) := by
  have hbase :
      Primrec (fun p : ℕ × ℕ ↦ startOneBuilder p.1) :=
    startOne.comp Primrec.fst
  have hstep :
      Primrec₂
        (fun (p : ℕ × ℕ)
          (state : ℕ × ArithmeticBuilder) ↦
            powerBuilderStep p.2 state.2) :=
    powerStep.comp₂
      (Primrec.snd.comp₂ Primrec₂.left)
      (Primrec.snd.comp₂ Primrec₂.right)
  exact
    (Primrec.nat_rec hbase hstep).of_eq fun p k ↦ by
      induction k with
      | zero => rfl
      | succ k ih =>
          simp only [compilePowerBuilder, ih]

theorem appendMul :
    Primrec₂ appendMulBuilder := by
  have hout :
      Primrec
        (fun p : ArithmeticBuilder × ArithmeticBuilder ↦ p.2.next) :=
    builderNext.comp Primrec.snd
  have hgate :
      Primrec
        (fun p : ArithmeticBuilder × ArithmeticBuilder ↦
          ArithmeticGateCode.mul
            p.1.output p.2.output p.2.next) :=
    gateMul.comp
      (Primrec.pair
        (builderOutput.comp Primrec.fst)
        (Primrec.pair
          (builderOutput.comp Primrec.snd)
          (builderNext.comp Primrec.snd)))
  have hgates :
      Primrec
        (fun p : ArithmeticBuilder × ArithmeticBuilder ↦
          p.1.gates ++ p.2.gates ++
            [ArithmeticGateCode.mul
              p.1.output p.2.output p.2.next]) :=
    Primrec.list_append.comp
      (Primrec.list_append.comp
        (builderGates.comp Primrec.fst)
        (builderGates.comp Primrec.snd))
      (singleton hgate)
  exact
    (Primrec.pair
      (Primrec.succ.comp hout)
      (Primrec.pair hgates hout)).to₂.of_eq fun _ _ ↦ rfl

theorem appendAdd :
    Primrec₂ appendAddBuilder := by
  have hout :
      Primrec
        (fun p : ArithmeticBuilder × ArithmeticBuilder ↦ p.2.next) :=
    builderNext.comp Primrec.snd
  have hgate :
      Primrec
        (fun p : ArithmeticBuilder × ArithmeticBuilder ↦
          ArithmeticGateCode.add
            p.1.output p.2.output p.2.next) :=
    gateAdd.comp
      (Primrec.pair
        (builderOutput.comp Primrec.fst)
        (Primrec.pair
          (builderOutput.comp Primrec.snd)
          (builderNext.comp Primrec.snd)))
  have hgates :
      Primrec
        (fun p : ArithmeticBuilder × ArithmeticBuilder ↦
          p.1.gates ++ p.2.gates ++
            [ArithmeticGateCode.add
              p.1.output p.2.output p.2.next]) :=
    Primrec.list_append.comp
      (Primrec.list_append.comp
        (builderGates.comp Primrec.fst)
        (builderGates.comp Primrec.snd))
      (singleton hgate)
  exact
    (Primrec.pair
      (Primrec.succ.comp hout)
      (Primrec.pair hgates hout)).to₂.of_eq fun _ _ ↦ rfl

theorem appendPoweredInput {n : ℕ} :
    Primrec₂ (appendPoweredInput :
      ArithmeticBuilder → (Fin n × ℕ) → ArithmeticBuilder) := by
  have hparameters :
      Primrec
        (fun p : ArithmeticBuilder × (Fin n × ℕ) ↦
          (p.1.next, p.2.1.1)) :=
    Primrec.pair
      (builderNext.comp Primrec.fst)
      (Primrec.fin_val.comp
        (Primrec.fst.comp Primrec.snd))
  have hexponent :
      Primrec
        (fun p : ArithmeticBuilder × (Fin n × ℕ) ↦ p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hpower :
      Primrec
        (fun p : ArithmeticBuilder × (Fin n × ℕ) ↦
          compilePowerBuilder p.1.next p.2.1.1 p.2.2) :=
    compilePower.comp hparameters hexponent
  exact
    (appendMul.comp Primrec.fst hpower).to₂.of_eq fun _ _ ↦ rfl

theorem exponentEntries {n : ℕ} :
    Primrec (exponentEntries : ExponentCode n → List (Fin n × ℕ)) := by
  exact Primrec.list_ofFn fun i ↦
    Primrec.pair
      (Primrec.const i)
      (Primrec.fin_app.comp Primrec.id (Primrec.const i))

theorem compileMonomial {n : ℕ} :
    Primrec₂
      (compileMonomialBuilder :
        ℕ → ExponentCode n → ArithmeticBuilder) := by
  have hstep :
      Primrec₂
        (fun (_ : ℕ × ExponentCode n)
          (state : ArithmeticBuilder × (Fin n × ℕ)) ↦
            PolynomialGateCompiler.appendPoweredInput
              state.1 state.2) :=
    appendPoweredInput.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.right)
  exact
    (Primrec.list_foldl
      (exponentEntries.comp Primrec.snd)
      (startOne.comp Primrec.fst)
      hstep).to₂.of_eq fun _ _ ↦ rfl

theorem compileNaturalTerm {n : ℕ} :
    Primrec₂
      (compileNaturalTermBuilder :
        ℕ → (ExponentCode n × ℕ) → ArithmeticBuilder) := by
  have hcoefficient :
      Primrec
        (fun p : ℕ × (ExponentCode n × ℕ) ↦
          compileNumeralBuilder p.1 p.2.2) :=
    compileNumeral.comp
      Primrec.fst
      (Primrec.snd.comp Primrec.snd)
  have hmonomial :
      Primrec
        (fun p : ℕ × (ExponentCode n × ℕ) ↦
          compileMonomialBuilder
            (compileNumeralBuilder p.1 p.2.2).next p.2.1) :=
    compileMonomial.comp
      (builderNext.comp hcoefficient)
      (Primrec.fst.comp Primrec.snd)
  exact
    (appendMul.comp hcoefficient hmonomial).to₂.of_eq
      fun _ _ ↦ rfl

theorem appendNaturalTerm_primrec {n : ℕ} :
    Primrec₂ (appendNaturalTerm :
      ArithmeticBuilder → (ExponentCode n × ℕ) → ArithmeticBuilder) := by
  have hterm :
      Primrec
        (fun p : ArithmeticBuilder × (ExponentCode n × ℕ) ↦
          compileNaturalTermBuilder p.1.next p.2) :=
    compileNaturalTerm.comp
      (builderNext.comp Primrec.fst)
      Primrec.snd
  exact
    (appendAdd.comp Primrec.fst hterm).to₂.of_eq fun _ _ ↦ rfl

theorem compileNaturalPolynomial {n : ℕ} :
    Primrec₂
      (compileNaturalPolynomialBuilder :
        ℕ → NaturalPolynomialCode n → ArithmeticBuilder) := by
  have hstep :
      Primrec₂
        (fun (_ : ℕ × NaturalPolynomialCode n)
          (state :
            ArithmeticBuilder × (ExponentCode n × ℕ)) ↦
              appendNaturalTerm state.1 state.2) :=
    appendNaturalTerm_primrec.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.right)
  exact
    (Primrec.list_foldl
      Primrec.snd
      (startZero.comp Primrec.fst)
      hstep).to₂.of_eq fun _ _ ↦ rfl

theorem naturalPolynomialEquationCodeDirect_primrec {n : ℕ} :
    Primrec₂ (naturalPolynomialEquationCodeDirect :
      NaturalPolynomialCode n → NaturalPolynomialCode n →
        ℕ × List ArithmeticGateCode) := by
  let zeroBuilder := startZeroBuilder n
  have hleft :
      Primrec
        (fun p :
            NaturalPolynomialCode n × NaturalPolynomialCode n ↦
          compileNaturalPolynomialBuilder zeroBuilder.next p.1) :=
    compileNaturalPolynomial.comp
      (Primrec.const zeroBuilder.next)
      Primrec.fst
  have hright :
      Primrec
        (fun p :
            NaturalPolynomialCode n × NaturalPolynomialCode n ↦
          compileNaturalPolynomialBuilder
            (compileNaturalPolynomialBuilder
              zeroBuilder.next p.1).next p.2) :=
    compileNaturalPolynomial.comp
      (builderNext.comp hleft)
      Primrec.snd
  have hequationGate :
      Primrec
        (fun p :
            NaturalPolynomialCode n × NaturalPolynomialCode n ↦
          ArithmeticGateCode.add
            (compileNaturalPolynomialBuilder
              zeroBuilder.next p.1).output n
            (compileNaturalPolynomialBuilder
              (compileNaturalPolynomialBuilder
                zeroBuilder.next p.1).next p.2).output) :=
    gateAdd.comp
      (Primrec.pair
        (builderOutput.comp hleft)
        (Primrec.pair
          (Primrec.const n)
          (builderOutput.comp hright)))
  have hgates :
      Primrec
        (fun p :
            NaturalPolynomialCode n × NaturalPolynomialCode n ↦
          zeroBuilder.gates ++
              (compileNaturalPolynomialBuilder
                zeroBuilder.next p.1).gates ++
              (compileNaturalPolynomialBuilder
                (compileNaturalPolynomialBuilder
                  zeroBuilder.next p.1).next p.2).gates ++
            [ArithmeticGateCode.add
              (compileNaturalPolynomialBuilder
                zeroBuilder.next p.1).output n
              (compileNaturalPolynomialBuilder
                (compileNaturalPolynomialBuilder
                  zeroBuilder.next p.1).next p.2).output]) :=
    Primrec.list_append.comp
      (Primrec.list_append.comp
        (Primrec.list_append.comp
          (Primrec.const zeroBuilder.gates)
          (builderGates.comp hleft))
        (builderGates.comp hright))
      (singleton hequationGate)
  exact
    (Primrec.pair
      (builderNext.comp hright)
      hgates).to₂.of_eq fun _ _ ↦ rfl

theorem naturalPolynomialEquationCode_primrec {n : ℕ} :
    Primrec₂ (naturalPolynomialEquationCode :
      NaturalPolynomialCode n → NaturalPolynomialCode n →
        ℕ × List ArithmeticGateCode) :=
  naturalPolynomialEquationCodeDirect_primrec.of_eq
    naturalPolynomialEquationCodeDirect_eq

theorem positivePart {n : ℕ} :
    Primrec (IntegerPolynomialCode.positivePart :
      IntegerPolynomialCode n → NaturalPolynomialCode n) := by
  have hcoefficient :
      Primrec
        (fun t : ExponentCode n × SignedMagnitudeCode ↦
          if t.2.1 then 0 else t.2.2) :=
    (Primrec.cond
      (Primrec.fst.comp Primrec.snd)
      (Primrec.const 0)
      (Primrec.snd.comp Primrec.snd)).of_eq fun t ↦ by
        cases t.2.1 <;> rfl
  have hterm :
      Primrec₂
        (fun (_ : IntegerPolynomialCode n)
          (t : ExponentCode n × SignedMagnitudeCode) ↦
            (t.1, if t.2.1 then 0 else t.2.2)) :=
    Primrec.pair
      (Primrec.fst.comp₂ Primrec₂.right)
      (hcoefficient.comp₂ Primrec₂.right)
  exact
    (Primrec.list_map Primrec.id hterm).of_eq fun _ ↦ rfl

theorem negativePart {n : ℕ} :
    Primrec (IntegerPolynomialCode.negativePart :
      IntegerPolynomialCode n → NaturalPolynomialCode n) := by
  have hcoefficient :
      Primrec
        (fun t : ExponentCode n × SignedMagnitudeCode ↦
          if t.2.1 then t.2.2 else 0) :=
    (Primrec.cond
      (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)
      (Primrec.const 0)).of_eq fun t ↦ by
        cases t.2.1 <;> rfl
  have hterm :
      Primrec₂
        (fun (_ : IntegerPolynomialCode n)
          (t : ExponentCode n × SignedMagnitudeCode) ↦
            (t.1, if t.2.1 then t.2.2 else 0)) :=
    Primrec.pair
      (Primrec.fst.comp₂ Primrec₂.right)
      (hcoefficient.comp₂ Primrec₂.right)
  exact
    (Primrec.list_map Primrec.id hterm).of_eq fun _ ↦ rfl

end CompilerPrimrec

/-- Finite arithmetic circuit for a sparse natural polynomial equation. -/
def naturalPolynomialEquationCircuit
    (left right : NaturalPolynomialCode n) :=
  expressionEquationCircuit
    (NaturalArithmeticExpression.ofPolynomialForward left)
    (NaturalArithmeticExpression.ofPolynomialForward right)

/-- DQL compilation of a sparse natural polynomial equation. -/
def naturalPolynomialEquationDQL
    (left right : NaturalPolynomialCode n) :=
  expressionEquationDQL
    (NaturalArithmeticExpression.ofPolynomialForward left)
    (NaturalArithmeticExpression.ofPolynomialForward right)

theorem naturalPolynomialEquationDQL_solvable_iff
    (left right : NaturalPolynomialCode n) :
    (naturalPolynomialEquationDQL left right).Solvable ↔
      ∃ x : Fin n → ℕ,
        NaturalPolynomialCode.eval left x =
          NaturalPolynomialCode.eval right x := by
  simpa [naturalPolynomialEquationDQL] using
    expressionEquationDQL_solvable_iff
      (NaturalArithmeticExpression.ofPolynomialForward left)
      (NaturalArithmeticExpression.ofPolynomialForward right)

/-- Raw compiler code for the integer equation `p(x)=0`. -/
def integerPolynomialEquationCode (p : IntegerPolynomialCode n) :
    ℕ × List ArithmeticGateCode :=
  naturalPolynomialEquationCode
    (IntegerPolynomialCode.positivePart p)
    (IntegerPolynomialCode.negativePart p)

/-- The complete sparse-integer-polynomial to raw-circuit compiler is
primitive recursive (and hence total computable). -/
theorem integerPolynomialEquationCode_primrec :
    Primrec (integerPolynomialEquationCode :
      IntegerPolynomialCode n →
        ℕ × List ArithmeticGateCode) := by
  exact
    CompilerPrimrec.naturalPolynomialEquationCode_primrec.comp
      CompilerPrimrec.positivePart
      CompilerPrimrec.negativePart

theorem integerPolynomialEquationCode_computable :
    Computable (integerPolynomialEquationCode :
      IntegerPolynomialCode n →
        ℕ × List ArithmeticGateCode) :=
  integerPolynomialEquationCode_primrec.to_comp

/-- Finite arithmetic circuit for `p(x)=0` over natural witnesses. -/
def integerPolynomialEquationCircuit (p : IntegerPolynomialCode n) :=
  naturalPolynomialEquationCircuit
    (IntegerPolynomialCode.positivePart p)
    (IntegerPolynomialCode.negativePart p)

/-- DQL compilation of the integer equation `p(x)=0`. -/
def integerPolynomialEquationDQL (p : IntegerPolynomialCode n) :=
  naturalPolynomialEquationDQL
    (IntegerPolynomialCode.positivePart p)
    (IntegerPolynomialCode.negativePart p)

/-- Main exact reduction theorem for sparse integer polynomial equations. -/
theorem integerPolynomialEquationDQL_solvable_iff
    (p : IntegerPolynomialCode n) :
    (integerPolynomialEquationDQL p).Solvable ↔
      ∃ x : Fin n → ℕ, IntegerPolynomialCode.eval p x = 0 := by
  rw [integerPolynomialEquationDQL,
    naturalPolynomialEquationDQL_solvable_iff]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x,
      (IntegerPolynomialCode.positivePart_eq_negativePart_iff p x).mp
        hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x,
      (IntegerPolynomialCode.positivePart_eq_negativePart_iff p x).mpr
        hx⟩

end PolynomialGateCompiler

end HGAS
