import HGAS.Arithmetic.PolynomialGateCompiler
import Mathlib.Tactic

/-!
# Input-preserving semantics of compiled expression circuits

`PolynomialGateCompiler.expressionEquationCircuit_solvable_iff` says
that the circuit compiled from `left = right` is satisfiable exactly when
the source equation has a solution.  For the sparse-cipher construction
we need a slightly sharper interface: the first `n` circuit registers
must retain a *prescribed* input tuple.

This module proves that input-preserving statement in two transparent
steps.

1. At the raw, unbounded-register level, a satisfying forward circuit
   computes the two expressions from its first `n` registers.
2. Conversely, any prescribed tuple satisfying the source equation
   extends to a complete circuit assignment without changing those
   registers.

The final theorem, `expressionEquationCircuit_with_inputs_iff`, packages
the exact finite-circuit equivalence.  It is useful independently of the
sparse-radix encoding.
-/

namespace HGAS

namespace PolynomialGateCompiler

variable {n : ℕ}

/-- Every source input register lies strictly below the register count of
the compiled equation circuit. -/
theorem expressionEquation_input_lt_variableCount
    (left right : NaturalArithmeticExpression n) :
    n < expressionEquationVariableCount left right := by
  simp [expressionEquationVariableCount, rightFragment, rightStart,
    leftFragment, ArithmeticFragment.next]
  omega

/-- The finite circuit register occupied by source input `i`.  The
compiler deliberately leaves the first `n` registers untouched. -/
def expressionEquationInput
    (left right : NaturalArithmeticExpression n) (i : Fin n) :
    Fin (expressionEquationVariableCount left right) :=
  ⟨i.1,
    i.isLt.trans
      (expressionEquation_input_lt_variableCount left right)⟩

@[simp]
theorem expressionEquationInput_val
    (left right : NaturalArithmeticExpression n) (i : Fin n) :
    (expressionEquationInput left right i).1 = i.1 :=
  rfl

/-! ## Raw-register semantics -/

/-- A satisfying raw equation circuit forces equality of the source
expressions evaluated at its first `n` registers. -/
theorem expressionEquation_raw_holds_implies_eval_eq
    (left right : NaturalArithmeticExpression n)
    (value : ℕ → ℕ)
    (hvalue :
      RawArithmeticCircuitHolds
        (expressionEquationGateCodes left right) value) :
    left.eval (fun i => value i.1) =
      right.eval (fun i => value i.1) := by
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
    intro gate hgate
    exact hprogram gate (by
      simp only [expressionEquationProgram, List.mem_cons,
        List.mem_append]
      exact Or.inr (Or.inl hgate))
  have hright :
      RawArithmeticCircuitHolds
        (rightFragment left right).gates value := by
    intro gate hgate
    exact hprogram gate (by
      simp only [expressionEquationProgram, List.mem_cons,
        List.mem_append]
      exact Or.inr (Or.inr hgate))
  have hleftEval :=
    NaturalArithmeticExpression.compileFrom_output_eq_eval
      left (n + 1) value hleft
  have hrightEval :=
    NaturalArithmeticExpression.compileFrom_output_eq_eval
      right (rightStart left) value hright
  rw [← hleftEval, ← hrightEval]
  have hequation := htail.1
  simpa [expressionEquationGate, ArithmeticGateCode.Holds,
    ArithmeticGateCode.add, ArithmeticGateCode.tag,
    ArithmeticGateCode.x, ArithmeticGateCode.y,
    ArithmeticGateCode.z, hzero] using hequation

/-- A prescribed source tuple satisfying `left = right` extends to a
complete raw circuit assignment, while the first `n` registers remain
literally equal to that tuple. -/
theorem exists_expressionEquation_raw_holds_agrees
    (left right : NaturalArithmeticExpression n)
    (input : Fin n → ℕ)
    (hequation : left.eval input = right.eval input) :
    ∃ value : ℕ → ℕ,
      RawArithmeticCircuitHolds
        (expressionEquationGateCodes left right) value ∧
      ∀ i : Fin n, value i.1 = input i := by
  obtain ⟨value, hprogram, hagrees⟩ :=
    exists_rawArithmeticCircuitHolds_of_forward
      (expressionEquationProgram left right) n
      (inputExtension input)
      (expressionEquationProgram_forward left right)
  have hinputs :
      (fun i : Fin n => value i.1) = input := by
    funext i
    rw [hagrees i.1 i.isLt]
    exact inputExtension_apply input i
  have hzero :
      value n = 0 := by
    exact hprogram (ArithmeticGateCode.zero n) (by
      simp [expressionEquationProgram])
  have hleft :
      RawArithmeticCircuitHolds
        (leftFragment left).gates value := by
    intro gate hgate
    exact hprogram gate (by
      simp only [expressionEquationProgram, List.mem_cons,
        List.mem_append]
      exact Or.inr (Or.inl hgate))
  have hright :
      RawArithmeticCircuitHolds
        (rightFragment left right).gates value := by
    intro gate hgate
    exact hprogram gate (by
      simp only [expressionEquationProgram, List.mem_cons,
        List.mem_append]
      exact Or.inr (Or.inr hgate))
  have hleftEval :=
    NaturalArithmeticExpression.compileFrom_output_eq_eval
      left (n + 1) value hleft
  have hrightEval :=
    NaturalArithmeticExpression.compileFrom_output_eq_eval
      right (rightStart left) value hright
  change
    value (leftFragment left).output =
      NaturalArithmeticExpression.eval
        (fun i => value i.1) left at hleftEval
  change
    value (rightFragment left right).output =
      NaturalArithmeticExpression.eval
        (fun i => value i.1) right at hrightEval
  have hgate :
      ArithmeticGateCode.Holds
        (expressionEquationGate left right) value := by
    simp only [expressionEquationGate, ArithmeticGateCode.Holds,
      ArithmeticGateCode.add, ArithmeticGateCode.tag,
      ArithmeticGateCode.x, ArithmeticGateCode.y,
      ArithmeticGateCode.z]
    rw [hzero, add_zero, hleftEval, hrightEval, hinputs]
    exact hequation
  refine ⟨value, ?_, ?_⟩
  · rw [expressionEquationGateCodes,
      rawArithmeticCircuitHolds_append]
    exact ⟨hprogram,
      (rawArithmeticCircuitHolds_cons
        (expressionEquationGate left right) [] value).mpr
          ⟨hgate, rawArithmeticCircuitHolds_nil value⟩⟩
  · intro i
    exact congrFun hinputs i

/-! ## Finite-register semantics -/

/-- A satisfying finite circuit computes equal source expressions from
the explicitly identified input registers. -/
theorem expressionEquationCircuit_holds_implies_eval_eq
    (left right : NaturalArithmeticExpression n)
    (value :
      Fin (expressionEquationVariableCount left right) → ℕ)
    (hvalue :
      GateDQLCompiler.NaturalCircuitHolds
        (expressionEquationCircuit left right) value) :
    left.eval
        (fun i => value (expressionEquationInput left right i)) =
      right.eval
        (fun i => value (expressionEquationInput left right i)) := by
  let bound := expressionEquationVariableCount left right
  have hpositive : 0 < bound :=
    expressionEquationVariableCount_positive left right
  have hbounded :
      ∀ gate ∈ expressionEquationGateCodes left right,
        ArithmeticGateCode.BoundedBy gate bound :=
    expressionEquationGateCodes_bounded left right
  have hraw :
      RawArithmeticCircuitHolds
        (expressionEquationGateCodes left right)
        (ArithmeticGateCode.liftFiniteValue value) :=
    (naturalCircuitHolds_realize_iff
      hpositive (expressionEquationGateCodes left right)
      hbounded value).mp hvalue
  have heq :=
    expressionEquation_raw_holds_implies_eval_eq
      left right
      (ArithmeticGateCode.liftFiniteValue value) hraw
  have hinputs :
      (fun i : Fin n =>
        ArithmeticGateCode.liftFiniteValue value i.1) =
      (fun i : Fin n =>
        value (expressionEquationInput left right i)) := by
    funext i
    rw [ArithmeticGateCode.liftFiniteValue_of_lt value
      (i.isLt.trans
        (expressionEquation_input_lt_variableCount left right))]
    rfl
  rwa [hinputs] at heq

/-- A prescribed tuple satisfying the source equation extends to a
satisfying assignment of the finite circuit and is unchanged in every
input register. -/
theorem exists_expressionEquationCircuit_holds_agrees
    (left right : NaturalArithmeticExpression n)
    (input : Fin n → ℕ)
    (hequation : left.eval input = right.eval input) :
    ∃ value :
        Fin (expressionEquationVariableCount left right) → ℕ,
      GateDQLCompiler.NaturalCircuitHolds
        (expressionEquationCircuit left right) value ∧
      ∀ i : Fin n,
        value (expressionEquationInput left right i) = input i := by
  obtain ⟨rawValue, hraw, hrawInputs⟩ :=
    exists_expressionEquation_raw_holds_agrees
      left right input hequation
  let bound := expressionEquationVariableCount left right
  let value : Fin bound → ℕ := fun i => rawValue i.1
  have hpositive : 0 < bound :=
    expressionEquationVariableCount_positive left right
  have hbounded :
      ∀ gate ∈ expressionEquationGateCodes left right,
        ArithmeticGateCode.BoundedBy gate bound :=
    expressionEquationGateCodes_bounded left right
  have hagrees :
      ∀ i, i < bound →
        ArithmeticGateCode.liftFiniteValue value i =
          rawValue i := by
    intro i hi
    simp [ArithmeticGateCode.liftFiniteValue, value, hi]
  have hlifted :
      RawArithmeticCircuitHolds
        (expressionEquationGateCodes left right)
        (ArithmeticGateCode.liftFiniteValue value) := by
    intro gate hgate
    exact
      (ArithmeticGateCode.holds_congr_of_boundedBy
        gate (hbounded gate hgate) hagrees).mpr
          (hraw gate hgate)
  refine ⟨value, ?_, ?_⟩
  · exact
      (naturalCircuitHolds_realize_iff
        hpositive (expressionEquationGateCodes left right)
        hbounded value).mpr hlifted
  · intro i
    exact hrawInputs i

/-- Exact input-preserving specification of the compiled equation
circuit.  This is stronger than bare solvability: the source tuple appears
in known, reusable finite registers. -/
theorem expressionEquationCircuit_with_inputs_iff
    (left right : NaturalArithmeticExpression n)
    (input : Fin n → ℕ) :
    (∃ value :
        Fin (expressionEquationVariableCount left right) → ℕ,
        GateDQLCompiler.NaturalCircuitHolds
          (expressionEquationCircuit left right) value ∧
        ∀ i : Fin n,
          value (expressionEquationInput left right i) = input i) ↔
      left.eval input = right.eval input := by
  constructor
  · rintro ⟨value, hvalue, hinput⟩
    have heq :=
      expressionEquationCircuit_holds_implies_eval_eq
        left right value hvalue
    simpa only [hinput] using heq
  · intro heq
    exact
      exists_expressionEquationCircuit_holds_agrees
        left right input heq

end PolynomialGateCompiler

end HGAS
