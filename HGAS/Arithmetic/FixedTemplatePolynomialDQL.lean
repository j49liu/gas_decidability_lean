import HGAS.Arithmetic.EffectivePolynomialSolvability
import HGAS.Arithmetic.FixedCoordinateDQL
import HGAS.Arithmetic.FiniteRepresentationDQL
import Mathlib.Tactic

/-!
# A fixed-resource sparse-polynomial-to-DQL compiler

The earlier polynomial compiler expands a coefficient `c` as a unary
arithmetic expression.  Consequently its number of registers depends on
the magnitude of `c`.  That is suitable for variable-resource
enumerability but not for a reduction into one fixed DQL type.

Here a fixed sparse polynomial template gets one coefficient register per
term.  The monomial circuit depends only on the exponent vectors.  At a
parameter value, the coefficient registers are fixed by the RHS rows from
`FixedCoordinateDQL`; changing the parameter changes coefficients of the
system, but never its two dimensions.
-/

namespace HGAS

open scoped BigOperators

namespace FixedTemplatePolynomialDQL

variable {m k : ℕ}

/-- Inputs of the fixed arithmetic circuit consist of the natural witness
tuple followed by one magnitude register for each sparse term. -/
abbrev templateInputCount
    (polynomial : IntegerPolynomialCode (m + k)) : ℕ :=
  k + polynomial.length

/-- Witness coordinate in the fixed circuit input block. -/
def witnessInput
    (polynomial : IntegerPolynomialCode (m + k))
    (i : Fin k) : Fin (templateInputCount polynomial) :=
  finSumFinEquiv (Sum.inl i)

/-- Magnitude coordinate belonging to one sparse term. -/
def coefficientInput
    (polynomial : IntegerPolynomialCode (m + k))
    (i : Fin polynomial.length) :
    Fin (templateInputCount polynomial) :=
  finSumFinEquiv (Sum.inr i)

/-- Specialized nonnegative magnitude of a template coefficient. -/
def specializedMagnitude
    (polynomial : IntegerPolynomialCode (m + k))
    (parameters : Fin m → ℕ)
    (i : Fin polynomial.length) : ℕ :=
  (polynomial.get i).2.2 *
    IntegerPolynomialCode.parameterFactor parameters
      (polynomial.get i).1

/-- Assignment to the fixed circuit inputs. -/
def templateInputAssignment
    (polynomial : IntegerPolynomialCode (m + k))
    (parameters : Fin m → ℕ)
    (witnesses : Fin k → ℕ) :
    Fin (templateInputCount polynomial) → ℕ :=
  Fin.addCases witnesses
    (specializedMagnitude polynomial parameters)

@[simp]
theorem templateInputAssignment_witness
    (polynomial : IntegerPolynomialCode (m + k))
    (parameters : Fin m → ℕ)
    (witnesses : Fin k → ℕ) (i : Fin k) :
    templateInputAssignment polynomial parameters witnesses
        (witnessInput polynomial i) =
      witnesses i := by
  simp [templateInputAssignment, witnessInput]

@[simp]
theorem templateInputAssignment_coefficient
    (polynomial : IntegerPolynomialCode (m + k))
    (parameters : Fin m → ℕ)
    (witnesses : Fin k → ℕ) (i : Fin polynomial.length) :
    templateInputAssignment polynomial parameters witnesses
        (coefficientInput polynomial i) =
      specializedMagnitude polynomial parameters i := by
  simp [templateInputAssignment, coefficientInput]

/-- A monomial expression using only witness inputs. -/
def templateMonomial
    (polynomial : IntegerPolynomialCode (m + k))
    (exponent : ExponentCode k) :
    NaturalArithmeticExpression (templateInputCount polynomial) :=
  (List.ofFn fun i ↦
    NaturalArithmeticExpression.power
      (.input (witnessInput polynomial i)) (exponent i)).foldr
        .mul .one

private theorem eval_foldr_mul
    (x : Fin n → ℕ)
    (expressions : List (NaturalArithmeticExpression n)) :
    NaturalArithmeticExpression.eval x
        (expressions.foldr .mul .one) =
      (expressions.map
        (NaturalArithmeticExpression.eval x)).prod := by
  induction expressions with
  | nil => rfl
  | cons expression expressions ih =>
      simp [NaturalArithmeticExpression.eval, ih]

@[simp]
theorem eval_templateMonomial
    (polynomial : IntegerPolynomialCode (m + k))
    (parameters : Fin m → ℕ)
    (witnesses : Fin k → ℕ)
    (exponent : ExponentCode k) :
    NaturalArithmeticExpression.eval
        (templateInputAssignment polynomial parameters witnesses)
        (templateMonomial polynomial exponent) =
      NaturalPolynomialCode.evalMonomial exponent witnesses := by
  rw [templateMonomial, eval_foldr_mul]
  unfold NaturalPolynomialCode.evalMonomial
  rw [← List.ofFn_comp']
  congr 1
  apply congrArg List.ofFn
  funext i
  simp [NaturalArithmeticExpression.eval]

/-- The term expression multiplies a coefficient-magnitude input by the
corresponding witness monomial. -/
def templateTerm
    (polynomial : IntegerPolynomialCode (m + k))
    (i : Fin polynomial.length) :
    NaturalArithmeticExpression (templateInputCount polynomial) :=
  .mul (.input (coefficientInput polynomial i))
    (templateMonomial polynomial
      (IntegerPolynomialCode.witnessExponent
        (polynomial.get i).1))

@[simp]
theorem eval_templateTerm
    (polynomial : IntegerPolynomialCode (m + k))
    (parameters : Fin m → ℕ)
    (witnesses : Fin k → ℕ)
    (i : Fin polynomial.length) :
    NaturalArithmeticExpression.eval
        (templateInputAssignment polynomial parameters witnesses)
        (templateTerm polynomial i) =
      specializedMagnitude polynomial parameters i *
        NaturalPolynomialCode.evalMonomial
          (IntegerPolynomialCode.witnessExponent
            (polynomial.get i).1) witnesses := by
  simp [templateTerm, NaturalArithmeticExpression.eval]

/-- Nonnegative side of the specialized integer equation.  The original
sign bit is part of the fixed template. -/
def positiveExpression
    (polynomial : IntegerPolynomialCode (m + k)) :
    NaturalArithmeticExpression (templateInputCount polynomial) :=
  (List.ofFn fun i ↦
    if (polynomial.get i).2.1 then .zero
    else templateTerm polynomial i).foldr .add .zero

/-- Nonpositive side of the specialized integer equation. -/
def negativeExpression
    (polynomial : IntegerPolynomialCode (m + k)) :
    NaturalArithmeticExpression (templateInputCount polynomial) :=
  (List.ofFn fun i ↦
    if (polynomial.get i).2.1 then templateTerm polynomial i
    else .zero).foldr .add .zero

private theorem eval_foldr_add
    (x : Fin n → ℕ)
    (expressions : List (NaturalArithmeticExpression n)) :
    NaturalArithmeticExpression.eval x
        (expressions.foldr .add .zero) =
      (expressions.map
        (NaturalArithmeticExpression.eval x)).sum := by
  induction expressions with
  | nil => rfl
  | cons expression expressions ih =>
      simp [NaturalArithmeticExpression.eval, ih]

theorem eval_positiveExpression
    (polynomial : IntegerPolynomialCode (m + k))
    (parameters : Fin m → ℕ)
    (witnesses : Fin k → ℕ) :
    NaturalArithmeticExpression.eval
        (templateInputAssignment polynomial parameters witnesses)
        (positiveExpression polynomial) =
      ∑ i : Fin polynomial.length,
        if (polynomial.get i).2.1 then 0
        else specializedMagnitude polynomial parameters i *
          NaturalPolynomialCode.evalMonomial
            (IntegerPolynomialCode.witnessExponent
              (polynomial.get i).1) witnesses := by
  rw [positiveExpression, eval_foldr_add]
  simp only [List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp_all [NaturalArithmeticExpression.eval]

theorem eval_negativeExpression
    (polynomial : IntegerPolynomialCode (m + k))
    (parameters : Fin m → ℕ)
    (witnesses : Fin k → ℕ) :
    NaturalArithmeticExpression.eval
        (templateInputAssignment polynomial parameters witnesses)
        (negativeExpression polynomial) =
      ∑ i : Fin polynomial.length,
        if (polynomial.get i).2.1 then
          specializedMagnitude polynomial parameters i *
            NaturalPolynomialCode.evalMonomial
              (IntegerPolynomialCode.witnessExponent
                (polynomial.get i).1) witnesses
        else 0 := by
  rw [negativeExpression, eval_foldr_add]
  simp only [List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp_all [NaturalArithmeticExpression.eval]

/-- The two fixed expressions are equal exactly when the original
parameterized polynomial vanishes. -/
theorem expressions_equal_iff
    (polynomial : IntegerPolynomialCode (m + k))
    (parameters : Fin m → ℕ)
    (witnesses : Fin k → ℕ) :
    NaturalArithmeticExpression.eval
        (templateInputAssignment polynomial parameters witnesses)
        (positiveExpression polynomial) =
      NaturalArithmeticExpression.eval
        (templateInputAssignment polynomial parameters witnesses)
        (negativeExpression polynomial) ↔
      IntegerPolynomialCode.eval polynomial
        (Fin.addCases parameters witnesses) = 0 := by
  rw [eval_positiveExpression, eval_negativeExpression]
  have hidentity :
      ((∑ i : Fin polynomial.length,
        if (polynomial.get i).2.1 then 0
        else specializedMagnitude polynomial parameters i *
          NaturalPolynomialCode.evalMonomial
            (IntegerPolynomialCode.witnessExponent
              (polynomial.get i).1) witnesses : ℕ) : ℤ) -
        ((∑ i : Fin polynomial.length,
          if (polynomial.get i).2.1 then
            specializedMagnitude polynomial parameters i *
              NaturalPolynomialCode.evalMonomial
                (IntegerPolynomialCode.witnessExponent
                  (polynomial.get i).1) witnesses
          else 0 : ℕ) : ℤ) =
        IntegerPolynomialCode.eval polynomial
          (Fin.addCases parameters witnesses) := by
    rw [IntegerPolynomialCode.eval]
    calc
      ((↑(∑ i : Fin polynomial.length,
            if (polynomial.get i).2.1 then 0
            else specializedMagnitude polynomial parameters i *
              NaturalPolynomialCode.evalMonomial
                (IntegerPolynomialCode.witnessExponent
                  (polynomial.get i).1) witnesses) : ℤ) -
          ↑(∑ i : Fin polynomial.length,
            if (polynomial.get i).2.1 then
              specializedMagnitude polynomial parameters i *
                NaturalPolynomialCode.evalMonomial
                  (IntegerPolynomialCode.witnessExponent
                    (polynomial.get i).1) witnesses
            else 0)) =
          ∑ i : Fin polynomial.length,
            (Int.ofNat
                (if (polynomial.get i).2.1 then 0
                else specializedMagnitude polynomial parameters i *
                  NaturalPolynomialCode.evalMonomial
                    (IntegerPolynomialCode.witnessExponent
                      (polynomial.get i).1) witnesses) -
              Int.ofNat
                (if (polynomial.get i).2.1 then
                  specializedMagnitude polynomial parameters i *
                    NaturalPolynomialCode.evalMonomial
                      (IntegerPolynomialCode.witnessExponent
                        (polynomial.get i).1) witnesses
                else 0)) := by
            rw [Nat.cast_sum, Nat.cast_sum,
              ← Finset.sum_sub_distrib]
            rfl
      _ = ∑ i : Fin polynomial.length,
          SignedMagnitudeCode.decode (polynomial.get i).2 *
            (NaturalPolynomialCode.evalMonomial
              (polynomial.get i).1
              (Fin.addCases parameters witnesses) : ℤ) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [IntegerPolynomialCode.evalMonomial_addCases]
        simp only [specializedMagnitude, SignedMagnitudeCode.decode]
        by_cases hsign : (polynomial.get i).2.1 = true
        · simp only [if_pos hsign]
          simp [Nat.cast_mul, mul_assoc]
        · simp only [if_neg hsign]
          simp [Nat.cast_mul, mul_assoc]
      _ =
          (List.ofFn fun i : Fin polynomial.length ↦
            SignedMagnitudeCode.decode (polynomial.get i).2 *
              (NaturalPolynomialCode.evalMonomial
                (polynomial.get i).1
                (Fin.addCases parameters witnesses) : ℤ)).sum := by
        rw [List.sum_ofFn]
      _ =
          (polynomial.map fun t ↦
            SignedMagnitudeCode.decode t.2 *
              (NaturalPolynomialCode.evalMonomial t.1
                (Fin.addCases parameters witnesses) : ℤ)).sum := by
        apply congrArg List.sum
        exact
          (List.ofFn_getElem_eq_map polynomial
            (fun t ↦
              SignedMagnitudeCode.decode t.2 *
                (NaturalPolynomialCode.evalMonomial t.1
                  (Fin.addCases parameters witnesses) : ℤ)))
  rw [← hidentity]
  constructor
  · intro h
    rw [h]
    ring
  · intro h
    have hcast :
        ((∑ i : Fin polynomial.length,
          if (polynomial.get i).2.1 then 0
          else specializedMagnitude polynomial parameters i *
            NaturalPolynomialCode.evalMonomial
              (IntegerPolynomialCode.witnessExponent
                (polynomial.get i).1) witnesses : ℕ) : ℤ) =
          ((∑ i : Fin polynomial.length,
            if (polynomial.get i).2.1 then
              specializedMagnitude polynomial parameters i *
                NaturalPolynomialCode.evalMonomial
                  (IntegerPolynomialCode.witnessExponent
                    (polynomial.get i).1) witnesses
            else 0 : ℕ) : ℤ) :=
      sub_eq_zero.mp h
    exact_mod_cast hcast

/-! ## Expression circuits with prescribed input registers

The generic expression compiler previously exposed only an existential
solvability theorem.  For the fixed-template construction we need the
slightly stronger fact that its first `n` registers retain the chosen
input tuple.  This formulation is useful independently of polynomial
templates. -/

/-- The original input coordinate inside the register file of an
expression-equation circuit. -/
def expressionInputRegister
    (left right : NaturalArithmeticExpression n) (i : Fin n) :
    Fin (PolynomialGateCompiler.expressionEquationVariableCount
      left right) :=
  ⟨i.1, by
    have hlength :=
      PolynomialGateCompiler.expressionEquationProgram_length left right
    omega⟩

/-- A finite expression-equation circuit has a satisfying assignment
extending exactly `x` iff the two expressions agree at `x`. -/
theorem expressionEquationCircuit_holds_with_inputs_iff
    (left right : NaturalArithmeticExpression n)
    (x : Fin n → ℕ) :
    (∃ value :
        Fin (PolynomialGateCompiler.expressionEquationVariableCount
          left right) → ℕ,
        GateDQLCompiler.NaturalCircuitHolds
          (PolynomialGateCompiler.expressionEquationCircuit left right)
          value ∧
        ∀ i, value (expressionInputRegister left right i) = x i) ↔
      left.eval x = right.eval x := by
  let bound :=
    PolynomialGateCompiler.expressionEquationVariableCount left right
  have hpositive : 0 < bound :=
    PolynomialGateCompiler.expressionEquationVariableCount_positive
      left right
  have hbounded :
      ∀ g ∈
          PolynomialGateCompiler.expressionEquationGateCodes left right,
        ArithmeticGateCode.BoundedBy g bound :=
    PolynomialGateCompiler.expressionEquationGateCodes_bounded left right
  constructor
  · rintro ⟨value, hvalue, hinputs⟩
    have hraw :
        RawArithmeticCircuitHolds
          (PolynomialGateCompiler.expressionEquationGateCodes left right)
          (ArithmeticGateCode.liftFiniteValue value) :=
      (naturalCircuitHolds_realize_iff hpositive
        (PolynomialGateCompiler.expressionEquationGateCodes left right)
        hbounded value).mp hvalue
    have hparts :=
      (rawArithmeticCircuitHolds_append
        (PolynomialGateCompiler.expressionEquationProgram left right)
        [PolynomialGateCompiler.expressionEquationGate left right]
        (ArithmeticGateCode.liftFiniteValue value)).mp hraw
    have hprogram := hparts.1
    have htail :=
      (rawArithmeticCircuitHolds_cons
        (PolynomialGateCompiler.expressionEquationGate left right) []
        (ArithmeticGateCode.liftFiniteValue value)).mp hparts.2
    have hzero :
        ArithmeticGateCode.liftFiniteValue value n = 0 := by
      exact hprogram (ArithmeticGateCode.zero n) (by
        simp [PolynomialGateCompiler.expressionEquationProgram])
    have hleft :
        RawArithmeticCircuitHolds
          (PolynomialGateCompiler.leftFragment left).gates
          (ArithmeticGateCode.liftFiniteValue value) := by
      intro g hg
      exact hprogram g (by
        simp only [
          PolynomialGateCompiler.expressionEquationProgram,
          List.mem_cons, List.mem_append]
        exact Or.inr (Or.inl hg))
    have hright :
        RawArithmeticCircuitHolds
          (PolynomialGateCompiler.rightFragment left right).gates
          (ArithmeticGateCode.liftFiniteValue value) := by
      intro g hg
      exact hprogram g (by
        simp only [
          PolynomialGateCompiler.expressionEquationProgram,
          List.mem_cons, List.mem_append]
        exact Or.inr (Or.inr hg))
    have hleftEval :=
      NaturalArithmeticExpression.compileFrom_output_eq_eval
        left (n + 1) (ArithmeticGateCode.liftFiniteValue value) hleft
    have hrightEval :=
      NaturalArithmeticExpression.compileFrom_output_eq_eval
        right (PolynomialGateCompiler.rightStart left)
        (ArithmeticGateCode.liftFiniteValue value) hright
    have hinputTuple :
        (fun i : Fin n ↦
          ArithmeticGateCode.liftFiniteValue value i.1) = x := by
      funext i
      have hi :
          i.1 <
            PolynomialGateCompiler.expressionEquationVariableCount
              left right :=
        (expressionInputRegister left right i).isLt
      rw [ArithmeticGateCode.liftFiniteValue_of_lt value hi]
      simpa [expressionInputRegister] using hinputs i
    change
      NaturalArithmeticExpression.eval x left =
        NaturalArithmeticExpression.eval x right
    rw [← hinputTuple, ← hleftEval, ← hrightEval]
    have hequation := htail.1
    simpa [
      PolynomialGateCompiler.expressionEquationGate,
      ArithmeticGateCode.Holds, ArithmeticGateCode.add,
      ArithmeticGateCode.tag, ArithmeticGateCode.x,
      ArithmeticGateCode.y, ArithmeticGateCode.z, hzero] using
        hequation
  · intro hequation
    obtain ⟨rawValue, hprogram, hagrees⟩ :=
      exists_rawArithmeticCircuitHolds_of_forward
        (PolynomialGateCompiler.expressionEquationProgram left right) n
        (PolynomialGateCompiler.inputExtension x)
        (PolynomialGateCompiler.expressionEquationProgram_forward
          left right)
    have hinputTuple :
        (fun i : Fin n ↦ rawValue i.1) = x := by
      funext i
      rw [hagrees i.1 i.isLt]
      exact PolynomialGateCompiler.inputExtension_apply x i
    have hzero :
        rawValue n = 0 := by
      exact hprogram (ArithmeticGateCode.zero n) (by
        simp [PolynomialGateCompiler.expressionEquationProgram])
    have hleft :
        RawArithmeticCircuitHolds
          (PolynomialGateCompiler.leftFragment left).gates rawValue := by
      intro g hg
      exact hprogram g (by
        simp only [
          PolynomialGateCompiler.expressionEquationProgram,
          List.mem_cons, List.mem_append]
        exact Or.inr (Or.inl hg))
    have hright :
        RawArithmeticCircuitHolds
          (PolynomialGateCompiler.rightFragment left right).gates
          rawValue := by
      intro g hg
      exact hprogram g (by
        simp only [
          PolynomialGateCompiler.expressionEquationProgram,
          List.mem_cons, List.mem_append]
        exact Or.inr (Or.inr hg))
    have hleftEval :=
      NaturalArithmeticExpression.compileFrom_output_eq_eval
        left (n + 1) rawValue hleft
    have hrightEval :=
      NaturalArithmeticExpression.compileFrom_output_eq_eval
        right (PolynomialGateCompiler.rightStart left) rawValue hright
    change
      rawValue (PolynomialGateCompiler.leftFragment left).output =
        NaturalArithmeticExpression.eval
          (fun i : Fin n ↦ rawValue i.1) left at hleftEval
    change
      rawValue
          (PolynomialGateCompiler.rightFragment left right).output =
        NaturalArithmeticExpression.eval
          (fun i : Fin n ↦ rawValue i.1) right at hrightEval
    have hgate :
        ArithmeticGateCode.Holds
          (PolynomialGateCompiler.expressionEquationGate left right)
          rawValue := by
      simp only [
        PolynomialGateCompiler.expressionEquationGate,
        ArithmeticGateCode.Holds, ArithmeticGateCode.add,
        ArithmeticGateCode.tag, ArithmeticGateCode.x,
        ArithmeticGateCode.y, ArithmeticGateCode.z]
      rw [hzero, add_zero, hleftEval, hrightEval, hinputTuple]
      exact hequation
    have hraw :
        RawArithmeticCircuitHolds
          (PolynomialGateCompiler.expressionEquationGateCodes left right)
          rawValue := by
      rw [PolynomialGateCompiler.expressionEquationGateCodes,
        rawArithmeticCircuitHolds_append]
      exact ⟨hprogram,
        (rawArithmeticCircuitHolds_cons
          (PolynomialGateCompiler.expressionEquationGate left right) []
          rawValue).mpr
            ⟨hgate, rawArithmeticCircuitHolds_nil rawValue⟩⟩
    let value : Fin bound → ℕ := fun i ↦ rawValue i.1
    have hliftAgrees :
        ∀ i, i < bound →
          ArithmeticGateCode.liftFiniteValue value i = rawValue i := by
      intro i hi
      simp [ArithmeticGateCode.liftFiniteValue, value, hi]
    have hlifted :
        RawArithmeticCircuitHolds
          (PolynomialGateCompiler.expressionEquationGateCodes left right)
          (ArithmeticGateCode.liftFiniteValue value) := by
      intro g hg
      exact
        (ArithmeticGateCode.holds_congr_of_boundedBy
          g (hbounded g hg) hliftAgrees).mpr (hraw g hg)
    refine ⟨value, ?_, ?_⟩
    · exact
        (naturalCircuitHolds_realize_iff hpositive
          (PolynomialGateCompiler.expressionEquationGateCodes left right)
          hbounded value).mpr hlifted
    · intro i
      change rawValue i.1 = x i
      exact congrFun hinputTuple i

/-! ## Fixed-resource DQL specialization -/

/-- Register count of the circuit attached to a fixed sparse template. -/
abbrev templateCircuitVariableCount
    (polynomial : IntegerPolynomialCode (m + k)) : ℕ :=
  PolynomialGateCompiler.expressionEquationVariableCount
    (positiveExpression polynomial) (negativeExpression polynomial)

/-- The arithmetic circuit attached to a fixed sparse template. -/
abbrev templateCircuit
    (polynomial : IntegerPolynomialCode (m + k)) :
    List (ArithmeticGate (templateCircuitVariableCount polynomial)) :=
  PolynomialGateCompiler.expressionEquationCircuit
    (positiveExpression polynomial) (negativeExpression polynomial)

/-- Equation count before coefficient coordinates are fixed. -/
abbrev templateBaseEquationCount
    (polynomial : IntegerPolynomialCode (m + k)) : ℕ :=
  (templateCircuit polynomial).length * 2 +
    templateCircuitVariableCount polynomial

/-- Variable count of the final fixed-resource DQL system. -/
abbrev templateVariableCount
    (polynomial : IntegerPolynomialCode (m + k)) : ℕ :=
  (templateCircuitVariableCount polynomial +
      (templateCircuit polynomial).length) +
    templateCircuitVariableCount polynomial * 4

/-- Equation count after one RHS row is added per sparse term. -/
abbrev templateEquationCount
    (polynomial : IntegerPolynomialCode (m + k)) : ℕ :=
  templateBaseEquationCount polynomial + polynomial.length

/-- Circuit register in which the magnitude of term `i` is stored. -/
def coefficientCircuitRegister
    (polynomial : IntegerPolynomialCode (m + k))
    (i : Fin polynomial.length) :
    Fin (templateCircuitVariableCount polynomial) :=
  expressionInputRegister
    (positiveExpression polynomial) (negativeExpression polynomial)
    (coefficientInput polynomial i)

/-- Final DQL coordinate containing the coefficient register of term
`i`, after gate polarization and four-square augmentation. -/
def coefficientDQLRegister
    (polynomial : IntegerPolynomialCode (m + k))
    (i : Fin polynomial.length) :
    Fin (templateVariableCount polynomial) :=
  GateDQLCompiler.naturalCircuitRegister
    (templateCircuit polynomial) (coefficientCircuitRegister polynomial i)

/-- Specialize a fixed sparse polynomial template without changing the
numbers of equations or variables.  Only the RHS values of the final
`polynomial.length` rows depend on `parameters`. -/
def fixedTemplateDQL
    (polynomial : IntegerPolynomialCode (m + k))
    (parameters : Fin m → ℕ) :
    DQLSystem (templateEquationCount polynomial)
      (templateVariableCount polynomial) :=
  FixedCoordinateDQL.fixCoordinates
    (GateDQLCompiler.compileNaturalCircuit (templateCircuit polynomial))
    (coefficientDQLRegister polynomial)
    (fun i ↦ (specializedMagnitude polynomial parameters i : ℤ))

/-- Exact semantics of the fixed-resource compiler.  In particular, the
output type is fixed once the sparse template is fixed. -/
theorem fixedTemplateDQL_solvable_iff
    (polynomial : IntegerPolynomialCode (m + k))
    (parameters : Fin m → ℕ) :
    (fixedTemplateDQL polynomial parameters).Solvable ↔
      ∃ witnesses : Fin k → ℕ,
        IntegerPolynomialCode.eval polynomial
          (Fin.addCases parameters witnesses) = 0 := by
  change
    (FixedCoordinateDQL.fixCoordinates
      (GateDQLCompiler.compileNaturalCircuit (templateCircuit polynomial))
      (fun i ↦ GateDQLCompiler.naturalCircuitRegister
        (templateCircuit polynomial)
        (coefficientCircuitRegister polynomial i))
      (fun i ↦ (specializedMagnitude polynomial parameters i : ℤ))).Solvable ↔
      _
  rw [GateDQLCompiler.fixNaturalCircuitRegisters_solvable_iff]
  constructor
  · rintro ⟨value, hcircuit, hcoefficients⟩
    let witnesses : Fin k → ℕ :=
      fun i ↦ value
        (expressionInputRegister
          (positiveExpression polynomial) (negativeExpression polynomial)
          (witnessInput polynomial i))
    have hinputs :
        ∀ i : Fin (templateInputCount polynomial),
          value
              (expressionInputRegister
                (positiveExpression polynomial)
                (negativeExpression polynomial) i) =
            templateInputAssignment polynomial parameters witnesses i := by
      intro i
      obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective i
      · change
          value
              (expressionInputRegister
                (positiveExpression polynomial)
                (negativeExpression polynomial)
                (witnessInput polynomial i)) =
            templateInputAssignment polynomial parameters witnesses
              (witnessInput polynomial i)
        rw [templateInputAssignment_witness]
      · change
          value
              (expressionInputRegister
                (positiveExpression polynomial)
                (negativeExpression polynomial)
                (coefficientInput polynomial i)) =
            templateInputAssignment polynomial parameters witnesses
              (coefficientInput polynomial i)
        rw [templateInputAssignment_coefficient]
        exact hcoefficients i
    have hequation :
        NaturalArithmeticExpression.eval
            (templateInputAssignment polynomial parameters witnesses)
            (positiveExpression polynomial) =
          NaturalArithmeticExpression.eval
            (templateInputAssignment polynomial parameters witnesses)
            (negativeExpression polynomial) :=
      (expressionEquationCircuit_holds_with_inputs_iff
        (positiveExpression polynomial) (negativeExpression polynomial)
        (templateInputAssignment polynomial parameters witnesses)).mp
          ⟨value, hcircuit, hinputs⟩
    exact ⟨witnesses,
      (expressions_equal_iff polynomial parameters witnesses).mp
        hequation⟩
  · rintro ⟨witnesses, hzero⟩
    have hequation :
        NaturalArithmeticExpression.eval
            (templateInputAssignment polynomial parameters witnesses)
            (positiveExpression polynomial) =
          NaturalArithmeticExpression.eval
            (templateInputAssignment polynomial parameters witnesses)
            (negativeExpression polynomial) :=
      (expressions_equal_iff polynomial parameters witnesses).mpr hzero
    obtain ⟨value, hcircuit, hinputs⟩ :=
      (expressionEquationCircuit_holds_with_inputs_iff
        (positiveExpression polynomial) (negativeExpression polynomial)
        (templateInputAssignment polynomial parameters witnesses)).mpr
          hequation
    refine ⟨value, hcircuit, ?_⟩
    intro i
    simpa [coefficientCircuitRegister] using
      hinputs (coefficientInput polynomial i)

/-! ## Executability -/

/-- For a fixed template term, its specialized magnitude is primitive
recursive in the parameter tuple. -/
theorem specializedMagnitude_fixed_primrec
    (polynomial : IntegerPolynomialCode (m + k))
    (i : Fin polynomial.length) :
    Primrec
      (fun parameters : Fin m → ℕ ↦
        specializedMagnitude polynomial parameters i) := by
  exact
    (Primrec.nat_mul.comp
      (Primrec.const (polynomial.get i).2.2)
      (IntegerPolynomialCode.parameterFactor_primrec.comp
        Primrec.id (Primrec.const (polynomial.get i).1))).of_eq
          fun _ => rfl

/-- A finite function is primitive recursive when each of its finitely
many coordinate functions is. -/
private theorem primrec_finFunction_of_components
    {α σ : Type*} [Primcodable α] [Primcodable σ]
    {count : ℕ} {f : α → Fin count → σ}
    (hf : ∀ i, Primrec (fun a ↦ f a i)) :
    Primrec f := by
  exact
    (Primrec.vector_get'.comp (Primrec.vector_ofFn hf)).of_eq
      fun a => by
        funext i
        simp

/-- Specialization of one fixed template is a total computable map into
one literal DQL type. -/
theorem fixedTemplateDQL_computable
    (polynomial : IntegerPolynomialCode (m + k)) :
    Computable
      (fixedTemplateDQL polynomial :
        (Fin m → ℕ) →
          DQLSystem (templateEquationCount polynomial)
            (templateVariableCount polynomial)) := by
  let zeroParameters : Fin m → ℕ := fun _ ↦ 0
  have hquadratic :
      Primrec
        (fun parameters : Fin m → ℕ ↦
          fun r j ↦
            intSignedCodeEquiv
              ((fixedTemplateDQL polynomial parameters).quadratic r j)) := by
    exact
      (Primrec.const
        (fun r j ↦
          intSignedCodeEquiv
            ((fixedTemplateDQL polynomial zeroParameters).quadratic
              r j))).of_eq fun parameters => by
          funext r j
          rfl
  have hlinear :
      Primrec
        (fun parameters : Fin m → ℕ ↦
          fun r j ↦
            intSignedCodeEquiv
              ((fixedTemplateDQL polynomial parameters).linear r j)) := by
    exact
      (Primrec.const
        (fun r j ↦
          intSignedCodeEquiv
            ((fixedTemplateDQL polynomial zeroParameters).linear
              r j))).of_eq fun parameters => by
          funext r j
          rfl
  have hrhs :
      Primrec
        (fun parameters : Fin m → ℕ ↦
          fun r ↦
            intSignedCodeEquiv
              ((fixedTemplateDQL polynomial parameters).rhs r)) := by
    apply primrec_finFunction_of_components
    intro r
    cases hrow : finSumFinEquiv.symm r with
    | inl old =>
        exact
          (Primrec.const
            (intSignedCodeEquiv
              ((GateDQLCompiler.compileNaturalCircuit
                (templateCircuit polynomial)).rhs old))).of_eq
                  fun parameters => by
                    simp [fixedTemplateDQL,
                      FixedCoordinateDQL.fixCoordinates, hrow]
    | inr i =>
        exact
          (Primrec.sumInl.comp
            (specializedMagnitude_fixed_primrec polynomial i)).of_eq
              fun parameters => by
                simp [fixedTemplateDQL,
                  FixedCoordinateDQL.fixCoordinates, hrow]
                rfl
  have hcode :
      Primrec
        (fun parameters : Fin m → ℕ ↦
          dqlSystemCodeEquiv
              (templateEquationCount polynomial)
              (templateVariableCount polynomial)
            (fixedTemplateDQL polynomial parameters)) := by
    exact
      (Primrec.pair (Primrec.pair hquadratic hlinear) hrhs).of_eq
        fun _ => rfl
  exact
    ((Primrec.of_equiv_iff
      (dqlSystemCodeEquiv
        (templateEquationCount polynomial)
        (templateVariableCount polynomial))).mp hcode).to_comp

end FixedTemplatePolynomialDQL

end HGAS
