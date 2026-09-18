import HGAS.Arithmetic.DQL
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-!
# Compiling arithmetic gates to diagonal--quadratic--linear systems

This is the finite, executable heart of the reduction in Lemma 4.1 of the
paper.  An arithmetic circuit uses only the four gate relations

```
x = 0,       x = 1,       x + y = z,       x * y = z.
```

For each multiplication gate we allocate one fresh variable `w` and replace
`x*y=z` by

```
w = x + y,
w² - x² - y² - 2z = 0.
```

Every resulting row is a linear combination of individual variables and
their squares.  We allocate two rows for every gate; the unused second row
of a nonmultiplication gate is the harmless identity `0=0`.  This uniform
layout makes the output dimensions literal computable expressions:

* `vars + gates.length` variables;
* `gates.length * 2` equations.

The main theorem proves exact satisfiability preservation over `ℤ`.  A later
module adds the four-square rows that restrict all circuit-value variables
to natural numbers.
-/

namespace HGAS

open scoped BigOperators

/-- The four arithmetic relations used by a straight-line Diophantine
circuit.  All variable references point into one fixed finite register
file. -/
inductive ArithmeticGate (vars : ℕ) where
  | zero (x : Fin vars)
  | one (x : Fin vars)
  | add (x y z : Fin vars)
  | mul (x y z : Fin vars)
deriving DecidableEq, Repr

namespace ArithmeticGate

variable {vars : ℕ}

/-- Semantic validity of one gate over the integers. -/
def Holds (g : ArithmeticGate vars) (value : Fin vars → ℤ) : Prop :=
  match g with
  | .zero x => value x = 0
  | .one x => value x = 1
  | .add x y z => value x + value y = value z
  | .mul x y z => value x * value y = value z

instance (g : ArithmeticGate vars) (value : Fin vars → ℤ) :
    Decidable (g.Holds value) := by
  unfold Holds
  split <;> infer_instance

end ArithmeticGate

/-- Every gate in a finite arithmetic circuit is valid. -/
def ArithmeticCircuitHolds
    {vars : ℕ}
    (gates : List (ArithmeticGate vars))
    (value : Fin vars → ℤ) : Prop :=
  ∀ i : Fin gates.length, (gates.get i).Holds value

instance {vars : ℕ} (gates : List (ArithmeticGate vars))
    (value : Fin vars → ℤ) :
    Decidable (ArithmeticCircuitHolds gates value) := by
  unfold ArithmeticCircuitHolds
  infer_instance

namespace GateDQLCompiler

variable {vars : ℕ}

/-- Original circuit register `i` in the compiled register file. -/
def originalIndex (gateCount : ℕ) (i : Fin vars) :
    Fin (vars + gateCount) :=
  finSumFinEquiv (Sum.inl i)

/-- Fresh polarization register belonging to gate `i`. -/
def auxiliaryIndex {gateCount : ℕ} (i : Fin gateCount) :
    Fin (vars + gateCount) :=
  finSumFinEquiv (Sum.inr i)

/-- A sparse Kronecker coefficient.  Sums of these functions automatically
combine coefficients when a gate repeats a variable. -/
def coefficientAt {n : ℕ} (target : Fin n) (c : ℤ) (j : Fin n) : ℤ :=
  if j = target then c else 0

@[simp]
theorem sum_coefficientAt_mul
    {n : ℕ} (target : Fin n) (c : ℤ) (value : Fin n → ℤ) :
    (∑ j, coefficientAt target c j * value j) =
      c * value target := by
  simp [coefficientAt]

@[simp]
theorem sum_coefficientAt_mul_sq
    {n : ℕ} (target : Fin n) (c : ℤ) (value : Fin n → ℤ) :
    (∑ j, coefficientAt target c j * value j ^ 2) =
      c * value target ^ 2 := by
  simp [coefficientAt]

/-- Quadratic coefficients of the second row of one compiled gate. -/
def secondQuadratic
    (gateCount : ℕ) (i : Fin gateCount)
    (g : ArithmeticGate vars) (j : Fin (vars + gateCount)) : ℤ :=
  match g with
  | .mul x y _ =>
      coefficientAt (auxiliaryIndex i) 1 j +
      coefficientAt (originalIndex gateCount x) (-1) j +
      coefficientAt (originalIndex gateCount y) (-1) j
  | _ => 0

/-- Linear coefficients of the first row of one compiled gate. -/
def firstLinear
    (gateCount : ℕ) (i : Fin gateCount)
    (g : ArithmeticGate vars) (j : Fin (vars + gateCount)) : ℤ :=
  match g with
  | .zero x =>
      coefficientAt (originalIndex gateCount x) 1 j
  | .one x =>
      coefficientAt (originalIndex gateCount x) 1 j
  | .add x y z =>
      coefficientAt (originalIndex gateCount x) 1 j +
      coefficientAt (originalIndex gateCount y) 1 j +
      coefficientAt (originalIndex gateCount z) (-1) j
  | .mul x y _ =>
      coefficientAt (auxiliaryIndex i) 1 j +
      coefficientAt (originalIndex gateCount x) (-1) j +
      coefficientAt (originalIndex gateCount y) (-1) j

/-- Linear coefficients of the second row of one compiled gate. -/
def secondLinear
    (gateCount : ℕ) (g : ArithmeticGate vars)
    (j : Fin (vars + gateCount)) : ℤ :=
  match g with
  | .mul _ _ z =>
      coefficientAt (originalIndex gateCount z) (-2) j
  | _ => 0

/-- Right-hand side of the first row. -/
def firstRhs (g : ArithmeticGate vars) : ℤ :=
  match g with
  | .one _ => 1
  | _ => 0

/-- Decode one of the two uniform rows belonging to a gate. -/
def rowAddress {gateCount : ℕ} (r : Fin (gateCount * 2)) :
    Fin gateCount × Fin 2 :=
  finProdFinEquiv.symm r

@[simp]
theorem rowAddress_pair
    {gateCount : ℕ} (i : Fin gateCount) (half : Fin 2) :
    rowAddress (finProdFinEquiv (i, half)) = (i, half) :=
  finProdFinEquiv.symm_apply_apply (i, half)

/-- Compile a finite arithmetic circuit to a literal DQL matrix system.
The definition is data only: it contains no semantic witness and no
classical choice. -/
def compileIntegerCircuit
    (gates : List (ArithmeticGate vars)) :
    DQLSystem (gates.length * 2) (vars + gates.length) where
  quadratic r j :=
    let address := rowAddress r
    let g := gates.get address.1
    if address.2 = 0 then 0
    else secondQuadratic gates.length address.1 g j
  linear r j :=
    let address := rowAddress r
    let g := gates.get address.1
    if address.2 = 0 then
      firstLinear gates.length address.1 g j
    else
      secondLinear gates.length g j
  rhs r :=
    let address := rowAddress r
    let g := gates.get address.1
    if address.2 = 0 then firstRhs g else 0

/-- Left-hand side of one row of the compiled system.  Naming this
expression pins all finite index types and keeps later calculations
readable. -/
def compiledRowValue
    (gates : List (ArithmeticGate vars))
    (value : Fin (vars + gates.length) → ℤ)
    (r : Fin (gates.length * 2)) : ℤ :=
  ∑ j : Fin (vars + gates.length),
    ((compileIntegerCircuit gates).quadratic r j * value j ^ 2 +
      (compileIntegerCircuit gates).linear r j * value j)

/-- Restrict a compiled assignment to the original circuit registers. -/
def originalValues
    {gateCount : ℕ} (value : Fin (vars + gateCount) → ℤ) :
    Fin vars → ℤ :=
  fun i ↦ value (originalIndex gateCount i)

/-- Canonical value of the fresh register for a gate.  Only multiplication
uses it; giving zero to all other fresh registers keeps the construction
uniform. -/
def canonicalAuxiliary
    (value : Fin vars → ℤ) (g : ArithmeticGate vars) : ℤ :=
  match g with
  | .mul x y _ => value x + value y
  | _ => 0

/-- Extend an original circuit assignment by its canonical fresh
polarization values. -/
def extendAssignment
    (gates : List (ArithmeticGate vars)) (value : Fin vars → ℤ) :
    Fin (vars + gates.length) → ℤ :=
  fun j ↦
    match finSumFinEquiv.symm j with
    | Sum.inl i => value i
    | Sum.inr k => canonicalAuxiliary value (gates.get k)

@[simp]
theorem extendAssignment_original
    (gates : List (ArithmeticGate vars)) (value : Fin vars → ℤ)
    (i : Fin vars) :
    extendAssignment gates value (originalIndex gates.length i) =
      value i := by
  simp [extendAssignment, originalIndex]

@[simp]
theorem extendAssignment_auxiliary
    (gates : List (ArithmeticGate vars)) (value : Fin vars → ℤ)
    (i : Fin gates.length) :
    extendAssignment gates value (auxiliaryIndex i) =
      canonicalAuxiliary value (gates.get i) := by
  simp [extendAssignment, auxiliaryIndex]

@[simp]
theorem originalValues_extendAssignment
    (gates : List (ArithmeticGate vars)) (value : Fin vars → ℤ) :
    originalValues (extendAssignment gates value) = value := by
  funext i
  simp [originalValues]

/-- Evaluation of the first DQL row associated to a gate. -/
theorem firstRow_evaluation
    (gates : List (ArithmeticGate vars))
    (i : Fin gates.length)
    (value : Fin (vars + gates.length) → ℤ) :
    compiledRowValue gates value
      (finProdFinEquiv (i, (0 : Fin 2))) =
      match gates.get i with
      | .zero x => value (originalIndex gates.length x)
      | .one x => value (originalIndex gates.length x)
      | .add x y z =>
          value (originalIndex gates.length x) +
          value (originalIndex gates.length y) -
          value (originalIndex gates.length z)
      | .mul x y _ =>
          value (auxiliaryIndex i) -
          value (originalIndex gates.length x) -
          value (originalIndex gates.length y) := by
  simp only [compiledRowValue, compileIntegerCircuit, rowAddress_pair,
    ↓reduceIte, zero_mul, zero_add]
  generalize gates.get i = gate
  cases gate <;>
    simp [firstLinear, add_mul, Finset.sum_add_distrib]
  all_goals ring

/-- Evaluation of the second DQL row associated to a gate. -/
theorem secondRow_evaluation
    (gates : List (ArithmeticGate vars))
    (i : Fin gates.length)
    (value : Fin (vars + gates.length) → ℤ) :
    compiledRowValue gates value
      (finProdFinEquiv (i, (1 : Fin 2))) =
      match gates.get i with
      | .mul x y z =>
          value (auxiliaryIndex i) ^ 2 -
          value (originalIndex gates.length x) ^ 2 -
          value (originalIndex gates.length y) ^ 2 -
          2 * value (originalIndex gates.length z)
      | _ => 0 := by
  simp only [compiledRowValue, compileIntegerCircuit, rowAddress_pair]
  have hone : (1 : Fin 2) ≠ 0 := by decide
  simp only [if_neg hone, Finset.sum_add_distrib]
  generalize gates.get i = gate
  cases gate <;>
    simp [secondQuadratic, secondLinear, add_mul,
      Finset.sum_add_distrib]
  all_goals ring

/-- Right-hand side of the first row. -/
@[simp]
theorem firstRow_rhs
    (gates : List (ArithmeticGate vars))
    (i : Fin gates.length) :
    (compileIntegerCircuit gates).rhs
        (finProdFinEquiv (i, (0 : Fin 2))) =
      firstRhs (gates.get i) := by
  simp [compileIntegerCircuit, rowAddress_pair]

/-- Right-hand side of the second row. -/
@[simp]
theorem secondRow_rhs
    (gates : List (ArithmeticGate vars))
    (i : Fin gates.length) :
    (compileIntegerCircuit gates).rhs
        (finProdFinEquiv (i, (1 : Fin 2))) = 0 := by
  simp [compileIntegerCircuit, rowAddress_pair]

/-- Every satisfying DQL assignment restricts to a satisfying arithmetic
circuit assignment. -/
theorem circuitHolds_of_compiledSatisfies
    (gates : List (ArithmeticGate vars))
    (value : Fin (vars + gates.length) → ℤ)
    (hvalue : (compileIntegerCircuit gates).Satisfies value) :
    ArithmeticCircuitHolds gates (originalValues value) := by
  intro i
  have hfirst := hvalue (finProdFinEquiv (i, (0 : Fin 2)))
  have hsecond := hvalue (finProdFinEquiv (i, (1 : Fin 2)))
  change
    compiledRowValue gates value
      (finProdFinEquiv (i, (0 : Fin 2))) =
        (compileIntegerCircuit gates).rhs
          (finProdFinEquiv (i, (0 : Fin 2))) at hfirst
  change
    compiledRowValue gates value
      (finProdFinEquiv (i, (1 : Fin 2))) =
        (compileIntegerCircuit gates).rhs
          (finProdFinEquiv (i, (1 : Fin 2))) at hsecond
  rw [firstRow_evaluation, firstRow_rhs] at hfirst
  rw [secondRow_evaluation, secondRow_rhs] at hsecond
  change (gates.get i).Holds (originalValues value)
  generalize hgate : gates.get i = gate
  rw [hgate] at hfirst hsecond
  cases gate with
  | zero x =>
      simpa [ArithmeticGate.Holds, originalValues, firstRhs] using hfirst
  | one x =>
      simpa [ArithmeticGate.Holds, originalValues, firstRhs] using hfirst
  | add x y z =>
      change
        value (originalIndex gates.length x) +
          value (originalIndex gates.length y) -
          value (originalIndex gates.length z) = 0 at hfirst
      simp only [ArithmeticGate.Holds, originalValues]
      exact sub_eq_zero.mp hfirst
  | mul x y z =>
      change
        value (auxiliaryIndex i) -
          value (originalIndex gates.length x) -
          value (originalIndex gates.length y) = 0 at hfirst
      change
        value (auxiliaryIndex i) ^ 2 -
          value (originalIndex gates.length x) ^ 2 -
          value (originalIndex gates.length y) ^ 2 -
          2 * value (originalIndex gates.length z) = 0 at hsecond
      simp only [ArithmeticGate.Holds, originalValues]
      have hw :
          value (auxiliaryIndex i) =
            value (originalIndex gates.length x) +
            value (originalIndex gates.length y) := by
        linear_combination hfirst
      rw [hw] at hsecond
      nlinarith

/-- A satisfying arithmetic assignment extends canonically to a satisfying
DQL assignment. -/
theorem compiledSatisfies_extendAssignment
    (gates : List (ArithmeticGate vars))
    (value : Fin vars → ℤ)
    (hvalue : ArithmeticCircuitHolds gates value) :
    (compileIntegerCircuit gates).Satisfies
      (extendAssignment gates value) := by
  intro r
  obtain ⟨⟨i, half⟩, rfl⟩ := finProdFinEquiv.surjective r
  fin_cases half
  · change
      compiledRowValue gates (extendAssignment gates value)
        (finProdFinEquiv (i, (0 : Fin 2))) =
          (compileIntegerCircuit gates).rhs
            (finProdFinEquiv (i, (0 : Fin 2)))
    rw [firstRow_evaluation, firstRow_rhs]
    simp only [extendAssignment_original, extendAssignment_auxiliary]
    have hi := hvalue i
    generalize hgate : gates.get i = gate at hi ⊢
    cases gate with
    | zero x =>
        simpa [ArithmeticGate.Holds, firstRhs] using hi
    | one x =>
        simpa [ArithmeticGate.Holds, firstRhs] using hi
    | add x y z =>
        simp only [ArithmeticGate.Holds] at hi
        change value x + value y - value z = 0
        exact sub_eq_zero.mpr hi
    | mul x y z =>
        simp [canonicalAuxiliary, firstRhs]
  · change
      compiledRowValue gates (extendAssignment gates value)
        (finProdFinEquiv (i, (1 : Fin 2))) =
          (compileIntegerCircuit gates).rhs
            (finProdFinEquiv (i, (1 : Fin 2)))
    rw [secondRow_evaluation, secondRow_rhs]
    simp only [extendAssignment_original, extendAssignment_auxiliary]
    have hi := hvalue i
    generalize hgate : gates.get i = gate at hi ⊢
    cases gate with
    | zero x => simp
    | one x => simp
    | add x y z => simp
    | mul x y z =>
        simp only [ArithmeticGate.Holds] at hi
        simp [canonicalAuxiliary]
        nlinarith

/-- Exact semantic correctness of the integer gate-to-DQL compiler. -/
theorem compileIntegerCircuit_solvable_iff
    (gates : List (ArithmeticGate vars)) :
    (compileIntegerCircuit gates).Solvable ↔
      ∃ value : Fin vars → ℤ,
        ArithmeticCircuitHolds gates value := by
  constructor
  · rintro ⟨value, hvalue⟩
    exact
      ⟨originalValues value,
        circuitHolds_of_compiledSatisfies gates value hvalue⟩
  · rintro ⟨value, hvalue⟩
    exact
      ⟨extendAssignment gates value,
        compiledSatisfies_extendAssignment gates value hvalue⟩

end GateDQLCompiler

end HGAS
