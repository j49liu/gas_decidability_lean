import HGAS.Arithmetic.GateDQLCompiler
import Mathlib.Tactic

/-!
# Four-square enforcement of natural-valued circuit registers

The gate compiler works over integer assignments.  A Diophantine circuit,
however, starts over `ℕ`.  For every selected register `xᵢ` this module adds
four fresh, freely integer-valued variables and the DQL row

```
xᵢ - aᵢ₀² - aᵢ₁² - aᵢ₂² - aᵢ₃² = 0.
```

Lagrange's four-square theorem makes the new row equivalent to `xᵢ ≥ 0`.
Only the selected value registers are constrained; the fresh polarization
variables introduced for multiplication gates remain unrestricted, just as
in the paper.

The construction is reusable for any DQL system and any finite family of
selected coordinates.  Its output sizes are explicit:

* `oldVars + selected * 4` variables;
* `oldEqs + selected` rows.
-/

namespace HGAS

open scoped BigOperators

namespace FourSquareAugmentation

variable {oldEqs oldVars selectedCount : ℕ}

/-- An old variable inside the augmented variable block. -/
def oldVariableIndex (selectedCount : ℕ) (j : Fin oldVars) :
    Fin (oldVars + selectedCount * 4) :=
  finSumFinEquiv (Sum.inl j)

/-- One of the four square-root variables belonging to a selected
coordinate. -/
def rootVariableIndex
    (i : Fin selectedCount) (a : Fin 4) :
    Fin (oldVars + selectedCount * 4) :=
  finSumFinEquiv (Sum.inr (finProdFinEquiv (i, a)))

/-- An old equation inside the augmented row block. -/
def oldEquationIndex (selectedCount : ℕ) (r : Fin oldEqs) :
    Fin (oldEqs + selectedCount) :=
  finSumFinEquiv (Sum.inl r)

/-- The four-square row belonging to a selected coordinate. -/
def nonnegativeEquationIndex (i : Fin selectedCount) :
    Fin (oldEqs + selectedCount) :=
  finSumFinEquiv (Sum.inr i)

/-- Quadratic coefficient of an old row, embedded sparsely in the larger
variable block. -/
def embeddedOldQuadratic
    (I : DQLSystem oldEqs oldVars) (r : Fin oldEqs)
    (j : Fin (oldVars + selectedCount * 4)) : ℤ :=
  ∑ v : Fin oldVars,
    GateDQLCompiler.coefficientAt
      (oldVariableIndex selectedCount v) (I.quadratic r v) j

/-- Linear coefficient of an old row in the larger variable block. -/
def embeddedOldLinear
    (I : DQLSystem oldEqs oldVars) (r : Fin oldEqs)
    (j : Fin (oldVars + selectedCount * 4)) : ℤ :=
  ∑ v : Fin oldVars,
    GateDQLCompiler.coefficientAt
      (oldVariableIndex selectedCount v) (I.linear r v) j

/-- Quadratic part `-a₀²-⋯-a₃²` of a new nonnegativity row. -/
def rootQuadratic
    (i : Fin selectedCount)
    (j : Fin (oldVars + selectedCount * 4)) : ℤ :=
  ∑ a : Fin 4,
    GateDQLCompiler.coefficientAt (rootVariableIndex i a) (-1) j

/-- Add four-square nonnegativity rows for the coordinates named by
`selected`.  This is a total finite-data transformation. -/
def augment
    (I : DQLSystem oldEqs oldVars)
    (selected : Fin selectedCount → Fin oldVars) :
    DQLSystem (oldEqs + selectedCount)
      (oldVars + selectedCount * 4) where
  quadratic r j :=
    match finSumFinEquiv.symm r with
    | Sum.inl oldRow => embeddedOldQuadratic I oldRow j
    | Sum.inr i => rootQuadratic i j
  linear r j :=
    match finSumFinEquiv.symm r with
    | Sum.inl oldRow => embeddedOldLinear I oldRow j
    | Sum.inr i =>
        GateDQLCompiler.coefficientAt
          (oldVariableIndex selectedCount (selected i)) 1 j
  rhs r :=
    match finSumFinEquiv.symm r with
    | Sum.inl oldRow => I.rhs oldRow
    | Sum.inr _ => 0

/-- Restriction of an augmented assignment to the old variable block. -/
def restrictOld
    (value : Fin (oldVars + selectedCount * 4) → ℤ) :
    Fin oldVars → ℤ :=
  fun j ↦ value (oldVariableIndex selectedCount j)

@[simp]
theorem sum_embeddedOldQuadratic_mul_sq
    (I : DQLSystem oldEqs oldVars) (r : Fin oldEqs)
    (value : Fin (oldVars + selectedCount * 4) → ℤ) :
    (∑ j,
      embeddedOldQuadratic (selectedCount := selectedCount) I r j *
        value j ^ 2) =
      ∑ v, I.quadratic r v *
        value (oldVariableIndex selectedCount v) ^ 2 := by
  simp only [embeddedOldQuadratic, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  exact GateDQLCompiler.sum_coefficientAt_mul_sq
    (oldVariableIndex selectedCount v) (I.quadratic r v) value

@[simp]
theorem sum_embeddedOldLinear_mul
    (I : DQLSystem oldEqs oldVars) (r : Fin oldEqs)
    (value : Fin (oldVars + selectedCount * 4) → ℤ) :
    (∑ j,
      embeddedOldLinear (selectedCount := selectedCount) I r j *
        value j) =
      ∑ v, I.linear r v *
        value (oldVariableIndex selectedCount v) := by
  simp only [embeddedOldLinear, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  exact GateDQLCompiler.sum_coefficientAt_mul
    (oldVariableIndex selectedCount v) (I.linear r v) value

@[simp]
theorem sum_rootQuadratic_mul_sq
    (i : Fin selectedCount)
    (value : Fin (oldVars + selectedCount * 4) → ℤ) :
    (∑ j, rootQuadratic (oldVars := oldVars) i j * value j ^ 2) =
      -∑ a : Fin 4, value (rootVariableIndex i a) ^ 2 := by
  simp only [rootQuadratic, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [GateDQLCompiler.sum_coefficientAt_mul_sq]
  simp only [neg_one_mul, Finset.sum_neg_distrib]

/-- Evaluation of an embedded old row agrees exactly with its original
evaluation on the restricted assignment. -/
theorem oldRow_evaluation
    (I : DQLSystem oldEqs oldVars)
    (selected : Fin selectedCount → Fin oldVars)
    (r : Fin oldEqs)
    (value : Fin (oldVars + selectedCount * 4) → ℤ) :
    (∑ j,
      ((augment I selected).quadratic
          (oldEquationIndex selectedCount r) j * value j ^ 2 +
        (augment I selected).linear
          (oldEquationIndex selectedCount r) j * value j)) =
      ∑ v,
        (I.quadratic r v * (restrictOld value v) ^ 2 +
          I.linear r v * restrictOld value v) := by
  simp only [augment, oldEquationIndex, Equiv.symm_apply_apply,
    Finset.sum_add_distrib, sum_embeddedOldQuadratic_mul_sq,
    sum_embeddedOldLinear_mul, restrictOld]

/-- Evaluation of a new row is the selected value minus four squares. -/
theorem nonnegativeRow_evaluation
    (I : DQLSystem oldEqs oldVars)
    (selected : Fin selectedCount → Fin oldVars)
    (i : Fin selectedCount)
    (value : Fin (oldVars + selectedCount * 4) → ℤ) :
    (∑ j,
      ((augment I selected).quadratic
          (nonnegativeEquationIndex i) j * value j ^ 2 +
        (augment I selected).linear
          (nonnegativeEquationIndex i) j * value j)) =
      restrictOld value (selected i) -
        ∑ a : Fin 4, value (rootVariableIndex i a) ^ 2 := by
  simp only [augment, nonnegativeEquationIndex,
    Equiv.symm_apply_apply, Finset.sum_add_distrib,
    sum_rootQuadratic_mul_sq,
    GateDQLCompiler.sum_coefficientAt_mul, restrictOld]
  ring

@[simp]
theorem oldRow_rhs
    (I : DQLSystem oldEqs oldVars)
    (selected : Fin selectedCount → Fin oldVars)
    (r : Fin oldEqs) :
    (augment I selected).rhs (oldEquationIndex selectedCount r) =
      I.rhs r := by
  simp [augment, oldEquationIndex]

@[simp]
theorem nonnegativeRow_rhs
    (I : DQLSystem oldEqs oldVars)
    (selected : Fin selectedCount → Fin oldVars)
    (i : Fin selectedCount) :
    (augment I selected).rhs (nonnegativeEquationIndex i) = 0 := by
  simp [augment, nonnegativeEquationIndex]

/-- Any augmented solution restricts to an old solution. -/
theorem oldSatisfies_of_augmentedSatisfies
    (I : DQLSystem oldEqs oldVars)
    (selected : Fin selectedCount → Fin oldVars)
    (value : Fin (oldVars + selectedCount * 4) → ℤ)
    (hvalue : (augment I selected).Satisfies value) :
    I.Satisfies (restrictOld value) := by
  intro r
  have hr := hvalue (oldEquationIndex selectedCount r)
  rw [oldRow_evaluation, oldRow_rhs] at hr
  exact hr

/-- Every selected old value in an augmented solution is nonnegative. -/
theorem selected_nonnegative_of_augmentedSatisfies
    (I : DQLSystem oldEqs oldVars)
    (selected : Fin selectedCount → Fin oldVars)
    (value : Fin (oldVars + selectedCount * 4) → ℤ)
    (hvalue : (augment I selected).Satisfies value) :
    ∀ i, 0 ≤ restrictOld value (selected i) := by
  intro i
  have hi := hvalue (nonnegativeEquationIndex i)
  rw [nonnegativeRow_evaluation, nonnegativeRow_rhs] at hi
  have hsquares :
      0 ≤ ∑ a : Fin 4, value (rootVariableIndex i a) ^ 2 := by
    positivity
  linarith

/-- Four integer square roots chosen for every nonnegative selected
coordinate. -/
theorem exists_roots
    (value : Fin oldVars → ℤ)
    (selected : Fin selectedCount → Fin oldVars)
    (hvalue : ∀ i, 0 ≤ value (selected i)) :
    ∃ roots : Fin selectedCount → Fin 4 → ℤ,
      ∀ i, value (selected i) =
        ∑ a : Fin 4, roots i a ^ 2 := by
  have hi :
      ∀ i : Fin selectedCount,
        ∃ a b c d : ℤ,
          value (selected i) = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
    intro i
    exact (nonneg_iff_exists_sum_four_int_squares
      (value (selected i))).mp (hvalue i)
  choose a b c d habcd using hi
  let roots : Fin selectedCount → Fin 4 → ℤ :=
    fun i k ↦ ![a i, b i, c i, d i] k
  refine ⟨roots, ?_⟩
  intro i
  rw [show (∑ k : Fin 4, roots i k ^ 2) =
      a i ^ 2 + b i ^ 2 + c i ^ 2 + d i ^ 2 by
        simp [roots, Fin.sum_univ_four]]
  exact habcd i

/-- Extend an old assignment by a chosen four-square representation. -/
def extendWithRoots
    (value : Fin oldVars → ℤ)
    (roots : Fin selectedCount → Fin 4 → ℤ) :
    Fin (oldVars + selectedCount * 4) → ℤ :=
  fun j ↦
    match finSumFinEquiv.symm j with
    | Sum.inl old => value old
    | Sum.inr root =>
        let address := finProdFinEquiv.symm root
        roots address.1 address.2

@[simp]
theorem extendWithRoots_old
    (value : Fin oldVars → ℤ)
    (roots : Fin selectedCount → Fin 4 → ℤ)
    (j : Fin oldVars) :
    extendWithRoots value roots (oldVariableIndex selectedCount j) =
      value j := by
  simp [extendWithRoots, oldVariableIndex]

@[simp]
theorem extendWithRoots_root
    (value : Fin oldVars → ℤ)
    (roots : Fin selectedCount → Fin 4 → ℤ)
    (i : Fin selectedCount) (a : Fin 4) :
    extendWithRoots value roots (rootVariableIndex i a) =
      roots i a := by
  simp [extendWithRoots, rootVariableIndex]

@[simp]
theorem restrictOld_extendWithRoots
    (value : Fin oldVars → ℤ)
    (roots : Fin selectedCount → Fin 4 → ℤ) :
    restrictOld (extendWithRoots value roots) = value := by
  funext j
  simp [restrictOld]

/-- An old solution whose selected coordinates are nonnegative extends to
an augmented DQL solution. -/
theorem augmentedSatisfies_of_old
    (I : DQLSystem oldEqs oldVars)
    (selected : Fin selectedCount → Fin oldVars)
    (value : Fin oldVars → ℤ)
    (hI : I.Satisfies value)
    (hnonnegative : ∀ i, 0 ≤ value (selected i)) :
    ∃ extended, (augment I selected).Satisfies extended := by
  obtain ⟨roots, hroots⟩ :=
    exists_roots value selected hnonnegative
  refine ⟨extendWithRoots value roots, ?_⟩
  intro r
  obtain ⟨oldRow | i, rfl⟩ := finSumFinEquiv.surjective r
  · change
      (∑ j,
        ((augment I selected).quadratic
            (oldEquationIndex selectedCount oldRow) j *
              extendWithRoots value roots j ^ 2 +
          (augment I selected).linear
            (oldEquationIndex selectedCount oldRow) j *
              extendWithRoots value roots j)) =
        (augment I selected).rhs
          (oldEquationIndex selectedCount oldRow)
    rw [oldRow_evaluation, oldRow_rhs,
      restrictOld_extendWithRoots]
    exact hI oldRow
  · change
      (∑ j,
        ((augment I selected).quadratic
            (nonnegativeEquationIndex i) j *
              extendWithRoots value roots j ^ 2 +
          (augment I selected).linear
            (nonnegativeEquationIndex i) j *
              extendWithRoots value roots j)) =
        (augment I selected).rhs
          (nonnegativeEquationIndex i)
    rw [nonnegativeRow_evaluation, nonnegativeRow_rhs,
      restrictOld_extendWithRoots]
    simp only [extendWithRoots_root]
    exact sub_eq_zero.mpr (hroots i)

/-- Exact semantic specification of four-square augmentation. -/
theorem augment_solvable_iff
    (I : DQLSystem oldEqs oldVars)
    (selected : Fin selectedCount → Fin oldVars) :
    (augment I selected).Solvable ↔
      ∃ value : Fin oldVars → ℤ,
        I.Satisfies value ∧
          ∀ i, 0 ≤ value (selected i) := by
  constructor
  · rintro ⟨extended, hextended⟩
    exact
      ⟨restrictOld extended,
        oldSatisfies_of_augmentedSatisfies
          I selected extended hextended,
        selected_nonnegative_of_augmentedSatisfies
          I selected extended hextended⟩
  · rintro ⟨value, hI, hnonnegative⟩
    exact augmentedSatisfies_of_old
      I selected value hI hnonnegative

end FourSquareAugmentation

namespace GateDQLCompiler

variable {vars : ℕ}

/-- The complete compiler for a natural-valued arithmetic circuit: first
polarize multiplication gates, then impose four-square nonnegativity on
every original circuit register. -/
def compileNaturalCircuit
    (gates : List (ArithmeticGate vars)) :
    DQLSystem (gates.length * 2 + vars)
      ((vars + gates.length) + vars * 4) :=
  FourSquareAugmentation.augment
    (compileIntegerCircuit gates)
    (fun i ↦ originalIndex gates.length i)

/-- Semantic validity of a circuit assignment by natural numbers. -/
def NaturalCircuitHolds
    (gates : List (ArithmeticGate vars))
    (value : Fin vars → ℕ) : Prop :=
  ArithmeticCircuitHolds gates (fun i ↦ (value i : ℤ))

instance (gates : List (ArithmeticGate vars))
    (value : Fin vars → ℕ) :
    Decidable (NaturalCircuitHolds gates value) := by
  unfold NaturalCircuitHolds
  infer_instance

/-- Exact end-to-end correctness of the gate and four-square compiler.
This is the constructive content of the circuit-to-DQL part of Lemma 4.1. -/
theorem compileNaturalCircuit_solvable_iff
    (gates : List (ArithmeticGate vars)) :
    (compileNaturalCircuit gates).Solvable ↔
      ∃ value : Fin vars → ℕ,
        NaturalCircuitHolds gates value := by
  constructor
  · rintro ⟨extended, hextended⟩
    let oldValue :=
      FourSquareAugmentation.restrictOld extended
    have hold :
        (compileIntegerCircuit gates).Satisfies oldValue :=
      FourSquareAugmentation.oldSatisfies_of_augmentedSatisfies
        (compileIntegerCircuit gates)
        (fun i ↦ originalIndex gates.length i)
        extended hextended
    let circuitValue : Fin vars → ℤ :=
      originalValues oldValue
    have hcircuit :
        ArithmeticCircuitHolds gates circuitValue :=
      circuitHolds_of_compiledSatisfies gates oldValue hold
    have hnonnegative :
        ∀ i, 0 ≤ circuitValue i := by
      intro i
      exact
        FourSquareAugmentation.selected_nonnegative_of_augmentedSatisfies
          (compileIntegerCircuit gates)
          (fun j ↦ originalIndex gates.length j)
          extended hextended i
    let naturalValue : Fin vars → ℕ :=
      fun i ↦ (circuitValue i).toNat
    refine ⟨naturalValue, ?_⟩
    unfold NaturalCircuitHolds
    have heq :
        (fun i ↦ ((naturalValue i : ℕ) : ℤ)) =
          circuitValue := by
      funext i
      exact Int.toNat_of_nonneg (hnonnegative i)
    rw [heq]
    exact hcircuit
  · rintro ⟨value, hvalue⟩
    let intValue : Fin vars → ℤ :=
      fun i ↦ (value i : ℤ)
    have hcircuit :
        ArithmeticCircuitHolds gates intValue := by
      exact hvalue
    let oldValue := extendAssignment gates intValue
    have hold :
        (compileIntegerCircuit gates).Satisfies oldValue :=
      compiledSatisfies_extendAssignment gates intValue hcircuit
    have hnonnegative :
        ∀ i,
          0 ≤ oldValue (originalIndex gates.length i) := by
      intro i
      simp [oldValue, intValue]
    exact
      FourSquareAugmentation.augmentedSatisfies_of_old
        (compileIntegerCircuit gates)
        (fun i ↦ originalIndex gates.length i)
        oldValue hold hnonnegative

end GateDQLCompiler

end HGAS
