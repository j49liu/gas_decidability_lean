import HGAS.Arithmetic.DQLEnumerability
import HGAS.Arithmetic.FourSquareAugmentation
import Mathlib.Tactic

/-!
# Fixing finitely many DQL coordinates by right-hand sides

A magnitude-independent arithmetic compiler should allocate one register
for a numerical constant and impose

```
                         x_j = c
```

with `c` on the right-hand side.  The number of variables and equations is
then independent of the size of `c`.

This module implements that operation for an arbitrary DQL system.  It is
kept separate from the polynomial-template compiler because fixing selected
registers is useful for other fixed-resource reductions as well.
-/

namespace HGAS

open scoped BigOperators

namespace FixedCoordinateDQL

variable {oldEqs oldVars count : ℕ}

/-- An old row in the enlarged row block. -/
def oldRow (count : ℕ) (r : Fin oldEqs) :
    Fin (oldEqs + count) :=
  finSumFinEquiv (Sum.inl r)

/-- The row fixing selected coordinate `i`. -/
def fixedRow (i : Fin count) :
    Fin (oldEqs + count) :=
  finSumFinEquiv (Sum.inr i)

/-- Append the equations `x_(selected i) = constants i`.

No variables are added.  In particular, both output dimensions depend only
on `oldEqs`, `oldVars`, and the number of selected coordinates, never on
the magnitudes of the constants. -/
def fixCoordinates
    (I : DQLSystem oldEqs oldVars)
    (selected : Fin count → Fin oldVars)
    (constants : Fin count → ℤ) :
    DQLSystem (oldEqs + count) oldVars where
  quadratic r j :=
    match finSumFinEquiv.symm r with
    | Sum.inl old => I.quadratic old j
    | Sum.inr _ => 0
  linear r j :=
    match finSumFinEquiv.symm r with
    | Sum.inl old => I.linear old j
    | Sum.inr i =>
        GateDQLCompiler.coefficientAt (selected i) 1 j
  rhs r :=
    match finSumFinEquiv.symm r with
    | Sum.inl old => I.rhs old
    | Sum.inr i => constants i

@[simp]
theorem oldRow_quadratic
    (I : DQLSystem oldEqs oldVars)
    (selected : Fin count → Fin oldVars)
    (constants : Fin count → ℤ)
    (r : Fin oldEqs) (j : Fin oldVars) :
    (fixCoordinates I selected constants).quadratic
        (oldRow count r) j =
      I.quadratic r j := by
  simp [fixCoordinates, oldRow]

@[simp]
theorem oldRow_linear
    (I : DQLSystem oldEqs oldVars)
    (selected : Fin count → Fin oldVars)
    (constants : Fin count → ℤ)
    (r : Fin oldEqs) (j : Fin oldVars) :
    (fixCoordinates I selected constants).linear
        (oldRow count r) j =
      I.linear r j := by
  simp [fixCoordinates, oldRow]

@[simp]
theorem oldRow_rhs
    (I : DQLSystem oldEqs oldVars)
    (selected : Fin count → Fin oldVars)
    (constants : Fin count → ℤ)
    (r : Fin oldEqs) :
    (fixCoordinates I selected constants).rhs
        (oldRow count r) =
      I.rhs r := by
  simp [fixCoordinates, oldRow]

@[simp]
theorem fixedRow_quadratic
    (I : DQLSystem oldEqs oldVars)
    (selected : Fin count → Fin oldVars)
    (constants : Fin count → ℤ)
    (i : Fin count) (j : Fin oldVars) :
    (fixCoordinates I selected constants).quadratic
        (fixedRow (oldEqs := oldEqs) i) j = 0 := by
  simp [fixCoordinates, fixedRow]

@[simp]
theorem fixedRow_linear
    (I : DQLSystem oldEqs oldVars)
    (selected : Fin count → Fin oldVars)
    (constants : Fin count → ℤ)
    (i : Fin count) (j : Fin oldVars) :
    (fixCoordinates I selected constants).linear
        (fixedRow (oldEqs := oldEqs) i) j =
      GateDQLCompiler.coefficientAt (selected i) 1 j := by
  simp [fixCoordinates, fixedRow]

@[simp]
theorem fixedRow_rhs
    (I : DQLSystem oldEqs oldVars)
    (selected : Fin count → Fin oldVars)
    (constants : Fin count → ℤ)
    (i : Fin count) :
    (fixCoordinates I selected constants).rhs
        (fixedRow (oldEqs := oldEqs) i) =
      constants i := by
  simp [fixCoordinates, fixedRow]

/-- Evaluation of a new row is exactly the selected coordinate. -/
theorem fixedRow_evaluation
    (I : DQLSystem oldEqs oldVars)
    (selected : Fin count → Fin oldVars)
    (constants : Fin count → ℤ)
    (value : Fin oldVars → ℤ) (i : Fin count) :
    (∑ j,
      ((fixCoordinates I selected constants).quadratic
          (fixedRow (oldEqs := oldEqs) i) j * value j ^ 2 +
        (fixCoordinates I selected constants).linear
          (fixedRow (oldEqs := oldEqs) i) j * value j)) =
      value (selected i) := by
  simp

/-- Pointwise semantic specification of the appended system. -/
theorem satisfies_fixCoordinates_iff
    (I : DQLSystem oldEqs oldVars)
    (selected : Fin count → Fin oldVars)
    (constants : Fin count → ℤ)
    (value : Fin oldVars → ℤ) :
    (fixCoordinates I selected constants).Satisfies value ↔
      I.Satisfies value ∧
        ∀ i, value (selected i) = constants i := by
  constructor
  · intro h
    constructor
    · intro r
      simpa using h (oldRow count r)
    · intro i
      have hi := h (fixedRow (oldEqs := oldEqs) i)
      rwa [fixedRow_evaluation, fixedRow_rhs] at hi
  · rintro ⟨hI, hfixed⟩ r
    cases haddress : finSumFinEquiv.symm r with
    | inl old =>
        simpa [fixCoordinates, haddress] using hI old
    | inr i =>
        simpa [fixCoordinates, haddress,
          GateDQLCompiler.sum_coefficientAt_mul] using hfixed i

/-- Solvability specification.  This is the reusable constant/RHS-gate
lemma used by the fixed polynomial-template compiler. -/
theorem fixCoordinates_solvable_iff
    (I : DQLSystem oldEqs oldVars)
    (selected : Fin count → Fin oldVars)
    (constants : Fin count → ℤ) :
    (fixCoordinates I selected constants).Solvable ↔
      ∃ value : Fin oldVars → ℤ,
        I.Satisfies value ∧
          ∀ i, value (selected i) = constants i := by
  simp only [DQLSystem.Solvable, satisfies_fixCoordinates_iff]

end FixedCoordinateDQL

namespace GateDQLCompiler

variable {vars count oldEqs oldVars : ℕ}

/-- The final DQL coordinate containing original circuit register `j`
after multiplication polarization and four-square augmentation. -/
def naturalCircuitRegister
    (gates : List (ArithmeticGate vars)) (j : Fin vars) :
    Fin ((vars + gates.length) + vars * 4) :=
  FourSquareAugmentation.oldVariableIndex vars
    (originalIndex gates.length j)

/-- A version of `augmentedSatisfies_of_old` with an already chosen
four-square representation.  Retaining the explicit witness is useful when
additional equations must refer to the old coordinates. -/
theorem extendWithRoots_satisfies
    (I : DQLSystem oldEqs oldVars)
    (selected : Fin count → Fin oldVars)
    (value : Fin oldVars → ℤ)
    (roots : Fin count → Fin 4 → ℤ)
    (hI : I.Satisfies value)
    (hroots : ∀ i, value (selected i) =
      ∑ a : Fin 4, roots i a ^ 2) :
    (FourSquareAugmentation.augment I selected).Satisfies
      (FourSquareAugmentation.extendWithRoots value roots) := by
  intro r
  obtain ⟨oldRow | i, rfl⟩ := finSumFinEquiv.surjective r
  · change
      (∑ j,
        ((FourSquareAugmentation.augment I selected).quadratic
            (FourSquareAugmentation.oldEquationIndex count oldRow) j *
              FourSquareAugmentation.extendWithRoots value roots j ^ 2 +
          (FourSquareAugmentation.augment I selected).linear
            (FourSquareAugmentation.oldEquationIndex count oldRow) j *
              FourSquareAugmentation.extendWithRoots value roots j)) =
        (FourSquareAugmentation.augment I selected).rhs
          (FourSquareAugmentation.oldEquationIndex count oldRow)
    rw [FourSquareAugmentation.oldRow_evaluation,
      FourSquareAugmentation.oldRow_rhs,
      FourSquareAugmentation.restrictOld_extendWithRoots]
    exact hI oldRow
  · change
      (∑ j,
        ((FourSquareAugmentation.augment I selected).quadratic
            (FourSquareAugmentation.nonnegativeEquationIndex i) j *
              FourSquareAugmentation.extendWithRoots value roots j ^ 2 +
          (FourSquareAugmentation.augment I selected).linear
            (FourSquareAugmentation.nonnegativeEquationIndex i) j *
              FourSquareAugmentation.extendWithRoots value roots j)) =
        (FourSquareAugmentation.augment I selected).rhs
          (FourSquareAugmentation.nonnegativeEquationIndex i)
    rw [FourSquareAugmentation.nonnegativeRow_evaluation,
      FourSquareAugmentation.nonnegativeRow_rhs,
      FourSquareAugmentation.restrictOld_extendWithRoots]
    simp only [FourSquareAugmentation.extendWithRoots_root]
    exact sub_eq_zero.mpr (hroots i)

/-- Compiling a natural circuit and then fixing selected original
registers by RHS rows has exactly the expected natural-number semantics. -/
theorem fixNaturalCircuitRegisters_solvable_iff
    (gates : List (ArithmeticGate vars))
    (selected : Fin count → Fin vars)
    (constants : Fin count → ℕ) :
    (FixedCoordinateDQL.fixCoordinates
      (compileNaturalCircuit gates)
      (fun i ↦ naturalCircuitRegister gates (selected i))
      (fun i ↦ (constants i : ℤ))).Solvable ↔
      ∃ value : Fin vars → ℕ,
        NaturalCircuitHolds gates value ∧
          ∀ i, value (selected i) = constants i := by
  rw [FixedCoordinateDQL.fixCoordinates_solvable_iff]
  constructor
  · rintro ⟨extended, hbase, hfixed⟩
    let oldValue :=
      FourSquareAugmentation.restrictOld extended
    have hold :
        (compileIntegerCircuit gates).Satisfies oldValue :=
      FourSquareAugmentation.oldSatisfies_of_augmentedSatisfies
        (compileIntegerCircuit gates)
        (fun i ↦ originalIndex gates.length i)
        extended hbase
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
          extended hbase i
    let naturalValue : Fin vars → ℕ :=
      fun i ↦ (circuitValue i).toNat
    have heq :
        (fun i ↦ ((naturalValue i : ℕ) : ℤ)) =
          circuitValue := by
      funext i
      exact Int.toNat_of_nonneg (hnonnegative i)
    refine ⟨naturalValue, ?_, ?_⟩
    · unfold NaturalCircuitHolds
      rw [heq]
      exact hcircuit
    · intro i
      have hfixedInt := hfixed i
      change
        extended
            (FourSquareAugmentation.oldVariableIndex vars
              (originalIndex gates.length (selected i))) =
          (constants i : ℤ) at hfixedInt
      have hcircuitFixed :
          circuitValue (selected i) = (constants i : ℤ) := by
        simpa [circuitValue, oldValue,
          FourSquareAugmentation.restrictOld] using hfixedInt
      have hnaturalCast :
          (naturalValue (selected i) : ℤ) = (constants i : ℤ) := by
        rw [show (naturalValue (selected i) : ℤ) =
            circuitValue (selected i) by
          exact congrFun heq (selected i)]
        exact hcircuitFixed
      exact_mod_cast hnaturalCast
  · rintro ⟨value, hvalue, hfixed⟩
    let intValue : Fin vars → ℤ :=
      fun i ↦ (value i : ℤ)
    have hcircuit :
        ArithmeticCircuitHolds gates intValue :=
      hvalue
    let oldValue := extendAssignment gates intValue
    have hold :
        (compileIntegerCircuit gates).Satisfies oldValue :=
      compiledSatisfies_extendAssignment gates intValue hcircuit
    have hnonnegative :
        ∀ i,
          0 ≤ oldValue (originalIndex gates.length i) := by
      intro i
      simp [oldValue, intValue]
    obtain ⟨roots, hroots⟩ :=
      FourSquareAugmentation.exists_roots oldValue
        (fun i ↦ originalIndex gates.length i) hnonnegative
    let extended :=
      FourSquareAugmentation.extendWithRoots oldValue roots
    have hbase :
        (compileNaturalCircuit gates).Satisfies extended := by
      exact extendWithRoots_satisfies
        (compileIntegerCircuit gates)
        (fun i ↦ originalIndex gates.length i)
        oldValue roots hold hroots
    refine ⟨extended, hbase, ?_⟩
    intro i
    change
      extended
          (FourSquareAugmentation.oldVariableIndex vars
            (originalIndex gates.length (selected i))) =
        (constants i : ℤ)
    simp only [extended,
      FourSquareAugmentation.extendWithRoots_old,
      oldValue, extendAssignment_original, intValue]
    exact_mod_cast hfixed i

end GateDQLCompiler

end HGAS
