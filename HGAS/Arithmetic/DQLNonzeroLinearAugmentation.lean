import HGAS.Arithmetic.DetectorCharacterComputability
import Mathlib.Tactic

/-!
# A solvability-preserving DQL augmentation with no zero linear columns

The three-moment Jacobi detector can identify its intended Bloch
coefficient whenever the corresponding DQL variable occurs linearly in
at least one row.  A general DQL presentation need not have this harmless
syntactic property: a variable may occur only quadratically.

This file supplies a reusable preprocessing step.  For every old variable
`x_j` we introduce a duplicate `y_j` and append the linear equation

`x_j - y_j = 0`.

The old equations use only the `x` variables.  Hence the new system is
solvable exactly when the old one is, while both the `x_j` and `y_j`
columns contain a visibly nonzero linear coefficient (`1` and `-1`,
respectively).  The transformation is also primitive recursive.
-/

namespace HGAS

open scoped BigOperators

namespace DQLNonzeroLinearAugmentation

variable {eqs vars : ℕ}

/-- Every variable occurs with a nonzero linear coefficient in some row. -/
def HasNonzeroLinearColumn (I : DQLSystem eqs vars) : Prop :=
  ∀ j : Fin vars, ∃ row : Fin eqs, I.linear row j ≠ 0

/-- The old equation-row embedding. -/
def oldRow (row : Fin eqs) : Fin (eqs + vars) :=
  finSumFinEquiv (Sum.inl row)

/-- The new equality-row embedding. -/
def equalityRow (j : Fin vars) : Fin (eqs + vars) :=
  finSumFinEquiv (Sum.inr j)

/-- The old-variable embedding. -/
def oldVariable (j : Fin vars) : Fin (vars + vars) :=
  finSumFinEquiv (Sum.inl j)

/-- The duplicate-variable embedding. -/
def duplicateVariable (j : Fin vars) : Fin (vars + vars) :=
  finSumFinEquiv (Sum.inr j)

@[simp] theorem finSumFinEquiv_symm_oldRow (row : Fin eqs) :
    finSumFinEquiv.symm (oldRow (vars := vars) row) = Sum.inl row := by
  simp [oldRow]

@[simp] theorem finSumFinEquiv_symm_equalityRow (j : Fin vars) :
    finSumFinEquiv.symm (equalityRow (eqs := eqs) j) = Sum.inr j := by
  simp [equalityRow]

@[simp] theorem finSumFinEquiv_symm_oldVariable (j : Fin vars) :
    finSumFinEquiv.symm (oldVariable j) = Sum.inl j := by
  simp [oldVariable]

@[simp] theorem finSumFinEquiv_symm_duplicateVariable (j : Fin vars) :
    finSumFinEquiv.symm (duplicateVariable j) = Sum.inr j := by
  exact Equiv.symm_apply_apply finSumFinEquiv (Sum.inr j)

@[simp] theorem finSumFinEquiv_symm_castAdd
    (j : Fin vars) :
    (finSumFinEquiv :
      (Fin vars ⊕ Fin vars) ≃ Fin (vars + vars)).symm
        (Fin.castAdd vars j) = Sum.inl j := by
  exact Equiv.symm_apply_apply finSumFinEquiv (Sum.inl j)

@[simp] theorem finSumFinEquiv_symm_addNat
    (j : Fin vars) :
    (finSumFinEquiv :
      (Fin vars ⊕ Fin vars) ≃ Fin (vars + vars)).symm
        (j.addNat vars) = Sum.inr j := by
  have h :
      j.addNat vars = Fin.natAdd vars j := by
    apply Fin.ext
    simp [Nat.add_comm]
  rw [h]
  exact finSumFinEquiv_symm_apply_natAdd j

/-- Add one duplicate variable and one equality row per old variable. -/
def augment (I : DQLSystem eqs vars) :
    DQLSystem (eqs + vars) (vars + vars) where
  quadratic row j :=
    match finSumFinEquiv.symm row, finSumFinEquiv.symm j with
    | Sum.inl r, Sum.inl k => I.quadratic r k
    | _, _ => 0
  linear row j :=
    match finSumFinEquiv.symm row, finSumFinEquiv.symm j with
    | Sum.inl r, Sum.inl k => I.linear r k
    | Sum.inl _, Sum.inr _ => 0
    | Sum.inr k, Sum.inl j => if j = k then 1 else 0
    | Sum.inr k, Sum.inr j => if j = k then -1 else 0
  rhs row :=
    match finSumFinEquiv.symm row with
    | Sum.inl r => I.rhs r
    | Sum.inr _ => 0

/-- Duplicate an old witness into both halves of the enlarged vector. -/
def liftWitness (x : Fin vars → ℤ) : Fin (vars + vars) → ℤ :=
  fun j =>
    match finSumFinEquiv.symm j with
    | Sum.inl k => x k
    | Sum.inr k => x k

/-- Restrict an enlarged witness to its first (old-variable) half. -/
def restrictWitness (z : Fin (vars + vars) → ℤ) : Fin vars → ℤ :=
  fun j => z (oldVariable j)

@[simp] theorem liftWitness_oldVariable
    (x : Fin vars → ℤ) (j : Fin vars) :
    liftWitness x (oldVariable j) = x j := by
  simp [liftWitness]

@[simp] theorem liftWitness_duplicateVariable
    (x : Fin vars → ℤ) (j : Fin vars) :
    liftWitness x (duplicateVariable j) = x j := by
  simp [liftWitness]

@[simp] theorem restrictWitness_apply
    (z : Fin (vars + vars) → ℤ) (j : Fin vars) :
    restrictWitness z j = z (oldVariable j) :=
  rfl

@[simp] theorem augment_quadratic_oldRow_oldVariable
    (I : DQLSystem eqs vars) (row : Fin eqs) (j : Fin vars) :
    (augment I).quadratic (oldRow (vars := vars) row) (oldVariable j) =
      I.quadratic row j := by
  simp [augment]

@[simp] theorem augment_linear_oldRow_oldVariable
    (I : DQLSystem eqs vars) (row : Fin eqs) (j : Fin vars) :
    (augment I).linear (oldRow (vars := vars) row) (oldVariable j) =
      I.linear row j := by
  simp [augment]

@[simp] theorem augment_quadratic_oldRow_duplicateVariable
    (I : DQLSystem eqs vars) (row : Fin eqs) (j : Fin vars) :
    (augment I).quadratic (oldRow (vars := vars) row)
        (duplicateVariable j) = 0 := by
  simp [augment]

@[simp] theorem augment_linear_oldRow_duplicateVariable
    (I : DQLSystem eqs vars) (row : Fin eqs) (j : Fin vars) :
    (augment I).linear (oldRow (vars := vars) row)
        (duplicateVariable j) = 0 := by
  simp [augment]

@[simp] theorem augment_rhs_oldRow
    (I : DQLSystem eqs vars) (row : Fin eqs) :
    (augment I).rhs (oldRow (vars := vars) row) = I.rhs row := by
  simp [augment]

@[simp] theorem augment_quadratic_equalityRow
    (I : DQLSystem eqs vars) (j : Fin vars) (k : Fin (vars + vars)) :
    (augment I).quadratic (equalityRow (eqs := eqs) j) k = 0 := by
  simp [augment]

@[simp] theorem augment_linear_equalityRow_oldVariable
    (I : DQLSystem eqs vars) (j k : Fin vars) :
    (augment I).linear (equalityRow (eqs := eqs) j) (oldVariable k) =
      if k = j then 1 else 0 := by
  simp [augment]

@[simp] theorem augment_linear_equalityRow_duplicateVariable
    (I : DQLSystem eqs vars) (j k : Fin vars) :
    (augment I).linear (equalityRow (eqs := eqs) j)
        (duplicateVariable k) =
      if k = j then -1 else 0 := by
  simp [augment]

@[simp] theorem augment_rhs_equalityRow
    (I : DQLSystem eqs vars) (j : Fin vars) :
    (augment I).rhs (equalityRow (eqs := eqs) j) = 0 := by
  simp [augment]

/-- The value of an old row depends only on the first half of an enlarged
witness and is exactly the corresponding old row value. -/
theorem oldRow_sum_eq
    (I : DQLSystem eqs vars) (z : Fin (vars + vars) → ℤ)
    (row : Fin eqs) :
    (∑ j, ((augment I).quadratic (oldRow (vars := vars) row) j *
          (z j) ^ 2 +
        (augment I).linear (oldRow (vars := vars) row) j * z j)) =
      ∑ j, (I.quadratic row j * (restrictWitness z j) ^ 2 +
        I.linear row j * restrictWitness z j) := by
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp [augment, restrictWitness, oldVariable]

/-- A newly appended row evaluates to `x_j-y_j`. -/
theorem equalityRow_sum_eq
    (I : DQLSystem eqs vars) (z : Fin (vars + vars) → ℤ)
    (j : Fin vars) :
    (∑ k, ((augment I).quadratic (equalityRow (eqs := eqs) j) k *
          (z k) ^ 2 +
        (augment I).linear (equalityRow (eqs := eqs) j) k * z k)) =
      z (oldVariable j) - z (duplicateVariable j) := by
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp [augment, oldVariable, duplicateVariable, eq_comm]
  ring

/-- Lifting any old solution gives an enlarged solution. -/
theorem satisfies_augment_liftWitness
    (I : DQLSystem eqs vars) (x : Fin vars → ℤ)
    (hx : I.Satisfies x) :
    (augment I).Satisfies (liftWitness x) := by
  intro row
  obtain ⟨r | j, rfl⟩ := finSumFinEquiv.surjective row
  · change
      (∑ k, ((augment I).quadratic (oldRow (vars := vars) r) k *
          (liftWitness x k) ^ 2 +
        (augment I).linear (oldRow (vars := vars) r) k *
          liftWitness x k)) =
        (augment I).rhs (oldRow (vars := vars) r)
    rw [oldRow_sum_eq]
    simpa [restrictWitness] using hx r
  · change
      (∑ k, ((augment I).quadratic (equalityRow (eqs := eqs) j) k *
          (liftWitness x k) ^ 2 +
        (augment I).linear (equalityRow (eqs := eqs) j) k *
          liftWitness x k)) =
        (augment I).rhs (equalityRow (eqs := eqs) j)
    rw [equalityRow_sum_eq]
    simp

/-- Restricting any enlarged solution gives an old solution. -/
theorem satisfies_restrictWitness_of_satisfies_augment
    (I : DQLSystem eqs vars) (z : Fin (vars + vars) → ℤ)
    (hz : (augment I).Satisfies z) :
    I.Satisfies (restrictWitness z) := by
  intro row
  rw [← oldRow_sum_eq]
  simpa using hz (oldRow (vars := vars) row)

/-- The augmentation preserves and reflects integer solvability. -/
theorem augment_solvable_iff (I : DQLSystem eqs vars) :
    (augment I).Solvable ↔ I.Solvable := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨restrictWitness z, satisfies_restrictWitness_of_satisfies_augment I z hz⟩
  · rintro ⟨x, hx⟩
    exact ⟨liftWitness x, satisfies_augment_liftWitness I x hx⟩

/-- The appended equality rows make every linear column nonzero. -/
theorem augment_hasNonzeroLinearColumn (I : DQLSystem eqs vars) :
    HasNonzeroLinearColumn (augment I) := by
  intro column
  obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective column
  · refine ⟨equalityRow (eqs := eqs) j, ?_⟩
    norm_num [augment, equalityRow]
  · refine ⟨equalityRow (eqs := eqs) j, ?_⟩
    norm_num [augment, equalityRow]

/-! ## Effectivity -/

private theorem intSignedCodeEquiv_primrec :
    Primrec intSignedCodeEquiv := by
  rw [← Primrec.encode_iff]
  exact
    (Primrec.encode :
      Primrec (fun z : ℤ ↦ Encodable.encode z)).of_eq
      (by
        intro z
        cases z <;> rfl)

private theorem augmentQuadraticCode_primrec :
    Primrec
      (fun I : DQLSystem eqs vars ↦
        fun row : Fin (eqs + vars) ↦
          fun j : Fin (vars + vars) ↦
            intSignedCodeEquiv ((augment I).quadratic row j)) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro row
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro j
  cases hrow : finSumFinEquiv.symm row with
  | inl r =>
      cases hj : finSumFinEquiv.symm j with
      | inl k =>
          exact
            (intSignedCodeEquiv_primrec.comp
              (DetectorCharacterCode.quadraticEntry_primrec r k)).of_eq
                fun I ↦ by simp [augment, hrow, hj]
      | inr k =>
          exact
            (Primrec.const (intSignedCodeEquiv (0 : ℤ))).of_eq
              fun I ↦ by simp [augment, hrow, hj]
  | inr r =>
      exact
        (Primrec.const (intSignedCodeEquiv (0 : ℤ))).of_eq
          fun I ↦ by simp [augment, hrow]

private theorem augmentLinearCode_primrec :
    Primrec
      (fun I : DQLSystem eqs vars ↦
        fun row : Fin (eqs + vars) ↦
          fun j : Fin (vars + vars) ↦
            intSignedCodeEquiv ((augment I).linear row j)) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro row
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro j
  cases hrow : finSumFinEquiv.symm row with
  | inl r =>
      cases hj : finSumFinEquiv.symm j with
      | inl k =>
          exact
            (intSignedCodeEquiv_primrec.comp
              (DetectorCharacterCode.linearEntry_primrec r k)).of_eq
                fun I ↦ by simp [augment, hrow, hj]
      | inr k =>
          exact
            (Primrec.const (intSignedCodeEquiv (0 : ℤ))).of_eq
              fun I ↦ by simp [augment, hrow, hj]
  | inr k =>
      cases hj : finSumFinEquiv.symm j with
      | inl l =>
          by_cases hlk : l = k
          · exact
              (Primrec.const (intSignedCodeEquiv (1 : ℤ))).of_eq
                fun I ↦ by simp [augment, hrow, hj, hlk]
          · exact
              (Primrec.const (intSignedCodeEquiv (0 : ℤ))).of_eq
                fun I ↦ by simp [augment, hrow, hj, hlk]
      | inr l =>
          by_cases hlk : l = k
          · exact
              (Primrec.const (intSignedCodeEquiv (-1 : ℤ))).of_eq
                fun I ↦ by simp [augment, hrow, hj, hlk]
          · exact
              (Primrec.const (intSignedCodeEquiv (0 : ℤ))).of_eq
                fun I ↦ by simp [augment, hrow, hj, hlk]

private theorem augmentRhsCode_primrec :
    Primrec
      (fun I : DQLSystem eqs vars ↦
        fun row : Fin (eqs + vars) ↦
          intSignedCodeEquiv ((augment I).rhs row)) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro row
  cases hrow : finSumFinEquiv.symm row with
  | inl r =>
      exact
        (intSignedCodeEquiv_primrec.comp
          (DetectorCharacterCode.rhsEntry_primrec r)).of_eq
            fun I ↦ by simp [augment, hrow]
  | inr j =>
      exact
        (Primrec.const (intSignedCodeEquiv (0 : ℤ))).of_eq
          fun I ↦ by simp [augment, hrow]

/-- The finite coefficient code of the augmented system is primitive
recursive in the finite coefficient code of the old system. -/
theorem augmentFiniteCode_primrec :
    Primrec
      (fun I : DQLSystem eqs vars ↦
        dqlSystemCodeEquiv (eqs + vars) (vars + vars) (augment I)) := by
  exact
    (Primrec.pair
      (Primrec.pair augmentQuadraticCode_primrec
        augmentLinearCode_primrec)
      augmentRhsCode_primrec).of_eq fun I ↦ rfl

/-- The solvability-preserving augmentation is primitive recursive. -/
theorem augment_primrec :
    Primrec
      (augment :
        DQLSystem eqs vars →
          DQLSystem (eqs + vars) (vars + vars)) := by
  exact
    (Primrec.of_equiv_symm.comp augmentFiniteCode_primrec).of_eq
      fun I ↦ by
        simp

/-- Computable form of `augment_primrec`, convenient for compiler
composition. -/
theorem augment_computable :
    Computable
      (augment :
        DQLSystem eqs vars →
          DQLSystem (eqs + vars) (vars + vars)) :=
  augment_primrec.to_comp

end DQLNonzeroLinearAugmentation

end HGAS
