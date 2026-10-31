import Stability.Computability.RegisterMachine
import Stability.Simulation.TransitionGates
import Mathlib.Data.Fintype.Sum

/-!
# The real extension of a restarting register program

The finite program supplies literal increment/decrement branches. The
real map blends them with disjoint label gates, reserving label zero for
a clean reset and using the halting branch away from active labels.

Source: Section 3, https://arxiv.org/html/2609.22058v2#S3.
-/

namespace Stability.Simulation

open Set

/-- Three administrative coordinates and a finite family of registers. -/
inductive MachineCoordinate (k : ℕ) where
  | budget
  | countdown
  | label
  | register (i : Fin k)
  deriving DecidableEq, Fintype

namespace RegisterTransition

open MachineCoordinate

noncomputable section

variable {k s : ℕ}

/-- The machine's optional label is placed after the reserved restart label. -/
def realLabel : Option (Fin s) → ℝ
  | none => (s : ℝ) + 1
  | some q => (q.val : ℝ) + 1

/-- A reset loads the specified initial registers and entry label, retaining
only the old budget, increased by one and floored at one. -/
def resetBranch (entry : Fin s) (initial : Fin k → ℕ)
    (x : MachineCoordinate k → ℝ) : MachineCoordinate k → ℝ
  | .budget => max (x budget) 0 + 1
  | .countdown => max (x budget) 0 + 1
  | .label => realLabel (some entry)
  | .register i => initial i

/-- The halting branch preserves every coordinate except the real label. -/
def haltBranch (x : MachineCoordinate k → ℝ) : MachineCoordinate k → ℝ
  | .label => (s : ℝ) + 1
  | i => x i

/-- The literal real INC/DEC branch, including exhaustion of the countdown. -/
def instructionBranch (instruction : RegisterMachine.Instruction k s)
    (x : MachineCoordinate k → ℝ) : MachineCoordinate k → ℝ :=
  match instruction with
  | .inc i next => fun
      | .budget => x budget
      | .countdown => x countdown - 1
      | .label => (1 - zeroGate (x countdown)) * realLabel next
      | .register j => x (.register j) + if j = i then 1 - zeroGate (x countdown) else 0
  | .dec i zero positive => fun
      | .budget => x budget
      | .countdown => x countdown - 1
      | .label => (1 - zeroGate (x countdown)) *
          (zeroGate (x (.register i)) * realLabel zero +
            (1 - zeroGate (x (.register i))) * realLabel positive)
      | .register j => x (.register j) -
          if j = i then (1 - zeroGate (x countdown)) * (1 - zeroGate (x (.register i))) else 0

/-- The global real transition map. Its definition never runs the program. -/
def transitionMap (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (x : MachineCoordinate k → ℝ) :
    MachineCoordinate k → ℝ := fun coordinate ↦
  haltBranch (s := s) x coordinate +
    labelGate (x label) *
      (resetBranch entry initial x coordinate - haltBranch (s := s) x coordinate) +
    ∑ q : Fin s, labelGate (x label - realLabel (some q)) *
      (instructionBranch (program q) x coordinate - haltBranch (s := s) x coordinate)

@[simp] theorem instructionBranch_budget (instruction : RegisterMachine.Instruction k s)
    (x : MachineCoordinate k → ℝ) : instructionBranch instruction x budget = x budget := by
  cases instruction <;> rfl

/-- The exact budget formula holds at every real state, including garbage. -/
theorem transitionMap_budget (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (x : MachineCoordinate k → ℝ) :
    transitionMap program entry initial x budget =
      x budget + labelGate (x label) * (1 + max (-x budget) 0) := by
  simp only [transitionMap, haltBranch, resetBranch, instructionBranch_budget,
    sub_self, mul_zero, Finset.sum_const_zero, add_zero]
  rcases le_total 0 (x budget) with h | h
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
    ring
  · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
    ring

/-- The real transition never decreases its budget coordinate. -/
theorem budget_le_transitionMap (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (x : MachineCoordinate k → ℝ) :
    x budget ≤ transitionMap program entry initial x budget := by
  rw [transitionMap_budget]
  exact le_add_of_nonneg_right (mul_nonneg (labelGate_nonneg _) (by positivity))

/-- Every state in the reset plateau is sent to the exact clean-reset map. -/
theorem transitionMap_eq_resetBranch (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {x : MachineCoordinate k → ℝ}
    (hlabel : |x label| ≤ 1 / 8) :
    transitionMap program entry initial x = resetBranch entry initial x := by
  have hzero (q : Fin s) : labelGate (x label - realLabel (some q)) = 0 := by
    have h := labelGate_eq_zero_of_near_other_nat (i := 0) (j := q.val + 1)
      (by simpa only [Nat.cast_zero, sub_zero] using hlabel) (by omega)
    simpa only [realLabel, Nat.cast_add, Nat.cast_one] using h
  ext coordinate
  simp only [transitionMap, hzero, zero_mul, Finset.sum_const_zero, add_zero,
    labelGate_eq_one hlabel, one_mul]
  ring

/-- The reset map is nonexpansive in the finite sup norm. -/
theorem lipschitzWith_resetBranch (entry : Fin s) (initial : Fin k → ℕ) :
    LipschitzWith 1 (resetBranch entry initial) := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro coordinate
  have hmax := (LipschitzWith.id.max_const (0 : ℝ)).dist_le_mul (x budget) (y budget)
  simp only [NNReal.coe_one, one_mul, Real.dist_eq, id_eq] at hmax
  have hbound := hmax.trans (norm_le_pi_norm (x - y) budget)
  cases coordinate with
  | budget => simpa [resetBranch] using hbound
  | countdown => simpa [resetBranch] using hbound
  | label => simp [resetBranch]
  | register i => simp [resetBranch]

/-- A plateau around an active label selects exactly its literal instruction. -/
theorem transitionMap_eq_instructionBranch (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {x : MachineCoordinate k → ℝ} (q : Fin s)
    (hlabel : |x label - realLabel (some q)| ≤ 1 / 8) :
    transitionMap program entry initial x = instructionBranch (program q) x := by
  have hnear : |x label - ((q.val + 1 : ℕ) : ℝ)| ≤ 1 / 8 := by
    simpa only [realLabel, Nat.cast_add, Nat.cast_one] using hlabel
  have hzero : labelGate (x label) = 0 := by
    simpa only [Nat.cast_zero, sub_zero] using
      labelGate_eq_zero_of_near_other_nat hnear (show q.val + 1 ≠ 0 by omega)
  have hother (p : Fin s) (hp : p ≠ q) : labelGate (x label - realLabel (some p)) = 0 := by
    have hne : q.val + 1 ≠ p.val + 1 := by
      intro h
      exact hp (Fin.ext (Nat.add_right_cancel h).symm)
    simpa only [realLabel, Nat.cast_add, Nat.cast_one] using
      labelGate_eq_zero_of_near_other_nat hnear hne
  ext coordinate
  have hsum : (∑ p : Fin s, labelGate (x label - realLabel (some p)) *
      (instructionBranch (program p) x coordinate - haltBranch (s := s) x coordinate)) =
      instructionBranch (program q) x coordinate - haltBranch (s := s) x coordinate := by
    rw [Finset.sum_eq_single q]
    · rw [labelGate_eq_one hlabel, one_mul]
    · intro p _ hp
      rw [hother p hp, zero_mul]
    · simp
  simp only [transitionMap, hzero, zero_mul, add_zero, hsum]
  ring

/-- Near the halting label, all active and reset gates vanish. -/
theorem transitionMap_eq_haltBranch (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {x : MachineCoordinate k → ℝ}
    (hlabel : |x label - ((s : ℝ) + 1)| ≤ 1 / 8) :
    transitionMap program entry initial x = haltBranch (s := s) x := by
  have hnear : |x label - ((s + 1 : ℕ) : ℝ)| ≤ 1 / 8 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hlabel
  have hzero : labelGate (x label) = 0 := by
    simpa only [Nat.cast_zero, sub_zero] using
      labelGate_eq_zero_of_near_other_nat hnear (show s + 1 ≠ 0 by omega)
  have hother (q : Fin s) : labelGate (x label - realLabel (some q)) = 0 := by
    have hne : s + 1 ≠ q.val + 1 := by have := q.isLt; omega
    simpa only [realLabel, Nat.cast_add, Nat.cast_one] using
      labelGate_eq_zero_of_near_other_nat hnear hne
  ext coordinate
  simp [transitionMap, hzero, hother]

end

end RegisterTransition

end Stability.Simulation
