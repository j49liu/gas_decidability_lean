import Stability.Simulation.RegisterLocalBranches

/-!
# Agreement with literal register-machine execution

Natural register configurations are embedded with real budgets and
countdowns. At active labels, an available budget executes the actual
finite program instruction; an exhausted budget moves to restart.
Reset and halt have their stated exact actions.

Source: Section 3, https://arxiv.org/html/2609.22058v2#S3.
-/

namespace Stability.Simulation.RegisterTransition

open MachineCoordinate

noncomputable section

variable {k s : ℕ}

/-- Embed natural registers, with arbitrary real administrative values. -/
def registerState (h c : ℝ) (r : Fin k → ℕ) (q : ℝ) : MachineCoordinate k → ℝ
  | .budget => h
  | .countdown => c
  | .label => q
  | .register i => r i

/-- Embed an actual register-machine configuration using its encoded label. -/
def configurationState (h c : ℝ) (configuration : RegisterMachine.Configuration k s) :
    MachineCoordinate k → ℝ :=
  registerState h c configuration.registers (realLabel configuration.label)

/-- If the countdown permits execution, the real branch performs exactly
the natural-number instruction, including both decrement cases. -/
theorem instructionBranch_eq_execute (instruction : RegisterMachine.Instruction k s)
    (h c q : ℝ) (r : Fin k → ℕ) (hc : 1 ≤ c) :
    instructionBranch instruction (registerState h c r q) =
      configurationState h (c - 1) (RegisterMachine.execute instruction r) := by
  have hz : zeroGate c = 0 := zeroGate_eq_zero (by linarith)
  cases instruction with
  | inc i next =>
      ext coordinate
      cases coordinate with
      | budget => rfl
      | countdown => rfl
      | label =>
          simp [instructionBranch, configurationState, registerState, RegisterMachine.execute, hz]
      | register j =>
          by_cases hji : j = i <;>
            simp [instructionBranch, configurationState, registerState,
              RegisterMachine.execute, hz, hji]
  | dec i zero positive =>
      by_cases hzero : r i = 0
      · have hzi : zeroGate (0 : ℝ) = 1 := zeroGate_eq_one (by norm_num)
        ext coordinate
        cases coordinate <;>
          simp [instructionBranch, configurationState, registerState,
            RegisterMachine.execute, hz, hzi, hzero]
      · have hri : 1 ≤ r i := Nat.one_le_iff_ne_zero.mpr hzero
        have hriReal : (1 : ℝ) ≤ r i := by exact_mod_cast hri
        have hzi : zeroGate (r i : ℝ) = 0 := zeroGate_eq_zero (by linarith)
        have hcast : ((r i - 1 : ℕ) : ℝ) = (r i : ℝ) - 1 := by
          rw [Nat.cast_sub hri, Nat.cast_one]
        ext coordinate
        cases coordinate with
        | budget => rfl
        | countdown => rfl
        | label =>
            simp [instructionBranch, configurationState, registerState,
              RegisterMachine.execute, hzero, hz, hzi]
        | register j =>
            by_cases hji : j = i <;>
              simp [instructionBranch, configurationState, registerState,
                RegisterMachine.execute, hzero, hz, hzi, hji, hcast]

/-- At an active label with an exhausted countdown, no register changes
and the next label is the literal restart label zero. -/
theorem instructionBranch_eq_exhausted (instruction : RegisterMachine.Instruction k s)
    (h c q : ℝ) (r : Fin k → ℕ) (hc : c ≤ 0) :
    instructionBranch instruction (registerState h c r q) = registerState h (c - 1) r 0 := by
  have hz : zeroGate c = 1 := zeroGate_eq_one (by linarith)
  cases instruction <;> ext coordinate <;> cases coordinate <;>
    simp [instructionBranch, registerState, hz]

/-- The full real extension executes the finite program at honest active
labels. The initial input affects only the separate restart branch. -/
theorem transitionMap_eq_execute (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (q : Fin s)
    (h c : ℝ) (r : Fin k → ℕ) (hc : 1 ≤ c) :
    transitionMap program entry initial (configurationState h c ⟨some q, r⟩) =
      configurationState h (c - 1) (RegisterMachine.execute (program q) r) := by
  rw [transitionMap_eq_instructionBranch program entry initial q (by
    simp [configurationState, registerState])]
  exact instructionBranch_eq_execute (program q) h c (realLabel (some q)) r hc

theorem transitionMap_eq_exhausted (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (q : Fin s)
    (h c : ℝ) (r : Fin k → ℕ) (hc : c ≤ 0) :
    transitionMap program entry initial (configurationState h c ⟨some q, r⟩) =
      registerState h (c - 1) r 0 := by
  rw [transitionMap_eq_instructionBranch program entry initial q (by
    simp [configurationState, registerState])]
  exact instructionBranch_eq_exhausted (program q) h c (realLabel (some q)) r hc

/-- Restart erases every old register and countdown but retains and
increases the nonnegative part of the old budget. -/
theorem transitionMap_eq_restart (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (h c : ℝ) (r : Fin k → ℕ) :
    transitionMap program entry initial (registerState h c r 0) =
      configurationState (max h 0 + 1) (max h 0 + 1) ⟨some entry, initial⟩ := by
  rw [transitionMap_eq_resetBranch program entry initial (by simp [registerState])]
  rfl

/-- Honest halted states are fixed points of the full real transition. -/
theorem transitionMap_halted (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (h c : ℝ) (r : Fin k → ℕ) :
    transitionMap program entry initial (configurationState (s := s) h c ⟨none, r⟩) =
      configurationState (s := s) h c ⟨none, r⟩ := by
  rw [transitionMap_eq_haltBranch program entry initial (by
    simp [configurationState, registerState, realLabel])]
  ext coordinate
  cases coordinate <;> rfl

end

end Stability.Simulation.RegisterTransition
