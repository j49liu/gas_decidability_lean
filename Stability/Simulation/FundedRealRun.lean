import Stability.Simulation.RegisterTransitionExactness

/-!
# Funded clean attempts with real countdowns

For the first `T` steps of an attempt funded by a real countdown `B ≥ T`,
the actual real map follows the original register computation. A halt
freezes the unused countdown. The proof does not claim regularity after
an arbitrary fractional countdown has been exhausted.

Source: the late-reset argument in Section 4,
https://arxiv.org/html/2609.22058v2#S4.
-/

namespace Stability.Simulation.RegisterTransition

noncomputable section

variable {k s : ℕ}

/-- A real-funded clean attempt agrees with the original computation up
to its funded horizon. The remaining countdown is bounded below because
an early halt stops spending it. -/
theorem iterate_funded_configuration (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (h B : ℝ)
    (configuration : RegisterMachine.Configuration k s) (n : ℕ) (hn : (n : ℝ) ≤ B) :
    ∃ countdown : ℝ, B - (n : ℝ) ≤ countdown ∧
      (transitionMap program entry initial)^[n] (configurationState h B configuration) =
        configurationState h countdown (RegisterMachine.run program n configuration) := by
  induction n with
  | zero => exact ⟨B, by simp, rfl⟩
  | succ n ih =>
      have hnReal : (n : ℝ) + 1 ≤ B := by exact_mod_cast hn
      obtain ⟨countdown, hcountdown, hrun⟩ := ih (by linarith)
      have hpositive : 1 ≤ countdown := by linarith
      have hnext : ∃ nextCountdown : ℝ, B - ((n + 1 : ℕ) : ℝ) ≤ nextCountdown ∧
          transitionMap program entry initial
              (configurationState h countdown (RegisterMachine.run program n configuration)) =
            configurationState h nextCountdown
              (RegisterMachine.step program (RegisterMachine.run program n configuration)) := by
        generalize RegisterMachine.run program n configuration = current
        cases current with
        | mk label registers =>
            cases label with
            | none =>
                refine ⟨countdown, ?_, ?_⟩
                · push_cast
                  linarith
                · exact transitionMap_halted program entry initial h countdown registers
            | some q =>
                refine ⟨countdown - 1, ?_, ?_⟩
                · push_cast
                  linarith
                · exact transitionMap_eq_execute program entry initial q h countdown
                    registers hpositive
      obtain ⟨nextCountdown, hbound, hnext⟩ := hnext
      have hmachine : RegisterMachine.run program (n + 1) configuration =
          RegisterMachine.step program (RegisterMachine.run program n configuration) := by
        simpa only [RegisterMachine.run] using
          RegisterMachine.run_add program n 1 configuration
      refine ⟨nextCountdown, hbound, ?_⟩
      rw [Function.iterate_succ_apply', hrun, hnext, hmachine]

/-- Funding the input's halting time reaches an actual fixed point of
the real map, even when the granted budget is not an integer. -/
theorem iterate_funded_halt_fixed (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (h B : ℝ) (T : ℕ) (hB : (T : ℝ) ≤ B)
    (hhalt : (RegisterMachine.run program T ⟨some entry, initial⟩).label = none) :
    transitionMap program entry initial
        ((transitionMap program entry initial)^[T]
          (configurationState h B ⟨some entry, initial⟩)) =
      (transitionMap program entry initial)^[T]
        (configurationState h B ⟨some entry, initial⟩) := by
  obtain ⟨countdown, _, hrun⟩ := iterate_funded_configuration program entry initial h B
    ⟨some entry, initial⟩ T hB
  rw [hrun]
  generalize RegisterMachine.run program T ⟨some entry, initial⟩ = current at hhalt ⊢
  cases current with
  | mk label registers =>
      change label = none at hhalt
      subst label
      exact transitionMap_halted program entry initial h countdown registers

/-- An arbitrary real state in the reset plateau is sent to a clean
attempt; sufficient budget makes that attempt halt after `T` more steps. -/
theorem iterate_reset_plateau_halt_fixed (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (x : MachineCoordinate k → ℝ)
    (hreset : |x MachineCoordinate.label| ≤ 1 / 8) (T : ℕ)
    (hbudget : (T : ℝ) ≤ max (x MachineCoordinate.budget) 0 + 1)
    (hhalt : (RegisterMachine.run program T ⟨some entry, initial⟩).label = none) :
    transitionMap program entry initial ((transitionMap program entry initial)^[T + 1] x) =
      (transitionMap program entry initial)^[T + 1] x := by
  rw [Function.iterate_succ_apply, transitionMap_eq_resetBranch program entry initial hreset]
  have hclean : resetBranch entry initial x =
      configurationState (max (x MachineCoordinate.budget) 0 + 1)
        (max (x MachineCoordinate.budget) 0 + 1) ⟨some entry, initial⟩ := by
    ext coordinate
    cases coordinate <;> rfl
  rw [hclean]
  exact iterate_funded_halt_fixed program entry initial _ _ T hbudget hhalt

end

end Stability.Simulation.RegisterTransition
