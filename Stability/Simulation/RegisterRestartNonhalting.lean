import Stability.Simulation.RegisterRestart

/-!
# Unbounded resets from the designated nonhalting start

Each nonhalting clean attempt spends its full budget and returns to
restart. Budgets grow by one, so the actual reset count is unbounded.
Only this designated starting state is used in the nonhalting direction;
an already-halted starting state would remain halted.

Source: Section 3, https://arxiv.org/html/2609.22058v2#S3.
-/

namespace Stability.Simulation.RestartMachine

variable {k s : ℕ}

/-- Before a nonhalting clean attempt exhausts its budget, its countdown
and underlying configuration agree exactly with the literal machine run. -/
theorem run_clean_nonhalting_prefix (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (budget : ℕ)
    (configuration : RegisterMachine.Configuration k s)
    (hnonhalt : ∀ j : ℕ, (RegisterMachine.run program j configuration).label ≠ none)
    (n : ℕ) (hn : n ≤ budget) :
    run program entry initial n (ofConfiguration budget budget configuration) =
      ofConfiguration budget ((budget : ℤ) - (n : ℤ))
        (RegisterMachine.run program n configuration) := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
      rw [run, ih (by omega)]
      have hnInt : (n : ℤ) + 1 ≤ (budget : ℤ) := by exact_mod_cast hn
      have hpositive : ¬(budget : ℤ) - (n : ℤ) ≤ 0 := by omega
      have hnext : RegisterMachine.run program (n + 1) configuration =
          RegisterMachine.step program (RegisterMachine.run program n configuration) := by
        simpa only [RegisterMachine.run] using
          RegisterMachine.run_add program n 1 configuration
      rw [hnext]
      have hactive := hnonhalt n
      generalize RegisterMachine.run program n configuration = current at hactive ⊢
      cases current with
      | mk label registers =>
          cases label with
          | none => exact False.elim (hactive rfl)
          | some q =>
              simp [step, ofConfiguration, machineLabel, hpositive,
                RegisterMachine.step, sub_sub]

/-- The first step after spending a nonhalting clean attempt's budget
returns to restart and leaves the spent countdown equal to `-1`. -/
theorem run_clean_nonhalting_exhausts (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (budget : ℕ)
    (configuration : RegisterMachine.Configuration k s)
    (hnonhalt : ∀ j : ℕ, (RegisterMachine.run program j configuration).label ≠ none) :
    run program entry initial (budget + 1) (ofConfiguration budget budget configuration) =
      ⟨budget, -1, .restart, (RegisterMachine.run program budget configuration).registers⟩ := by
  rw [run, run_clean_nonhalting_prefix program entry initial budget configuration
    hnonhalt budget le_rfl]
  have hactive := hnonhalt budget
  generalize RegisterMachine.run program budget configuration = current at hactive ⊢
  cases current with
  | mk label registers =>
      cases label with
      | none => exact False.elim (hactive rfl)
      | some q => simp [step, ofConfiguration, machineLabel]

/-- A reset followed by its entire nonhalting attempt returns to reset
with budget increased by exactly one. -/
theorem run_nonhalting_reset_cycle (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ)
    (hnonhalt : ¬RegisterMachine.Halts program ⟨some entry, initial⟩)
    (state : State k s) (hreset : state.label = .restart) :
    run program entry initial (state.budget + 3) state =
      ⟨state.budget + 1, -1, .restart,
        (RegisterMachine.run program (state.budget + 1) ⟨some entry, initial⟩).registers⟩ := by
  have hnever (j : ℕ) :
      (RegisterMachine.run program j ⟨some entry, initial⟩).label ≠ none :=
    fun h ↦ hnonhalt ⟨j, h⟩
  have hstart : step program entry initial state =
      ofConfiguration (state.budget + 1) ((state.budget + 1 : ℕ) : ℤ)
        ⟨some entry, initial⟩ := by
    simp [step, hreset, ofConfiguration, machineLabel]
  rw [show state.budget + 3 = (state.budget + 1 + 1) + 1 by omega,
    run_succ_start, hstart]
  exact run_clean_nonhalting_exhausts program entry initial (state.budget + 1)
    ⟨some entry, initial⟩ hnever

/-- The designated restart start has budget and countdown zero. -/
def initialState (initial : Fin k → ℕ) : State k s := ⟨0, 0, .restart, initial⟩

/-- Every natural budget occurs at an actual reset of the designated
nonhalting run. This supplies a concrete unbounded sequence of events. -/
theorem exists_run_restart_budget (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ)
    (hnonhalt : ¬RegisterMachine.Halts program ⟨some entry, initial⟩) (budget : ℕ) :
    ∃ t : ℕ, (run program entry initial t (initialState initial)).budget = budget ∧
      (run program entry initial t (initialState initial)).label = .restart := by
  induction budget with
  | zero => exact ⟨0, rfl, rfl⟩
  | succ budget ih =>
      obtain ⟨t, hbudget, hreset⟩ := ih
      let current := run program entry initial t (initialState initial)
      have hcycle := run_nonhalting_reset_cycle program entry initial hnonhalt current hreset
      refine ⟨t + (current.budget + 3), ?_, ?_⟩
      · rw [run_add]
        change (run program entry initial (current.budget + 3) current).budget = budget + 1
        rw [hcycle]
        exact congrArg (fun n : ℕ ↦ n + 1) hbudget
      · rw [run_add]
        change (run program entry initial (current.budget + 3) current).label = .restart
        rw [hcycle]

/-- The literal reset count of the designated nonhalting run is unbounded. -/
theorem exists_restartCount_eq (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ)
    (hnonhalt : ¬RegisterMachine.Halts program ⟨some entry, initial⟩) (count : ℕ) :
    ∃ t : ℕ, restartCount program entry initial (initialState initial) t = count := by
  obtain ⟨t, hbudget, _⟩ := exists_run_restart_budget program entry initial hnonhalt count
  refine ⟨t, ?_⟩
  rw [run_budget_eq_initial_add_restartCount] at hbudget
  simpa [initialState] using hbudget

/-- Halting is equivalent to a uniform finite reset-count bound over all
discrete initial states in this natural-budget, integer-countdown model. -/
theorem halts_iff_uniformly_bounded_restarts (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) :
    RegisterMachine.Halts program ⟨some entry, initial⟩ ↔
      ∃ bound : ℕ, ∀ (state : State k s) (n : ℕ),
        restartCount program entry initial state n ≤ bound := by
  constructor
  · rintro ⟨T, hhalt⟩
    exact ⟨T, restartCount_le_haltingTime program entry initial T hhalt⟩
  · rintro ⟨bound, hbound⟩
    by_contra hnonhalt
    obtain ⟨t, ht⟩ := exists_restartCount_eq program entry initial hnonhalt (bound + 1)
    have h := hbound (initialState initial) t
    rw [ht] at h
    omega

end Stability.Simulation.RestartMachine
