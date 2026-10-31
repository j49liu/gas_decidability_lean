import Stability.Computability.RegisterMachine
import Stability.Simulation.RestartBudget

/-!
# Literal restart runs with growing budgets

Budgets are natural numbers and countdowns are integers. Registers are
natural numbers, as in the underlying finite INC/DEC machine. These
discrete statements do not claim invariance of regular states for
arbitrary fractional countdowns in the real extension.

Source: Section 3, https://arxiv.org/html/2609.22058v2#S3.
-/

namespace Stability.Simulation.RestartMachine

/-- Restart, active instruction, and absorbing halt are distinct labels. -/
inductive Label (s : ℕ) where
  | restart
  | active (q : Fin s)
  | halt
  deriving DecidableEq

@[ext] structure State (k s : ℕ) where
  budget : ℕ
  countdown : ℤ
  label : Label s
  registers : Fin k → ℕ
  deriving DecidableEq

variable {k s : ℕ}

def machineLabel : Option (Fin s) → Label s
  | none => .halt
  | some q => .active q

def ofConfiguration (budget : ℕ) (countdown : ℤ)
    (configuration : RegisterMachine.Configuration k s) : State k s :=
  ⟨budget, countdown, machineLabel configuration.label, configuration.registers⟩

/-- A reset loads the input. Otherwise the literal program executes until
its countdown expires or it halts. No simulation predicate is built in. -/
def step (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) (state : State k s) : State k s :=
  match state.label with
  | .restart => ⟨state.budget + 1, (state.budget : ℤ) + 1, .active entry, initial⟩
  | .halt => state
  | .active q =>
      if state.countdown ≤ 0 then
        { state with countdown := state.countdown - 1, label := .restart }
      else ofConfiguration state.budget (state.countdown - 1)
        (RegisterMachine.execute (program q) state.registers)

/-- Actual finite iteration, with the final step performed last. -/
def run (program : RegisterMachine.Program k s) (entry : Fin s) (initial : Fin k → ℕ) :
    ℕ → State k s → State k s
  | 0, state => state
  | n + 1, state => step program entry initial (run program entry initial n state)

theorem run_succ_start (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (n : ℕ) (state : State k s) :
    run program entry initial (n + 1) state =
      run program entry initial n (step program entry initial state) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [run] at ih ⊢; rw [ih]

theorem run_add (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (m n : ℕ) (state : State k s) :
    run program entry initial (m + n) state =
      run program entry initial n (run program entry initial m state) := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
      change step program entry initial (run program entry initial (m + n) state) =
        step program entry initial (run program entry initial n (run program entry initial m state))
      rw [ih]

/-- Count the actual reset labels visited strictly before time `n`. -/
def restartCount (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (state : State k s) (n : ℕ) : ℕ :=
  productiveCount (fun j ↦ (run program entry initial j state).label = .restart) n

theorem step_budget (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (state : State k s) :
    (step program entry initial state).budget =
      state.budget + if state.label = .restart then 1 else 0 := by
  cases state with
  | mk budget countdown label registers =>
      cases label <;> simp [step, ofConfiguration, apply_ite]

/-- The budget is exactly its initial value plus the number of actual
reset steps, not a hypothesized productive-step sequence. -/
theorem run_budget_eq_initial_add_restartCount (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (state : State k s) (n : ℕ) :
    (run program entry initial n state).budget =
      state.budget + restartCount program entry initial state n := by
  induction n with
  | zero => simp [run, restartCount]
  | succ n ih =>
      rw [run, step_budget, ih]
      simp only [restartCount, productiveCount_succ]
      omega

private theorem machine_run_succ (program : RegisterMachine.Program k s)
    (n : ℕ) (configuration : RegisterMachine.Configuration k s) :
    RegisterMachine.run program (n + 1) configuration =
      RegisterMachine.step program (RegisterMachine.run program n configuration) := by
  simpa only [RegisterMachine.run] using RegisterMachine.run_add program n 1 configuration

/-- For the first `budget` steps, a clean attempt agrees with the original
machine. If it halts early, the unused countdown is retained; otherwise
one unit is spent per step. The lower bound includes both cases. -/
theorem run_clean_attempt (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (budget : ℕ)
    (configuration : RegisterMachine.Configuration k s) (n : ℕ) (hn : n ≤ budget) :
    ∃ countdown : ℤ, (budget : ℤ) - (n : ℤ) ≤ countdown ∧
      run program entry initial n (ofConfiguration budget budget configuration) =
        ofConfiguration budget countdown (RegisterMachine.run program n configuration) := by
  induction n with
  | zero => exact ⟨budget, by omega, rfl⟩
  | succ n ih =>
      obtain ⟨countdown, hcountdown, hrun⟩ := ih (by omega)
      have hnInt : (n : ℤ) + 1 ≤ (budget : ℤ) := by exact_mod_cast hn
      have hpositive : ¬countdown ≤ 0 := by omega
      have hnext : ∃ nextCountdown : ℤ, (budget : ℤ) - ((n + 1 : ℕ) : ℤ) ≤ nextCountdown ∧
          step program entry initial
              (ofConfiguration budget countdown (RegisterMachine.run program n configuration)) =
            ofConfiguration budget nextCountdown
              (RegisterMachine.step program (RegisterMachine.run program n configuration)) := by
        generalize RegisterMachine.run program n configuration = current
        cases current with
        | mk label registers =>
            cases label with
            | none => exact ⟨countdown, by omega, rfl⟩
            | some q =>
                refine ⟨countdown - 1, by omega, ?_⟩
                simp [step, ofConfiguration, machineLabel, hpositive, RegisterMachine.step]
      obtain ⟨nextCountdown, hbound, hnext⟩ := hnext
      refine ⟨nextCountdown, hbound, ?_⟩
      rw [run, hrun, hnext, machine_run_succ]

/-- A sufficiently funded reset reaches the literal halt label whenever
the original machine does, after the reset step and its halting time. -/
theorem run_halts_after_sufficient_reset (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (state : State k s)
    (hreset : state.label = .restart) (T : ℕ)
    (hbudget : T ≤ state.budget + 1)
    (hhalt : (RegisterMachine.run program T ⟨some entry, initial⟩).label = none) :
    (run program entry initial (T + 1) state).label = .halt := by
  have hstart : step program entry initial state =
      ofConfiguration (state.budget + 1) ((state.budget + 1 : ℕ) : ℤ)
        ⟨some entry, initial⟩ := by
    simp [step, hreset, ofConfiguration, machineLabel]
  obtain ⟨countdown, _, hrun⟩ := run_clean_attempt program entry initial
    (state.budget + 1) ⟨some entry, initial⟩ T hbudget
  rw [run_succ_start, hstart, hrun]
  simp [ofConfiguration, hhalt, machineLabel]

/-- Halt remains absorbing for the restart machine. -/
theorem run_halted (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {state : State k s}
    (hhalt : state.label = .halt) (n : ℕ) :
    run program entry initial n state = state := by
  induction n with
  | zero => rfl
  | succ n ih => simp [run, ih, step, hhalt]

private theorem machineLabel_ne_restart (label : Option (Fin s)) :
    machineLabel label ≠ .restart := by
  cases label <;> simp [machineLabel]

/-- A funded clean attempt cannot visit restart during its funded prefix. -/
theorem run_clean_attempt_ne_restart (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (budget : ℕ)
    (configuration : RegisterMachine.Configuration k s) (n : ℕ) (hn : n ≤ budget) :
    (run program entry initial n (ofConfiguration budget budget configuration)).label ≠
      .restart := by
  obtain ⟨_, _, hrun⟩ := run_clean_attempt program entry initial budget configuration n hn
  rw [hrun]
  exact machineLabel_ne_restart _

/-- Once a reset grants enough budget for the halting computation, no
later reset occurs, including times before that computation has finished. -/
theorem no_restart_after_sufficient_reset (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (state : State k s)
    (hreset : state.label = .restart) (T : ℕ)
    (hbudget : T ≤ state.budget + 1)
    (hhalt : (RegisterMachine.run program T ⟨some entry, initial⟩).label = none)
    (n : ℕ) (hn : 0 < n) :
    (run program entry initial n state).label ≠ .restart := by
  by_cases hsmall : n ≤ T + 1
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    have hstart : step program entry initial state =
        ofConfiguration (state.budget + 1) ((state.budget + 1 : ℕ) : ℤ)
          ⟨some entry, initial⟩ := by
      simp [step, hreset, ofConfiguration, machineLabel]
    rw [run_succ_start, hstart]
    exact run_clean_attempt_ne_restart program entry initial (state.budget + 1)
      ⟨some entry, initial⟩ m (by omega)
  · obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (show T + 1 ≤ n by omega)
    have hfinal := run_halts_after_sufficient_reset program entry initial state
      hreset T hbudget hhalt
    rw [hm, run_add, run_halted program entry initial hfinal m, hfinal]
    simp

/-- If the original input halts in `T` steps, every finite restart run
contains at most `T` resets, uniformly over natural initial budgets,
integer countdowns, registers, and labels. -/
theorem restartCount_le_haltingTime (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (T : ℕ)
    (hhalt : (RegisterMachine.run program T ⟨some entry, initial⟩).label = none)
    (state : State k s) (n : ℕ) : restartCount program entry initial state n ≤ T := by
  have hT : 0 < T := by
    by_contra h
    have hzero : T = 0 := by omega
    simp [hzero] at hhalt
  have hsucc (j : ℕ) : restartCount program entry initial state (j + 1) =
      restartCount program entry initial state j +
        if (run program entry initial j state).label = .restart then 1 else 0 :=
    productiveCount_succ _ j
  have hinvariant : ∀ j : ℕ,
      restartCount program entry initial state j ≤ T ∧
        (restartCount program entry initial state j = T →
          ∀ m : ℕ, (run program entry initial (j + m) state).label ≠ .restart) := by
    intro j
    induction j with
    | zero =>
        constructor
        · simp [restartCount]
        · intro h
          have : T = 0 := by simpa [restartCount] using h.symm
          omega
    | succ j ih =>
        by_cases hp : (run program entry initial j state).label = .restart
        · rw [hsucc, if_pos hp]
          have hlt : restartCount program entry initial state j < T := by
            apply lt_of_le_of_ne ih.1
            intro heq
            exact ih.2 heq 0 (by simpa using hp)
          refine ⟨by omega, ?_⟩
          intro hfull m
          have hbudget : T ≤ (run program entry initial j state).budget + 1 := by
            rw [run_budget_eq_initial_add_restartCount]
            omega
          have hfuture := no_restart_after_sufficient_reset program entry initial
            (run program entry initial j state) hp T hbudget hhalt (m + 1) (by omega)
          have htime : j + 1 + m = j + (m + 1) := by omega
          rw [htime, run_add]
          exact hfuture
        · rw [hsucc, if_neg hp, Nat.add_zero]
          refine ⟨ih.1, ?_⟩
          intro hfull m
          have htime : j + 1 + m = j + (m + 1) := by omega
          rw [htime]
          exact ih.2 hfull (m + 1)
  exact (hinvariant n).1

end Stability.Simulation.RestartMachine
