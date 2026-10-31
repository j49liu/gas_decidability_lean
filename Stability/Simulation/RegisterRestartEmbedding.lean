import Stability.Simulation.RegisterRestartNonhalting
import Stability.Simulation.RegisterTransitionExactness

/-!
# Embedding the literal restart runs in the real transition map

Every discrete step agrees with the already defined real map, including
negative integer countdowns. Consequently the finite reset-count bound
holds along its embedded integer trajectories. Arbitrary real starting
states and fractional-countdown tracking are not covered by this result.
-/

namespace Stability.Simulation.RestartMachine

open MachineCoordinate RegisterTransition

noncomputable section

variable {k s : ℕ}

def realRestartLabel : Label s → ℝ
  | .restart => 0
  | .active q => realLabel (some q)
  | .halt => realLabel (s := s) none

def realState (state : State k s) : MachineCoordinate k → ℝ :=
  registerState state.budget state.countdown state.registers (realRestartLabel state.label)

@[simp] theorem realState_ofConfiguration (budget : ℕ) (countdown : ℤ)
    (configuration : RegisterMachine.Configuration k s) :
    realState (ofConfiguration budget countdown configuration) =
      configurationState budget countdown configuration := by
  cases configuration with
  | mk label registers => cases label <;> rfl

/-- The explicit real transition map intertwines with the literal discrete
restart step, rather than a postulated simulation relation. -/
theorem transitionMap_realState (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (state : State k s) :
    transitionMap program entry initial (realState state) =
      realState (step program entry initial state) := by
  cases state with
  | mk budget countdown label registers =>
      cases label with
      | restart =>
          change transitionMap program entry initial
            (registerState budget countdown registers 0) = _
          rw [transitionMap_eq_restart]
          ext coordinate
          cases coordinate <;>
            simp [realState, step, registerState, configurationState,
              realRestartLabel]
      | active q =>
          change transitionMap program entry initial
            (configurationState budget countdown ⟨some q, registers⟩) = _
          by_cases hc : countdown ≤ 0
          · rw [transitionMap_eq_exhausted program entry initial q _ _ registers
              (by exact_mod_cast hc)]
            ext coordinate
            cases coordinate <;> simp [realState, step, registerState, realRestartLabel, hc]
          · have hcInt : (1 : ℤ) ≤ countdown := by omega
            have hcReal : (1 : ℝ) ≤ (countdown : ℝ) := by exact_mod_cast hcInt
            rw [transitionMap_eq_execute program entry initial q _ _ registers hcReal]
            simp [step, hc]
      | halt =>
          change transitionMap program entry initial
            (configurationState (s := s) budget countdown ⟨none, registers⟩) = _
          rw [transitionMap_halted]
          rfl

/-- All finite iterates, not just individual steps, agree with the real map. -/
theorem iterate_transitionMap_realState (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (state : State k s) (n : ℕ) :
    (transitionMap program entry initial)^[n] (realState state) =
      realState (run program entry initial n state) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, transitionMap_realState, run]

@[simp] theorem realState_label_eq_zero_iff (state : State k s) :
    realState state MachineCoordinate.label = 0 ↔ state.label = .restart := by
  cases state with
  | mk budget countdown label registers =>
      cases label with
      | restart => simp [realState, registerState, realRestartLabel]
      | active q =>
          have hpos : (0 : ℝ) < (q.val : ℝ) + 1 := by positivity
          simp [realState, registerState, realRestartLabel, realLabel, ne_of_gt hpos]
      | halt =>
          have hpos : (0 : ℝ) < (s : ℝ) + 1 := by positivity
          simp [realState, registerState, realRestartLabel, realLabel, ne_of_gt hpos]

/-- The actual real-map orbit has at most `T` reset labels on every finite
prefix when started from an embedded discrete state and the input halts. -/
theorem real_restartCount_le_haltingTime (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (T : ℕ)
    (hhalt : (RegisterMachine.run program T ⟨some entry, initial⟩).label = none)
    (state : State k s) (n : ℕ) :
    productiveCount (fun j ↦
      ((transitionMap program entry initial)^[j] (realState state)) MachineCoordinate.label = 0) n ≤
      T := by
  simpa only [restartCount, iterate_transitionMap_realState, realState_label_eq_zero_iff] using
    restartCount_le_haltingTime program entry initial T hhalt state n

/-- The designated actual real-map orbit has unbounded reset count when
the original input does not halt. -/
theorem real_exists_restartCount_eq (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ)
    (hnonhalt : ¬RegisterMachine.Halts program ⟨some entry, initial⟩) (count : ℕ) :
    ∃ t : ℕ, productiveCount (fun j ↦
      ((transitionMap program entry initial)^[j]
        (realState (initialState (s := s) initial))) MachineCoordinate.label = 0) t = count := by
  simpa only [restartCount, iterate_transitionMap_realState, realState_label_eq_zero_iff] using
    exists_restartCount_eq program entry initial hnonhalt count

/-- The discrete reset-count equivalence holds for actual real-map iterates
on the explicitly embedded discrete states. This does not quantify over
arbitrary real initial states. -/
theorem halts_iff_bounded_real_restarts_on_embedded_states
    (program : RegisterMachine.Program k s) (entry : Fin s) (initial : Fin k → ℕ) :
    RegisterMachine.Halts program ⟨some entry, initial⟩ ↔
      ∃ bound : ℕ, ∀ (state : State k s) (n : ℕ), productiveCount (fun j ↦
        ((transitionMap program entry initial)^[j] (realState state))
          MachineCoordinate.label = 0) n ≤ bound := by
  simpa only [restartCount, iterate_transitionMap_realState, realState_label_eq_zero_iff] using
    halts_iff_uniformly_bounded_restarts program entry initial

end

end Stability.Simulation.RestartMachine
