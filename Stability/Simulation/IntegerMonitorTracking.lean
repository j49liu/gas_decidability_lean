import Stability.Simulation.FundedMonitorTracking
import Stability.Simulation.RegisterRestartEmbedding

/-!
# Robust tracking of embedded integer restart runs

Integer countdowns always lie outside the open unit interval. Every
embedded restart state therefore has a concrete nonexpansive local branch,
including exhaustion, reset, and halt. The actual monitor tracks all finite
prefixes with the fixed summable error allowance.
-/

namespace Stability.Simulation.RestartMachine

open MachineCoordinate RegisterTransition

noncomputable section

variable {k s : ℕ}

theorem exists_nonexpansive_branch_realState (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (state : State k s) :
    ∃ F : (MachineCoordinate k → ℝ) → MachineCoordinate k → ℝ,
      LipschitzWith 1 F ∧ ∀ x, ‖x - realState state‖ ≤ 1 / 8 →
        transitionMap program entry initial x = F x := by
  cases state with
  | mk budget countdown label registers =>
      cases label with
      | restart =>
          refine ⟨resetBranch entry initial, lipschitzWith_resetBranch entry initial,
            fun x hx ↦ transitionMap_eq_resetBranch program entry initial ?_⟩
          simpa [realState, registerState, realRestartLabel] using
            (norm_le_pi_norm
              (x - realState ⟨budget, countdown, .restart, registers⟩) .label).trans hx
      | active q =>
          refine ⟨frozenInstructionBranch (program q)
              (realState ⟨budget, countdown, .active q, registers⟩),
            lipschitzWith_frozenInstructionBranch _ _, fun x hx ↦ ?_⟩
          apply transitionMap_eq_frozen_of_near program entry initial q rfl _
            (fun i ↦ ⟨registers i, rfl⟩) hx
          change (countdown : ℝ) ≤ 0 ∨ 1 ≤ (countdown : ℝ)
          by_cases hc : countdown ≤ 0
          · exact Or.inl (by exact_mod_cast hc)
          · exact Or.inr (by exact_mod_cast (show (1 : ℤ) ≤ countdown by omega))
      | halt =>
          refine ⟨haltBranch (s := s), lipschitzWith_haltBranch, fun x hx ↦ ?_⟩
          apply transitionMap_eq_haltBranch program entry initial
          exact (norm_le_pi_norm
            (x - realState ⟨budget, countdown, .halt, registers⟩) .label).trans hx

end

end Stability.Simulation.RestartMachine

namespace Stability.Simulation.ClockedMonitor

open Set MonitorCoordinate

noncomputable section

variable {k s : ℕ}

/-- The actual two-buffer dynamics track any embedded integer restart
orbit. No local-branch or update-error conclusion is assumed. -/
theorem forced_integer_tracking_error_lt_fixedBudget (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ)
    {origin finish radius : ℝ} {x : ℝ → MonitorCoordinate k → ℝ}
    {forcingA forcingB : ℝ → MachineCoordinate k → ℝ}
    (hx : ContinuousOn x (Icc origin finish))
    (hforcingA : ContinuousOn forcingA (Icc origin finish))
    (hforcingB : ContinuousOn forcingB (Icc origin finish))
    (hderiv : ∀ t ∈ Ioo origin finish, HasDerivAt x
      (field program entry initial (x t) + forcingVector (forcingA t) (forcingB t)) t)
    (hu0 : x origin u = 0) (hv0 : x origin v = -radius) (hradius : 0 ≤ radius)
    (hamplitude : (1 / 2 : ℝ) < radius ^ 2) (N : ℕ)
    (hend : halfTurnBoundary origin (2 * N) ≤ finish)
    (state : RestartMachine.State k s) {δ : ℝ}
    (hinitial : ‖bufferA (x origin) - RestartMachine.realState state‖ ≤ δ)
    (hδ : δ ≤ 1 / 16)
    (hmass : forcingMass (jointForcingMagnitude forcingA forcingB) origin finish ≤ 1 / 256) :
    ∀ n ≤ N,
      ‖bufferA (x (halfTurnBoundary origin (2 * n))) -
        (RegisterTransition.transitionMap program entry initial)^[n]
          (RestartMachine.realState state)‖ < δ + 11 / 1024 := by
  have hmagnitude : ContinuousOn (jointForcingMagnitude forcingA forcingB)
      (Icc origin finish) := hforcingA.norm.sup hforcingB.norm
  have hbudget := turnErrorBudget_lt_fixedBudget (x origin clock) N hmagnitude hend hmass
  have hmargin : δ + turnErrorBudget (x origin clock) origin
      (jointForcingMagnitude forcingA forcingB) N +
      forcingMass (jointForcingMagnitude forcingA forcingB) origin finish ≤ 1 / 8 := by
    linarith
  have htrack := forced_tracking_error_le_of_local_branches program entry initial hx
    hforcingA hforcingB hderiv hu0 hv0 hradius hamplitude N hend _ hinitial hmargin
    (fun n _ ↦ by
      rw [RestartMachine.iterate_transitionMap_realState]
      exact RestartMachine.exists_nonexpansive_branch_realState program entry initial _)
  intro n hn
  have hmono := turnErrorBudget_monotone (x origin clock) origin
    (jointForcingMagnitude forcingA forcingB) hn
  exact (htrack n hn).trans_lt (by linarith)

end

end Stability.Simulation.ClockedMonitor
