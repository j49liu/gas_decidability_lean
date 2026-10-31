import Stability.Simulation.SmoothedMonitorCompleteness

/-!
# Global forward trajectories on the actual radical graph

Global existence for the smoothed monitor and the exact graph derivative
give a genuine lifted trajectory from every canonical graph point. The
one-sided derivative at time zero is included. This is not a claim of
forward completeness from arbitrary off-graph states, nor after a later
polynomial time acceleration.
-/

namespace Stability.Simulation.ClockedMonitor

noncomputable section

open AbsFormula

variable {k s : ℕ}

theorem isForwardTrajectory_liftGraph (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1)
    {x : ℝ → MonitorCoordinate k → ℝ} {x₀ : MonitorCoordinate k → ℝ}
    (hx : HGAS.IsForwardTrajectory (smoothedField program entry initial ε) x x₀) :
    HGAS.IsForwardTrajectory (liftedField program entry initial ε)
      (fun t ↦ liftGraph program entry initial ε (x t))
      (liftGraph program entry initial ε x₀) := by
  refine ⟨congrArg (liftGraph program entry initial ε) hx.1, ?_⟩
  intro t ht
  apply CompiledFormulaLift.hasDerivWithinAt_graph _ _ _
    (precision_one_le program entry initial hε hεOne)
  simpa only [formulaList_get, formulas] using hx.2 t ht

/-- For every real base initial state, an actual global smoothed
trajectory and its actual global rational lift exist simultaneously. -/
theorem exists_forwardTrajectory_on_graph (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1)
    (x₀ : MonitorCoordinate k → ℝ) :
    ∃ x : ℝ → MonitorCoordinate k → ℝ,
      HGAS.IsForwardTrajectory (smoothedField program entry initial ε) x x₀ ∧
      HGAS.IsForwardTrajectory (liftedField program entry initial ε)
        (fun t ↦ liftGraph program entry initial ε (x t))
        (liftGraph program entry initial ε x₀) := by
  obtain ⟨x, hx⟩ := forwardComplete_smoothedField program entry initial hε hεOne x₀
  exact ⟨x, hx, isForwardTrajectory_liftGraph program entry initial hε hεOne hx⟩

end

end Stability.Simulation.ClockedMonitor
