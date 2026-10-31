import Stability.Simulation.BoundedContinuation
import Stability.Simulation.MonitorFiniteBounds

/-!
# Global forward existence for the actual monitor

Local Lipschitz regularity and the proved finite-horizon bounds discharge
the continuation theorem for the literal unsmoothed vector field. Every
real initial state is covered, without phase or machine-state restrictions.
-/

namespace Stability.Simulation.ClockedMonitor

open Set

noncomputable section

variable {k s : ℕ}

/-- The actual oscillator-gated register monitor is forward complete. -/
theorem forwardComplete_field (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) : HGAS.ForwardComplete (field program entry initial) := by
  intro x₀
  apply exists_global_forward_solution_of_finite_bounds
    (locallyLipschitz_field program entry initial) x₀
  intro T _
  obtain ⟨bound, _, hbound⟩ := exists_uniform_finite_bound program entry initial T
    (R := ‖x₀‖) (M := 0) (norm_nonneg _) le_rfl
  refine ⟨bound, ?_⟩
  intro b hb γ hγ₀ hγ hderiv
  have hforceZero : forcingVector (0 : MachineCoordinate k → ℝ) 0 = 0 := by
    funext i
    cases i <;> rfl
  apply hbound 0 b γ (fun _ ↦ 0) (fun _ ↦ 0) hb.1 (by simpa using hb.2)
    hγ continuousOn_const continuousOn_const
    (fun t ht ↦ by simpa only [hforceZero, add_zero] using hderiv t ht)
  · rw [hγ₀]
  · simp [jointForcingMagnitude, forcingMass]

end

end Stability.Simulation.ClockedMonitor
