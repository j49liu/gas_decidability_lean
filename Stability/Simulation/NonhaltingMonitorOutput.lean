import Stability.Simulation.ResetTurnOutput
import Stability.Simulation.SmoothedMonitorCompleteness

/-!
# Nonhalting trajectories with unbounded output integral

The designated integer restart orbit has arbitrarily many reset labels.
Actual robust tracking turns these labels into output integrals of two.
Global existence supplies a genuine smoothed trajectory, whose actual
smoothing residual satisfies the required forcing budget.
-/

namespace Stability.Simulation.ClockedMonitor

open Set MonitorCoordinate MeasureTheory

noncomputable section

variable {k s : ℕ}

/-- An aligned unit oscillator with the designated clean integer restart
in the active buffer. The copy buffer starts at zero. -/
def restartInitialPoint (s : ℕ) (initial : Fin k → ℕ) : MonitorCoordinate k → ℝ
  | .clock => 0
  | .u => 0
  | .v => -1
  | .a i => RestartMachine.realState (RestartMachine.initialState (s := s) initial) i
  | .b _ => 0

/-- Any actual globally defined forced monitor from the designated
restart point has unbounded finite-time output integrals when the source
does not halt and the total forcing remains below the fixed budget. -/
theorem integral_output_unbounded_of_nonhalting (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ)
    (hnonhalt : ¬RegisterMachine.Halts program ⟨some entry, initial⟩)
    {x : ℝ → MonitorCoordinate k → ℝ}
    {forcingA forcingB : ℝ → MachineCoordinate k → ℝ}
    (hx : ContinuousOn x (Ici 0))
    (hforcingA : ContinuousOn forcingA (Ici 0))
    (hforcingB : ContinuousOn forcingB (Ici 0))
    (hderiv : ∀ t > 0, HasDerivAt x
      (field program entry initial (x t) + forcingVector (forcingA t) (forcingB t)) t)
    (hx0 : x 0 = restartInitialPoint s initial)
    (hmass : ∀ b ≥ 0,
      forcingMass (jointForcingMagnitude forcingA forcingB) 0 b ≤ 1 / 256) :
    ∀ L : ℝ, ∃ b ≥ 0, L < ∫ t in 0..b, output (x t) := by
  intro L
  obtain ⟨count, hcount⟩ := exists_nat_gt (L / 2)
  obtain ⟨N, hN⟩ := RestartMachine.real_exists_restartCount_eq
    program entry initial hnonhalt count
  let finish := halfTurnBoundary 0 (2 * N)
  have hfinish : 0 ≤ finish := by
    dsimp only [finish, halfTurnBoundary]
    positivity
  have hsubset : Icc 0 finish ⊆ Ici 0 := fun _ ht ↦ ht.1
  have hbound := integral_output_ge_twice_resetCount program entry initial (hx.mono hsubset)
    (hforcingA.mono hsubset) (hforcingB.mono hsubset) (fun t ht ↦ hderiv t ht.1)
    (by rw [hx0]; rfl) (by rw [hx0]; rfl) (RestartMachine.initialState initial)
    (by rw [hx0]; rfl) (hmass finish hfinish) N (le_refl finish)
  rw [hN] at hbound
  exact ⟨finish, hfinish, by linarith⟩

/-- Every smoothed trajectory from the designated point witnesses
unbounded raw monitor output. The forcing premise is discharged from the
literal smoothing construction, not supplied independently. -/
theorem smoothed_integral_output_unbounded (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ)
    (hnonhalt : ¬RegisterMachine.Halts program ⟨some entry, initial⟩)
    {ε : ℚ} (hε : 0 < ε) (hεSmall : ε ≤ 1 / 1024)
    {x : ℝ → MonitorCoordinate k → ℝ}
    (htrajectory : HGAS.IsForwardTrajectory (smoothedField program entry initial ε) x
      (restartInitialPoint s initial)) :
    ∀ L : ℝ, ∃ b ≥ 0, L < ∫ t in 0..b, output (x t) := by
  have hεOne : ε ≤ 1 := by linarith
  have hx : ContinuousOn x (Ici 0) := fun t ht ↦ (htrajectory.2 t ht).continuousWithinAt
  have hderiv : ∀ t > 0, HasDerivAt x (smoothedField program entry initial ε (x t)) t :=
    fun t ht ↦ (htrajectory.2 t ht.le).hasDerivAt (Ici_mem_nhds ht)
  let residual (t : ℝ) := smoothedField program entry initial ε (x t) -
    field program entry initial (x t)
  have hresidual : ContinuousOn residual (Ici 0) :=
    ((contDiff_smoothedField program entry initial hε hεOne).continuous.comp_continuousOn hx).sub
      ((locallyLipschitz_field program entry initial).continuous.comp_continuousOn hx)
  apply integral_output_unbounded_of_nonhalting program entry initial hnonhalt hx
    (continuous_bufferA.comp_continuousOn hresidual)
    (continuous_bufferB.comp_continuousOn hresidual) (fun t ht ↦ ?_) htrajectory.1
  · intro b hb
    have hsmall : (1024 : ℝ) * (ε : ℝ) ≤ 1 := by
      exact_mod_cast (show (1024 : ℚ) * ε ≤ 1 by linarith)
    have hpos : (0 : ℝ) < ε := by exact_mod_cast hε
    have hmass := smoothed_forcingMass_lt_pi program entry initial hε hεOne hb
      (hx.mono (fun _ ht ↦ ht.1)) (fun t ht ↦ hderiv t ht.1)
    have hpi := Real.pi_lt_four
    exact hmass.le.trans (by nlinarith)
  · convert hderiv t ht using 1
    exact (smoothedField_eq_forced program entry initial ε (x t)).symm

/-- A genuine global smoothed nonhalting witness exists. Divergence is
expressed as unbounded finite integrals, avoiding the default value of a
nonintegrable Bochner integral over an infinite interval. -/
theorem exists_smoothed_nonhalting_output_witness (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ)
    (hnonhalt : ¬RegisterMachine.Halts program ⟨some entry, initial⟩)
    {ε : ℚ} (hε : 0 < ε) (hεSmall : ε ≤ 1 / 1024) :
    ∃ x : ℝ → MonitorCoordinate k → ℝ,
      HGAS.IsForwardTrajectory (smoothedField program entry initial ε) x
        (restartInitialPoint s initial) ∧
      ∀ L : ℝ, ∃ b ≥ 0, L < ∫ t in 0..b, output (x t) := by
  obtain ⟨x, hx⟩ := forwardComplete_smoothedField program entry initial hε
    (show ε ≤ 1 by linarith) (restartInitialPoint s initial)
  exact ⟨x, hx, smoothed_integral_output_unbounded program entry initial hnonhalt hε hεSmall hx⟩

end

end Stability.Simulation.ClockedMonitor
