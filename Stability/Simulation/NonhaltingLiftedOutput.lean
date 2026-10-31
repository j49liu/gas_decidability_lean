import Stability.Simulation.NonhaltingMonitorOutput
import Stability.Simulation.LiftedMonitorExistence
import Stability.Simulation.ClockedMonitorPenalty

/-!
# Unbounded penalized output on a genuine rational trajectory

On the canonical graph the penalty vanishes exactly. The remaining
output smoothing error has total mass at most `ε π`, so it cannot remove
the unbounded output of the nonhalting monitor trajectory.
-/

namespace Stability.Simulation.ClockedMonitor

open AbsFormula Set MonitorCoordinate MeasureTheory

noncomputable section

variable {k s : ℕ}

/-- On any finite unit-clock curve, the actual graph output differs from
the literal monitor output by at most the proved smoothing budget. -/
theorem integral_output_le_integral_penalized_graph_add
    (program : RegisterMachine.Program k s) (entry : Fin s) (initial : Fin k → ℕ)
    {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1)
    {a b : ℝ} {x : ℝ → MonitorCoordinate k → ℝ} (hab : a ≤ b)
    (hx : ContinuousOn x (Icc a b))
    (hclock : ∀ t ∈ Ioo a b, HasDerivAt (fun r ↦ x r clock) 1 t) :
    (∫ t in a..b, output (x t)) ≤
      (∫ t in a..b, PolynomialFraction.value (liftGraph program entry initial ε (x t))
        (penalizedOutput program entry initial ε)) + (ε : ℝ) * Real.pi := by
  let g (z : MonitorCoordinate k → ℝ) :=
    PolynomialFraction.value (liftGraph program entry initial ε z)
      (penalizedOutput program entry initial ε)
  have hgEq : g = fun z ↦ smoothEval
      (polynomialValue z (precision program entry initial ε)) z outputFormula :=
    funext (penalizedOutput_liftGraph program entry initial hε hεOne)
  have hg : Continuous g := by
    rw [hgEq]
    exact (contDiff_smoothEval_precisionPolynomial (formulas program entry initial) clock
      hε hεOne outputFormula).continuous
  have herror := (continuous_smoothingError (formulas program entry initial) clock
    hε hεOne).comp_continuousOn hx
  have hcomparison := intervalIntegral.integral_mono_on (μ := volume) hab
    ((continuous_output.comp_continuousOn hx).intervalIntegrable_of_Icc hab)
    (((hg.comp_continuousOn hx).add herror.norm).intervalIntegrable_of_Icc hab)
    (fun t _ ↦ by
      have he := norm_le_pi_norm
        (smoothingError (formulas program entry initial) clock ε (x t)) none
      have heq : smoothingError (formulas program entry initial) clock ε (x t) none =
          g (x t) - output (x t) := by
        rw [hgEq]
        simp only [smoothingError, formulas, eval_outputFormula]
        rfl
      rw [heq, Real.norm_eq_abs] at he
      have hlower := (abs_le.mp he).1
      change output (x t) ≤ g (x t) +
        ‖smoothingError (formulas program entry initial) clock ε (x t)‖
      linarith)
  have hsum := intervalIntegral.integral_add (μ := volume)
    ((hg.comp_continuousOn hx).intervalIntegrable_of_Icc hab)
    (herror.norm.intervalIntegrable_of_Icc hab)
  simp only [Pi.add_apply, Function.comp_apply] at hcomparison hsum
  rw [hsum] at hcomparison
  exact hcomparison.trans (add_le_add le_rfl
    (integral_norm_smoothingError_lt_pi (formulas program entry initial) clock
      hε hεOne hab hx hclock).le)

/-- The actual penalized rational output is unbounded along the canonical
lift of every designated smoothed nonhalting trajectory. -/
theorem integral_penalized_graph_unbounded (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ)
    (hnonhalt : ¬RegisterMachine.Halts program ⟨some entry, initial⟩)
    {ε : ℚ} (hε : 0 < ε) (hεSmall : ε ≤ 1 / 1024)
    {x : ℝ → MonitorCoordinate k → ℝ}
    (htrajectory : HGAS.IsForwardTrajectory (smoothedField program entry initial ε) x
      (restartInitialPoint s initial)) :
    ∀ L : ℝ, ∃ b ≥ 0,
      L < ∫ t in 0..b, PolynomialFraction.value (liftGraph program entry initial ε (x t))
        (penalizedOutput program entry initial ε) := by
  intro L
  obtain ⟨b, hb, hlarge⟩ := smoothed_integral_output_unbounded program entry initial
    hnonhalt hε hεSmall htrajectory (L + (ε : ℝ) * Real.pi)
  have hx : ContinuousOn x (Icc 0 b) :=
    fun t ht ↦ (htrajectory.2 t ht.1).continuousWithinAt.mono (fun _ hr ↦ hr.1)
  have hclock : ∀ t ∈ Ioo 0 b, HasDerivAt (fun r ↦ x r clock) 1 t := by
    intro t ht
    simpa only [smoothedField_clock] using
      (hasDerivAt_pi.mp ((htrajectory.2 t ht.1.le).hasDerivAt (Ici_mem_nhds ht.1))) clock
  have hbound := integral_output_le_integral_penalized_graph_add program entry initial
    hε (show ε ≤ 1 by linarith) hb hx hclock
  exact ⟨b, hb, by linarith⟩

/-- Nonhalting supplies an actual global rational trajectory whose
actual penalized output has unbounded finite-time integrals. -/
theorem exists_lifted_nonhalting_output_witness (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ)
    (hnonhalt : ¬RegisterMachine.Halts program ⟨some entry, initial⟩)
    {ε : ℚ} (hε : 0 < ε) (hεSmall : ε ≤ 1 / 1024) :
    ∃ y : ℝ → LiftCoordinate program entry initial ε → ℝ,
      HGAS.IsForwardTrajectory (liftedField program entry initial ε) y
        (liftGraph program entry initial ε (restartInitialPoint s initial)) ∧
      ∀ L : ℝ, ∃ b ≥ 0,
        L < ∫ t in 0..b, PolynomialFraction.value (y t)
          (penalizedOutput program entry initial ε) := by
  obtain ⟨x, hx, hlift⟩ := exists_forwardTrajectory_on_graph program entry initial hε
    (show ε ≤ 1 by linarith) (restartInitialPoint s initial)
  exact ⟨fun t ↦ liftGraph program entry initial ε (x t), hlift,
    integral_penalized_graph_unbounded program entry initial hnonhalt hε hεSmall hx⟩

end

end Stability.Simulation.ClockedMonitor
