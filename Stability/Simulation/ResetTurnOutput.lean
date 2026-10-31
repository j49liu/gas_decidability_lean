import Stability.Simulation.IntegerMonitorTracking
import Stability.Simulation.MonitorOutputIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Output produced by actual tracked restart turns

At unit oscillator amplitude, an exact reset label in the reference orbit
keeps the actual held label in the output plateau throughout computation.
The actual output is then the local sine, whose integral is two.
-/

namespace Stability.Simulation.ClockedMonitor

open Set MonitorCoordinate MeasureTheory
open scoped BigOperators

noncomputable section

variable {k s : ℕ}

section

variable (program : RegisterMachine.Program k s) (entry : Fin s) (initial : Fin k → ℕ)
  {origin finish : ℝ} {x : ℝ → MonitorCoordinate k → ℝ}
  {forcingA forcingB : ℝ → MachineCoordinate k → ℝ}
  (hx : ContinuousOn x (Icc origin finish))
  (hforcingA : ContinuousOn forcingA (Icc origin finish))
  (hforcingB : ContinuousOn forcingB (Icc origin finish))
  (hderiv : ∀ t ∈ Ioo origin finish, HasDerivAt x
    (field program entry initial (x t) + forcingVector (forcingA t) (forcingB t)) t)
  (hu0 : x origin u = 0) (hv0 : x origin v = -1)
  (state : RestartMachine.State k s)
  (hinitial : bufferA (x origin) = RestartMachine.realState state)
  (hmass : forcingMass (jointForcingMagnitude forcingA forcingB) origin finish ≤ 1 / 256)

include hx hforcingA hforcingB hderiv hu0 hv0 hinitial hmass

/-- On a tracked reset turn the literal output equals the positive
oscillator sine throughout its compute half. -/
theorem output_eq_sin_on_reset_compute (j : ℕ)
    (hend : halfTurnBoundary origin (2 * j + 2) ≤ finish)
    (hreset : ((RegisterTransition.transitionMap program entry initial)^[j]
      (RestartMachine.realState state)) MachineCoordinate.label = 0)
    {t : ℝ} (ht : t ∈ Icc (halfTurnBoundary origin (2 * j))
      (halfTurnBoundary origin (2 * j + 1))) :
    output (x t) = Real.sin (t - halfTurnBoundary origin (2 * j)) := by
  have hstart : origin ≤ halfTurnBoundary origin (2 * j) := by
    simpa only [halfTurnBoundary_zero] using
      (halfTurnBoundary_strictMono origin).monotone (Nat.zero_le (2 * j))
  have hendCompute : halfTurnBoundary origin (2 * j + 1) ≤ finish :=
    ((halfTurnBoundary_strictMono origin).monotone (by omega)).trans hend
  have htFull := Icc_subset_Icc hstart hendCompute ht
  have htrack := forced_integer_tracking_error_lt_fixedBudget program entry initial hx
    hforcingA hforcingB hderiv hu0 hv0 (by norm_num) (by norm_num) (j + 1)
    (by simpa only [show 2 * (j + 1) = 2 * j + 2 by omega] using hend) state
    (δ := 0) (by simp only [hinitial, sub_self, norm_zero, le_refl]) (by norm_num)
    hmass j (by omega)
  have hmotion := held_compute_motion_le_total_mass program entry initial hx hforcingA
    hforcingB hderiv hu0 hv0 (by norm_num) j hendCompute ht
  have hnear := norm_sub_le_norm_sub_add_norm_sub (bufferA (x t))
    (bufferA (x (halfTurnBoundary origin (2 * j))))
    ((RegisterTransition.transitionMap program entry initial)^[j] (RestartMachine.realState state))
  have hcoordinate := norm_le_pi_norm
    (bufferA (x t) - (RegisterTransition.transitionMap program entry initial)^[j]
      (RestartMachine.realState state)) MachineCoordinate.label
  change |x t (.a MachineCoordinate.label) -
    ((RegisterTransition.transitionMap program entry initial)^[j]
      (RestartMachine.realState state)) MachineCoordinate.label| ≤ _ at hcoordinate
  rw [hreset, sub_zero] at hcoordinate
  have hlabel : |4 * x t (.a MachineCoordinate.label)| ≤ 1 / 8 := by
    rw [abs_mul]
    norm_num
    linarith
  have hdu : ∀ r ∈ Ioo origin finish, HasDerivAt (fun z ↦ x z u) (-x r v) r := by
    intro r hr
    simpa [field, forcingVector] using (hasDerivAt_pi.mp (hderiv r hr)) u
  have hdv : ∀ r ∈ Ioo origin finish, HasDerivAt (fun z ↦ x z v) (x r u) r := by
    intro r hr
    simpa [field, forcingVector] using (hasDerivAt_pi.mp (hderiv r hr)) v
  have hcu := (continuous_apply u).comp_continuousOn hx
  have hcv := (continuous_apply v).comp_continuousOn hx
  have hamp := oscillator_amplitude_sq_eq hcu hcv hdu hdv htFull
  have hsin := normalizedOscillator_eq_sin hcu hcv hdu hdv hu0 hv0 (2 * j) htFull
  have hpos := normalizedOscillator_nonneg_on_halfTurn hcu hcv hdu hdv hu0 hv0
    (by norm_num) (2 * j) htFull ht
  simp only [Function.comp_apply] at hamp hsin hpos
  simp only [hu0, hv0] at hamp
  norm_num at hamp
  simp only [pow_mul, neg_one_sq, one_pow, one_mul] at hsin hpos
  rw [output, hamp, labelGate_eq_one hlabel, max_eq_left hpos]
  norm_num [amplitudeCutoff, hsin]

/-- Each tracked reference reset contributes exactly two on its compute
half-turn, independent of the initial copy buffer. -/
theorem integral_output_reset_compute_eq_two (j : ℕ)
    (hend : halfTurnBoundary origin (2 * j + 2) ≤ finish)
    (hreset : ((RegisterTransition.transitionMap program entry initial)^[j]
      (RestartMachine.realState state)) MachineCoordinate.label = 0) :
    (∫ t in halfTurnBoundary origin (2 * j)..halfTurnBoundary origin (2 * j + 1),
      output (x t)) = 2 := by
  have horder := (halfTurnBoundary_strictMono origin).monotone (Nat.le_succ (2 * j))
  have heq : (∫ t in halfTurnBoundary origin (2 * j)..halfTurnBoundary origin (2 * j + 1),
      output (x t)) = ∫ t in halfTurnBoundary origin (2 * j)..
        halfTurnBoundary origin (2 * j + 1), Real.sin (t - halfTurnBoundary origin (2 * j)) := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le horder]
    exact fun t ht ↦ output_eq_sin_on_reset_compute program entry initial hx hforcingA hforcingB
      hderiv hu0 hv0 state hinitial hmass j hend hreset ht
  rw [heq, intervalIntegral.integral_comp_sub_right]
  simp only [halfTurnBoundary_succ, add_sub_cancel_left, sub_self,
    integral_sin, Real.cos_zero, Real.cos_pi]
  norm_num

/-- The actual integral dominates twice the number of reset labels in
the exact integer orbit. The reset count is not an assumed event count. -/
theorem integral_output_ge_twice_resetCount (N : ℕ)
    (hend : halfTurnBoundary origin (2 * N) ≤ finish) :
    2 * (productiveCount (fun j ↦
      ((RegisterTransition.transitionMap program entry initial)^[j]
        (RestartMachine.realState state)) MachineCoordinate.label = 0) N : ℝ) ≤
      ∫ t in origin..halfTurnBoundary origin (2 * N), output (x t) := by
  classical
  let reset := fun j ↦ ((RegisterTransition.transitionMap program entry initial)^[j]
    (RestartMachine.realState state)) MachineCoordinate.label = 0
  have endFor (j : ℕ) (hj : j < N) : halfTurnBoundary origin (2 * j + 2) ≤ finish :=
    ((halfTurnBoundary_strictMono origin).monotone (by omega)).trans hend
  have startFor (j : ℕ) : origin ≤ halfTurnBoundary origin (2 * j) := by
    simpa only [halfTurnBoundary_zero] using
      (halfTurnBoundary_strictMono origin).monotone (Nat.zero_le (2 * j))
  have hint (j : ℕ) (hj : j < N) : IntervalIntegrable (fun t ↦ output (x t)) volume
      (halfTurnBoundary origin (2 * j)) (halfTurnBoundary origin (2 * j + 2)) :=
    ((continuous_output.comp_continuousOn hx).mono
      (Icc_subset_Icc (startFor j) (endFor j hj))).intervalIntegrable_of_Icc
        ((halfTurnBoundary_strictMono origin).monotone (by omega))
  have hturn (j : ℕ) (hj : j < N) : (if reset j then (2 : ℝ) else 0) ≤
      ∫ t in halfTurnBoundary origin (2 * j)..halfTurnBoundary origin (2 * j + 2),
        output (x t) := by
    by_cases hr : reset j
    · rw [if_pos hr, ← integral_output_reset_compute_eq_two program entry initial hx
        hforcingA hforcingB hderiv hu0 hv0 state hinitial hmass j (endFor j hj) hr]
      exact intervalIntegral.integral_mono_interval le_rfl
        ((halfTurnBoundary_strictMono origin).monotone (by omega))
        ((halfTurnBoundary_strictMono origin).monotone (by omega))
        (Filter.Eventually.of_forall (fun t ↦ output_nonneg (x t))) (hint j hj)
    · rw [if_neg hr]
      exact intervalIntegral.integral_nonneg
        ((halfTurnBoundary_strictMono origin).monotone (by omega))
        (fun t _ ↦ output_nonneg (x t))
  have hsum := Finset.sum_le_sum (s := Finset.range N) (fun j hj ↦ hturn j (Finset.mem_range.mp hj))
  have htel := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (a := fun j ↦ halfTurnBoundary origin (2 * j)) (n := N)
    (f := fun t ↦ output (x t)) (fun j hj ↦ by
      simpa only [show 2 * (j + 1) = 2 * j + 2 by omega] using hint j hj)
  simp only [show 2 * 0 = 0 by omega, halfTurnBoundary_zero,
    show ∀ j : ℕ, 2 * (j + 1) = 2 * j + 2 by omega] at htel
  rw [htel] at hsum
  have hcount : (∑ j ∈ Finset.range N, if reset j then (2 : ℝ) else 0) =
      2 * (productiveCount reset N : ℝ) := by
    rw [← Finset.sum_filter]
    simp [productiveCount, mul_comm]
  simpa only [hcount] using hsum

end

end

end Stability.Simulation.ClockedMonitor
