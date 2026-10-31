import Stability.Simulation.HaltingMonitorTracking
import Stability.Simulation.ClockedBudget
import Stability.Simulation.RestartBudget

/-!
# Actual positive-output turns and their budget increments

An event is a positive value of the literal monitor output during a
complete turn. The vector equation gives the ordinary budget lower bound;
an actual output event gives the stronger reset lower bound. Thus the
finite productive-turn count applies to these monitor events themselves.
-/

namespace Stability.Simulation

/-- Reanchoring a half-turn grid adds its indices. -/
theorem halfTurnBoundary_add (origin : ℝ) (m n : ℕ) :
    halfTurnBoundary (halfTurnBoundary origin m) n = halfTurnBoundary origin (m + n) := by
  simp only [halfTurnBoundary, Nat.cast_add]
  ring

namespace ClockedMonitor

open Set MonitorCoordinate MeasureTheory
open scoped BigOperators

noncomputable section

variable {k s : ℕ}

/-- The actual output is positive somewhere in the specified complete turn. -/
def outputEvent (origin : ℝ) (x : ℝ → MonitorCoordinate k → ℝ) (j : ℕ) : Prop :=
  ∃ t ∈ Icc (halfTurnBoundary origin (2 * j)) (halfTurnBoundary origin (2 * j + 2)),
    0 < output (x t)

/-- Number of actual positive-output turns strictly before `N`. -/
def eventCount (origin : ℝ) (x : ℝ → MonitorCoordinate k → ℝ) (N : ℕ) : ℕ := by
  classical
  exact productiveCount (outputEvent origin x) N

def sampledBudget (origin : ℝ) (x : ℝ → MonitorCoordinate k → ℝ) (j : ℕ) : ℝ :=
  x (halfTurnBoundary origin (2 * j)) (.a MachineCoordinate.budget)

def turnErrorAllowance (clockAtOrigin origin : ℝ) (forcing : ℝ → ℝ) (j : ℕ) : ℝ :=
  halfTurnErrorAllowance (gain : ℝ) clockAtOrigin origin forcing (2 * j) +
    halfTurnErrorAllowance (gain : ℝ) clockAtOrigin origin forcing (2 * j + 1)

theorem turnErrorAllowance_nonneg (clockAtOrigin origin : ℝ) (forcing : ℝ → ℝ) (j : ℕ) :
    0 ≤ turnErrorAllowance clockAtOrigin origin forcing j := by
  have hhalf (i : ℕ) : 0 ≤ halfTurnErrorAllowance (gain : ℝ) clockAtOrigin origin forcing i := by
    have hmass := forcingMass_nonneg forcing
      ((halfTurnBoundary_strictMono origin).monotone (Nat.le_succ i))
    have hclock := clockError_nonneg (clockAtOrigin + Real.pi / 2 + (i : ℝ) * Real.pi)
    unfold halfTurnErrorAllowance
    positivity
  exact add_nonneg (hhalf _) (hhalf _)

theorem sum_turnErrorAllowance (clockAtOrigin origin : ℝ) (forcing : ℝ → ℝ) (N : ℕ) :
    ∑ j ∈ Finset.range N, turnErrorAllowance clockAtOrigin origin forcing j =
      turnErrorBudget clockAtOrigin origin forcing N := by
  induction N with
  | zero => simp [turnErrorBudget]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, turnErrorBudget_succ]
      unfold turnErrorAllowance
      ring

section

variable (program : RegisterMachine.Program k s) (entry : Fin s) (initial : Fin k → ℕ)
  {origin finish radius : ℝ} {x : ℝ → MonitorCoordinate k → ℝ}
  {forcingA forcingB : ℝ → MachineCoordinate k → ℝ}
  (hx : ContinuousOn x (Icc origin finish))
  (hforcingA : ContinuousOn forcingA (Icc origin finish))
  (hforcingB : ContinuousOn forcingB (Icc origin finish))
  (hderiv : ∀ t ∈ Ioo origin finish, HasDerivAt x
    (field program entry initial (x t) + forcingVector (forcingA t) (forcingB t)) t)
  (hu0 : x origin u = 0) (hv0 : x origin v = -radius) (hradius : 0 ≤ radius)

include hx hderiv hu0 hv0

/-- Every full-turn boundary is aligned, regardless of the initial
contents of the machine buffers. -/
theorem aligned_at_turn_boundary (j : ℕ)
    (hend : halfTurnBoundary origin (2 * j) ≤ finish) :
    x (halfTurnBoundary origin (2 * j)) u = 0 ∧
      x (halfTurnBoundary origin (2 * j)) v = -radius := by
  have hstart : origin ≤ halfTurnBoundary origin (2 * j) := by
    simpa only [halfTurnBoundary_zero] using
      (halfTurnBoundary_strictMono origin).monotone (Nat.zero_le (2 * j))
  have hrotation := oscillator_eq_rotation
    ((continuous_apply u).comp_continuousOn hx) ((continuous_apply v).comp_continuousOn hx)
    (fun t ht ↦ by simpa [field, forcingVector] using (hasDerivAt_pi.mp (hderiv t ht)) u)
    (fun t ht ↦ by simpa [field, forcingVector] using (hasDerivAt_pi.mp (hderiv t ht)) v)
    ⟨hstart, hend⟩
  simp only [Function.comp_apply] at hrotation
  have hsin : Real.sin (((2 * j : ℕ) : ℝ) * Real.pi) = 0 := Real.sin_nat_mul_pi (2 * j)
  have hcos : Real.cos (((2 * j : ℕ) : ℝ) * Real.pi) = 1 := by
    rw [Real.cos_nat_mul_pi]
    simp [pow_mul]
  simpa only [halfTurnBoundary, add_sub_cancel_left, hu0, hv0, hsin, hcos,
    zero_mul, mul_zero, zero_sub, neg_neg, neg_zero, mul_one, zero_add] using hrotation

/-- A positive-output event itself supplies the lower amplitude cutoff
needed for the relaxation and budget estimates. -/
theorem amplitude_lower_of_outputEvent (j : ℕ)
    (hend : halfTurnBoundary origin (2 * j + 2) ≤ finish)
    (hevent : outputEvent origin x j) : (1 / 2 : ℝ) < radius ^ 2 := by
  obtain ⟨t, ht, hp⟩ := hevent
  have hstart : origin ≤ halfTurnBoundary origin (2 * j) := by
    simpa only [halfTurnBoundary_zero] using
      (halfTurnBoundary_strictMono origin).monotone (Nat.zero_le (2 * j))
  have hamp := oscillator_amplitude_sq_eq
    ((continuous_apply u).comp_continuousOn hx) ((continuous_apply v).comp_continuousOn hx)
    (fun r hr ↦ by simpa [field, forcingVector] using (hasDerivAt_pi.mp (hderiv r hr)) u)
    (fun r hr ↦ by simpa [field, forcingVector] using (hasDerivAt_pi.mp (hderiv r hr)) v)
    ⟨hstart.trans ht.1, ht.2.trans hend⟩
  simp only [Function.comp_apply, hu0, hv0] at hamp
  have hwindow := ((output_pos_iff (x t)).mp hp).1.1
  nlinarith

include hforcingA hforcingB hradius

/-- Ordinary turns can decrease the actual sampled budget only by their
proved clock and forcing allowance. -/
theorem sampledBudget_nondecrease (hamplitude : (1 / 2 : ℝ) < radius ^ 2) (j : ℕ)
    (hend : halfTurnBoundary origin (2 * j + 2) ≤ finish) :
    sampledBudget origin x j -
      turnErrorAllowance (x origin clock) origin (jointForcingMagnitude forcingA forcingB) j ≤
        sampledBudget origin x (j + 1) := by
  have hcoord (i : MonitorCoordinate k) (t : ℝ) (ht : t ∈ Ioo origin finish) :=
    (hasDerivAt_pi.mp (hderiv t ht)) i
  have hbound := clocked_budget_nondecrease gain_pos hradius hamplitude
    ((continuous_apply clock).comp_continuousOn hx)
    (fun t ht ↦ by simpa [field, forcingVector] using hcoord clock t ht)
    ((continuous_apply u).comp_continuousOn hx) ((continuous_apply v).comp_continuousOn hx)
    (fun t ht ↦ by simpa [field, forcingVector] using hcoord u t ht)
    (fun t ht ↦ by simpa [field, forcingVector] using hcoord v t ht) hu0 hv0
    ((continuous_apply (.a MachineCoordinate.budget)).comp_continuousOn hx)
    ((continuous_apply (.b MachineCoordinate.budget)).comp_continuousOn hx)
    ((continuous_apply MachineCoordinate.budget).comp_continuousOn hforcingA)
    ((continuous_apply MachineCoordinate.budget).comp_continuousOn hforcingB)
    (hforcingA.norm.sup hforcingB.norm)
    (fun t _ ↦ (norm_le_pi_norm (forcingA t) MachineCoordinate.budget).trans (le_max_left _ _))
    (fun t _ ↦ (norm_le_pi_norm (forcingB t) MachineCoordinate.budget).trans (le_max_right _ _))
    (fun t ht ↦ by simpa [field, forcingVector] using hcoord (.a MachineCoordinate.budget) t ht)
    (fun t ht ↦ by simpa [field, forcingVector] using hcoord (.b MachineCoordinate.budget) t ht)
    j hend (fun t _ ↦
      RegisterTransition.budget_le_transitionMap program entry initial (bufferA (x t)))
  simpa only [sampledBudget, turnErrorAllowance,
    show 2 * (j + 1) = 2 * j + 2 by omega] using hbound

/-- An actual output event resets the sampled budget to at least one
and increases it by one, up to the same turn allowance. -/
theorem sampledBudget_reset_of_outputEvent (j : ℕ)
    (hend : halfTurnBoundary origin (2 * j + 2) ≤ finish)
    (hmass : forcingMass (jointForcingMagnitude forcingA forcingB)
      (halfTurnBoundary origin (2 * j)) (halfTurnBoundary origin (2 * j + 2)) ≤ 1 / 16)
    (hevent : outputEvent origin x j) :
    max (sampledBudget origin x j + 1) 1 -
      turnErrorAllowance (x origin clock) origin (jointForcingMagnitude forcingA forcingB) j ≤
        sampledBudget origin x (j + 1) := by
  have hreset := forced_reset_error_le program entry initial hx hforcingA hforcingB hderiv
    hu0 hv0 hradius j hend hmass hevent
  have hcoord := (norm_le_pi_norm _ MachineCoordinate.budget).trans hreset
  change |x (halfTurnBoundary origin (2 * j + 2)) (.a MachineCoordinate.budget) -
      (max (sampledBudget origin x j) 0 + 1)| ≤
    turnErrorAllowance (x origin clock) origin (jointForcingMagnitude forcingA forcingB) j at hcoord
  have hlower := (abs_le.mp hcoord).1
  have hmax : max (sampledBudget origin x j) 0 + 1 =
      max (sampledBudget origin x j + 1) 1 := by
    simpa only [zero_add] using
      (max_add_add_right (sampledBudget origin x j) 0 (1 : ℝ)).symm
  rw [hmax] at hlower
  change _ ≤ x (halfTurnBoundary origin (2 * (j + 1))) (.a MachineCoordinate.budget)
  rw [show 2 * (j + 1) = 2 * j + 2 by omega]
  linarith

end

end

end ClockedMonitor

end Stability.Simulation
