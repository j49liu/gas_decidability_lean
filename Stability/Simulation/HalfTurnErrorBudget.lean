import Stability.Simulation.HalfTurnForcingMass
import Stability.Simulation.ClockErrorSummability

/-!
# Finite sums of half-turn error allowances

Reference: the error budget preceding Lemma 4.4,
https://arxiv.org/html/2609.22058v2#S4.

The allowance is defined using actual forcing integrals and the explicit
clock-error sequence. This file bounds its finite sums. The actual
oscillator-gated update bound is proved in `ClockedDoubleBufferUpdate`;
the real transition map and arbitrary-phase alignment remain separate.
-/

namespace Stability.Simulation

open Set
open scoped BigOperators

/-- The contribution of one half-turn to the planned update-error budget:
twice its forcing mass plus its clock relaxation allowance. -/
noncomputable def halfTurnErrorAllowance
    (gain clockAtOrigin origin : ℝ) (forcing : ℝ → ℝ) (n : ℕ) : ℝ :=
  2 * forcingMass forcing (halfTurnBoundary origin n) (halfTurnBoundary origin (n + 1)) +
    (Real.sqrt gain)⁻¹ * clockError (clockAtOrigin + Real.pi / 2 + (n : ℝ) * Real.pi)

/-- The sum of the half-turn allowances is uniform in the initial clock
value and depends on forcing only through its actual total mass. -/
theorem sum_halfTurnErrorAllowance_lt
    {gain origin : ℝ} (hgain : 0 < gain) (clockAtOrigin : ℝ)
    {forcing : ℝ → ℝ} (N : ℕ)
    (hforcing : ContinuousOn forcing (Icc origin (halfTurnBoundary origin N))) :
    ∑ n ∈ Finset.range N, halfTurnErrorAllowance gain clockAtOrigin origin forcing n <
      2 * forcingMass forcing origin (halfTurnBoundary origin N) + 3 * (Real.sqrt gain)⁻¹ := by
  simp only [halfTurnErrorAllowance, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_halfTurn_forcingMass_eq N hforcing]
  have hclock := scaledClockErrors_sum_lt hgain (clockAtOrigin + Real.pi / 2) (Finset.range N)
  rw [← Finset.mul_sum] at hclock
  linarith

/-- With gain `2^20` and total forcing mass at most `2^-8`, the finite
allowance sum is strictly below `11 / 1024`, independently of both clocks. -/
theorem sum_halfTurnErrorAllowance_lt_fixedBudget
    {origin : ℝ} (clockAtOrigin : ℝ) {forcing : ℝ → ℝ} (N : ℕ)
    (hforcing : ContinuousOn forcing (Icc origin (halfTurnBoundary origin N)))
    (hmass : forcingMass forcing origin (halfTurnBoundary origin N) ≤ 1 / 256) :
    ∑ n ∈ Finset.range N,
      halfTurnErrorAllowance ((2 : ℝ) ^ 20) clockAtOrigin origin forcing n < 11 / 1024 := by
  have hbound := sum_halfTurnErrorAllowance_lt
    (gain := (2 : ℝ) ^ 20) (by norm_num) clockAtOrigin N hforcing
  norm_num at hbound
  linarith

end Stability.Simulation
