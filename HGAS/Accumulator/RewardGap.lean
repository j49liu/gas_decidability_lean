import Mathlib.Tactic

/-!
# Pointwise inequalities for the strict accumulator reward

The final compact source uses

```
R = W + 2 W₀ - 1 - ε,
```

where `W ∈ [-1,1]` is the stereographic accumulator coordinate and `W₀`
is the product of the finite-chart coordinates of all affine source
blocks.  The dynamics decides which invariant strata can occur; the sign
estimates themselves are elementary.  This module isolates them so the
later measure-theoretic proof can cite exact checked inequalities.
-/

namespace HGAS

/-- Reward used in equation (11.18). -/
def accumulatorReward (W W₀ ε : ℝ) : ℝ :=
  W + 2 * W₀ - 1 - ε

/-- Every source boundary face, where `W₀=0`, has reward at most `-ε`. -/
theorem accumulatorReward_le_neg_epsilon_on_source_face
    {W W₀ ε : ℝ} (hW : W ≤ 1) (hface : W₀ = 0) :
    accumulatorReward W W₀ ε ≤ -ε := by
  simp only [accumulatorReward, hface]
  linarith

/-- At the unique accumulator point at infinity, `W=-1`, the reward is at
most `-ε` whenever the chart product is at most one. -/
theorem accumulatorReward_le_neg_epsilon_at_infinity
    {W W₀ ε : ℝ} (hinfinity : W = -1) (hW₀ : W₀ ≤ 1) :
    accumulatorReward W W₀ ε ≤ -ε := by
  simp only [accumulatorReward, hinfinity]
  linarith

/-- The designated finite graph in a no-instance has a strictly positive
pointwise reward.  This is the calculation following equation (11.17). -/
theorem accumulatorReward_ge_finite_graph
    {W W₀ w ε : ℝ}
    (hW : 1 - w / 2 ≤ W) (hW₀ : w ≤ W₀) :
    3 * w / 2 - ε ≤ accumulatorReward W W₀ ε := by
  simp only [accumulatorReward]
  linarith

/-- With the paper's choice `ε=w/4`, the finite-graph lower bound is
`5w/4`, hence positive for `w>0`. -/
theorem finite_graph_gap_pos {w ε : ℝ}
    (hw : 0 < w) (hε : ε = w / 4) :
    0 < 3 * w / 2 - ε := by
  rw [hε]
  linarith

/-- The elementary stereographic estimate used for the finite graph:
`(1-a)/(1+a) ≥ 1-2a` for `a≥0`. -/
theorem one_sub_div_one_add_ge_one_sub_two_mul
    {a : ℝ} (ha : 0 ≤ a) :
    1 - 2 * a ≤ (1 - a) / (1 + a) := by
  have hden : 0 < 1 + a := by linarith
  apply (le_div_iff₀ hden).mpr
  nlinarith

/-- If `κ²K² ≤ w/4`, inverse stereographic projection of a vector of norm
at most `κK` has scalar coordinate at least `1-w/2`. -/
theorem stereoW_lower_bound_of_scaled_norm
    {a w : ℝ} (ha : 0 ≤ a) (haw : a ≤ w / 4) :
    1 - w / 2 ≤ (1 - a) / (1 + a) := by
  calc
    1 - w / 2 ≤ 1 - 2 * a := by linarith
    _ ≤ (1 - a) / (1 + a) :=
      one_sub_div_one_add_ge_one_sub_two_mul ha

end HGAS
