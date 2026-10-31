import Stability.Simulation.CubicRelaxation
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Constant-target cubic relaxation from arbitrary scalar states

Reference: the constant-target, unforced case of Lemma 4.1,
https://arxiv.org/html/2609.22058v2#S4.

The estimate follows from the actual scalar differential equation.
Squared error is nonincreasing, so a nonzero final error cannot
have passed through zero. The positive-excess estimate then applies to the
absolute error, irrespective of its initial sign.

The theorems concern solution segments already defined on a finite closed
interval. They do not assert existence, or handle moving targets or forcing.
-/

namespace Stability.Simulation

open Set MeasureTheory

/-- Squared error cannot increase along an unforced cubic relaxation toward
a constant target when the relaxation rate is nonnegative. -/
theorem sq_error_antitoneOn_of_cubic_relaxation
    {a b target : ℝ} {y rate : ℝ → ℝ}
    (hy : ContinuousOn y (Icc a b))
    (hrate : ∀ t ∈ Icc a b, 0 ≤ rate t)
    (hderiv : ∀ t ∈ Ioo a b,
      HasDerivAt y (rate t * (target - y t) ^ 3) t) :
    AntitoneOn (fun t ↦ (y t - target) ^ 2) (Icc a b) := by
  have henergy : ∀ t ∈ Ioo a b,
      HasDerivAt (fun t ↦ (y t - target) ^ 2)
        (-2 * rate t * (y t - target) ^ 4) t := by
    intro t ht
    convert ((hderiv t ht).sub_const target).pow 2 using 1
    ring
  refine antitoneOn_of_hasDerivWithinAt_nonpos
    (f' := fun t ↦ -2 * rate t * (y t - target) ^ 4) (convex_Icc a b)
    ((hy.sub continuousOn_const).pow 2) ?_ ?_
  · intro t ht
    rw [interior_Icc] at ht
    exact (henergy t ht).hasDerivWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    have hnonneg := mul_nonneg (hrate t (Ioo_subset_Icc_self ht))
      (show 0 ≤ (y t - target) ^ 4 by positivity)
    linarith

/-- Once a constant-target cubic relaxation reaches its target, it stays
there for the rest of the supplied solution segment. -/
theorem eq_target_of_eq_target_of_cubic_relaxation
    {a b target : ℝ} {y rate : ℝ → ℝ}
    (hy : ContinuousOn y (Icc a b))
    (hrate : ∀ t ∈ Icc a b, 0 ≤ rate t)
    (hderiv : ∀ t ∈ Ioo a b,
      HasDerivAt y (rate t * (target - y t) ^ 3) t)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (hst : s ≤ t) (hzero : y s = target) :
    y t = target := by
  have hbound := sq_error_antitoneOn_of_cubic_relaxation hy hrate hderiv hs ht hst
  change (y t - target) ^ 2 ≤ (y s - target) ^ 2 at hbound
  rw [hzero, sub_self, zero_pow (by decide : 2 ≠ 0)] at hbound
  have heq : (y t - target) ^ 2 = 0 := le_antisymm hbound (sq_nonneg _)
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp heq)

/-- The final error of a constant-target, unforced cubic relaxation is
bounded independently of the initial value, including either initial sign
and the exact-target solution. -/
theorem abs_sub_lt_inv_sqrt_integral_of_cubic_relaxation
    {a b target : ℝ} {y rate : ℝ → ℝ}
    (hab : a ≤ b)
    (hy : ContinuousOn y (Icc a b))
    (hrate : ContinuousOn rate (Icc a b))
    (hnonneg : ∀ t ∈ Icc a b, 0 ≤ rate t)
    (hderiv : ∀ t ∈ Ioo a b,
      HasDerivAt y (rate t * (target - y t) ^ 3) t)
    (hgain : 0 < ∫ t in a..b, rate t) :
    |y b - target| < (Real.sqrt (2 * (∫ t in a..b, rate t)))⁻¹ := by
  by_cases hfinal : y b = target
  · rw [hfinal, sub_self, abs_zero]
    apply inv_pos.mpr
    apply Real.sqrt_pos.mpr
    positivity
  have hnonzero : ∀ t ∈ Icc a b, y t - target ≠ 0 := by
    intro t ht hzero
    apply hfinal
    exact eq_target_of_eq_target_of_cubic_relaxation hy hnonneg hderiv
      ht (right_mem_Icc.mpr hab) ht.2 (sub_eq_zero.mp hzero)
  have habs : ∀ t ∈ Ioo a b,
      HasDerivAt (fun t ↦ |y t - target|)
        (-(rate t) * |y t - target| ^ 3) t := by
    intro t ht
    have hd := (hderiv t ht).sub_const target
    obtain hneg | hpos := (hnonzero t (Ioo_subset_Icc_self ht)).lt_or_gt
    · convert (hasDerivAt_abs_neg hneg).comp t hd using 1
      rw [abs_of_neg hneg]
      ring
    · convert (hasDerivAt_abs_pos hpos).comp t hd using 1
      rw [abs_of_pos hpos]
      ring
  exact lt_inv_sqrt_integral_of_cubic_decay hab
    (hy.sub continuousOn_const).abs hrate
    (fun t ht ↦ abs_pos.mpr (hnonzero t ht)) habs
    (fun _ _ ↦ le_rfl) hgain

end Stability.Simulation
