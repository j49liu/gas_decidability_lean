import HGAS.Dynamics.StateTimeChange
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Ordinary-time averages from bounded primitives

A bounded primitive gives a zero forward average at all real horizons.
For a positive time change, the inverse clock cancels the speed in the
primitive derivative. These elementary facts keep the horizon and clock
normalizations explicit in the source-trajectory converse.
-/

noncomputable section

namespace Stability.Selection

open HGAS Filter MeasureTheory Topology

/-- A uniformly bounded real primitive forces the full real-horizon mean
of its continuous derivative to vanish. -/
theorem forwardMean_zero_of_bounded_primitive
    {f F : ℝ → ℝ} (hf : Continuous f) (hF : ∀ t, HasDerivAt F (f t) t)
    (C : ℝ) (hbound : ∀ t, |F t| ≤ C) :
    Tendsto (fun H : ℝ ↦ H⁻¹ * ∫ t in (0 : ℝ)..H, f t) atTop (𝓝 0) := by
  have hint (H : ℝ) : (∫ t in (0 : ℝ)..H, f t) = F H - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ ↦ hF t) (hf.intervalIntegrable _ _)
  apply squeeze_zero_norm' (a := fun H : ℝ ↦ H⁻¹ * (2 * C))
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
    rw [hint, norm_mul, Real.norm_eq_abs, abs_inv, abs_of_pos hH]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hH.le)
    calc
      ‖F H - F 0‖ ≤ ‖F H‖ + ‖F 0‖ := norm_sub_le _ _
      _ ≤ C + C := add_le_add (hbound H) (hbound 0)
      _ = 2 * C := by ring
  · simpa using (tendsto_inv_atTop_zero.mul_const (2 * C))

/-- The inverse positive clock removes precisely the speed factor from a
primitive derivative, at every real time. -/
theorem primitive_hasDerivAt_inverseClock
    {F f w : ℝ → ℝ} (hclock : PositiveIntegralClock w)
    (hF : ∀ t, HasDerivAt F (w t * f t) t) (t : ℝ) :
    HasDerivAt (fun s ↦ F (hclock.orderIso.symm s))
      (f (hclock.orderIso.symm t)) t := by
  have h := (hF (hclock.orderIso.symm t)).comp t (hclock.symm_hasDerivAt t)
  convert h using 1
  field_simp [ne_of_gt (hclock.positive (hclock.orderIso.symm t))]

/-- A bounded primitive for a slowed observable yields its unscaled zero
mean in ordinary time, without a selected subsequence of horizons. -/
theorem forwardMean_zero_of_timeChanged_bounded_primitive
    {F f w : ℝ → ℝ} (hclock : PositiveIntegralClock w)
    (hf : Continuous f) (hF : ∀ t, HasDerivAt F (w t * f t) t)
    (C : ℝ) (hbound : ∀ t, |F t| ≤ C) :
    Tendsto (fun H : ℝ ↦ H⁻¹ * ∫ t in (0 : ℝ)..H,
      f (hclock.orderIso.symm t)) atTop (𝓝 0) := by
  exact forwardMean_zero_of_bounded_primitive
    (hf.comp hclock.orderIso.symm.continuous)
    (primitive_hasDerivAt_inverseClock hclock hF) C (fun t ↦ hbound _)

end Stability.Selection
