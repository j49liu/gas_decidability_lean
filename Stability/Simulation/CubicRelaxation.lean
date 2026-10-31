import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# The positive-excess estimate for cubic relaxation

Reference: the reciprocal-square argument in Lemma 4.1,
https://arxiv.org/html/2609.22058v2#S4.

The theorems concern an actual differential inequality on a finite interval.
They do not assume a simulation theorem.

Here the excess is strictly positive throughout the interval. Extending the
estimate across zeros, and handling moving targets and additive forcing,
require separate comparison arguments.
-/

namespace Stability.Simulation

open Set MeasureTheory

/-- A positive excess satisfying cubic decay gains at least twice the
integrated relaxation rate in reciprocal square.

Continuity is required on the closed interval and differentiation only on
its interior. No continuity of `w'` is needed. The rate need not be
nonnegative for this reciprocal inequality. -/
theorem reciprocal_sq_gain_of_cubic_decay
    {a b : ℝ} {w w' rate : ℝ → ℝ}
    (hab : a ≤ b)
    (hw : ContinuousOn w (Icc a b))
    (hrate : ContinuousOn rate (Icc a b))
    (hpositive : ∀ t ∈ Icc a b, 0 < w t)
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt w (w' t) t)
    (hdecay : ∀ t ∈ Ioo a b, w' t ≤ -(rate t) * (w t) ^ 3) :
    ((w a) ^ 2)⁻¹ + 2 * (∫ t in a..b, rate t) ≤ ((w b) ^ 2)⁻¹ := by
  have hcont : ContinuousOn (fun t ↦ ((w t) ^ 2)⁻¹) (Icc a b) :=
    (hw.pow 2).inv₀ fun t ht ↦ ne_of_gt (sq_pos_of_pos (hpositive t ht))
  have hreciprocal : ∀ t ∈ Ioo a b,
      HasDerivWithinAt (fun t ↦ ((w t) ^ 2)⁻¹)
        (-(2 * w t * w' t) / ((w t) ^ 2) ^ 2) (Ioi t) t := by
    intro t ht
    have hn : (w t) ^ 2 ≠ 0 :=
      ne_of_gt (sq_pos_of_pos (hpositive t (Ioo_subset_Icc_self ht)))
    simpa only [Pi.inv_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one] using
      (((hderiv t ht).pow 2).inv hn).hasDerivWithinAt
  have hcompare : ∀ t ∈ Ioo a b,
      2 * rate t ≤ -(2 * w t * w' t) / ((w t) ^ 2) ^ 2 := by
    intro t ht
    have hwt := hpositive t (Ioo_subset_Icc_self ht)
    apply (le_div_iff₀ (sq_pos_of_pos (sq_pos_of_pos hwt))).2
    have hscaled := mul_le_mul_of_nonneg_left (hdecay t ht)
      (show 0 ≤ 2 * w t by positivity)
    nlinarith
  have hbound := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le
    hab hcont hreciprocal
    ((continuousOn_const.mul hrate).integrableOn_Icc) hcompare
  change (∫ t in a..b, 2 * rate t) ≤ ((w b) ^ 2)⁻¹ - ((w a) ^ 2)⁻¹ at hbound
  rw [intervalIntegral.integral_const_mul] at hbound
  linarith

/-- Cubic decay gives a bound independent of the initial excess. The strict
bound records the positive initial reciprocal term retained by the proof. -/
theorem sq_mul_integral_lt_one_of_cubic_decay
    {a b : ℝ} {w w' rate : ℝ → ℝ}
    (hab : a ≤ b)
    (hw : ContinuousOn w (Icc a b))
    (hrate : ContinuousOn rate (Icc a b))
    (hpositive : ∀ t ∈ Icc a b, 0 < w t)
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt w (w' t) t)
    (hdecay : ∀ t ∈ Ioo a b, w' t ≤ -(rate t) * (w t) ^ 3) :
    2 * (∫ t in a..b, rate t) * (w b) ^ 2 < 1 := by
  have hbound := reciprocal_sq_gain_of_cubic_decay
    hab hw hrate hpositive hderiv hdecay
  have ha : 0 < ((w a) ^ 2)⁻¹ :=
    inv_pos.mpr (sq_pos_of_pos (hpositive a (left_mem_Icc.mpr hab)))
  have hb : 0 < (w b) ^ 2 :=
    sq_pos_of_pos (hpositive b (right_mem_Icc.mpr hab))
  have hstrict : 2 * (∫ t in a..b, rate t) < ((w b) ^ 2)⁻¹ := by
    linarith
  rw [inv_eq_one_div] at hstrict
  exact (lt_div_iff₀ hb).mp hstrict

/-- Positive integrated gain yields the usual inverse-square-root relaxation
bound, uniformly over the initial positive excess. -/
theorem lt_inv_sqrt_integral_of_cubic_decay
    {a b : ℝ} {w w' rate : ℝ → ℝ}
    (hab : a ≤ b)
    (hw : ContinuousOn w (Icc a b))
    (hrate : ContinuousOn rate (Icc a b))
    (hpositive : ∀ t ∈ Icc a b, 0 < w t)
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt w (w' t) t)
    (hdecay : ∀ t ∈ Ioo a b, w' t ≤ -(rate t) * (w t) ^ 3)
    (hgain : 0 < ∫ t in a..b, rate t) :
    w b < (Real.sqrt (2 * (∫ t in a..b, rate t)))⁻¹ := by
  have hbound := sq_mul_integral_lt_one_of_cubic_decay
    hab hw hrate hpositive hderiv hdecay
  have hgain' : 0 < 2 * (∫ t in a..b, rate t) := by positivity
  have hsqrt := Real.sqrt_pos.mpr hgain'
  have hsquare := Real.sq_sqrt hgain'.le
  have hproduct :
      (w b * Real.sqrt (2 * (∫ t in a..b, rate t))) ^ 2 =
        (w b) ^ 2 * (2 * (∫ t in a..b, rate t)) := by
    rw [mul_pow, hsquare]
  rw [inv_eq_one_div]
  apply (lt_div_iff₀ hsqrt).2
  nlinarith [sq_nonneg (w b * Real.sqrt (2 * (∫ t in a..b, rate t)) - 1)]

end Stability.Simulation
