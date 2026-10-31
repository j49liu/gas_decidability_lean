import Stability.Simulation.FormulaPrecision
import Stability.Simulation.ClockGain

/-!
# A clock-weighted quadratic penalty absorbs linear error costs

Completing the square gives a pointwise bound independent of the error
size. Along a unit-speed clock the remaining inverse-quadratic tail has
a uniform integral bound. This is the numerical estimate used in the
penalized-output argument; the monitor and radical-defect comparisons
which supply that argument's linear cost are separate theorems.
-/

namespace Stability.Simulation

open Set MeasureTheory

/-- A positive quadratic weight absorbs a linear cost of arbitrary sign. -/
theorem linear_sub_quadratic_le {weight : ℝ} (hweight : 0 < weight)
    (cost error : ℝ) :
    cost * error - weight * error ^ 2 ≤ cost ^ 2 / (4 * weight) := by
  apply (le_div_iff₀ (by positivity : 0 < 4 * weight)).mpr
  nlinarith [sq_nonneg (2 * weight * error - cost)]

/-- The penalty has a uniform upper integral bound on every supplied
finite forward clock segment, regardless of the size of the error or
of the initial clock offset. -/
theorem integral_clockWeightedPenalty_le
    {a b : ℝ} (hab : a ≤ b) {clock error : ℝ → ℝ}
    (hclock : ContinuousOn clock (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt clock 1 t)
    (herror : ContinuousOn error (Icc a b)) (cost : ℝ) :
    (∫ t in a..b, cost * error t - (1 + clock t ^ 2) * error t ^ 2) ≤
      Real.pi * cost ^ 2 / 4 := by
  have hclockValue (t : ℝ) (ht : t ∈ Icc a b) :
      clock t = (clock a - a) + t := by
    have h := unitSpeedClock_eq hclock hderiv ht
    linarith
  have hpenaltyContinuous : ContinuousOn
      (fun t ↦ cost * error t - (1 + clock t ^ 2) * error t ^ 2) (Icc a b) :=
    (continuousOn_const.mul herror).sub
      ((continuousOn_const.add (hclock.pow 2)).mul (herror.pow 2))
  have htailContinuous : Continuous
      (fun t : ℝ ↦ (cost ^ 2 / 4) / (1 + ((clock a - a) + t) ^ 2)) :=
    continuous_const.div (by fun_prop) (fun t ↦ ne_of_gt (by positivity))
  have hcomparison := intervalIntegral.integral_mono_on (μ := volume) hab
    (hpenaltyContinuous.intervalIntegrable_of_Icc hab)
    (htailContinuous.intervalIntegrable a b) (fun t ht ↦ by
      have h := linear_sub_quadratic_le (by positivity : 0 < 1 + clock t ^ 2)
        cost (error t)
      simpa only [hclockValue t ht, div_div, mul_comm] using h)
  apply hcomparison.trans
  rw [AbsFormula.integral_clockTail]
  have harctan : Real.arctan ((clock a - a) + b) -
      Real.arctan ((clock a - a) + a) ≤ Real.pi := by
    linarith [Real.arctan_lt_pi_div_two ((clock a - a) + b),
      Real.neg_pi_div_two_lt_arctan ((clock a - a) + a)]
  have h := mul_le_mul_of_nonneg_left harctan (by positivity : 0 ≤ cost ^ 2 / 4)
  nlinarith

end Stability.Simulation
