import HGAS.Dynamics.GenericUnboundedClockContradiction
import Mathlib.Tactic

/-!
# Positive rescaling of an integral clock's range

If `C(t) = ∫₀ᵗ w(s) ds` is a positive integral clock and `b > 0`, then

```text
  C_b(t) = C(t) / b
```

is the integral clock of `w_b(t) = b⁻¹ w(t)`.  Its inverse is

```text
  C_b⁻¹(τ) = C⁻¹(bτ),
```

and its reciprocal physical speed is therefore

```text
  1 / w_b(C_b⁻¹(τ))
    = b / w(C⁻¹(bτ)).
```

The construction is reusable whenever a physical trajectory has first
been subjected to a nonzero constant time normalization.
-/

namespace HGAS

open Filter Function Topology

noncomputable section

/-- Clock speed obtained by dividing a positive clock by a positive
range-scaling constant. -/
def rangeRescaledClockWeight
    (b : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  b⁻¹ * w t

/-- Exact integral identity for the range-rescaled clock. -/
theorem integralClock_rangeRescaledClockWeight
    (b : ℝ) (w : ℝ → ℝ) (T : ℝ) :
    integralClock (rangeRescaledClockWeight b w) T =
      b⁻¹ * integralClock w T := by
  unfold integralClock rangeRescaledClockWeight
  rw [intervalIntegral.integral_const_mul]

namespace PositiveIntegralClock

/-- Positive range rescaling preserves global clock completeness. -/
def rangeRescale
    {w : ℝ → ℝ}
    (hclock : PositiveIntegralClock w)
    {b : ℝ} (hb : 0 < b) :
    PositiveIntegralClock (rangeRescaledClockWeight b w) where
  continuous :=
    continuous_const.mul hclock.continuous
  positive := fun t ↦
    mul_pos (inv_pos.mpr hb) (hclock.positive t)
  tendsto_atTop := by
    rw [show
      integralClock (rangeRescaledClockWeight b w) =
        fun T ↦ b⁻¹ * integralClock w T by
          funext T
          exact integralClock_rangeRescaledClockWeight b w T]
    exact hclock.tendsto_atTop.const_mul_atTop
      (inv_pos.mpr hb)
  tendsto_atBot := by
    rw [show
      integralClock (rangeRescaledClockWeight b w) =
        fun T ↦ b⁻¹ * integralClock w T by
          funext T
          exact integralClock_rangeRescaledClockWeight b w T]
    exact hclock.tendsto_atBot.const_mul_atBot
      (inv_pos.mpr hb)

/-- The inverse of the range-rescaled clock evaluates the old inverse at
the multiplied physical time. -/
theorem rangeRescale_symm
    {w : ℝ → ℝ}
    (hclock : PositiveIntegralClock w)
    {b : ℝ} (hb : 0 < b)
    (τ : ℝ) :
    (PositiveIntegralClock.orderIso
        (hclock.rangeRescale hb)).symm τ =
      (PositiveIntegralClock.orderIso hclock).symm
        (b * τ) := by
  apply (PositiveIntegralClock.orderIso hclock).injective
  rw [PositiveIntegralClock.orderIso_apply]
  have hnew :
      integralClock (rangeRescaledClockWeight b w)
          ((PositiveIntegralClock.orderIso
            (hclock.rangeRescale hb)).symm τ) =
        τ := by
    rw [← PositiveIntegralClock.orderIso_apply]
    exact
      (PositiveIntegralClock.orderIso
        (hclock.rangeRescale hb)).apply_symm_apply τ
  rw [integralClock_rangeRescaledClockWeight] at hnew
  have hb0 : b ≠ 0 := hb.ne'
  have hold :
      integralClock w
          ((PositiveIntegralClock.orderIso
            (hclock.rangeRescale hb)).symm τ) =
        b * τ := by
    calc
      integralClock w
          ((PositiveIntegralClock.orderIso
            (hclock.rangeRescale hb)).symm τ) =
          b * (b⁻¹ *
            integralClock w
              ((PositiveIntegralClock.orderIso
                (hclock.rangeRescale hb)).symm τ)) := by
            field_simp
      _ = b * τ := by rw [hnew]
  rw [hold]
  exact
    (PositiveIntegralClock.orderIso hclock).apply_symm_apply
      (b * τ) |>.symm

end PositiveIntegralClock

namespace Dynamics

/-- Reciprocal speed for a range-rescaled clock. -/
theorem inverseClockReciprocal_rangeRescale
    {w : ℝ → ℝ}
    (hclock : PositiveIntegralClock w)
    {b : ℝ} (hb : 0 < b)
    (τ : ℝ) :
    inverseClockReciprocal (hclock.rangeRescale hb) τ =
      b * inverseClockReciprocal hclock (b * τ) := by
  rw [inverseClockReciprocal_apply,
    PositiveIntegralClock.rangeRescale_symm hclock hb τ,
    inverseClockReciprocal_apply]
  unfold rangeRescaledClockWeight
  have hb0 : b ≠ 0 := hb.ne'
  have hw0 :
      w ((PositiveIntegralClock.orderIso hclock).symm
        (b * τ)) ≠ 0 :=
    ne_of_gt (hclock.positive _)
  field_simp

/-- A positive-integer-horizon clock mean is divided by the same
positive range-scaling constant. -/
theorem positiveIntegerMean_rangeRescale
    {w : ℝ → ℝ}
    {b : ℝ}
    {c : ℝ}
    (hmean :
      Tendsto
        (fun n : ℕ ↦
          (positiveIntegerHorizon n)⁻¹ *
            integralClock w (positiveIntegerHorizon n))
        atTop (𝓝 c)) :
    Tendsto
      (fun n : ℕ ↦
        (positiveIntegerHorizon n)⁻¹ *
          integralClock
            (rangeRescaledClockWeight b w)
            (positiveIntegerHorizon n))
      atTop (𝓝 (b⁻¹ * c)) := by
  have hscaled :=
    hmean.const_mul (b⁻¹)
  convert hscaled using 1
  · funext n
    rw [integralClock_rangeRescaledClockWeight]
    ring

end Dynamics

end

end HGAS
