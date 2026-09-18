import HGAS.Dynamics.Recurrence
import HGAS.Dynamics.StateTimeChange
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Positive-mean clocks and time reparametrization

A positive state-dependent speed need not have a positive uniform lower
bound.  This is exactly what happens in a projective compactification: the
speed approaches zero near the equator.  Nevertheless, along a generic
orbit its integral clock is global as soon as the speed has a strictly
positive Cesàro mean.

This file isolates that elementary analytic bridge.  It proves:

* convergence of the positive-integer Cesàro averages of a continuous
  speed to a positive number forces its integral clock to tend to `+∞`;
* together with the standard constant negative-time extension this gives a
  `PositiveIntegralClock`;
* recurrence survives inverse-clock reparametrization; and
* interval integrals, hence normalized time averages, obey the expected
  change-of-variables formula.

The statements do not depend on polynomial vector fields or on the
particular compactification used later.
-/

namespace HGAS

open Filter Function Set Topology
open scoped Interval

noncomputable section

/-! ## Positive Cesàro mean implies a global clock -/

/-- The positive integer horizon used throughout the pointwise ergodic
part of the reduction. -/
def positiveIntegerHorizon (n : ℕ) : ℝ :=
  n + 1

@[simp]
theorem positiveIntegerHorizon_pos (n : ℕ) :
    0 < positiveIntegerHorizon n := by
  unfold positiveIntegerHorizon
  positivity

theorem positiveIntegerHorizon_tendsto_atTop :
    Tendsto positiveIntegerHorizon atTop atTop := by
  simpa only [positiveIntegerHorizon] using
    tendsto_atTop_add_const_right _ _
      tendsto_natCast_atTop_atTop

/-- A continuous speed whose averages on the horizons `n+1` converge to a
positive number has an integral clock tending to `+∞`.

Only the values of the clock at integer horizons enter the hypothesis.
Strict monotonicity of the clock fills the gaps between those horizons. -/
theorem integralClock_tendsto_atTop_of_positive_integerMean
    {w : ℝ → ℝ} (hw : Continuous w)
    (hwpos : ∀ t, 0 < w t)
    {c : ℝ} (hc : 0 < c)
    (hmean :
      Tendsto
        (fun n : ℕ ↦
          (positiveIntegerHorizon n)⁻¹ *
            integralClock w (positiveIntegerHorizon n))
        atTop (𝓝 c)) :
    Tendsto (integralClock w) atTop atTop := by
  have havgLower :
      ∀ᶠ n : ℕ in atTop,
        c / 2 ≤
          (positiveIntegerHorizon n)⁻¹ *
            integralClock w (positiveIntegerHorizon n) :=
    hmean.eventually (Ici_mem_nhds (by linarith))
  have hclockLower :
      ∀ᶠ n : ℕ in atTop,
        positiveIntegerHorizon n * (c / 2) ≤
          integralClock w (positiveIntegerHorizon n) := by
    filter_upwards [havgLower] with n hn
    have hTpos : 0 < positiveIntegerHorizon n :=
      positiveIntegerHorizon_pos n
    have hmul :=
      mul_le_mul_of_nonneg_left hn hTpos.le
    calc
      positiveIntegerHorizon n * (c / 2) ≤
          positiveIntegerHorizon n *
          ((positiveIntegerHorizon n)⁻¹ *
            integralClock w (positiveIntegerHorizon n)) :=
        hmul
      _ = integralClock w (positiveIntegerHorizon n) := by
        field_simp
  have hlinear :
      Tendsto
        (fun n : ℕ ↦ positiveIntegerHorizon n * (c / 2))
        atTop atTop :=
    (positiveIntegerHorizon_tendsto_atTop.atTop_mul_const
      (by linarith : 0 < c / 2))
  have hinteger :
      Tendsto
        (fun n : ℕ ↦ integralClock w (positiveIntegerHorizon n))
        atTop atTop :=
    tendsto_atTop_mono' atTop hclockLower hlinear
  have hmono : Monotone (integralClock w) :=
    (integralClock_strictMono hw hwpos).monotone
  apply tendsto_atTop_atTop.2
  intro R
  obtain ⟨N, hN⟩ :=
    (hinteger.eventually (eventually_ge_atTop R)).exists
  refine ⟨positiveIntegerHorizon N, ?_⟩
  intro t ht
  exact le_trans hN (hmono ht)

/-- Package a continuous positive speed as a global clock when its
positive-integer Cesàro mean is strictly positive and its negative-time
clock tends to `-∞`. -/
theorem positiveIntegralClock_of_positive_integerMean
    {w : ℝ → ℝ} (hw : Continuous w)
    (hwpos : ∀ t, 0 < w t)
    {c : ℝ} (hc : 0 < c)
    (hmean :
      Tendsto
        (fun n : ℕ ↦
          (positiveIntegerHorizon n)⁻¹ *
            integralClock w (positiveIntegerHorizon n))
        atTop (𝓝 c))
    (hbot : Tendsto (integralClock w) atBot atBot) :
    PositiveIntegralClock w :=
  { continuous := hw
    positive := hwpos
    tendsto_atTop :=
      integralClock_tendsto_atTop_of_positive_integerMean
        hw hwpos hc hmean
    tendsto_atBot := hbot }

/-! ## Recurrence and the inverse clock -/

/-- Applying the inverse clock to a clock value recovers the original
time. -/
@[simp]
theorem PositiveIntegralClock.symm_integralClock
    {w : ℝ → ℝ} (hclock : PositiveIntegralClock w) (t : ℝ) :
    (PositiveIntegralClock.orderIso hclock).symm
        (integralClock w t) =
      t := by
  rw [← PositiveIntegralClock.orderIso_apply hclock]
  exact (PositiveIntegralClock.orderIso hclock).symm_apply_apply t

/-- Reparametrizing a recurrent trajectory by the inverse of a positive
integral clock preserves forward recurrence at time zero.  The new return
times are the clock values of the old return times. -/
theorem ForwardRecurrentAt.inverseClock
    {X : Type*} [TopologicalSpace X]
    {γ : ℝ → X} {w : ℝ → ℝ}
    (hγ : ForwardRecurrentAt γ 0)
    (hclock : PositiveIntegralClock w) :
    ForwardRecurrentAt
      (fun τ ↦
        γ ((PositiveIntegralClock.orderIso hclock).symm τ))
      0 := by
  obtain ⟨returnTime, htime, hreturn⟩ := hγ
  refine
    ⟨fun n ↦ integralClock w (returnTime n),
      hclock.tendsto_atTop.comp htime, ?_⟩
  have horbit :
      (fun n ↦
          γ
            ((PositiveIntegralClock.orderIso hclock).symm
              (integralClock w (returnTime n)))) =
        fun n ↦ γ (returnTime n) := by
    funext n
    rw [PositiveIntegralClock.symm_integralClock]
  have hzero :
      γ ((PositiveIntegralClock.orderIso hclock).symm 0) =
        γ 0 := by
    rw [PositiveIntegralClock.symm_zero hclock]
  simpa only [horbit, hzero] using hreturn

/-! ## Exact change of variables -/

/-- Change variables from compact time to inverse-clock time. -/
theorem integral_inverseClock_eq
    {w h : ℝ → ℝ}
    (hclock : PositiveIntegralClock w)
    (hh : Continuous h) (T : ℝ) :
    (∫ τ in (0 : ℝ)..integralClock w T,
        h ((PositiveIntegralClock.orderIso hclock).symm τ)) =
      ∫ t in (0 : ℝ)..T, h t * w t := by
  let g : ℝ → ℝ :=
    fun τ ↦ h ((PositiveIntegralClock.orderIso hclock).symm τ)
  have hg : Continuous g :=
    hh.comp (PositiveIntegralClock.orderIso hclock).symm.continuous
  have hsub :=
    intervalIntegral.integral_comp_mul_deriv
      (a := (0 : ℝ)) (b := T)
      (f := integralClock w) (f' := w) (g := g)
      (fun t _ ↦ integralClock_hasDerivAt hclock.continuous t)
      hclock.continuous.continuousOn hg
  rw [integralClock_zero] at hsub
  rw [← hsub]
  apply intervalIntegral.integral_congr
  intro t _
  change
    h
        ((PositiveIntegralClock.orderIso hclock).symm
          (integralClock w t)) *
        w t =
      h t * w t
  rw [PositiveIntegralClock.symm_integralClock]

/-- The normalized inverse-clock average is the ratio of the corresponding
weighted original-time average and the speed average. -/
theorem inverseClockAverage_eq_ratio
    {w h : ℝ → ℝ}
    (hclock : PositiveIntegralClock w)
    (hh : Continuous h) {T : ℝ} (hT : T ≠ 0) :
    (integralClock w T)⁻¹ *
        (∫ τ in (0 : ℝ)..integralClock w T,
          h ((PositiveIntegralClock.orderIso hclock).symm τ)) =
      (T⁻¹ * ∫ t in (0 : ℝ)..T, h t * w t) /
        (T⁻¹ * integralClock w T) := by
  have hclockT : integralClock w T ≠ 0 := by
    intro hzero
    have hstrict :=
      integralClock_strictMono hclock.continuous hclock.positive
    rcases lt_trichotomy T 0 with hneg | hzeroT | hpos
    · have := hstrict hneg
      simp only [integralClock_zero, hzero] at this
      exact (lt_irrefl 0) this
    · exact hT hzeroT
    · have := hstrict hpos
      simp only [integralClock_zero, hzero] at this
      exact (lt_irrefl 0) this
  rw [integral_inverseClock_eq hclock hh T]
  field_simp

/-- If the speed averages tend to a nonzero number and the corresponding
weighted observable averages tend to `d`, then inverse-clock averages,
sampled at the clock values of the same horizons, tend to `d / c`. -/
theorem inverseClockAverage_tendsto_ratio
    {w h : ℝ → ℝ}
    (hclock : PositiveIntegralClock w)
    (hh : Continuous h)
    {c d : ℝ} (hc : c ≠ 0)
    (hspeed :
      Tendsto
        (fun n : ℕ ↦
          (positiveIntegerHorizon n)⁻¹ *
            integralClock w (positiveIntegerHorizon n))
        atTop (𝓝 c))
    (hweighted :
      Tendsto
        (fun n : ℕ ↦
          (positiveIntegerHorizon n)⁻¹ *
            ∫ t in (0 : ℝ)..positiveIntegerHorizon n,
              h t * w t)
        atTop (𝓝 d)) :
    Tendsto
      (fun n : ℕ ↦
        (integralClock w (positiveIntegerHorizon n))⁻¹ *
          ∫ τ in (0 : ℝ)..integralClock w (positiveIntegerHorizon n),
            h ((PositiveIntegralClock.orderIso hclock).symm τ))
      atTop (𝓝 (d / c)) := by
  have hratio :=
    hweighted.div hspeed hc
  apply hratio.congr'
  exact Eventually.of_forall fun n ↦ by
    symm
    exact inverseClockAverage_eq_ratio hclock hh
      (ne_of_gt (positiveIntegerHorizon_pos n))

end

end HGAS
