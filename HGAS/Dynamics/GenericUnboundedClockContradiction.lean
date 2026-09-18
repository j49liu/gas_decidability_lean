import HGAS.Dynamics.GenericUnboundedObservableDivergence
import HGAS.Dynamics.PositiveMeanTimeReparametrization
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# A positive-mean clock cannot hide a Haar-generic cusp excursion

This file isolates the analytic contradiction used to exclude the
nonperiodic modular branch.

Let `w(t) > 0` be the speed which converts compact time `t` into physical
time

```text
                         C(T) = ∫₀ᵀ w(t) dt.
```

If the compact-time averages of `w` tend to a positive number `c`, then
the physical-time average of the reciprocal speed, sampled at the clock
horizons `C(n+1)`, tends to `1/c`.  In particular it stays bounded.

On the other hand, suppose the physical orbit is generic for a
probability and carries a nonnegative continuous observable `R` below
the reciprocal speed.  If compactly supported continuous minorants of
`R` have arbitrarily large means, genericity forces the averages of `R`
to diverge.  Integer-horizon divergence also holds along every positive
real horizon tending to infinity, hence along `C(n+1)`.  The two
conclusions are incompatible.

The result is deliberately independent of modular geometry.  A modular
application only has to construct the compactly supported cusp
minorants and prove the pointwise comparison with reciprocal projective
speed.
-/

namespace HGAS.Dynamics

open Filter Function _root_.MeasureTheory Set Topology
open scoped BoundedContinuousFunction CompactlySupported Interval

noncomputable section

variable {X : Type*}
  [TopologicalSpace X] [MeasurableSpace X]

/-- The forward average on an arbitrary real horizon.  This is the
real-horizon companion of `forwardContinuousOrbitAverage`, whose horizon
is always the positive integer `n+1`. -/
def forwardContinuousOrbitAverageAt
    (ϕ : Flow ℝ X) (R : C(X, ℝ))
    (T : ℝ) (x : X) : ℝ :=
  T⁻¹ * ∫ t in (0 : ℝ)..T, R (ϕ t x)

omit [MeasurableSpace X] in
@[simp]
theorem forwardContinuousOrbitAverageAt_positiveIntegerHorizon
    (ϕ : Flow ℝ X) (R : C(X, ℝ))
    (n : ℕ) (x : X) :
    forwardContinuousOrbitAverageAt ϕ R
        (positiveIntegerHorizon n) x =
      forwardContinuousOrbitAverage ϕ R n x := by
  rfl

omit [MeasurableSpace X] in
/-- For a nonnegative observable, the average on a real horizon is at
least one half of the average on the preceding positive integer horizon.

The factor `1/2` is intentionally coarse.  If `N = ⌊T⌋ ≥ 1`, then
`N ≤ T < N+1 ≤ 2N`; nonnegativity lets us compare the two interval
integrals. -/
theorem half_floorAverage_le_forwardContinuousOrbitAverageAt
    (ϕ : Flow ℝ X) (R : C(X, ℝ))
    (hR : ∀ x, 0 ≤ R x)
    {T : ℝ} (hT : 1 ≤ T) (x : X) :
    (1 / 2 : ℝ) *
        forwardContinuousOrbitAverage ϕ R
          (⌊T⌋₊ - 1) x ≤
      forwardContinuousOrbitAverageAt ϕ R T x := by
  let N : ℕ := ⌊T⌋₊
  have hN : 1 ≤ N := by
    exact (Nat.one_le_floor_iff T).2 hT
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hNleT : (N : ℝ) ≤ T := by
    exact Nat.floor_le hTpos.le
  have hTltN : T < (N : ℝ) + 1 := by
    exact Nat.lt_floor_add_one T
  have hTleTwoN : T ≤ 2 * (N : ℝ) := by
    have hOneLeN : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  let f : ℝ → ℝ := fun t ↦ R (ϕ t x)
  have hfcont : Continuous f :=
    R.continuous.comp
      (ϕ.continuous continuous_id continuous_const)
  have hINnonneg :
      0 ≤ ∫ t in (0 : ℝ)..(N : ℝ), f t :=
    intervalIntegral.integral_nonneg hNpos.le
      (fun t _ ↦ hR (ϕ t x))
  have hmono :
      (∫ t in (0 : ℝ)..(N : ℝ), f t) ≤
        ∫ t in (0 : ℝ)..T, f t :=
    intervalIntegral.integral_mono_interval
      (a := (0 : ℝ)) (b := (N : ℝ))
      (c := (0 : ℝ)) (d := T)
      le_rfl hNpos.le hNleT
      (Filter.Eventually.of_forall
        (fun t ↦ hR (ϕ t x)))
      (hfcont.intervalIntegrable _ _)
  have hcross :
      (∫ t in (0 : ℝ)..(N : ℝ), f t) * T ≤
        (∫ t in (0 : ℝ)..T, f t) * (2 * (N : ℝ)) := by
    calc
      (∫ t in (0 : ℝ)..(N : ℝ), f t) * T ≤
          (∫ t in (0 : ℝ)..(N : ℝ), f t) *
            (2 * (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hTleTwoN hINnonneg
      _ ≤
          (∫ t in (0 : ℝ)..T, f t) *
            (2 * (N : ℝ)) :=
        mul_le_mul_of_nonneg_right hmono (by positivity)
  have hratio :
      (∫ t in (0 : ℝ)..(N : ℝ), f t) /
          (2 * (N : ℝ)) ≤
        (∫ t in (0 : ℝ)..T, f t) / T := by
    exact
      (div_le_div_iff₀ (by positivity : 0 < 2 * (N : ℝ))
        hTpos).2 hcross
  have hsub : N - 1 + 1 = N :=
    Nat.sub_add_cancel hN
  unfold forwardContinuousOrbitAverageAt
    forwardContinuousOrbitAverage
  change
    (1 / 2 : ℝ) *
        ((((N - 1 : ℕ) : ℝ) + 1)⁻¹ *
          ∫ t in (0 : ℝ)..((N - 1 : ℕ) : ℝ) + 1,
            f t) ≤
      T⁻¹ * ∫ t in (0 : ℝ)..T, f t
  rw [← Nat.cast_one, ← Nat.cast_add, hsub]
  simp only [Nat.cast_one]
  change
    (1 / 2 : ℝ) *
        ((N : ℝ)⁻¹ *
          ∫ t in (0 : ℝ)..(N : ℝ), f t) ≤
      T⁻¹ * ∫ t in (0 : ℝ)..T, f t
  calc
    (1 / 2 : ℝ) *
          ((N : ℝ)⁻¹ *
            ∫ t in (0 : ℝ)..(N : ℝ), f t) =
        (∫ t in (0 : ℝ)..(N : ℝ), f t) /
          (2 * (N : ℝ)) := by field_simp
    _ ≤
        (∫ t in (0 : ℝ)..T, f t) / T :=
      hratio
    _ =
        T⁻¹ * ∫ t in (0 : ℝ)..T, f t := by
      rw [div_eq_inv_mul]

omit [MeasurableSpace X] in
/-- Divergence on the defining positive integer horizons propagates to
every sequence of real horizons tending to `+∞`, provided the observable
is nonnegative. -/
theorem forwardContinuousOrbitAverageAt_tendsto_atTop_of_integer
    (ϕ : Flow ℝ X) (R : C(X, ℝ))
    (hR : ∀ x, 0 ≤ R x)
    {x : X}
    (hinteger :
      Tendsto
        (fun n ↦ forwardContinuousOrbitAverage ϕ R n x)
        atTop atTop)
    {H : ℕ → ℝ} (hH : Tendsto H atTop atTop) :
    Tendsto
      (fun n ↦ forwardContinuousOrbitAverageAt ϕ R (H n) x)
      atTop atTop := by
  have hfloor :
      Tendsto (fun n ↦ ⌊H n⌋₊ - 1) atTop atTop :=
    (tendsto_sub_atTop_nat 1).comp
      (tendsto_nat_floor_atTop.comp hH)
  have hsample :
      Tendsto
        (fun n ↦
          forwardContinuousOrbitAverage ϕ R
            (⌊H n⌋₊ - 1) x)
        atTop atTop :=
    hinteger.comp hfloor
  have hhalf :
      Tendsto
        (fun n ↦
          (1 / 2 : ℝ) *
            forwardContinuousOrbitAverage ϕ R
              (⌊H n⌋₊ - 1) x)
        atTop atTop :=
    hsample.const_mul_atTop (by norm_num)
  have hHone : ∀ᶠ n in atTop, (1 : ℝ) ≤ H n :=
    hH.eventually (eventually_ge_atTop 1)
  have hlower :
      ∀ᶠ n in atTop,
        (1 / 2 : ℝ) *
            forwardContinuousOrbitAverage ϕ R
              (⌊H n⌋₊ - 1) x ≤
          forwardContinuousOrbitAverageAt ϕ R (H n) x := by
    filter_upwards [hHone] with n hn
    exact
      half_floorAverage_le_forwardContinuousOrbitAverageAt
        ϕ R hR hn x
  exact tendsto_atTop_mono' atTop hlower hhalf

/-- The reciprocal speed observed in physical time is continuous. -/
def inverseClockReciprocal
    {w : ℝ → ℝ} (hclock : PositiveIntegralClock w) :
    C(ℝ, ℝ) :=
  ⟨fun τ ↦
      (w ((PositiveIntegralClock.orderIso hclock).symm τ))⁻¹,
    Continuous.inv₀
      (hclock.continuous.comp
        (PositiveIntegralClock.orderIso hclock).symm.continuous)
      (fun τ ↦ ne_of_gt
        (hclock.positive
          ((PositiveIntegralClock.orderIso hclock).symm τ)))⟩

@[simp]
theorem inverseClockReciprocal_apply
    {w : ℝ → ℝ} (hclock : PositiveIntegralClock w) (τ : ℝ) :
    inverseClockReciprocal hclock τ =
      (w ((PositiveIntegralClock.orderIso hclock).symm τ))⁻¹ :=
  rfl

/-- Exact reciprocal-clock identity:

```text
 ∫₀^{C(T)} 1 / w(C⁻¹(τ)) dτ = T.
```
-/
theorem integral_inverseClockReciprocal
    {w : ℝ → ℝ} (hclock : PositiveIntegralClock w) (T : ℝ) :
    (∫ τ in (0 : ℝ)..integralClock w T,
        inverseClockReciprocal hclock τ) = T := by
  change
    (∫ τ in (0 : ℝ)..integralClock w T,
      (w ((PositiveIntegralClock.orderIso hclock).symm τ))⁻¹) = T
  rw [integral_inverseClock_eq hclock
    (Continuous.inv₀ hclock.continuous
      (fun t ↦ ne_of_gt (hclock.positive t))) T]
  simp_rw [inv_mul_cancel₀ (ne_of_gt (hclock.positive _))]
  simp

/-- **Positive-mean clock versus generic cusp divergence.**

There is no generic physical orbit for which:

* compact-time speed has positive mean `c`;
* a nonnegative continuous observable `R` lies below reciprocal speed;
* and compactly supported continuous minorants of `R` have arbitrarily
  large probability means.

This is the reusable analytic endpoint of the nonperiodic modular
exclusion. -/
theorem not_generic_of_positiveMeanClock_and_unboundedMinorants
    (ϕ : Flow ℝ X)
    (μ : ProbabilityMeasure X)
    (R : C(X, ℝ))
    (hR : ∀ x, 0 ≤ R x)
    (hminorants :
      ∀ B : ℝ, ∃ f : C_c(X, ℝ),
        (∀ x, 0 ≤ f x) ∧
        (∀ x, f x ≤ R x) ∧
        B < ∫ x, f x ∂(μ : Measure X))
    {q : X}
    (hq : HGAS.Modular.IsForwardGenericFor ϕ μ q)
    {w : ℝ → ℝ}
    (hclock : PositiveIntegralClock w)
    {c : ℝ} (hc : 0 < c)
    (hmean :
      Tendsto
        (fun n : ℕ ↦
          (positiveIntegerHorizon n)⁻¹ *
            integralClock w (positiveIntegerHorizon n))
        atTop (𝓝 c))
    (hbound :
      ∀ τ : ℝ,
        R (ϕ τ q) ≤ inverseClockReciprocal hclock τ) :
    False := by
  have hinteger :
      Tendsto
        (fun n ↦ forwardContinuousOrbitAverage ϕ R n q)
        atTop atTop :=
    forwardContinuousOrbitAverage_tendsto_atTop_of_generic
      ϕ μ R hminorants hq
  let H : ℕ → ℝ :=
    fun n ↦ integralClock w (positiveIntegerHorizon n)
  have hH : Tendsto H atTop atTop :=
    hclock.tendsto_atTop.comp positiveIntegerHorizon_tendsto_atTop
  have hdiv :
      Tendsto
        (fun n ↦ forwardContinuousOrbitAverageAt ϕ R (H n) q)
        atTop atTop :=
    forwardContinuousOrbitAverageAt_tendsto_atTop_of_integer
      ϕ R hR hinteger hH
  have hweighted :
      Tendsto
        (fun n : ℕ ↦
          (positiveIntegerHorizon n)⁻¹ *
            ∫ t in (0 : ℝ)..positiveIntegerHorizon n,
              (w t)⁻¹ * w t)
        atTop (𝓝 1) := by
    have heq :
        (fun n : ℕ ↦
          (positiveIntegerHorizon n)⁻¹ *
            ∫ t in (0 : ℝ)..positiveIntegerHorizon n,
              (w t)⁻¹ * w t) =
          fun _ : ℕ ↦ (1 : ℝ) := by
      funext n
      simp_rw [inv_mul_cancel₀ (ne_of_gt (hclock.positive _))]
      simp only [intervalIntegral.integral_const, sub_zero,
        smul_eq_mul, mul_one]
      exact
        inv_mul_cancel₀
          (ne_of_gt (positiveIntegerHorizon_pos n))
    rw [heq]
    exact tendsto_const_nhds
  have hreciprocal :
      Tendsto
        (fun n : ℕ ↦
          (integralClock w (positiveIntegerHorizon n))⁻¹ *
            ∫ τ in (0 : ℝ)..
                integralClock w (positiveIntegerHorizon n),
              inverseClockReciprocal hclock τ)
        atTop (𝓝 (1 / c)) := by
    simpa only [inverseClockReciprocal_apply] using
      inverseClockAverage_tendsto_ratio
        hclock
        (Continuous.inv₀ hclock.continuous
          (fun t ↦ ne_of_gt (hclock.positive t)))
        hc.ne' hmean hweighted
  have hle :
      ∀ n : ℕ,
        forwardContinuousOrbitAverageAt ϕ R (H n) q ≤
          (integralClock w (positiveIntegerHorizon n))⁻¹ *
            ∫ τ in (0 : ℝ)..
                integralClock w (positiveIntegerHorizon n),
              inverseClockReciprocal hclock τ := by
    intro n
    have hTpos :
        0 < integralClock w (positiveIntegerHorizon n) := by
      have hstrict :=
        integralClock_strictMono hclock.continuous hclock.positive
          (positiveIntegerHorizon_pos n)
      simpa only [integralClock_zero] using hstrict
    have hRcont :
        Continuous (fun τ : ℝ ↦ R (ϕ τ q)) :=
      R.continuous.comp
        (ϕ.continuous continuous_id continuous_const)
    have hreccont :
        Continuous (fun τ : ℝ ↦ inverseClockReciprocal hclock τ) :=
      (inverseClockReciprocal hclock).continuous
    have hint :
        (∫ τ in (0 : ℝ)..
            integralClock w (positiveIntegerHorizon n),
            R (ϕ τ q)) ≤
          ∫ τ in (0 : ℝ)..
            integralClock w (positiveIntegerHorizon n),
            inverseClockReciprocal hclock τ :=
      intervalIntegral.integral_mono_on hTpos.le
        (hRcont.intervalIntegrable _ _)
        (hreccont.intervalIntegrable _ _)
        (fun τ _ ↦ hbound τ)
    unfold forwardContinuousOrbitAverageAt H
    exact
      mul_le_mul_of_nonneg_left hint
        (inv_nonneg.mpr hTpos.le)
  let B : ℝ := 1 / c + 1
  have hdivEventually :
      ∀ᶠ n in atTop,
        B <
          forwardContinuousOrbitAverageAt ϕ R (H n) q :=
    hdiv.eventually (eventually_gt_atTop B)
  have hrecEventually :
      ∀ᶠ n in atTop,
        (integralClock w (positiveIntegerHorizon n))⁻¹ *
            ∫ τ in (0 : ℝ)..
                integralClock w (positiveIntegerHorizon n),
              inverseClockReciprocal hclock τ <
          B := by
    exact
      (tendsto_order.1 hreciprocal).2
        _ (by dsimp only [B]; linarith)
  obtain ⟨n, hnDiv, hnRec⟩ :=
    (hdivEventually.and hrecEventually).exists
  have hBB : B < B :=
    (hnDiv.trans_le (hle n)).trans hnRec
  exact (lt_irrefl B) hBB

/-- A more flexible form of the clock contradiction, tailored to cusp
charts.

Instead of first assembling one globally continuous unbounded
observable, it is enough to produce, for every threshold `B`, a single
nonnegative compactly supported continuous test whose mean exceeds `B`
and whose value along the chosen orbit is bounded by reciprocal speed.
This is often substantially easier: regularity of Haar measure and an
injective cusp chart directly produce one compact bump at a time.

The loss of a factor four in the proof is harmless because the test
means are assumed arbitrarily large. -/
theorem not_generic_of_positiveMeanClock_and_largeCompactTests
    (ϕ : Flow ℝ X)
    (μ : ProbabilityMeasure X)
    {q : X}
    (hq : HGAS.Modular.IsForwardGenericFor ϕ μ q)
    {w : ℝ → ℝ}
    (hclock : PositiveIntegralClock w)
    {c : ℝ} (hc : 0 < c)
    (hmean :
      Tendsto
        (fun n : ℕ ↦
          (positiveIntegerHorizon n)⁻¹ *
            integralClock w (positiveIntegerHorizon n))
        atTop (𝓝 c))
    (hlarge :
      ∀ B : ℝ, ∃ f : C_c(X, ℝ),
        (∀ x, 0 ≤ f x) ∧
        B < ∫ x, f x ∂(μ : Measure X) ∧
        ∀ τ : ℝ,
          f (ϕ τ q) ≤ inverseClockReciprocal hclock τ) :
    False := by
  let D : ℝ := 1 / c + 1
  have hD : 0 < D := by
    dsimp only [D]
    positivity
  obtain ⟨f, hfnonneg, hfmean, hfbound⟩ :=
    hlarge (4 * D)
  let I : ℝ := ∫ x, f x ∂(μ : Measure X)
  have hI : 4 * D < I := by
    simpa only [I] using hfmean
  have hIpos : 0 < I := (mul_pos (by norm_num) hD).trans hI
  let R : C(X, ℝ) := f.toContinuousMap
  let H : ℕ → ℝ :=
    fun n ↦ integralClock w (positiveIntegerHorizon n)
  have hH : Tendsto H atTop atTop :=
    hclock.tendsto_atTop.comp positiveIntegerHorizon_tendsto_atTop
  have hfloor :
      Tendsto (fun n ↦ ⌊H n⌋₊ - 1) atTop atTop :=
    (tendsto_sub_atTop_nat 1).comp
      (tendsto_nat_floor_atTop.comp hH)
  have hsample :
      Tendsto
        (fun n ↦
          forwardContinuousOrbitAverage ϕ R
            (⌊H n⌋₊ - 1) q)
        atTop (𝓝 I) := by
    simpa only [R, I, forwardContinuousOrbitAverage,
      HGAS.Modular.forwardOrbitAverage,
      ContinuousMap.comp_apply,
      ContinuousMap.coe_mk] using
      (hq f).comp hfloor
  have hsampleLower :
      ∀ᶠ n in atTop,
        I / 2 <
          forwardContinuousOrbitAverage ϕ R
            (⌊H n⌋₊ - 1) q :=
    (tendsto_order.1 hsample).1
      _ (by linarith [hIpos])
  have hHone : ∀ᶠ n in atTop, (1 : ℝ) ≤ H n :=
    hH.eventually (eventually_ge_atTop 1)
  have hphysicalLower :
      ∀ᶠ n in atTop,
        D <
          forwardContinuousOrbitAverageAt ϕ R (H n) q := by
    filter_upwards [hsampleLower, hHone] with n hnSample hnH
    have hhalf :=
      half_floorAverage_le_forwardContinuousOrbitAverageAt
        ϕ R (by
          intro x
          exact hfnonneg x) hnH q
    have hquarter :
        D <
          (1 / 2 : ℝ) *
            forwardContinuousOrbitAverage ϕ R
              (⌊H n⌋₊ - 1) q := by
      have hDI : D < I / 4 := by linarith
      nlinarith
    exact hquarter.trans_le hhalf
  have hweighted :
      Tendsto
        (fun n : ℕ ↦
          (positiveIntegerHorizon n)⁻¹ *
            ∫ t in (0 : ℝ)..positiveIntegerHorizon n,
              (w t)⁻¹ * w t)
        atTop (𝓝 1) := by
    have heq :
        (fun n : ℕ ↦
          (positiveIntegerHorizon n)⁻¹ *
            ∫ t in (0 : ℝ)..positiveIntegerHorizon n,
              (w t)⁻¹ * w t) =
          fun _ : ℕ ↦ (1 : ℝ) := by
      funext n
      simp_rw [inv_mul_cancel₀ (ne_of_gt (hclock.positive _))]
      simp only [intervalIntegral.integral_const, sub_zero,
        smul_eq_mul, mul_one]
      exact
        inv_mul_cancel₀
          (ne_of_gt (positiveIntegerHorizon_pos n))
    rw [heq]
    exact tendsto_const_nhds
  have hreciprocal :
      Tendsto
        (fun n : ℕ ↦
          (integralClock w (positiveIntegerHorizon n))⁻¹ *
            ∫ τ in (0 : ℝ)..
                integralClock w (positiveIntegerHorizon n),
              inverseClockReciprocal hclock τ)
        atTop (𝓝 (1 / c)) := by
    simpa only [inverseClockReciprocal_apply] using
      inverseClockAverage_tendsto_ratio
        hclock
        (Continuous.inv₀ hclock.continuous
          (fun t ↦ ne_of_gt (hclock.positive t)))
        hc.ne' hmean hweighted
  have hreciprocalUpper :
      ∀ᶠ n in atTop,
        (integralClock w (positiveIntegerHorizon n))⁻¹ *
            ∫ τ in (0 : ℝ)..
                integralClock w (positiveIntegerHorizon n),
              inverseClockReciprocal hclock τ <
          D := by
    exact
      (tendsto_order.1 hreciprocal).2
        _ (by dsimp only [D]; linarith)
  have hle :
      ∀ n : ℕ,
        forwardContinuousOrbitAverageAt ϕ R (H n) q ≤
          (integralClock w (positiveIntegerHorizon n))⁻¹ *
            ∫ τ in (0 : ℝ)..
                integralClock w (positiveIntegerHorizon n),
              inverseClockReciprocal hclock τ := by
    intro n
    have hTpos :
        0 < integralClock w (positiveIntegerHorizon n) := by
      have hstrict :=
        integralClock_strictMono hclock.continuous hclock.positive
          (positiveIntegerHorizon_pos n)
      simpa only [integralClock_zero] using hstrict
    have hRcont :
        Continuous (fun τ : ℝ ↦ R (ϕ τ q)) :=
      R.continuous.comp
        (ϕ.continuous continuous_id continuous_const)
    have hreccont :
        Continuous (fun τ : ℝ ↦ inverseClockReciprocal hclock τ) :=
      (inverseClockReciprocal hclock).continuous
    have hint :
        (∫ τ in (0 : ℝ)..
            integralClock w (positiveIntegerHorizon n),
            R (ϕ τ q)) ≤
          ∫ τ in (0 : ℝ)..
            integralClock w (positiveIntegerHorizon n),
            inverseClockReciprocal hclock τ :=
      intervalIntegral.integral_mono_on hTpos.le
        (hRcont.intervalIntegrable _ _)
        (hreccont.intervalIntegrable _ _)
        (fun τ _ ↦ by
          change f (ϕ τ q) ≤ inverseClockReciprocal hclock τ
          exact hfbound τ)
    unfold forwardContinuousOrbitAverageAt H
    exact
      mul_le_mul_of_nonneg_left hint
        (inv_nonneg.mpr hTpos.le)
  obtain ⟨n, hnLower, hnUpper⟩ :=
    (hphysicalLower.and hreciprocalUpper).exists
  have hDD : D < D :=
    (hnLower.trans_le (hle n)).trans hnUpper
  exact (lt_irrefl D) hDD

end

end HGAS.Dynamics
