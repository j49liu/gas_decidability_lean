import HGAS.Dynamics.GenericUnboundedClockContradiction
import HGAS.Modular.GammaTwoHorocycleOrientationReversal
import HGAS.Modular.GammaTwoOffPeriodicUnique
import Mathlib.Tactic

/-!
# Pointwise equidistribution for every nonzero horocycle scale

The project's basic Dani--Smillie interface uses the unit-speed,
positively oriented horocycle flow.  Exact frame reconstructions,
however, naturally produce

```text
        t ↦ scaledGammaTwoHorocycleFlow σ t q
```

with an arbitrary nonzero real scale `σ`.  This file closes that
normalization gap.

There are two independent ingredients.

* A positive constant change of time preserves forward genericity.
  Because genericity was defined using the integer horizons `n+1`, this
  is not merely a syntactic substitution.  We first prove that convergence
  at those integer horizons implies convergence along every sequence of
  positive real horizons tending to infinity.  The proof compares a real
  horizon with the next integer and bounds the two boundary errors by
  `2 ‖f‖ / T`.

* A negative scale reverses time.  Forward genericity alone never implies
  backward genericity for a general flow.  Here the special involution
  `gammaTwoFrameOrientationReversal` conjugates the two horocycle
  orientations and preserves normalized frame Haar probability.

The final theorem is unconditional: every nonperiodic level-two
horocycle point is forward generic for normalized frame Haar probability
at every nonzero signed speed.
-/

namespace HGAS.Modular

open Filter Function _root_.MeasureTheory Set Topology
open scoped BoundedContinuousFunction CompactlySupported Interval

noncomputable section

/-! ## Integer horizons imply arbitrary unbounded positive horizons -/

variable {X : Type*}
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
/-- A bounded continuous orbit average at a positive real horizon differs
from the average at the next integer horizon by at most `2 ‖f‖ / T`.

The next integer is indexed as `⌊T⌋₊` in `forwardOrbitAverage`, because
that definition averages up to the horizon `⌊T⌋₊ + 1`. -/
theorem dist_forwardContinuousOrbitAverageAt_forwardOrbitAverage_floor_le
    (ϕ : Flow ℝ X) (f : C_c(X, ℝ))
    {T : ℝ} (hT : 1 ≤ T) (x : X) :
    dist
        (HGAS.Dynamics.forwardContinuousOrbitAverageAt
          ϕ f.toContinuousMap T x)
        (forwardOrbitAverage ϕ f ⌊T⌋₊ x) ≤
      2 * ‖f.toBoundedContinuousFunction‖ / T := by
  let Nnat : ℕ := ⌊T⌋₊ + 1
  let N : ℝ := Nnat
  let a : X →ᵇ ℝ := f.toBoundedContinuousFunction
  let I : ℝ := HGAS.Dynamics.orbitIntegral ϕ a T x
  let J : ℝ :=
    HGAS.Dynamics.orbitIntegral ϕ a (N - T) (ϕ T x)
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hfloorLe : (⌊T⌋₊ : ℝ) ≤ T :=
    Nat.floor_le hTpos.le
  have hTltN : T < N := by
    simpa only [N, Nnat, Nat.cast_add, Nat.cast_one] using
      Nat.lt_floor_add_one T
  have hTleN : T ≤ N := hTltN.le
  have hNpos : 0 < N := hTpos.trans hTltN
  have hdeltaNonneg : 0 ≤ N - T := sub_nonneg.mpr hTleN
  have hNle : N ≤ T + 1 := by
    dsimp only [N, Nnat]
    push_cast
    linarith
  have hdeltaLe : N - T ≤ 1 := by linarith
  have hI :
      |I| ≤ ‖a‖ * T := by
    simpa only [I, Real.norm_eq_abs, abs_of_pos hTpos] using
      HGAS.Dynamics.norm_orbitIntegral_le ϕ a T x
  have hJ :
      |J| ≤ ‖a‖ * (N - T) := by
    simpa only [J, Real.norm_eq_abs,
      abs_of_nonneg hdeltaNonneg] using
      HGAS.Dynamics.norm_orbitIntegral_le
        ϕ a (N - T) (ϕ T x)
  have hdecomp :
      HGAS.Dynamics.orbitIntegral ϕ a N x = I + J := by
    calc
      HGAS.Dynamics.orbitIntegral ϕ a N x =
          HGAS.Dynamics.orbitIntegral ϕ a
            (T + (N - T)) x := by
              congr 2
              ring
      _ =
          HGAS.Dynamics.orbitIntegral ϕ a T x +
            HGAS.Dynamics.orbitIntegral ϕ a
              (N - T) (ϕ T x) :=
        HGAS.Dynamics.orbitIntegral_add ϕ a T (N - T) x
      _ = I + J := rfl
  have haverageIdentity :
      HGAS.Dynamics.forwardContinuousOrbitAverageAt
            ϕ f.toContinuousMap T x -
          forwardOrbitAverage ϕ f ⌊T⌋₊ x =
        ((N - T) / (T * N)) * I - (1 / N) * J := by
    unfold HGAS.Dynamics.forwardContinuousOrbitAverageAt
      forwardOrbitAverage
    change
      T⁻¹ * I -
          ((⌊T⌋₊ + 1 : ℝ)⁻¹ *
            HGAS.Dynamics.orbitIntegral ϕ a
              (⌊T⌋₊ + 1 : ℝ) x) =
        ((N - T) / (T * N)) * I - (1 / N) * J
    have hNcast : (⌊T⌋₊ + 1 : ℝ) = N := by
      simp only [N, Nnat, Nat.cast_add, Nat.cast_one]
    rw [hNcast, hdecomp]
    field_simp [hTpos.ne', hNpos.ne']
    ring
  have hcoeffNonneg :
      0 ≤ (N - T) / (T * N) := by positivity
  have hinvNNonneg : 0 ≤ (1 / N : ℝ) := by positivity
  have hfraction :
      (N - T) / N ≤ 1 / T := by
    rw [div_le_div_iff₀ hNpos hTpos]
    calc
      (N - T) * T ≤ 1 * T :=
        mul_le_mul_of_nonneg_right hdeltaLe hTpos.le
      _ ≤ 1 * N := by linarith
  rw [Real.dist_eq, haverageIdentity]
  calc
    |((N - T) / (T * N)) * I - (1 / N) * J| ≤
        |((N - T) / (T * N)) * I| +
          |(1 / N) * J| :=
      abs_sub _ _
    _ =
        ((N - T) / (T * N)) * |I| +
          (1 / N) * |J| := by
      rw [abs_mul, abs_mul,
        abs_of_nonneg hcoeffNonneg,
        abs_of_nonneg hinvNNonneg]
    _ ≤
        ((N - T) / (T * N)) * (‖a‖ * T) +
          (1 / N) * (‖a‖ * (N - T)) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hI hcoeffNonneg)
        (mul_le_mul_of_nonneg_left hJ hinvNNonneg)
    _ = 2 * ‖a‖ * ((N - T) / N) := by
      field_simp [hTpos.ne', hNpos.ne']
      ring
    _ ≤ 2 * ‖a‖ * (1 / T) :=
      mul_le_mul_of_nonneg_left hfraction (by positivity)
    _ = 2 * ‖f.toBoundedContinuousFunction‖ / T := by
      simp only [a]
      ring

omit [BorelSpace X] in
/-- Forward genericity at the integer horizons used in its definition
implies convergence along every sequence of real horizons tending to
`+∞`. -/
theorem IsForwardGenericFor.tendsto_forwardContinuousOrbitAverageAt
    {ϕ : Flow ℝ X} {μ : ProbabilityMeasure X} {x : X}
    (hx : IsForwardGenericFor ϕ μ x)
    (f : C_c(X, ℝ))
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) :
    Tendsto
      (fun n ↦
        HGAS.Dynamics.forwardContinuousOrbitAverageAt
          ϕ f.toContinuousMap (T n) x)
      atTop
      (𝓝 (∫ y, f y ∂(μ : Measure X))) := by
  let m : ℕ → ℕ := fun n ↦ ⌊T n⌋₊
  have hm : Tendsto m atTop atTop :=
    tendsto_nat_floor_atTop.comp hT
  have hinteger :
      Tendsto
        (fun n ↦ forwardOrbitAverage ϕ f (m n) x)
        atTop
        (𝓝 (∫ y, f y ∂(μ : Measure X))) :=
    (hx f).comp hm
  have hTone : ∀ᶠ n in atTop, (1 : ℝ) ≤ T n :=
    hT.eventually (eventually_ge_atTop 1)
  have herror :
      Tendsto
        (fun n ↦
          2 * ‖f.toBoundedContinuousFunction‖ / T n)
        atTop (𝓝 0) := by
    have hinv : Tendsto (fun n ↦ (T n)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hT
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul hinv :
        Tendsto
          (fun n ↦
            (2 * ‖f.toBoundedContinuousFunction‖) *
              (T n)⁻¹)
          atTop
          (𝓝 ((2 * ‖f.toBoundedContinuousFunction‖) * 0)))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have herrorSmall :
      ∀ᶠ n in atTop,
        2 * ‖f.toBoundedContinuousFunction‖ / T n < ε / 2 :=
    (tendsto_order.1 herror).2 _
      (by simpa only [zero_add] using half_pos hε)
  have hintegerSmall :
      ∀ᶠ n in atTop,
        dist
          (forwardOrbitAverage ϕ f (m n) x)
          (∫ y, f y ∂(μ : Measure X)) < ε / 2 :=
    (Metric.tendsto_nhds.mp hinteger) (ε / 2) (half_pos hε)
  filter_upwards [hTone, herrorSmall, hintegerSmall]
    with n hnT hnError hnInteger
  calc
    dist
        (HGAS.Dynamics.forwardContinuousOrbitAverageAt
          ϕ f.toContinuousMap (T n) x)
        (∫ y, f y ∂(μ : Measure X)) ≤
      dist
          (HGAS.Dynamics.forwardContinuousOrbitAverageAt
            ϕ f.toContinuousMap (T n) x)
          (forwardOrbitAverage ϕ f (m n) x) +
        dist
          (forwardOrbitAverage ϕ f (m n) x)
          (∫ y, f y ∂(μ : Measure X)) :=
      dist_triangle _ _ _
    _ <
        ε / 2 + ε / 2 :=
      add_lt_add
        ((dist_forwardContinuousOrbitAverageAt_forwardOrbitAverage_floor_le
          ϕ f hnT x).trans_lt hnError)
        hnInteger
    _ = ε := by ring

/-! ## Positive constant rescaling -/

/-- Exact change of variables for a positive constant rescaling of an
already scaled horocycle flow. -/
theorem forwardOrbitAverage_scaledGammaTwoHorocycleFlow_mul
    (s : ℝ) {a : ℝ} (ha : 0 < a)
    (f : C_c(GammaTwoFrameQuotient, ℝ))
    (n : ℕ) (q : GammaTwoFrameQuotient) :
    forwardOrbitAverage
        (scaledGammaTwoHorocycleFlow (s * a)) f n q =
      HGAS.Dynamics.forwardContinuousOrbitAverageAt
        (scaledGammaTwoHorocycleFlow s)
        f.toContinuousMap
        (a * (n + 1 : ℝ)) q := by
  let g : ℝ → ℝ :=
    fun t ↦
      f.toBoundedContinuousFunction
        (scaledGammaTwoHorocycleFlow s t q)
  have hintegrand :
      (fun t : ℝ ↦
          f.toBoundedContinuousFunction
            (scaledGammaTwoHorocycleFlow (s * a) t q)) =
        fun t : ℝ ↦ g (a * t) := by
    funext t
    simp only [g, scaledGammaTwoHorocycleFlow_apply,
      CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply]
    congr 2
    ring
  unfold forwardOrbitAverage
    HGAS.Dynamics.forwardContinuousOrbitAverageAt
    HGAS.Dynamics.orbitIntegral
  change
    (n + 1 : ℝ)⁻¹ *
        (∫ t in (0 : ℝ)..(n + 1 : ℝ),
          f.toBoundedContinuousFunction
            (scaledGammaTwoHorocycleFlow (s * a) t q)) =
      (a * (n + 1 : ℝ))⁻¹ *
        (∫ t in (0 : ℝ)..a * (n + 1 : ℝ),
          f.toBoundedContinuousFunction
            (scaledGammaTwoHorocycleFlow s t q))
  rw [hintegrand]
  rw [intervalIntegral.integral_comp_mul_left g ha.ne']
  simp only [mul_zero, smul_eq_mul]
  field_simp [ha.ne']
  ring

/-- Multiplying a horocycle scale by a positive constant preserves
forward genericity. -/
theorem IsForwardGenericFor.scaledGammaTwoHorocycleFlow_mul_pos
    {ν : ProbabilityMeasure GammaTwoFrameQuotient}
    {q : GammaTwoFrameQuotient} {s a : ℝ}
    (hq :
      IsForwardGenericFor
        (scaledGammaTwoHorocycleFlow s) ν q)
    (ha : 0 < a) :
    IsForwardGenericFor
      (scaledGammaTwoHorocycleFlow (s * a)) ν q := by
  intro f
  let T : ℕ → ℝ := fun n ↦ a * (n + 1 : ℝ)
  have hT : Tendsto T atTop atTop := by
    exact
      (positiveIntegerHorizon_tendsto_atTop.const_mul_atTop ha)
  have hreal :=
    hq.tendsto_forwardContinuousOrbitAverageAt f hT
  simpa only [T,
    forwardOrbitAverage_scaledGammaTwoHorocycleFlow_mul
      s ha f] using hreal

/-! ## Reversing orientation -/

/-- A compactly supported test pulled back through frame orientation
reversal. -/
def orientationReversalCompactlySupportedTest
    (f : C_c(GammaTwoFrameQuotient, ℝ)) :
    C_c(GammaTwoFrameQuotient, ℝ) :=
  f.comp
    gammaTwoFrameOrientationReversalHomeomorph.toCocompactMap

@[simp]
theorem orientationReversalCompactlySupportedTest_apply
    (f : C_c(GammaTwoFrameQuotient, ℝ))
    (q : GammaTwoFrameQuotient) :
    orientationReversalCompactlySupportedTest f q =
      f (gammaTwoFrameOrientationReversal q) :=
  rfl

/-- Orbit averages of a reversed test along scale `s` are exactly the
original-test averages along scale `-s` from the reversed point. -/
theorem forwardOrbitAverage_orientationReversal
    (s : ℝ)
    (f : C_c(GammaTwoFrameQuotient, ℝ))
    (n : ℕ) (q : GammaTwoFrameQuotient) :
    forwardOrbitAverage
        (scaledGammaTwoHorocycleFlow (-s)) f n
        (gammaTwoFrameOrientationReversal q) =
      forwardOrbitAverage
        (scaledGammaTwoHorocycleFlow s)
        (orientationReversalCompactlySupportedTest f) n q := by
  unfold forwardOrbitAverage HGAS.Dynamics.orbitIntegral
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  change
    f (scaledGammaTwoHorocycleFlow (-s) t
        (gammaTwoFrameOrientationReversal q)) =
      f (gammaTwoFrameOrientationReversal
        (scaledGammaTwoHorocycleFlow s t q))
  rw [gammaTwoFrameOrientationReversal_scaledHorocycleFlow]

/-- The mean of a test is unchanged when it is pulled back through
orientation reversal, because normalized frame Haar probability is
fixed by that involution. -/
theorem integral_orientationReversalCompactlySupportedTest
    {ν : ProbabilityMeasure GammaTwoFrameQuotient}
    (hν : IsRightInvariantFrameProbability ν)
    (f : C_c(GammaTwoFrameQuotient, ℝ)) :
    (∫ q, orientationReversalCompactlySupportedTest f q
        ∂(ν : Measure GammaTwoFrameQuotient)) =
      ∫ q, f q ∂(ν : Measure GammaTwoFrameQuotient) := by
  calc
    (∫ q, orientationReversalCompactlySupportedTest f q
        ∂(ν : Measure GammaTwoFrameQuotient)) =
      ∫ q, f (gammaTwoFrameOrientationReversal q)
        ∂(ν : Measure GammaTwoFrameQuotient) := by rfl
    _ =
      ∫ q, f q
        ∂Measure.map gammaTwoFrameOrientationReversal
          (ν : Measure GammaTwoFrameQuotient) := by
      exact
        (gammaTwoFrameOrientationReversalHomeomorph
          |>.isClosedEmbedding.integral_map f).symm
    _ = ∫ q, f q ∂(ν : Measure GammaTwoFrameQuotient) := by
      rw [hν.measurePreservingOrientationReversal.map_eq]

/-- Orientation reversal transports forward genericity at scale `s`
to forward genericity at scale `-s` from the reversed point. -/
theorem IsForwardGenericFor.orientationReversal
    {ν : ProbabilityMeasure GammaTwoFrameQuotient}
    (hν : IsRightInvariantFrameProbability ν)
    {q : GammaTwoFrameQuotient} {s : ℝ}
    (hq :
      IsForwardGenericFor
        (scaledGammaTwoHorocycleFlow s) ν q) :
    IsForwardGenericFor
      (scaledGammaTwoHorocycleFlow (-s)) ν
      (gammaTwoFrameOrientationReversal q) := by
  intro f
  have h :=
    hq (orientationReversalCompactlySupportedTest f)
  rw [← integral_orientationReversalCompactlySupportedTest hν f]
  simpa only [forwardOrbitAverage_orientationReversal s f]
    using h

/-- A point is unit-speed periodic precisely when its orientation
reversal is. -/
theorem isPeriodicHorocyclePoint_one_orientationReversal_iff
    (q : GammaTwoFrameQuotient) :
    IsPeriodicHorocyclePoint 1
        (gammaTwoFrameOrientationReversal q) ↔
      IsPeriodicHorocyclePoint 1 q := by
  constructor
  · rintro ⟨T, hT, hperiod⟩
    have hreversed :=
      congrArg gammaTwoFrameOrientationReversal hperiod
    have hminus :
        scaledGammaTwoHorocycleFlow (-1) T q = q := by
      simpa only [
        gammaTwoFrameOrientationReversal_scaledHorocycleFlow,
        neg_one_mul, neg_neg,
        gammaTwoFrameOrientationReversal_involutive] using
          hreversed
    exact
      (isPeriodicHorocyclePoint_iff_of_ne_zero
        (by norm_num : (-1 : ℝ) ≠ 0) q).mp
        ⟨T, hT, hminus⟩
  · intro hq
    have hminus :
        IsPeriodicHorocyclePoint (-1) q :=
      (isPeriodicHorocyclePoint_iff_of_ne_zero
        (by norm_num : (-1 : ℝ) ≠ 0) q).mpr hq
    rcases hminus with ⟨T, hT, hperiod⟩
    refine ⟨T, hT, ?_⟩
    have hreversed :=
      congrArg gammaTwoFrameOrientationReversal hperiod
    simpa only [
      gammaTwoFrameOrientationReversal_scaledHorocycleFlow,
      neg_neg, one_mul,
      gammaTwoFrameOrientationReversal_involutive] using
        hreversed

/-! ## Unconditional signed Dani--Smillie equidistribution -/

/-- Every nonperiodic point is Haar generic at every nonzero signed
horocycle speed.  This is the signed, normalization-independent form of
the unconditional pointwise Dani--Smillie theorem. -/
theorem gammaTwoPointwiseScaledHorocycleEquidistribution_unconditional
    (ν : ProbabilityMeasure GammaTwoFrameQuotient)
    (hν : IsRightInvariantFrameProbability ν)
    (q : GammaTwoFrameQuotient)
    (hq : ¬ IsPeriodicHorocyclePoint 1 q)
    {s : ℝ} (hs : s ≠ 0) :
    IsForwardGenericFor
      (scaledGammaTwoHorocycleFlow s) ν q := by
  rcases lt_or_gt_of_ne hs with hsneg | hspos
  · have hqreverse :
        ¬ IsPeriodicHorocyclePoint 1
          (gammaTwoFrameOrientationReversal q) := by
      simpa only [
        isPeriodicHorocyclePoint_one_orientationReversal_iff]
        using hq
    have hunitReverse :
        IsForwardGenericFor gammaTwoHorocycleFlow ν
          (gammaTwoFrameOrientationReversal q) :=
      gammaTwoPointwiseHorocycleEquidistribution_unconditional
        ν hν (gammaTwoFrameOrientationReversal q) hqreverse
    have hminusOne :
        IsForwardGenericFor
          (scaledGammaTwoHorocycleFlow (-1)) ν q := by
      have hscaledOne :
          IsForwardGenericFor
            (scaledGammaTwoHorocycleFlow 1) ν
            (gammaTwoFrameOrientationReversal q) := by
        simpa only [scaledGammaTwoHorocycleFlow_one] using
          hunitReverse
      have horiented :=
        hscaledOne.orientationReversal hν
      simpa only [
        gammaTwoFrameOrientationReversal_involutive] using
          horiented
    have hrescaled :=
      hminusOne.scaledGammaTwoHorocycleFlow_mul_pos
        (neg_pos.mpr hsneg)
    have hscale : (-1 : ℝ) * (-s) = s := by ring
    simpa only [hscale] using hrescaled
  · have hunit :
        IsForwardGenericFor gammaTwoHorocycleFlow ν q :=
      gammaTwoPointwiseHorocycleEquidistribution_unconditional
        ν hν q hq
    have hscaledOne :
        IsForwardGenericFor
          (scaledGammaTwoHorocycleFlow 1) ν q := by
      simpa only [scaledGammaTwoHorocycleFlow_one] using hunit
    have hrescaled :=
      hscaledOne.scaledGammaTwoHorocycleFlow_mul_pos hspos
    simpa only [one_mul] using hrescaled

end

end HGAS.Modular
