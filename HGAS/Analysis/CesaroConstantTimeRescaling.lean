import HGAS.Analysis.CesaroExponentialSeriesArbitraryHorizon
import Mathlib.Tactic

/-!
# Cesàro means under a constant change of time

For a nonzero real number `a`, oriented interval integration gives the
exact identity

```text
  Cesàro(t ↦ f(a t), T / a) = Cesàro(f, T).
```

When `a > 0`, the new horizons `T/a` still tend to `+∞`.  For a negative
scale, forward averages of `f(a t)` are instead obtained from forward
averages of the reversed function `t ↦ f(-t)`, rescaled by the positive
number `-a`.  The final theorem packages this honest two-sided statement;
it never infers a backward average from a forward one.

The file also records the elementary passage from a centered mean
`Cesàro(f-c) → 0` to the raw mean `Cesàro(f) → c`.
-/

namespace HGAS.Analysis

open Filter
open scoped Topology Interval

noncomputable section

/-- Exact Cesàro substitution under multiplication of time by a nonzero
real constant.  The statement is valid for either sign because interval
integrals are oriented. -/
theorem cesaroMeanAt_comp_mul_div
    (f : ℝ → ℂ) {a T : ℝ} (ha : a ≠ 0) :
    cesaroMeanAt (fun t ↦ f (a * t)) (T / a) =
      cesaroMeanAt f T := by
  by_cases hT : T = 0
  · subst T
    simp [cesaroMeanAt]
  unfold cesaroMeanAt
  rw [intervalIntegral.integral_comp_mul_left f ha]
  simp only [mul_zero, Complex.real_smul]
  push_cast
  field_simp [ha, hT]

/-- A positive time rescaling transports a Cesàro limit along the
explicitly divided horizons. -/
theorem tendsto_cesaroMeanAt_comp_mul_of_pos
    (f : ℝ → ℂ) {a : ℝ} (ha : 0 < a)
    {T : ℕ → ℝ} {L : ℂ}
    (hT : Tendsto T atTop atTop)
    (hmean :
      Tendsto
        (fun n ↦ cesaroMeanAt f (T n))
        atTop (nhds L)) :
    Tendsto (fun n ↦ T n / a) atTop atTop ∧
      Tendsto
        (fun n ↦
          cesaroMeanAt (fun t ↦ f (a * t)) (T n / a))
        atTop (nhds L) := by
  refine ⟨hT.atTop_div_const ha, ?_⟩
  simpa only [cesaroMeanAt_comp_mul_div f ha.ne'] using hmean

/-- Forward and reversed Cesàro data for one function. -/
structure TwoSidedCesaroLimit
    (f : ℝ → ℂ) (L : ℂ) where
  forwardHorizon : ℕ → ℝ
  reverseHorizon : ℕ → ℝ
  forwardHorizon_tendsto :
    Tendsto forwardHorizon atTop atTop
  reverseHorizon_tendsto :
    Tendsto reverseHorizon atTop atTop
  forward_tendsto :
    Tendsto
      (fun n ↦ cesaroMeanAt f (forwardHorizon n))
      atTop (nhds L)
  reverse_tendsto :
    Tendsto
      (fun n ↦
        cesaroMeanAt (fun t ↦ f (-t)) (reverseHorizon n))
      atTop (nhds L)

/-- Every nonzero signed constant time change has a forward Cesàro
sequence, provided the original function has both forward and reversed
Cesàro limits.  The returned horizons are explicit in the proof:
`T₊/a` for `a>0`, and `T₋/(-a)` for `a<0`. -/
theorem TwoSidedCesaroLimit.exists_rescaled_forward
    {f : ℝ → ℂ} {L : ℂ}
    (h : TwoSidedCesaroLimit f L)
    {a : ℝ} (ha : a ≠ 0) :
    ∃ S : ℕ → ℝ,
      Tendsto S atTop atTop ∧
      Tendsto
        (fun n ↦ cesaroMeanAt (fun t ↦ f (a * t)) (S n))
        atTop (nhds L) := by
  rcases lt_or_gt_of_ne ha with haNeg | haPos
  · let b : ℝ := -a
    have hb : 0 < b := neg_pos.mpr haNeg
    refine ⟨fun n ↦ h.reverseHorizon n / b,
      h.reverseHorizon_tendsto.atTop_div_const hb, ?_⟩
    have htransport :=
      (tendsto_cesaroMeanAt_comp_mul_of_pos
        (fun t ↦ f (-t)) hb h.reverseHorizon_tendsto
        h.reverse_tendsto).2
    simpa only [b, neg_mul, neg_neg] using htransport
  · exact
      ⟨fun n ↦ h.forwardHorizon n / a,
        (tendsto_cesaroMeanAt_comp_mul_of_pos
          f haPos h.forwardHorizon_tendsto
          h.forward_tendsto).1,
        (tendsto_cesaroMeanAt_comp_mul_of_pos
          f haPos h.forwardHorizon_tendsto
          h.forward_tendsto).2⟩

/-- Cesàro averaging a constant along a nonzero horizon returns that
constant. -/
theorem cesaroMeanAt_const_of_ne
    (c : ℂ) {T : ℝ} (hT : T ≠ 0) :
    cesaroMeanAt (fun _ : ℝ ↦ c) T = c := by
  rw [cesaroMeanAt, intervalIntegral.integral_const]
  simp only [sub_zero, Complex.real_smul]
  rw [← mul_assoc,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hT),
    one_mul]

/-- A centered Cesàro limit yields the corresponding raw mean. -/
theorem tendsto_cesaroMeanAt_of_sub_const_tendsto_zero
    {f : ℝ → ℂ} (hf : Continuous f)
    (c : ℂ) {T : ℕ → ℝ}
    (hT : Tendsto T atTop atTop)
    (hcentered :
      Tendsto
        (fun n ↦
          cesaroMeanAt (fun t ↦ f t - c) (T n))
        atTop (nhds 0)) :
    Tendsto
      (fun n ↦ cesaroMeanAt f (T n))
      atTop (nhds c) := by
  have hsum :
      Tendsto
        (fun n ↦
          cesaroMeanAt (fun t ↦ f t - c) (T n) + c)
        atTop (nhds c) := by
    simpa only [zero_add] using hcentered.add_const c
  apply hsum.congr'
  have hTne : ∀ᶠ n in atTop, T n ≠ 0 :=
    (hT.eventually (eventually_gt_atTop 0)).mono
      fun _ hn ↦ hn.ne'
  filter_upwards [hTne] with n hn
  unfold cesaroMeanAt
  rw [intervalIntegral.integral_sub
    (hf.intervalIntegrable 0 (T n))
    (continuous_const.intervalIntegrable 0 (T n))]
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, Complex.real_smul]
  have hcancel :
      ((T n : ℂ)⁻¹) * (T n : ℂ) = 1 :=
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hn)
  calc
    ((T n : ℂ)⁻¹) *
          ((∫ t in (0 : ℝ)..T n, f t) -
            (T n : ℂ) * c) + c =
      ((T n : ℂ)⁻¹) *
          (∫ t in (0 : ℝ)..T n, f t) -
        ((T n : ℂ)⁻¹) * ((T n : ℂ) * c) + c := by ring
    _ =
      ((T n : ℂ)⁻¹) *
          (∫ t in (0 : ℝ)..T n, f t) -
        c + c := by rw [← mul_assoc, hcancel, one_mul]
    _ = ((T n : ℂ)⁻¹) *
          (∫ t in (0 : ℝ)..T n, f t) := by ring

end

end HGAS.Analysis
