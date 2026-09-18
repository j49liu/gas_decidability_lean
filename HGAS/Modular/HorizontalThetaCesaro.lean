import HGAS.Modular.HorizontalThetaSquareSeries
import Mathlib.Tactic

/-!
# Cesàro means of horizontal theta characteristics

This file evaluates the untwisted means needed by the closed-cusp
selector.  Along every nonzero-speed horizontal line:

* `θ₂` has mean zero;
* `θ₂²` has mean zero;
* `θ₃` and `θ₄` have mean one; and
* `θ₃²` and `θ₄²` have mean one.

All limits hold along an arbitrary sequence of real horizons tending to
`+∞`.  Thus they can be used after the physical-time change appearing in
the compact detector.
-/

namespace HGAS.Modular

open Filter Topology

noncomputable section

theorem integerSquarePairFrequency_eq_zero_iff
    {Ω s : ℝ} (hΩ : Ω ≠ 0) (hs : s ≠ 0)
    (nm : ℤ × ℤ) :
    integerSquarePairFrequency Ω s 0 nm = 0 ↔
      nm = (0, 0) := by
  rw [integerSquarePairFrequency, mul_eq_zero,
    or_iff_right hΩ]
  simp only [sub_zero, mul_eq_zero, hs, false_or]
  constructor
  · intro hsum
    have hfirst : (nm.1 : ℝ) ^ 2 = 0 := by
      nlinarith [sq_nonneg (nm.1 : ℝ), sq_nonneg (nm.2 : ℝ)]
    have hsecond : (nm.2 : ℝ) ^ 2 = 0 := by
      nlinarith [sq_nonneg (nm.1 : ℝ), sq_nonneg (nm.2 : ℝ)]
    have hn : nm.1 = 0 := by
      exact_mod_cast (sq_eq_zero_iff.mp hfirst)
    have hm : nm.2 = 0 := by
      exact_mod_cast (sq_eq_zero_iff.mp hsecond)
    exact Prod.ext hn hm
  · rintro rfl
    norm_num

theorem halfSquarePairFrequency_ne_zero
    {Ω s : ℝ} (hΩ : Ω ≠ 0) (hs : s ≠ 0)
    (nm : ℤ × ℤ) :
    halfSquarePairFrequency Ω s 0 nm ≠ 0 := by
  unfold halfSquarePairFrequency
  apply mul_ne_zero hΩ
  simp only [sub_zero]
  apply mul_ne_zero hs
  have hfirst :
      0 < ((nm.1 : ℝ) + 1 / 2) ^ 2 :=
    sq_pos_of_ne_zero (intCast_add_half_ne_zero nm.1)
  have hsecond :
      0 < ((nm.2 : ℝ) + 1 / 2) ^ 2 :=
    sq_pos_of_ne_zero (intCast_add_half_ne_zero nm.2)
  exact ne_of_gt (add_pos hfirst hsecond)

theorem cesaroMeanAt_const_mul
    (c : ℂ) (f : ℝ → ℂ) (T : ℝ) :
    HGAS.Analysis.cesaroMeanAt (fun t ↦ c * f t) T =
      c * HGAS.Analysis.cesaroMeanAt f T := by
  unfold HGAS.Analysis.cesaroMeanAt
  rw [intervalIntegral.integral_const_mul]
  ring

theorem cesaroMeanAt_theta₂_horizontalLine_tendsto_zero
    (x y s : ℝ) (hy : 0 < y) (hs : s ≠ 0)
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) :
    Tendsto
      (fun n ↦ HGAS.Analysis.cesaroMeanAt
        (fun t ↦ theta₂ (horizontalLine x y s hy t)) (T n))
      atTop (𝓝 0) := by
  have hseries :
      (fun t ↦ theta₂ (horizontalLine x y s hy t)) =
        HGAS.Analysis.exponentialSeries
          (theta2HorizontalCoefficient x y hy)
          (halfSquareMomentFrequency Real.pi s 0) := by
    funext t
    exact theta₂_horizontalLine_eq_halfSquareMomentSeries x y s hy t
  rw [hseries]
  convert
    HGAS.Analysis.cesaroMeanAt_exponentialSeries_tendsto
      (theta2HorizontalCoefficient x y hy)
      (halfSquareMomentFrequency Real.pi s 0)
      (summable_norm_theta2HorizontalCoefficient x y hy) hT using 1
  apply congrArg 𝓝
  have hzero :
      (fun n : ℤ ↦
        if halfSquareMomentFrequency Real.pi s 0 n = 0 then
          theta2HorizontalCoefficient x y hy n
        else 0) = 0 := by
    funext n
    simp [halfSquareMeanFrequency_ne_zero Real.pi_ne_zero hs n]
  rw [hzero]
  exact (tsum_zero (α := ℂ) (β := ℤ)).symm

theorem cesaroMeanAt_theta₂_sq_horizontalLine_tendsto_zero
    (x y s : ℝ) (hy : 0 < y) (hs : s ≠ 0)
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) :
    Tendsto
      (fun n ↦ HGAS.Analysis.cesaroMeanAt
        (fun t ↦ theta₂ (horizontalLine x y s hy t) ^ 2)
        (T n))
      atTop (𝓝 0) := by
  have hseries :
      (fun t ↦ theta₂ (horizontalLine x y s hy t) ^ 2) =
        HGAS.Analysis.exponentialSeries
          (pairCoefficient (theta2HorizontalCoefficient x y hy))
          (halfSquarePairFrequency Real.pi s 0) := by
    funext t
    exact theta₂_sq_horizontalLine_eq_exponentialSeries x y s hy t
  rw [hseries]
  convert
    HGAS.Analysis.cesaroMeanAt_exponentialSeries_tendsto
      (pairCoefficient (theta2HorizontalCoefficient x y hy))
      (halfSquarePairFrequency Real.pi s 0)
      (summable_norm_pairCoefficient
        (theta2HorizontalCoefficient x y hy)
        (summable_norm_theta2HorizontalCoefficient x y hy))
      hT using 1
  apply congrArg 𝓝
  have hzero :
      (fun nm : ℤ × ℤ ↦
        if halfSquarePairFrequency Real.pi s 0 nm = 0 then
          pairCoefficient
            (theta2HorizontalCoefficient x y hy) nm
        else 0) = 0 := by
    funext nm
    simp [halfSquarePairFrequency_ne_zero Real.pi_ne_zero hs nm]
  rw [hzero]
  exact (tsum_zero (α := ℂ) (β := ℤ × ℤ)).symm

theorem cesaroMeanAt_theta₃_horizontalLine_tendsto_one
    (x y s : ℝ) (hy : 0 < y) (hs : s ≠ 0)
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) :
    Tendsto
      (fun n ↦ HGAS.Analysis.cesaroMeanAt
        (fun t ↦ theta₃ (horizontalLine x y s hy t)) (T n))
      atTop (𝓝 1) := by
  have hseries :
      (fun t ↦ theta₃ (horizontalLine x y s hy t)) =
        HGAS.Analysis.exponentialSeries
          (theta3HorizontalCoefficient x y hy)
          (integerSquareMomentFrequency Real.pi s 0) := by
    funext t
    exact theta₃_horizontalLine_eq_integerSquareMomentSeries x y s hy t
  rw [hseries]
  convert
    HGAS.Analysis.cesaroMeanAt_exponentialSeries_tendsto
      (theta3HorizontalCoefficient x y hy)
      (integerSquareMomentFrequency Real.pi s 0)
      (summable_norm_theta3HorizontalCoefficient x y hy) hT using 1
  apply congrArg 𝓝
  simp_rw [
    integerSquareMeanFrequency_eq_zero_iff Real.pi_ne_zero hs]
  rw [tsum_ite_eq]
  simp [theta3HorizontalCoefficient, theta₃Term]

theorem cesaroMeanAt_theta₄_horizontalLine_tendsto_one
    (x y s : ℝ) (hy : 0 < y) (hs : s ≠ 0)
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) :
    Tendsto
      (fun n ↦ HGAS.Analysis.cesaroMeanAt
        (fun t ↦ theta₄ (horizontalLine x y s hy t)) (T n))
      atTop (𝓝 1) := by
  have hseries :
      (fun t ↦ theta₄ (horizontalLine x y s hy t)) =
        HGAS.Analysis.exponentialSeries
          (theta4HorizontalCoefficient x y hy)
          (integerSquareMomentFrequency Real.pi s 0) := by
    funext t
    exact theta₄_horizontalLine_eq_integerSquareMomentSeries x y s hy t
  rw [hseries]
  convert
    HGAS.Analysis.cesaroMeanAt_exponentialSeries_tendsto
      (theta4HorizontalCoefficient x y hy)
      (integerSquareMomentFrequency Real.pi s 0)
      (summable_norm_theta4HorizontalCoefficient x y hy) hT using 1
  apply congrArg 𝓝
  simp_rw [
    integerSquareMeanFrequency_eq_zero_iff Real.pi_ne_zero hs]
  rw [tsum_ite_eq]
  simp [theta4HorizontalCoefficient, theta₄Term]

theorem cesaroMeanAt_theta₃_sq_horizontalLine_tendsto_one
    (x y s : ℝ) (hy : 0 < y) (hs : s ≠ 0)
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) :
    Tendsto
      (fun n ↦ HGAS.Analysis.cesaroMeanAt
        (fun t ↦ theta₃ (horizontalLine x y s hy t) ^ 2)
        (T n))
      atTop (𝓝 1) := by
  have hseries :
      (fun t ↦ theta₃ (horizontalLine x y s hy t) ^ 2) =
        HGAS.Analysis.exponentialSeries
          (pairCoefficient (theta3HorizontalCoefficient x y hy))
          (integerSquarePairFrequency Real.pi s 0) := by
    funext t
    exact theta₃_sq_horizontalLine_eq_exponentialSeries x y s hy t
  rw [hseries]
  convert
    HGAS.Analysis.cesaroMeanAt_exponentialSeries_tendsto
      (pairCoefficient (theta3HorizontalCoefficient x y hy))
      (integerSquarePairFrequency Real.pi s 0)
      (summable_norm_pairCoefficient
        (theta3HorizontalCoefficient x y hy)
        (summable_norm_theta3HorizontalCoefficient x y hy))
      hT using 1
  apply congrArg 𝓝
  simp_rw [
    integerSquarePairFrequency_eq_zero_iff Real.pi_ne_zero hs]
  rw [tsum_ite_eq]
  simp [pairCoefficient, theta3HorizontalCoefficient, theta₃Term]

theorem cesaroMeanAt_theta₄_sq_horizontalLine_tendsto_one
    (x y s : ℝ) (hy : 0 < y) (hs : s ≠ 0)
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) :
    Tendsto
      (fun n ↦ HGAS.Analysis.cesaroMeanAt
        (fun t ↦ theta₄ (horizontalLine x y s hy t) ^ 2)
        (T n))
      atTop (𝓝 1) := by
  have hseries :
      (fun t ↦ theta₄ (horizontalLine x y s hy t) ^ 2) =
        HGAS.Analysis.exponentialSeries
          (pairCoefficient (theta4HorizontalCoefficient x y hy))
          (integerSquarePairFrequency Real.pi s 0) := by
    funext t
    exact theta₄_sq_horizontalLine_eq_exponentialSeries x y s hy t
  rw [hseries]
  convert
    HGAS.Analysis.cesaroMeanAt_exponentialSeries_tendsto
      (pairCoefficient (theta4HorizontalCoefficient x y hy))
      (integerSquarePairFrequency Real.pi s 0)
      (summable_norm_pairCoefficient
        (theta4HorizontalCoefficient x y hy)
        (summable_norm_theta4HorizontalCoefficient x y hy))
      hT using 1
  apply congrArg 𝓝
  simp_rw [
    integerSquarePairFrequency_eq_zero_iff Real.pi_ne_zero hs]
  rw [tsum_ite_eq]
  simp [pairCoefficient, theta4HorizontalCoefficient, theta₄Term]

end

end HGAS.Modular
