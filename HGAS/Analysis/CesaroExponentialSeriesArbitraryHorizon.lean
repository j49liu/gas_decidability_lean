import HGAS.Analysis.CesaroExponentialSeries
import Mathlib.Tactic

/-!
# Cesàro extraction along arbitrary unbounded horizons

The basic exponential-series theorem uses the convenient horizons `N+1`.
Time changes naturally produce different horizons.  This file proves that
the same constant-term extraction holds along every real sequence tending
to `+∞`.
-/

noncomputable section

open Filter MeasureTheory Topology
open scoped Interval

namespace HGAS.Analysis

variable {ι : Type*} [Countable ι]

/-- Normalized Cesàro mean at a real horizon. -/
def cesaroMeanAt (f : ℝ → ℂ) (T : ℝ) : ℂ :=
  ((T : ℂ)⁻¹) * ∫ t in (0 : ℝ)..T, f t

/-- Normalized one-frequency kernel at a real horizon. -/
def cesaroKernelAt (ω T : ℝ) : ℂ :=
  cesaroMeanAt (realFrequencyExponential ω) T

theorem cesaroKernelAt_zero
    {T : ℝ} (hT : T ≠ 0) :
    cesaroKernelAt 0 T = 1 := by
  simp only [cesaroKernelAt, cesaroMeanAt,
    realFrequencyExponential, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, intervalIntegral.integral_const, sub_zero,
    Complex.real_smul, mul_one]
  exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hT)

/-- At a positive horizon every unit-frequency average has norm at most
one. -/
theorem norm_cesaroKernelAt_le_one
    (ω : ℝ) {T : ℝ} (hT : 0 < T) :
    ‖cesaroKernelAt ω T‖ ≤ 1 := by
  have hintegral :
      ‖∫ t in (0 : ℝ)..T,
          realFrequencyExponential ω t‖ ≤ T := by
    have h :=
      intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0 : ℝ)) (b := T) (C := (1 : ℝ))
        (f := realFrequencyExponential ω)
        (fun t _ ↦ le_of_eq
          (norm_realFrequencyExponential ω t))
    simpa [abs_of_pos hT] using h
  rw [cesaroKernelAt, cesaroMeanAt]
  change
    ‖((T : ℂ)⁻¹) *
      ∫ t in (0 : ℝ)..T,
        realFrequencyExponential ω t‖ ≤ 1
  rw [norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hT]
  calc
    T⁻¹ * ‖∫ t in (0 : ℝ)..T,
        realFrequencyExponential ω t‖ ≤
        T⁻¹ * T :=
      mul_le_mul_of_nonneg_left hintegral
        (inv_nonneg.mpr hT.le)
    _ = 1 := inv_mul_cancel₀ hT.ne'

/-- A nonzero-frequency kernel tends to zero along every horizon tending
to `+∞`. -/
theorem cesaroKernelAt_tendsto_zero
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop)
    {ω : ℝ} (hω : ω ≠ 0) :
    Tendsto (fun n ↦ cesaroKernelAt ω (T n))
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hcoefficient : ((ω : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hω)
      Complex.I_ne_zero
  have hTpos : ∀ᶠ n in atTop, 0 < T n :=
    hT.eventually (eventually_gt_atTop 0)
  have hbound :
      ∀ᶠ n in atTop,
        ‖cesaroKernelAt ω (T n)‖ ≤
          (2 / |ω|) * (T n)⁻¹ := by
    filter_upwards [hTpos] with n hn
    have hformula :
        cesaroKernelAt ω (T n) =
          (((T n : ℝ) : ℂ)⁻¹) *
            ((Complex.exp
                (((ω : ℂ) * Complex.I) *
                  (((T n : ℝ) : ℂ))) - 1) /
              ((ω : ℂ) * Complex.I)) := by
      rw [cesaroKernelAt, cesaroMeanAt]
      congr 1
      simpa only [realFrequencyExponential,
        Complex.ofReal_zero, mul_zero, Complex.exp_zero] using
        (integral_exp_mul_complex
          (a := (0 : ℝ)) (b := T n)
          hcoefficient)
    rw [hformula, norm_mul, norm_inv, norm_div,
      norm_mul, Complex.norm_I, mul_one]
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hn]
    have hexp :
        ‖Complex.exp
              (((ω : ℂ) * Complex.I) *
                (((T n : ℝ) : ℂ))) - 1‖ ≤ 2 := by
      calc
        ‖Complex.exp
              (((ω : ℂ) * Complex.I) *
                (((T n : ℝ) : ℂ))) - 1‖ ≤
            ‖Complex.exp
              (((ω : ℂ) * Complex.I) *
                (((T n : ℝ) : ℂ)))‖ + ‖(1 : ℂ)‖ :=
          norm_sub_le _ _
        _ = 2 := by
          rw [Complex.norm_exp]
          norm_num
    have hωabs : 0 < |ω| := abs_pos.mpr hω
    change
      (T n)⁻¹ *
          (‖Complex.exp
                (((ω : ℂ) * Complex.I) *
                  (((T n : ℝ) : ℂ))) - 1‖ /
            |ω|) ≤
        (2 / |ω|) * (T n)⁻¹
    calc
      (T n)⁻¹ *
          (‖Complex.exp
                (((ω : ℂ) * Complex.I) *
                  (((T n : ℝ) : ℂ))) - 1‖ /
            |ω|) ≤
          (T n)⁻¹ * (2 / |ω|) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hexp hωabs.le)
          (inv_nonneg.mpr hn.le)
      _ = (2 / |ω|) * (T n)⁻¹ := by ring
  have hinv :
      Tendsto (fun n ↦ (T n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hT
  have hupper :
      Tendsto (fun n ↦ (2 / |ω|) * (T n)⁻¹)
        atTop (𝓝 0) := by
    simpa using hinv.const_mul (2 / |ω|)
  exact squeeze_zero'
    (Eventually.of_forall fun n ↦ norm_nonneg _)
    hbound hupper

/-- Arbitrary-horizon one-frequency limit. -/
theorem cesaroKernelAt_tendsto
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop)
    (ω : ℝ) :
    Tendsto (fun n ↦ cesaroKernelAt ω (T n))
      atTop (𝓝 (if ω = 0 then 1 else 0)) := by
  by_cases hω : ω = 0
  · subst ω
    have hTne : ∀ᶠ n in atTop, T n ≠ 0 :=
      (hT.eventually (eventually_gt_atTop 0)).mono
        fun _ hn ↦ hn.ne'
    apply tendsto_const_nhds.congr'
    filter_upwards [hTne] with n hn
    simpa using (cesaroKernelAt_zero hn).symm
  · simpa [hω] using cesaroKernelAt_tendsto_zero hT hω

omit [Countable ι] in
/-- One term factors into its coefficient and the arbitrary-horizon
kernel. -/
theorem cesaroMeanAt_exponentialSeriesTerm
    (coefficient : ι → ℂ) (frequency : ι → ℝ)
    (i : ι) (T : ℝ) :
    cesaroMeanAt
        (exponentialSeriesTerm coefficient frequency i) T =
      coefficient i * cesaroKernelAt (frequency i) T := by
  simp only [cesaroMeanAt, exponentialSeriesTerm,
    cesaroKernelAt, intervalIntegral.integral_const_mul]
  ring

/-- At a positive real horizon, averaging commutes with an absolutely
summable exponential series. -/
theorem cesaroMeanAt_exponentialSeries_eq_tsum
    (coefficient : ι → ℂ) (frequency : ι → ℝ)
    (hsum : Summable fun i ↦ ‖coefficient i‖)
    {T : ℝ} (hT : 0 < T) :
    cesaroMeanAt
        (exponentialSeries coefficient frequency) T =
      ∑' i, coefficient i * cesaroKernelAt (frequency i) T := by
  rw [cesaroMeanAt,
    intervalIntegral_exponentialSeries
      coefficient frequency hsum]
  have hintegralSummable :
      Summable fun i ↦
        ∫ t in (0 : ℝ)..T,
          exponentialSeriesTerm coefficient frequency i t := by
    have hbound (i : ι) :
        ‖∫ t in (0 : ℝ)..T,
            exponentialSeriesTerm coefficient frequency i t‖ ≤
          T * ‖coefficient i‖ := by
      have h :=
        intervalIntegral.norm_integral_le_of_norm_le_const
          (a := (0 : ℝ)) (b := T)
          (C := ‖coefficient i‖)
          (f := exponentialSeriesTerm coefficient frequency i)
          (fun t _ ↦ le_of_eq
            (norm_exponentialSeriesTerm
              coefficient frequency i t))
      simpa [abs_of_pos hT, mul_comm] using h
    exact
      (Summable.mul_left T hsum).of_norm_bounded hbound
  rw [← hintegralSummable.tsum_mul_left]
  apply tsum_congr
  intro i
  rw [← cesaroMeanAt_exponentialSeriesTerm
    coefficient frequency i T]
  rfl

/-- **Arbitrary-horizon constant-term extraction.** -/
theorem cesaroMeanAt_exponentialSeries_tendsto
    (coefficient : ι → ℂ) (frequency : ι → ℝ)
    (hsum : Summable fun i ↦ ‖coefficient i‖)
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) :
    Tendsto
      (fun n ↦ cesaroMeanAt
        (exponentialSeries coefficient frequency) (T n))
      atTop
      (𝓝 (∑' i,
        if frequency i = 0 then coefficient i else 0)) := by
  have hTpos : ∀ᶠ n in atTop, 0 < T n :=
    hT.eventually (eventually_gt_atTop 0)
  have heq :
      (fun n ↦ cesaroMeanAt
        (exponentialSeries coefficient frequency) (T n)) =ᶠ[atTop]
      fun n ↦ ∑' i,
        coefficient i * cesaroKernelAt (frequency i) (T n) := by
    filter_upwards [hTpos] with n hn
    exact cesaroMeanAt_exponentialSeries_eq_tsum
      coefficient frequency hsum hn
  apply Tendsto.congr' heq.symm
  apply tendsto_tsum_of_dominated_convergence hsum
  · intro i
    convert
      (cesaroKernelAt_tendsto hT (frequency i)).const_mul
        (coefficient i) using 1
    split_ifs <;> simp_all
  · filter_upwards [hTpos] with n hn
    intro i
    rw [norm_mul]
    exact mul_le_of_le_one_right
      (norm_nonneg (coefficient i))
      (norm_cesaroKernelAt_le_one (frequency i) hn)

end HGAS.Analysis
