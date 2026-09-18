import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Sets.Compacts
import Mathlib.Tactic

/-!
# Cesàro extraction for absolutely summable exponential series

This file isolates the analytic argument used by the finite-moment part of
the Jacobi selector.  Let

```
                    f(t) = ∑ i, c i · exp(i ωᵢ t),
```

where the coefficient norms are summable.  Averaging over the integer
horizons `[0,N+1]` kills every nonzero temporal frequency and retains
exactly the terms with frequency zero.

There are two points worth making explicit.

* No ergodic theorem is needed for this calculation.  It is ordinary
  Cesàro averaging of an absolutely and uniformly convergent series.
* The theorem is not tied to theta functions.  Any countable exponential
  series with summable coefficient norms can reuse it.

The natural-number horizon avoids an irrelevant singularity at `T = 0`.
-/

noncomputable section

open Filter MeasureTheory Topology
open scoped Interval

namespace HGAS.Analysis

variable {ι : Type*} [Countable ι]

/-- The unit-modulus exponential with real temporal frequency `ω`. -/
def realFrequencyExponential (ω t : ℝ) : ℂ :=
  Complex.exp (((ω : ℂ) * Complex.I) * (t : ℂ))

theorem norm_realFrequencyExponential (ω t : ℝ) :
    ‖realFrequencyExponential ω t‖ = 1 := by
  simp [realFrequencyExponential, Complex.norm_exp]

/-- One term of an exponential series. -/
def exponentialSeriesTerm
    (coefficient : ι → ℂ) (frequency : ι → ℝ)
    (i : ι) (t : ℝ) : ℂ :=
  coefficient i * realFrequencyExponential (frequency i) t

omit [Countable ι] in
theorem norm_exponentialSeriesTerm
    (coefficient : ι → ℂ) (frequency : ι → ℝ)
    (i : ι) (t : ℝ) :
    ‖exponentialSeriesTerm coefficient frequency i t‖ =
      ‖coefficient i‖ := by
  simp [exponentialSeriesTerm, norm_realFrequencyExponential]

/-- The pointwise sum of an absolutely summable exponential series. -/
def exponentialSeries
    (coefficient : ι → ℂ) (frequency : ι → ℝ)
    (t : ℝ) : ℂ :=
  ∑' i, exponentialSeriesTerm coefficient frequency i t

/-- The positive real horizon used for the `N`-th Cesàro average. -/
def naturalHorizon (N : ℕ) : ℝ := (N : ℝ) + 1

theorem naturalHorizon_pos (N : ℕ) :
    0 < naturalHorizon N := by
  exact add_pos_of_nonneg_of_pos
    (Nat.cast_nonneg N) zero_lt_one

/-- Cesàro averaging over the nonzero integer horizon `N+1`. -/
def naturalCesaroMean (f : ℝ → ℂ) (N : ℕ) : ℂ :=
  ((naturalHorizon N : ℂ)⁻¹) *
    ∫ t in (0 : ℝ)..naturalHorizon N, f t

/-- The normalized average of one unit exponential. -/
def naturalCesaroKernel (ω : ℝ) (N : ℕ) : ℂ :=
  naturalCesaroMean (realFrequencyExponential ω) N

@[simp]
theorem naturalCesaroKernel_zero (N : ℕ) :
    naturalCesaroKernel 0 N = 1 := by
  simp [naturalCesaroKernel, naturalCesaroMean,
    realFrequencyExponential, naturalHorizon]
  field_simp

/-- A normalized exponential average has norm at most one. -/
theorem norm_naturalCesaroKernel_le_one (ω : ℝ) (N : ℕ) :
    ‖naturalCesaroKernel ω N‖ ≤ 1 := by
  let T : ℝ := naturalHorizon N
  have hT : 0 < T := by
    exact naturalHorizon_pos N
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
  rw [naturalCesaroKernel, naturalCesaroMean]
  change
    ‖((T : ℂ)⁻¹) *
      ∫ t in (0 : ℝ)..T,
        realFrequencyExponential ω t‖ ≤ 1
  rw [norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs]
  have hTabs : |T| = T := abs_of_pos hT
  rw [hTabs]
  calc
    T⁻¹ * ‖∫ t in (0 : ℝ)..T,
        realFrequencyExponential ω t‖ ≤
        T⁻¹ * T :=
      mul_le_mul_of_nonneg_left hintegral (inv_nonneg.mpr hT.le)
    _ = 1 := inv_mul_cancel₀ hT.ne'

/-- At a nonzero frequency the normalized exponential average tends to
zero. -/
theorem naturalCesaroKernel_tendsto_zero
    {ω : ℝ} (hω : ω ≠ 0) :
    Tendsto (naturalCesaroKernel ω) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hcoefficient : ((ω : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hω)
      Complex.I_ne_zero
  have hformula (N : ℕ) :
      naturalCesaroKernel ω N =
        ((naturalHorizon N : ℂ)⁻¹) *
          ((Complex.exp
              (((ω : ℂ) * Complex.I) *
                (naturalHorizon N : ℂ)) - 1) /
            ((ω : ℂ) * Complex.I)) := by
    rw [naturalCesaroKernel, naturalCesaroMean]
    congr 1
    simpa only [realFrequencyExponential,
      Complex.ofReal_zero, mul_zero, Complex.exp_zero] using
      (integral_exp_mul_complex
        (a := (0 : ℝ)) (b := naturalHorizon N)
        hcoefficient)
  have hbound (N : ℕ) :
      ‖naturalCesaroKernel ω N‖ ≤
        (2 / |ω|) * (naturalHorizon N)⁻¹ := by
    rw [hformula, norm_mul, norm_inv, norm_div,
      norm_mul, Complex.norm_I, mul_one]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (naturalHorizon_pos N)]
    have hexp :
        ‖Complex.exp
              (((ω : ℂ) * Complex.I) *
                (naturalHorizon N : ℂ)) - 1‖ ≤ 2 := by
      calc
        ‖Complex.exp
              (((ω : ℂ) * Complex.I) *
                (naturalHorizon N : ℂ)) - 1‖ ≤
            ‖Complex.exp
              (((ω : ℂ) * Complex.I) *
                (naturalHorizon N : ℂ))‖ + ‖(1 : ℂ)‖ :=
          norm_sub_le _ _
        _ = 2 := by
          rw [Complex.norm_exp]
          norm_num
    have hωabs : 0 < |ω| := abs_pos.mpr hω
    have hN : 0 < naturalHorizon N :=
      naturalHorizon_pos N
    change
      (naturalHorizon N)⁻¹ *
          (‖Complex.exp
                (((ω : ℂ) * Complex.I) *
                  (naturalHorizon N : ℂ)) - 1‖ /
            |ω|) ≤
        (2 / |ω|) * (naturalHorizon N)⁻¹
    calc
      (naturalHorizon N)⁻¹ *
          (‖Complex.exp
                (((ω : ℂ) * Complex.I) *
                  (naturalHorizon N : ℂ)) - 1‖ /
            |ω|) ≤
          (naturalHorizon N)⁻¹ * (2 / |ω|) := by
        exact mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hexp hωabs.le)
          (inv_nonneg.mpr hN.le)
      _ = (2 / |ω|) *
          (naturalHorizon N)⁻¹ := by ring
  have htop :
      Tendsto naturalHorizon
        atTop atTop :=
    tendsto_atTop_add_const_right _ _
      tendsto_natCast_atTop_atTop
  have hinv :
      Tendsto (fun N : ℕ ↦ (naturalHorizon N)⁻¹)
        atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp htop
  have hupper :
      Tendsto
        (fun N : ℕ ↦
          (2 / |ω|) * (naturalHorizon N)⁻¹)
        atTop (𝓝 0) := by
    simpa [naturalHorizon] using
      hinv.const_mul (2 / |ω|)
  exact squeeze_zero
    (fun N ↦ norm_nonneg _)
    hbound hupper

/-- The one-frequency kernel converges to the indicator of zero
frequency. -/
theorem naturalCesaroKernel_tendsto (ω : ℝ) :
    Tendsto (naturalCesaroKernel ω) atTop
      (𝓝 (if ω = 0 then 1 else 0)) := by
  by_cases hω : ω = 0
  · subst ω
    have heq :
        naturalCesaroKernel 0 = fun _ : ℕ ↦ (1 : ℂ) := by
      funext N
      exact naturalCesaroKernel_zero N
    rw [heq]
    rw [if_pos rfl]
    exact tendsto_const_nhds
  · simpa [hω] using naturalCesaroKernel_tendsto_zero hω

omit [Countable ι] in
/-- Multiplying a unit exponential by a constant commutes with its
Cesàro average. -/
theorem naturalCesaroMean_exponentialSeriesTerm
    (coefficient : ι → ℂ) (frequency : ι → ℝ)
    (i : ι) (N : ℕ) :
    naturalCesaroMean
        (exponentialSeriesTerm coefficient frequency i) N =
      coefficient i * naturalCesaroKernel (frequency i) N := by
  simp only [naturalCesaroMean, exponentialSeriesTerm,
    naturalCesaroKernel, intervalIntegral.integral_const_mul]
  ring

/-- For a summable coefficient family, interval integration commutes with
the exponential series. -/
theorem intervalIntegral_exponentialSeries
    (coefficient : ι → ℂ) (frequency : ι → ℝ)
    (hsum : Summable fun i ↦ ‖coefficient i‖)
    (a b : ℝ) :
    (∫ t in a..b, exponentialSeries coefficient frequency t) =
      ∑' i, ∫ t in a..b,
        exponentialSeriesTerm coefficient frequency i t := by
  let f : ι → C(ℝ, ℂ) := fun i ↦
    ⟨exponentialSeriesTerm coefficient frequency i, by
      apply Continuous.mul continuous_const
      exact Complex.continuous_exp.comp <| by
        fun_prop⟩
  have hf_bound (i : ι) :
      ‖(f i).restrict
          (⟨Set.uIcc a b, isCompact_uIcc⟩ :
            TopologicalSpace.Compacts ℝ)‖ ≤
        ‖coefficient i‖ := by
    rw [ContinuousMap.norm_le _ (norm_nonneg _)]
    intro t
    simp [f, norm_exponentialSeriesTerm]
  have hf_sum :
      Summable fun i : ι ↦
        ‖(f i).restrict
          (⟨Set.uIcc a b, isCompact_uIcc⟩ :
            TopologicalSpace.Compacts ℝ)‖ :=
    hsum.of_nonneg_of_le
      (fun i ↦ norm_nonneg _)
      hf_bound
  have h :=
    intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm
      (a := a) (b := b) hf_sum
  simpa only [f, exponentialSeries] using h.symm

/-- The Cesàro mean of the full series is the sum of the one-frequency
Cesàro means. -/
theorem naturalCesaroMean_exponentialSeries_eq_tsum
    (coefficient : ι → ℂ) (frequency : ι → ℝ)
    (hsum : Summable fun i ↦ ‖coefficient i‖)
    (N : ℕ) :
    naturalCesaroMean
        (exponentialSeries coefficient frequency) N =
      ∑' i,
        coefficient i * naturalCesaroKernel (frequency i) N := by
  rw [naturalCesaroMean,
    intervalIntegral_exponentialSeries
      coefficient frequency hsum]
  have hintegralSummable :
      Summable fun i ↦
        ∫ t in (0 : ℝ)..naturalHorizon N,
          exponentialSeriesTerm coefficient frequency i t := by
    have hbound (i : ι) :
        ‖∫ t in (0 : ℝ)..naturalHorizon N,
            exponentialSeriesTerm coefficient frequency i t‖ ≤
          naturalHorizon N * ‖coefficient i‖ := by
      have h :=
        intervalIntegral.norm_integral_le_of_norm_le_const
          (a := (0 : ℝ)) (b := naturalHorizon N)
          (C := ‖coefficient i‖)
          (f := exponentialSeriesTerm coefficient frequency i)
          (fun t _ ↦ le_of_eq
            (norm_exponentialSeriesTerm
              coefficient frequency i t))
      simpa [abs_of_pos (naturalHorizon_pos N), mul_comm] using h
    exact
      (Summable.mul_left (naturalHorizon N)
        hsum).of_norm_bounded
        hbound
  rw [← hintegralSummable.tsum_mul_left]
  apply tsum_congr
  intro i
  rw [← naturalCesaroMean_exponentialSeriesTerm
    coefficient frequency i N]
  rfl

/-- **Cesàro constant-term extraction.**  An absolutely summable
exponential series has Cesàro mean equal in the limit to the sum of its
zero-frequency coefficients. -/
theorem naturalCesaroMean_exponentialSeries_tendsto
    (coefficient : ι → ℂ) (frequency : ι → ℝ)
    (hsum : Summable fun i ↦ ‖coefficient i‖) :
    Tendsto
      (fun N ↦ naturalCesaroMean
        (exponentialSeries coefficient frequency) N)
      atTop
      (𝓝 (∑' i, if frequency i = 0 then coefficient i else 0)) := by
  rw [show
    (fun N ↦ naturalCesaroMean
      (exponentialSeries coefficient frequency) N) =
      (fun N ↦ ∑' i,
        coefficient i * naturalCesaroKernel (frequency i) N) by
      funext N
      exact naturalCesaroMean_exponentialSeries_eq_tsum
        coefficient frequency hsum N]
  apply tendsto_tsum_of_dominated_convergence hsum
  · intro i
    convert
      (naturalCesaroKernel_tendsto (frequency i)).const_mul
        (coefficient i) using 1
    split_ifs <;> simp_all
  · filter_upwards with N
    intro i
    rw [norm_mul]
    exact mul_le_of_le_one_right
      (norm_nonneg (coefficient i))
      (norm_naturalCesaroKernel_le_one (frequency i) N)

end HGAS.Analysis
