import HGAS.Analysis.CesaroExponentialSeriesArbitraryHorizon
import HGAS.Modular.JacobiMomentResonance
import Mathlib.Tactic

/-!
# Jacobi resonance extraction along arbitrary physical horizons

The fixed-detector compactification samples ordinary physical time at the
clock values of integer compact-time horizons.  Those horizons need not be
integers.  The arbitrary-horizon exponential-series theorem nevertheless
retains exactly the same direct and reflected quadratic resonances.
-/

noncomputable section

open Filter Topology

namespace HGAS.Modular

/-- Arbitrary-horizon extraction for one quadratic Jacobi moment row. -/
theorem cesaroMeanAt_quadraticMomentSeries_tendsto
    (coefficient : ℤ → ℂ)
    (hsum : Summable fun n ↦ ‖coefficient n‖)
    {Ω : ℝ} (hΩ : Ω ≠ 0)
    (ρ a : ℝ) (r : ℤ)
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) :
    Tendsto
      (fun N ↦ HGAS.Analysis.cesaroMeanAt
        (quadraticMomentSeries coefficient Ω ρ a r) (T N))
      atTop
      (𝓝 (∑' n : ℤ,
        if (n : ℝ) + a = (r : ℝ) ∨
            (n : ℝ) + a = -ρ - (r : ℝ) then
          coefficient n
        else 0)) := by
  simpa only [quadraticMomentSeries,
    quadraticMomentFrequency_eq_zero_iff hΩ] using
    HGAS.Analysis.cesaroMeanAt_exponentialSeries_tendsto
      coefficient (quadraticMomentFrequency Ω ρ a r) hsum hT

/-- Mean-row arbitrary-horizon extraction. -/
theorem cesaroMeanAt_meanMomentSeries_tendsto
    (coefficient : ℤ → ℂ)
    (hsum : Summable fun n ↦ ‖coefficient n‖)
    {Ω : ℝ} (hΩ : Ω ≠ 0)
    (ρ a : ℝ)
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) :
    Tendsto
      (fun N ↦ HGAS.Analysis.cesaroMeanAt
        (quadraticMomentSeries coefficient Ω ρ a 0) (T N))
      atTop
      (𝓝 (∑' n : ℤ,
        if (n : ℝ) + a = 0 ∨
            (n : ℝ) + a = -ρ then
          coefficient n
        else 0)) := by
  simpa using
    cesaroMeanAt_quadraticMomentSeries_tendsto
      coefficient hsum hΩ ρ a 0 hT

/-- A mean-row limit one along arbitrary unbounded physical horizons
forces the ordinary or reflected Bloch class. -/
theorem blochClasses_of_cesaroMeanAt_meanMoment_tendsto_one
    (coefficient : ℤ → ℂ)
    (hsum : Summable fun n ↦ ‖coefficient n‖)
    {Ω : ℝ} (hΩ : Ω ≠ 0)
    (ρ a : ℝ)
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop)
    (hone :
      Tendsto
        (fun N ↦ HGAS.Analysis.cesaroMeanAt
          (quadraticMomentSeries coefficient Ω ρ a 0) (T N))
        atTop (𝓝 1)) :
    IsIntegralBlochClass a ∨
      IsReflectedBlochClass ρ a := by
  have hextract :=
    cesaroMeanAt_meanMomentSeries_tendsto
      coefficient hsum hΩ ρ a hT
  have hsum_eq :
      meanResonantCoefficientSum coefficient ρ a = 1 :=
    tendsto_nhds_unique hextract hone
  apply
    blochClasses_of_meanResonantCoefficientSum_ne_zero
      coefficient ρ a
  rw [hsum_eq]
  norm_num

/-- `(1,1)`-row arbitrary-horizon extraction. -/
theorem cesaroMeanAt_plusMomentSeries_tendsto
    (coefficient : ℤ → ℂ)
    (hsum : Summable fun n ↦ ‖coefficient n‖)
    {Ω : ℝ} (hΩ : Ω ≠ 0)
    (ρ a : ℝ)
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) :
    Tendsto
      (fun N ↦ HGAS.Analysis.cesaroMeanAt
        (quadraticMomentSeries coefficient Ω ρ a 1) (T N))
      atTop
      (𝓝 (∑' n : ℤ,
        if (n : ℝ) + a = 1 ∨
            (n : ℝ) + a = -1 - ρ then
          coefficient n
        else 0)) := by
  convert
    cesaroMeanAt_quadraticMomentSeries_tendsto
      coefficient hsum hΩ ρ a 1 hT using 1
  apply congrArg 𝓝
  apply tsum_congr
  intro n
  congr 1
  apply propext
  constructor <;> rintro (h | h)
  · left
    norm_num at h ⊢
    exact h
  · right
    norm_num at h ⊢
    linarith
  · left
    norm_num at h ⊢
    exact h
  · right
    norm_num at h ⊢
    linarith

/-- `(1,-1)`-row arbitrary-horizon extraction. -/
theorem cesaroMeanAt_minusMomentSeries_tendsto
    (coefficient : ℤ → ℂ)
    (hsum : Summable fun n ↦ ‖coefficient n‖)
    {Ω : ℝ} (hΩ : Ω ≠ 0)
    (ρ a : ℝ)
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) :
    Tendsto
      (fun N ↦ HGAS.Analysis.cesaroMeanAt
        (quadraticMomentSeries coefficient Ω ρ a (-1)) (T N))
      atTop
      (𝓝 (∑' n : ℤ,
        if (n : ℝ) + a = -1 ∨
            (n : ℝ) + a = 1 - ρ then
          coefficient n
        else 0)) := by
  convert
    cesaroMeanAt_quadraticMomentSeries_tendsto
      coefficient hsum hΩ ρ a (-1) hT using 1
  apply congrArg 𝓝
  apply tsum_congr
  intro n
  congr 1
  apply propext
  constructor <;> rintro (h | h)
  · left
    norm_num at h ⊢
    exact h
  · exact Or.inr (by norm_num at h ⊢; linarith)
  · left
    norm_num at h ⊢
    exact h
  · exact Or.inr (by norm_num at h ⊢; linarith)

end HGAS.Modular
