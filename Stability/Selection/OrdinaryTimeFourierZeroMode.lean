import Stability.Selection.OrdinaryTimeRadicalPrimitive
import Stability.Selection.OrdinaryTimeBoundedPrimitive

/-!
# Identifying the constant Fourier mode from one orbit mean

A bounded primitive of the centered function shows that its full forward
mean equals the actual constant Haar coefficient. If the same trace has
zero mean, uniqueness of limits forces that coefficient to vanish.
-/

namespace Stability.Selection

noncomputable section

open HGAS.Analysis HGAS.Clocks Filter Topology

theorem forwardMean_of_bounded_centered_primitive {f F : ℝ → ℝ}
    (hf : Continuous f) (c : ℝ) (hF : ∀ t, HasDerivAt F (f t - c) t)
    (C : ℝ) (hbound : ∀ t, |F t| ≤ C) :
    Tendsto (fun H : ℝ ↦ H⁻¹ * ∫ t in (0 : ℝ)..H, f t) atTop (𝓝 c) := by
  have hzero := forwardMean_zero_of_bounded_primitive (hf.sub continuous_const) hF C hbound
  have hsum : Tendsto (fun H : ℝ ↦
      H⁻¹ * ∫ t in (0 : ℝ)..H, (f t - c)) atTop (𝓝 0) := hzero
  have h := hsum.add_const c
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
  rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _)
    (continuous_const.intervalIntegrable _ _), intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  have hc : H⁻¹ * H = 1 := inv_mul_cancel₀ hH.ne'
  linear_combination -c * hc

/-- Exponential summability supplies the bounded primitive; the mean
assumption refers to every real horizon, not a subsequence. -/
theorem fourierZeroMode_re_eq_zero_of_forwardMean {d : Type*} [Fintype d]
    (p : d → ℕ) (hp : ∀ i, (p i).Prime) (hinjective : Function.Injective p)
    (sign : d → ℤ) (hsign : ∀ i, sign i = 1 ∨ sign i = -1)
    (m : ℕ) (hm : 0 < m) (f : UnitAddTorus d → ℝ) (hf : Continuous f)
    (hweighted : Summable fun a ↦
      ‖UnitAddTorus.mFourierCoeff (fun y ↦ (f y : ℂ)) a‖ *
        (1 + 1 / (m : ℝ)) ^ (∑ i, |(a i : ℝ)|))
    (x : UnitAddTorus d)
    (hmean : Tendsto (fun H : ℝ ↦ H⁻¹ * ∫ t in (0 : ℝ)..H,
      f (RadicalClock.torusTranslationFlow
        (ScaledRadicalClock.scaledSignedPrimeSqrtFrequency (1 / (2 * Real.pi)) p sign) t x))
      atTop (𝓝 0)) :
    (UnitAddTorus.mFourierCoeff (fun y ↦ (f y : ℂ)) 0).re = 0 := by
  let ω := ScaledRadicalClock.scaledSignedPrimeSqrtFrequency (1 / (2 * Real.pi)) p sign
  let trace := fun t : ℝ ↦ f (RadicalClock.torusTranslationFlow ω t x)
  let F := fun t : ℝ ↦ (radicalFourierPrimitive p sign (fun y ↦ (f y : ℂ))
    (RadicalClock.torusTranslationFlow ω t x)).re
  let c := (UnitAddTorus.mFourierCoeff (fun y ↦ (f y : ℂ)) 0).re
  have htrace : Continuous trace := by
    apply hf.comp
    exact (RadicalClock.torusTranslationFlow ω).continuous continuous_id continuous_const
  have hF (t : ℝ) : HasDerivAt F (trace t - c) t := by
    have hd := radicalFourierPrimitive_hasDerivAt p hp hinjective sign hsign m hm
      (fun y ↦ (f y : ℂ)) (Complex.continuous_ofReal.comp hf) hweighted x t
    simpa only [F, trace, c, ω, Complex.sub_re, Complex.ofReal_re] using
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hd
  have hbound := (radicalFourierPrimitive_continuous_bound p hp hinjective sign hsign m hm
    (fun y ↦ (f y : ℂ)) hweighted).2
  have hlimit := forwardMean_of_bounded_centered_primitive htrace c hF _
    (fun t ↦ (Complex.abs_re_le_norm _).trans (hbound (RadicalClock.torusTranslationFlow ω t x)))
  exact tendsto_nhds_unique hlimit hmean

end

end Stability.Selection
