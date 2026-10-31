import HGAS.Dynamics.CuspMeasureDivergence
import Mathlib.Analysis.SpecialFunctions.NonIntegrable

/-!
# The divergent first moment of cusp height

Step 2 of the revised manuscript's Proposition `prop:modselect` uses
bounded ordinary-time averages of `|m|^μ` for every real `μ ≥ 1`. The
published cusp lemmas cover natural powers at least two. This file proves
the missing critical first moment: multiplying the cusp density `dy/y²`
by height leaves the nonintegrable tail `dy/y`.

The result uses the existing `cuspHeightMeasure` and permits arbitrary
finite cusp cutoffs. Its marginal form applies directly to the already
constructed level-two Haar cusp marginal, without an invariant measure
on the source trajectory or a compactification clock.
-/

noncomputable section

namespace Stability.Selection

open Filter MeasureTheory Set HGAS.Dynamics
open scoped ENNReal NNReal

/-- The first height moment diverges even after discarding an arbitrary
finite initial portion of a cusp. -/
theorem lintegral_cuspTailHeightPower_one_eq_top (Y₀ Y : ℝ) :
    ∫⁻ y, cuspTailHeightPower Y 1 y ∂cuspHeightMeasure Y₀ = ∞ := by
  rw [cuspHeightMeasure, lintegral_withDensity_eq_lintegral_mul
    (volume.restrict (Ici Y₀)) measurable_cuspHeightDensity
    (measurable_cuspTailHeightPower Y 1)]
  let A : ℝ := max (max Y₀ Y) 1
  have hApos : 0 < A := zero_lt_one.trans_le (le_max_right _ _)
  have hAY₀ : Y₀ ≤ A := (le_max_left Y₀ Y).trans (le_max_left _ _)
  have hAY : Y ≤ A := (le_max_right Y₀ Y).trans (le_max_left _ _)
  have hinv : (∫⁻ y in Ioi A, ENNReal.ofReal (y⁻¹)) = ∞ := by
    by_contra hfinite
    have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi A)] (fun y : ℝ ↦ y⁻¹) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact inv_nonneg.mpr (hApos.trans hy).le
    have hint : IntegrableOn (fun y : ℝ ↦ y⁻¹) (Ioi A) :=
      (lintegral_ofReal_ne_top_iff_integrable
        measurable_inv.aestronglyMeasurable hnonneg).mp hfinite
    exact not_integrableOn_Ioi_inv hint
  have hpoint : ∀ᵐ y ∂volume.restrict (Ioi A),
      ENNReal.ofReal (y⁻¹) ≤
        ENNReal.ofReal ((y ^ 2)⁻¹) * cuspTailHeightPower Y 1 y := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hypos : 0 < y := hApos.trans hy
    have hyY : y ∈ Ici Y := hAY.trans hy.le
    simp only [cuspTailHeightPower, indicator_of_mem hyY, cuspHeightPower,
      pow_one, max_eq_left hypos.le]
    rw [← ENNReal.ofReal_mul (by positivity)]
    have heq : (y ^ 2)⁻¹ * y = y⁻¹ := by field_simp
    rw [heq]
  have hrestrict : volume.restrict (Ioi A) ≤ volume.restrict (Ici Y₀) :=
    Measure.restrict_mono_set volume (fun y hy ↦ hAY₀.trans hy.le)
  apply top_unique
  calc
    ∞ = ∫⁻ y in Ioi A, ENNReal.ofReal (y⁻¹) := hinv.symm
    _ ≤ ∫⁻ y in Ioi A,
        ENNReal.ofReal ((y ^ 2)⁻¹) * cuspTailHeightPower Y 1 y :=
      lintegral_mono_ae hpoint
    _ ≤ ∫⁻ y in Ici Y₀,
        ENNReal.ofReal ((y ^ 2)⁻¹) * cuspTailHeightPower Y 1 y :=
      lintegral_mono' hrestrict le_rfl

/-- A positive cusp-density lower bound forces divergent linear height
moment in the marginal, including an arbitrary positive scaling. -/
theorem lintegral_scaled_cuspTailHeight_one_eq_top_of_cusp_marginal
    {Q : Type*} [MeasurableSpace Q]
    (ν : Measure Q) (height : Q → ℝ) (hheight : Measurable height)
    (Y₀ Y : ℝ) (c : ℝ≥0) (hc : c ≠ 0)
    (hcusp : c • cuspHeightMeasure Y₀ ≤ Measure.map height ν)
    (κ : ℝ≥0) (hκ : κ ≠ 0) :
    ∫⁻ q, (κ : ℝ≥0∞) * cuspTailHeightPower Y 1 (height q) ∂ν = ∞ := by
  have htail : (∫⁻ y, cuspTailHeightPower Y 1 y
      ∂(c • cuspHeightMeasure Y₀)) = ∞ := by
    rw [lintegral_smul_measure, lintegral_cuspTailHeightPower_one_eq_top,
      ENNReal.smul_top, if_neg hc]
  have hmono := lintegral_mono' hcusp
    (le_refl (cuspTailHeightPower Y 1))
  rw [lintegral_map (measurable_cuspTailHeightPower Y 1) hheight] at hmono
  have hbase : (∫⁻ q, cuspTailHeightPower Y 1 (height q) ∂ν) = ∞ :=
    top_unique (htail ▸ hmono)
  have hmeas : Measurable (fun q ↦ cuspTailHeightPower Y 1 (height q)) :=
    (measurable_cuspTailHeightPower Y 1).comp hheight
  rw [lintegral_const_mul _ hmeas, hbase]
  exact ENNReal.mul_top (ENNReal.coe_ne_zero.mpr hκ)

end Stability.Selection
