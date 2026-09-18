import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.NumberTheory.Modular
import Mathlib.Tactic

/-!
# Finite hyperbolic area of the standard modular domain

This file proves the finite-area geometric input underlying the
finite-covolume argument for the modular frame quotient.
-/

namespace HGAS.Modular

open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

/-- The rectangular cusp strip containing the standard modular
fundamental domain. -/
def modularCuspStrip : Set ℂ :=
  {z | z.re ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2) ∧
    z.im ∈ Set.Ioi (1 / 2 : ℝ)}

theorem measurableSet_modularCuspStrip :
    MeasurableSet modularCuspStrip := by
  exact
    ((measurableSet_Icc.prod measurableSet_Ioi).preimage
      Complex.measurableEquivRealProd.measurable)

theorem modular_fd_image_subset_cuspStrip :
    UpperHalfPlane.coe '' ModularGroup.fd ⊆ modularCuspStrip := by
  rintro z ⟨τ, hτ, rfl⟩
  constructor
  · simpa only [Set.mem_Icc, neg_div, neg_le, UpperHalfPlane.coe_re,
      abs_le] using hτ.2
  · rw [Set.mem_Ioi]
    have hsq :=
      ModularGroup.three_le_four_mul_im_sq_of_mem_fd hτ
    have him := τ.im_pos
    norm_num at hsq ⊢
    nlinarith [sq_nonneg (τ.im - 1 / 2)]

private theorem integrableOn_cuspStrip_density :
    IntegrableOn
      (fun z : ℂ ↦ (z.im : ℝ) ^ (-2 : ℝ))
      modularCuspStrip := by
  let X : Set ℝ := Set.Icc (-1 / 2 : ℝ) (1 / 2)
  let Y : Set ℝ := Set.Ioi (1 / 2 : ℝ)
  have hX : IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) X := by
    exact integrableOn_const (by simp [X, Real.volume_Icc]) (by simp)
  have hY :
      IntegrableOn (fun y : ℝ ↦ y ^ (-2 : ℝ)) Y := by
    exact integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have hprod :
      IntegrableOn
        (fun p : ℝ × ℝ ↦ (1 : ℝ) * p.2 ^ (-2 : ℝ))
        (X ×ˢ Y) (volume.prod volume) := by
    rw [IntegrableOn, ← Measure.prod_restrict]
    exact hX.mul_prod hY
  have hstrip :
      modularCuspStrip =
        Complex.measurableEquivRealProd ⁻¹' (X ×ˢ Y) := by
    ext z
    simp only [modularCuspStrip, Set.mem_setOf_eq,
      Set.mem_preimage, Set.mem_prod, Complex.measurableEquivRealProd_apply,
      X, Y]
  rw [hstrip]
  change
    IntegrableOn
      ((fun p : ℝ × ℝ ↦ p.2 ^ (-2 : ℝ)) ∘
        Complex.measurableEquivRealProd)
      (Complex.measurableEquivRealProd ⁻¹' (X ×ˢ Y)) volume
  rw [Complex.volume_preserving_equiv_real_prod.integrableOn_comp_preimage
    Complex.measurableEquivRealProd.measurableEmbedding]
  simpa only [one_mul] using hprod

private theorem hyperbolicDensity_eq_enorm_rpow
    {y : ℝ} (hy : 0 < y) :
    (↑((1 / ‖y‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) =
      ‖y ^ (-2 : ℝ)‖ₑ := by
  rw [Real.rpow_neg_ofNat, zpow_neg, enorm_eq_nnnorm]
  norm_cast
  ext
  simp [Real.nnnorm_of_nonneg hy.le]

/-- The standard closed modular fundamental domain has finite
hyperbolic area. -/
theorem modular_fd_volume_ne_top :
    (volume : Measure UpperHalfPlane) ModularGroup.fd ≠ ∞ := by
  rw [UpperHalfPlane.volume_eq_lintegral]
  apply ne_of_lt
  refine lt_of_le_of_lt
    (lintegral_mono_set modular_fd_image_subset_cuspStrip) ?_
  have hfinite :
      HasFiniteIntegral
        (fun z : ℂ ↦ z.im ^ (-2 : ℝ))
        (volume.restrict modularCuspStrip) := by
    exact integrableOn_cuspStrip_density.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_enorm] at hfinite
  rw [setLIntegral_congr_fun measurableSet_modularCuspStrip
    (fun z hz ↦ hyperbolicDensity_eq_enorm_rpow
      (show 0 < z.im by
        exact (by norm_num : (0 : ℝ) < 1 / 2).trans
          (show z.im ∈ Set.Ioi (1 / 2 : ℝ) from hz.2)))]
  exact hfinite

end

end HGAS.Modular
