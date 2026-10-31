import Stability.Selection.OrdinaryTimeFourierAlgebra

/-!
# Real and imaginary coordinates in the actual Fourier norm

Complex conjugation reflects frequency and conjugates the Haar coefficient.
The symmetric exponential weight is therefore unchanged. Taking a real or
imaginary coordinate averages two reflected coefficient families and cannot
increase the weighted norm.
-/

noncomputable section

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace Stability.Selection

local instance realification_circleMeasure : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance realification_circleProbability :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {d : Type*} [Fintype d]

/-- Conjugation reflects the actual Haar Fourier coefficients. No
continuity assumption is needed for this integral identity. -/
theorem fourierCoeff_conj (f : UnitAddTorus d → ℂ) (a : d → ℤ) :
    UnitAddTorus.mFourierCoeff (fun x ↦ conj (f x)) a =
      conj (UnitAddTorus.mFourierCoeff f (-a)) := by
  unfold UnitAddTorus.mFourierCoeff
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [smul_eq_mul, neg_neg, map_mul, ← UnitAddTorus.mFourier_neg]

/-- Conjugation preserves both weighted summability and the exact norm. -/
theorem exponential_fourierCoeff_conj
    (f : UnitAddTorus d → ℂ) (ρ : ℝ)
    (hf : Summable fun a ↦ ‖UnitAddTorus.mFourierCoeff f a‖ *
      ρ ^ (∑ j, |(a j : ℝ)|)) :
    Summable (fun a ↦ ‖UnitAddTorus.mFourierCoeff (fun x ↦ conj (f x)) a‖ *
      ρ ^ (∑ j, |(a j : ℝ)|)) ∧
    (∑' a, ‖UnitAddTorus.mFourierCoeff (fun x ↦ conj (f x)) a‖ *
      ρ ^ (∑ j, |(a j : ℝ)|)) =
        ∑' a, ‖UnitAddTorus.mFourierCoeff f a‖ * ρ ^ (∑ j, |(a j : ℝ)|) := by
  have he (a : d → ℤ) :
      ‖UnitAddTorus.mFourierCoeff (fun x ↦ conj (f x)) a‖ *
          ρ ^ (∑ j, |(a j : ℝ)|) =
        ‖UnitAddTorus.mFourierCoeff f (-a)‖ * ρ ^ (∑ j, |((-a) j : ℝ)|) := by
    simp [fourierCoeff_conj]
  simp_rw [he]
  refine ⟨(Equiv.neg (d → ℤ)).summable_iff.mpr hf, ?_⟩
  simpa using (Equiv.neg (d → ℤ)).tsum_eq
    (fun a ↦ ‖UnitAddTorus.mFourierCoeff f a‖ * ρ ^ (∑ j, |(a j : ℝ)|))

private theorem integrable_fourierIntegrand
    (f : UnitAddTorus d → ℂ) (hfc : Continuous f) (a : d → ℤ) :
    Integrable fun x ↦ UnitAddTorus.mFourier (-a) x * f x :=
  ((UnitAddTorus.mFourier (-a)).continuous.mul hfc).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The real coordinate is the symmetric average of reflected coefficients. -/
theorem fourierCoeff_re (f : UnitAddTorus d → ℂ) (hfc : Continuous f) (a : d → ℤ) :
    UnitAddTorus.mFourierCoeff (fun x ↦ ((f x).re : ℂ)) a =
      (UnitAddTorus.mFourierCoeff f a + conj (UnitAddTorus.mFourierCoeff f (-a))) / 2 := by
  rw [← fourierCoeff_conj]
  unfold UnitAddTorus.mFourierCoeff
  simp only [smul_eq_mul, Complex.re_eq_add_conj, ← mul_div_assoc, mul_add]
  rw [integral_div]
  exact congrArg (fun z : ℂ ↦ z / 2)
    (integral_add (integrable_fourierIntegrand f hfc a)
      (integrable_fourierIntegrand _ (Complex.continuous_conj.comp hfc) a))

/-- The imaginary coordinate has the same reflected average with the
antisymmetric sign and the factor `1/i`. -/
theorem fourierCoeff_im (f : UnitAddTorus d → ℂ) (hfc : Continuous f) (a : d → ℤ) :
    UnitAddTorus.mFourierCoeff (fun x ↦ ((f x).im : ℂ)) a =
      (UnitAddTorus.mFourierCoeff f a - conj (UnitAddTorus.mFourierCoeff f (-a))) /
        (2 * Complex.I) := by
  rw [← fourierCoeff_conj]
  unfold UnitAddTorus.mFourierCoeff
  simp only [smul_eq_mul, Complex.im_eq_sub_conj, ← mul_div_assoc, mul_sub]
  rw [integral_div]
  exact congrArg (fun z : ℂ ↦ z / (2 * Complex.I))
    (integral_sub (integrable_fourierIntegrand f hfc a)
      (integrable_fourierIntegrand _ (Complex.continuous_conj.comp hfc) a))

private theorem exponential_fourierCoeff_of_symmetric_bound
    (f g : UnitAddTorus d → ℂ) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hf : Summable fun a ↦ ‖UnitAddTorus.mFourierCoeff f a‖ *
      ρ ^ (∑ j, |(a j : ℝ)|))
    (hbound : ∀ a, ‖UnitAddTorus.mFourierCoeff g a‖ ≤
      (‖UnitAddTorus.mFourierCoeff f a‖ + ‖UnitAddTorus.mFourierCoeff f (-a)‖) / 2) :
    Summable (fun a ↦ ‖UnitAddTorus.mFourierCoeff g a‖ * ρ ^ (∑ j, |(a j : ℝ)|)) ∧
    (∑' a, ‖UnitAddTorus.mFourierCoeff g a‖ * ρ ^ (∑ j, |(a j : ℝ)|)) ≤
      ∑' a, ‖UnitAddTorus.mFourierCoeff f a‖ * ρ ^ (∑ j, |(a j : ℝ)|) := by
  let v := fun a : d → ℤ ↦ ‖UnitAddTorus.mFourierCoeff f a‖ * ρ ^ (∑ j, |(a j : ℝ)|)
  have href : Summable fun a ↦ v (-a) := (Equiv.neg (d → ℤ)).summable_iff.mpr hf
  have hmajor : Summable fun a ↦ (v a + v (-a)) / 2 := (hf.add href).div_const 2
  have hle (a : d → ℤ) :
      ‖UnitAddTorus.mFourierCoeff g a‖ * ρ ^ (∑ j, |(a j : ℝ)|) ≤
        (v a + v (-a)) / 2 := by
    have h := mul_le_mul_of_nonneg_right (hbound a)
      (Real.rpow_nonneg (zero_le_one.trans hρ) (∑ j, |(a j : ℝ)|))
    simpa only [v, Pi.neg_apply, Int.cast_neg, abs_neg, add_mul, div_mul_eq_mul_div] using h
  have hg := hmajor.of_nonneg_of_le (fun a ↦ by positivity) hle
  refine ⟨hg, (hg.tsum_le_tsum hle hmajor).trans_eq ?_⟩
  have hrefsum : (∑' a, v (-a)) = ∑' a, v a := by
    simp
  rw [tsum_div_const, hf.tsum_add href, hrefsum]
  dsimp [v]
  ring

/-- Realification cannot increase the actual exponential Fourier norm. -/
theorem exponential_fourierCoeff_re
    (f : UnitAddTorus d → ℂ) (hfc : Continuous f) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hf : Summable fun a ↦ ‖UnitAddTorus.mFourierCoeff f a‖ *
      ρ ^ (∑ j, |(a j : ℝ)|)) :
    Summable (fun a ↦ ‖UnitAddTorus.mFourierCoeff (fun x ↦ ((f x).re : ℂ)) a‖ *
      ρ ^ (∑ j, |(a j : ℝ)|)) ∧
    (∑' a, ‖UnitAddTorus.mFourierCoeff (fun x ↦ ((f x).re : ℂ)) a‖ *
      ρ ^ (∑ j, |(a j : ℝ)|)) ≤
        ∑' a, ‖UnitAddTorus.mFourierCoeff f a‖ * ρ ^ (∑ j, |(a j : ℝ)|) := by
  apply exponential_fourierCoeff_of_symmetric_bound f _ hρ hf
  intro a
  rw [fourierCoeff_re f hfc, norm_div]
  simpa only [Complex.norm_ofNat, Complex.norm_conj] using
    div_le_div_of_nonneg_right (norm_add_le (UnitAddTorus.mFourierCoeff f a)
      (conj (UnitAddTorus.mFourierCoeff f (-a)))) (by norm_num : (0 : ℝ) ≤ 2)

/-- The imaginary coordinate satisfies the same actual norm estimate. -/
theorem exponential_fourierCoeff_im
    (f : UnitAddTorus d → ℂ) (hfc : Continuous f) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hf : Summable fun a ↦ ‖UnitAddTorus.mFourierCoeff f a‖ *
      ρ ^ (∑ j, |(a j : ℝ)|)) :
    Summable (fun a ↦ ‖UnitAddTorus.mFourierCoeff (fun x ↦ ((f x).im : ℂ)) a‖ *
      ρ ^ (∑ j, |(a j : ℝ)|)) ∧
    (∑' a, ‖UnitAddTorus.mFourierCoeff (fun x ↦ ((f x).im : ℂ)) a‖ *
      ρ ^ (∑ j, |(a j : ℝ)|)) ≤
        ∑' a, ‖UnitAddTorus.mFourierCoeff f a‖ * ρ ^ (∑ j, |(a j : ℝ)|) := by
  apply exponential_fourierCoeff_of_symmetric_bound f _ hρ hf
  intro a
  rw [fourierCoeff_im f hfc, norm_div]
  simpa only [norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one, Complex.norm_conj] using
    div_le_div_of_nonneg_right (norm_sub_le (UnitAddTorus.mFourierCoeff f a)
      (conj (UnitAddTorus.mFourierCoeff f (-a)))) (by norm_num : (0 : ℝ) ≤ 2)

end Stability.Selection
