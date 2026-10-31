import Stability.Selection.OrdinaryTimeFourierCharacters

/-!
# Multiplication in the actual weighted Fourier norm

Absolute Fourier reconstruction identifies each continuous function with
its Haar-coefficient series. Multiplying these series and collecting equal
frequencies gives the weighted product bound. No chosen expansion or
injectivity of its frequency map is assumed.
-/

noncomputable section

open scoped BigOperators

namespace Stability.Selection

open HGAS.Analysis

variable {d : Type*} [Fintype d]

/-- A weight at least one controls ordinary absolute summability. -/
theorem summable_norm_fourierCoeff_of_weighted
    (f : UnitAddTorus d → ℂ) (w : (d → ℤ) → ℝ) (hw : ∀ a, 1 ≤ w a)
    (hf : Summable fun a ↦ ‖UnitAddTorus.mFourierCoeff f a‖ * w a) :
    Summable fun a ↦ ‖UnitAddTorus.mFourierCoeff f a‖ :=
  hf.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (fun a ↦ le_mul_of_one_le_right (norm_nonneg _) (hw a))

/-- Absolute Fourier reconstruction uses the actual Haar coefficients. -/
theorem torusFourierSeries_fourierCoeff
    (f : UnitAddTorus d → ℂ) (hcont : Continuous f)
    (hf : Summable fun a ↦ ‖UnitAddTorus.mFourierCoeff f a‖) :
    torusFourierSeries (UnitAddTorus.mFourierCoeff f) id = f := by
  funext x
  simpa only [torusFourierSeries, torusSeriesTerm, id_eq, smul_eq_mul] using
    (UnitAddTorus.hasSum_mFourier_series_apply_of_summable
      (f := ⟨f, hcont⟩) hf.of_norm x).tsum_eq

/-- The pointwise product of two absolutely convergent presentations is
the double series with multiplied coefficients and added frequencies. -/
theorem torusFourierSeries_mul {ι κ : Type*}
    (c : ι → ℂ) (e : ι → d → ℤ) (b : κ → ℂ) (v : κ → d → ℤ)
    (hc : Summable fun i ↦ ‖c i‖) (hb : Summable fun j ↦ ‖b j‖)
    (x : UnitAddTorus d) :
    torusFourierSeries c e x * torusFourierSeries b v x =
      torusFourierSeries (fun ij : ι × κ ↦ c ij.1 * b ij.2)
        (fun ij ↦ e ij.1 + v ij.2) x := by
  have hc' : Summable fun i ↦ ‖torusSeriesTerm c e i x‖ := by
    simpa only [norm_torusSeriesTerm] using hc
  have hb' : Summable fun j ↦ ‖torusSeriesTerm b v j x‖ := by
    simpa only [norm_torusSeriesTerm] using hb
  unfold torusFourierSeries
  rw [tsum_mul_tsum_of_summable_norm hc' hb']
  apply tsum_congr
  intro ij
  simp only [torusSeriesTerm, UnitAddTorus.mFourier_add]
  ring

/-- The actual weighted Haar norm is submultiplicative for every
submultiplicative frequency weight bounded below by one. -/
theorem weighted_fourierCoeff_mul
    (f g : UnitAddTorus d → ℂ) (hfc : Continuous f) (hgc : Continuous g)
    (w : (d → ℤ) → ℝ) (hw : ∀ a, 1 ≤ w a)
    (hadd : ∀ a b, w (a + b) ≤ w a * w b)
    (hf : Summable fun a ↦ ‖UnitAddTorus.mFourierCoeff f a‖ * w a)
    (hg : Summable fun a ↦ ‖UnitAddTorus.mFourierCoeff g a‖ * w a) :
    Summable (fun a ↦ ‖UnitAddTorus.mFourierCoeff (fun x ↦ f x * g x) a‖ * w a) ∧
      (∑' a, ‖UnitAddTorus.mFourierCoeff (fun x ↦ f x * g x) a‖ * w a) ≤
        (∑' a, ‖UnitAddTorus.mFourierCoeff f a‖ * w a) *
          ∑' a, ‖UnitAddTorus.mFourierCoeff g a‖ * w a := by
  have hw0 (a) : 0 ≤ w a := zero_le_one.trans (hw a)
  have hf0 := summable_norm_fourierCoeff_of_weighted f w hw hf
  have hg0 := summable_norm_fourierCoeff_of_weighted g w hw hg
  let c := fun ab : (d → ℤ) × (d → ℤ) ↦
    UnitAddTorus.mFourierCoeff f ab.1 * UnitAddTorus.mFourierCoeff g ab.2
  let e := fun ab : (d → ℤ) × (d → ℤ) ↦ ab.1 + ab.2
  have hc : Summable fun ab ↦ ‖c ab‖ := hf0.mul_norm hg0
  have hprod := hf.mul_of_nonneg hg (fun _ ↦ mul_nonneg (norm_nonneg _) (hw0 _))
    (fun _ ↦ mul_nonneg (norm_nonneg _) (hw0 _))
  have hle (ab : (d → ℤ) × (d → ℤ)) : ‖c ab‖ * w (e ab) ≤
      (‖UnitAddTorus.mFourierCoeff f ab.1‖ * w ab.1) *
        (‖UnitAddTorus.mFourierCoeff g ab.2‖ * w ab.2) := by
    dsimp [c, e]
    rw [norm_mul]
    calc
      _ ≤ (‖UnitAddTorus.mFourierCoeff f ab.1‖ *
          ‖UnitAddTorus.mFourierCoeff g ab.2‖) * (w ab.1 * w ab.2) :=
        mul_le_mul_of_nonneg_left (hadd _ _) (by positivity)
      _ = _ := by ring
  have hcw : Summable fun ab ↦ ‖c ab‖ * w (e ab) :=
    hprod.of_nonneg_of_le (fun _ ↦ mul_nonneg (norm_nonneg _) (hw0 _)) hle
  have heq : (fun x ↦ f x * g x) = torusFourierSeries c e := by
    funext x
    rw [← torusFourierSeries_fourierCoeff f hfc hf0,
      ← torusFourierSeries_fourierCoeff g hgc hg0]
    exact torusFourierSeries_mul _ _ _ _ hf0 hg0 x
  rw [heq]
  refine ⟨summable_weighted_fourierCoeff_of_expansion c e w hw0 hc hcw, ?_⟩
  exact (tsum_weighted_fourierCoeff_le c e w hw0 hc hcw).trans
    ((hcw.tsum_le_tsum hle hprod).trans_eq (hf.tsum_mul_tsum hg hprod).symm)

/-- The exponential `ℓ¹` frequency weight gives the usual Banach-algebra
product estimate for actual Fourier coefficients. -/
theorem exponential_fourierCoeff_mul
    (f g : UnitAddTorus d → ℂ) (hfc : Continuous f) (hgc : Continuous g)
    {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hf : Summable fun a ↦ ‖UnitAddTorus.mFourierCoeff f a‖ *
      ρ ^ (∑ j, |(a j : ℝ)|))
    (hg : Summable fun a ↦ ‖UnitAddTorus.mFourierCoeff g a‖ *
      ρ ^ (∑ j, |(a j : ℝ)|)) :
    Summable (fun a ↦ ‖UnitAddTorus.mFourierCoeff (fun x ↦ f x * g x) a‖ *
      ρ ^ (∑ j, |(a j : ℝ)|)) ∧
    (∑' a, ‖UnitAddTorus.mFourierCoeff (fun x ↦ f x * g x) a‖ *
      ρ ^ (∑ j, |(a j : ℝ)|)) ≤
        (∑' a, ‖UnitAddTorus.mFourierCoeff f a‖ * ρ ^ (∑ j, |(a j : ℝ)|)) *
          ∑' a, ‖UnitAddTorus.mFourierCoeff g a‖ * ρ ^ (∑ j, |(a j : ℝ)|) :=
  weighted_fourierCoeff_mul f g hfc hgc _
    (fun _ ↦ Real.one_le_rpow hρ (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _))
    (fourierExponentialWeight_add_le hρ) hf hg

/-- A constant has only its actual zero-mode coefficient. -/
theorem fourierCoeff_const (c : ℂ) (a : d → ℤ) :
    UnitAddTorus.mFourierCoeff (fun _ : UnitAddTorus d ↦ c) a =
      if a = 0 then c else 0 := by
  classical
  have h := fourierCoeff_scalar_character_mul
    (UnitAddTorus.mFourier (0 : d → ℤ)) c 0 a
  rw [sub_zero, fourierCoeff_character] at h
  simpa [UnitAddTorus.mFourier_zero, mul_ite] using h

/-- Constants have weighted norm equal to their ordinary norm. -/
theorem exponential_fourierCoeff_const (c : ℂ) (ρ : ℝ) :
    Summable (fun a : d → ℤ ↦
      ‖UnitAddTorus.mFourierCoeff (fun _ : UnitAddTorus d ↦ c) a‖ *
        ρ ^ (∑ j, |(a j : ℝ)|)) ∧
    (∑' a : d → ℤ, ‖UnitAddTorus.mFourierCoeff
      (fun _ : UnitAddTorus d ↦ c) a‖ * ρ ^ (∑ j, |(a j : ℝ)|)) = ‖c‖ := by
  classical
  have he (a : d → ℤ) :
      ‖UnitAddTorus.mFourierCoeff (fun _ : UnitAddTorus d ↦ c) a‖ *
          ρ ^ (∑ j, |(a j : ℝ)|) = if a = 0 then ‖c‖ else 0 := by
    by_cases ha : a = 0 <;> simp [fourierCoeff_const, ha]
  simp_rw [he]
  exact ⟨(hasSum_ite_eq (0 : d → ℤ) ‖c‖).summable,
    (hasSum_ite_eq (0 : d → ℤ) ‖c‖).tsum_eq⟩

/-- Natural powers obey the corresponding power bound, including the
zeroth power of the zero function. -/
theorem exponential_fourierCoeff_pow
    (f : UnitAddTorus d → ℂ) (hfc : Continuous f) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hf : Summable fun a ↦ ‖UnitAddTorus.mFourierCoeff f a‖ *
      ρ ^ (∑ j, |(a j : ℝ)|)) (n : ℕ) :
    Summable (fun a ↦ ‖UnitAddTorus.mFourierCoeff (fun x ↦ f x ^ n) a‖ *
      ρ ^ (∑ j, |(a j : ℝ)|)) ∧
    (∑' a, ‖UnitAddTorus.mFourierCoeff (fun x ↦ f x ^ n) a‖ *
      ρ ^ (∑ j, |(a j : ℝ)|)) ≤
        (∑' a, ‖UnitAddTorus.mFourierCoeff f a‖ * ρ ^ (∑ j, |(a j : ℝ)|)) ^ n := by
  induction n with
  | zero =>
    simpa only [pow_zero, norm_one] using
      (exponential_fourierCoeff_const (d := d) 1 ρ).imp_right (fun h ↦ h.le)
  | succ n ih =>
    have hm := exponential_fourierCoeff_mul (fun x ↦ f x ^ n) f
      (hfc.pow n) hfc hρ ih.1 hf
    simp only [pow_succ]
    refine ⟨hm.1, hm.2.trans ?_⟩
    exact mul_le_mul_of_nonneg_right ih.2 (tsum_nonneg fun _ ↦ by positivity)

end Stability.Selection
