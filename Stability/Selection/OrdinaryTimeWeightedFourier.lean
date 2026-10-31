import HGAS.Analysis.CenteredTorusFourierOperations

/-!
# Weighted Fourier bounds for character expansions

The Fourier coefficients here are Haar integrals, not a chosen presentation
of a series. Repeated exponents are collected before taking their norms.
This is the weighted-norm convention in Section 9, Lemma `bounds`.
-/

noncomputable section

open MeasureTheory

namespace Stability.Selection

open HGAS.Analysis

local instance weightedFourier_circleMeasure : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

variable {d ι : Type*} [Fintype d] [Countable ι]

/-- The actual Haar Fourier coefficient of an absolutely convergent
character expansion is the sum over its exponent fiber. -/
theorem fourierCoeff_torusFourierSeries
    (c : ι → ℂ) (e : ι → d → ℤ)
    (hc : Summable fun i ↦ ‖c i‖) (a : d → ℤ) :
    UnitAddTorus.mFourierCoeff (torusFourierSeries c e) a =
      aggregateFourierCoefficient c e a := by
  classical
  rw [UnitAddTorus.mFourierCoeff,
    aggregateFourierCoefficient_eq_tsum_ite]
  simp only [smul_eq_mul]
  simp_rw [mFourier_mul_torusFourierSeries]
  change (∫ x, ∑' i, torusSeriesTerm c (fun i ↦ -a + e i) i x) = _
  rw [integral_tsum_torusSeriesTerm_eq_constantTerms c _ hc]
  apply tsum_congr
  intro i
  congr 1
  simp [add_comm, ← sub_eq_add_neg, sub_eq_zero]

/-- A nonnegative weighted estimate for a character presentation bounds
the actual Fourier coefficients, including when exponents repeat. -/
theorem summable_weighted_fourierCoeff_of_expansion
    (c : ι → ℂ) (e : ι → d → ℤ) (w : (d → ℤ) → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hc : Summable fun i ↦ ‖c i‖)
    (hcw : Summable fun i ↦ ‖c i‖ * w (e i)) :
    Summable fun a ↦
      ‖UnitAddTorus.mFourierCoeff (torusFourierSeries c e) a‖ * w a := by
  simp_rw [fourierCoeff_torusFourierSeries c e hc]
  exact summable_norm_aggregateFourierCoefficient_mul_weight c e w hw hc hcw

/-- The weighted norm of the actual Fourier coefficients is no larger
than that of the raw expansion. -/
theorem tsum_weighted_fourierCoeff_le
    (c : ι → ℂ) (e : ι → d → ℤ) (w : (d → ℤ) → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hc : Summable fun i ↦ ‖c i‖)
    (hcw : Summable fun i ↦ ‖c i‖ * w (e i)) :
    (∑' a, ‖UnitAddTorus.mFourierCoeff (torusFourierSeries c e) a‖ * w a) ≤
      ∑' i, ‖c i‖ * w (e i) := by
  have hmajor := summable_aggregateFourierWeightedMajorant c e w hcw
  have hsum :
      (∑' a, aggregateFourierWeightedMajorant c e w a) =
        ∑' i, ‖c i‖ * w (e i) := by
    have hfiber := hcw.hasSum.tsum_fiberwise e
    convert hfiber.tsum_eq using 1
    congr 1
    funext a
    unfold aggregateFourierWeightedMajorant
    apply tsum_congr
    intro i
    rw [i.2]
  rw [← hsum]
  apply Summable.tsum_le_tsum _
    (summable_weighted_fourierCoeff_of_expansion c e w hw hc hcw) hmajor
  intro a
  rw [fourierCoeff_torusFourierSeries c e hc,
    aggregateFourierWeightedMajorant, tsum_mul_right]
  exact mul_le_mul_of_nonneg_right
    (norm_aggregateFourierCoefficient_le_majorant c e hc a) (hw a)

/-- A character has exactly one nonzero Haar Fourier coefficient. -/
theorem fourierCoeff_character (b a : d → ℤ) :
    UnitAddTorus.mFourierCoeff (UnitAddTorus.mFourier b) a =
      if a = b then 1 else 0 := by
  classical
  rw [UnitAddTorus.mFourierCoeff]
  simp only [smul_eq_mul, ← UnitAddTorus.mFourier_add]
  rw [integral_mFourier]
  congr 1
  simp [add_comm, ← sub_eq_add_neg, sub_eq_zero, eq_comm]

/-- The exact weighted Fourier norm of a character is its weight. -/
theorem tsum_weighted_fourierCoeff_character (b : d → ℤ) (w : (d → ℤ) → ℝ) :
    (∑' a, ‖UnitAddTorus.mFourierCoeff (UnitAddTorus.mFourier b) a‖ * w a) = w b := by
  classical
  rw [tsum_eq_single b]
  · simp [fourierCoeff_character]
  · intro a ha
    simp [fourierCoeff_character, ha]

end Stability.Selection
