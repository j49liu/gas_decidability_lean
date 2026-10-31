import Stability.Selection.OrdinaryTimeWeightedFourier

/-!
# Character multiplication in the weighted Fourier norm

Multiplication by a gauge character translates actual Haar coefficients.
The exponential `ℓ¹` weight changes by at most the weight of that character.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Stability.Selection

variable {d : Type*} [Fintype d]

/-- Fundamental torus characters on a real phase lift use the full
`2π` pairing, with no additional arithmetic frequency scaling. -/
theorem fourierCharacter_realLift (a : d → ℤ) (x : d → ℝ) :
    UnitAddTorus.mFourier a (fun i ↦ (x i : UnitAddCircle)) =
      Complex.exp (2 * Real.pi * Complex.I * (∑ i, (a i : ℝ) * x i)) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_coe_apply,
    Complex.ofReal_one, div_one]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Multiplication by a scalar character translates the actual Fourier
coefficient and multiplies it by that scalar. -/
theorem fourierCoeff_scalar_character_mul
    (f : UnitAddTorus d → ℂ) (c : ℂ) (b a : d → ℤ) :
    UnitAddTorus.mFourierCoeff (fun x ↦ c * UnitAddTorus.mFourier b x * f x) a =
      c * UnitAddTorus.mFourierCoeff f (a - b) := by
  unfold UnitAddTorus.mFourierCoeff
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [smul_eq_mul]
  have he : -a + b = -(a - b) := by abel
  have hc := UnitAddTorus.mFourier_add (m := -a) (n := b) (x := x)
  rw [he] at hc
  rw [hc]
  ring

/-- The exponential `ℓ¹` frequency weight is submultiplicative. -/
theorem fourierExponentialWeight_add_le {ρ : ℝ} (hρ : 1 ≤ ρ) (a b : d → ℤ) :
    ρ ^ (∑ j, |((a + b) j : ℝ)|) ≤
      ρ ^ (∑ j, |(a j : ℝ)|) * ρ ^ (∑ j, |(b j : ℝ)|) := by
  rw [← Real.rpow_add (zero_lt_one.trans_le hρ)]
  apply Real.rpow_le_rpow_of_exponent_le hρ
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  simpa only [Pi.add_apply, Int.cast_add] using abs_add_le (a j : ℝ) (b j : ℝ)

/-- A scalar gauge character preserves weighted Fourier summability,
with the expected multiplicative norm bound. -/
theorem exponential_fourierCoeff_scalar_character_mul
    (f : UnitAddTorus d → ℂ) (c : ℂ) (b : d → ℤ) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hf : Summable fun a ↦ ‖UnitAddTorus.mFourierCoeff f a‖ *
      ρ ^ (∑ j, |(a j : ℝ)|)) :
    Summable (fun a ↦
      ‖UnitAddTorus.mFourierCoeff (fun x ↦ c * UnitAddTorus.mFourier b x * f x) a‖ *
        ρ ^ (∑ j, |(a j : ℝ)|)) ∧
    (∑' a, ‖UnitAddTorus.mFourierCoeff
      (fun x ↦ c * UnitAddTorus.mFourier b x * f x) a‖ * ρ ^ (∑ j, |(a j : ℝ)|)) ≤
        ‖c‖ * ρ ^ (∑ j, |(b j : ℝ)|) *
          ∑' a, ‖UnitAddTorus.mFourierCoeff f a‖ * ρ ^ (∑ j, |(a j : ℝ)|) := by
  let C := ‖c‖ * ρ ^ (∑ j, |(b j : ℝ)|)
  let v : (d → ℤ) → ℝ := fun a ↦ ‖UnitAddTorus.mFourierCoeff
    (fun x ↦ c * UnitAddTorus.mFourier b x * f x) a‖ * ρ ^ (∑ j, |(a j : ℝ)|)
  have hle (a : d → ℤ) : v (a + b) ≤
      C * (‖UnitAddTorus.mFourierCoeff f a‖ * ρ ^ (∑ j, |(a j : ℝ)|)) := by
    dsimp [v, C]
    rw [fourierCoeff_scalar_character_mul, add_sub_cancel_right, norm_mul]
    have h := mul_le_mul_of_nonneg_left (fourierExponentialWeight_add_le hρ a b)
      (mul_nonneg (norm_nonneg c) (norm_nonneg (UnitAddTorus.mFourierCoeff f a)))
    simpa only [Pi.add_apply, Int.cast_add, mul_assoc, mul_left_comm, mul_comm] using h
  have hshift : Summable fun a ↦ v (a + b) :=
    (hf.mul_left C).of_nonneg_of_le (fun a ↦ by dsimp [v]; positivity) hle
  have hsum : Summable v := (Equiv.addRight b).summable_iff.mp hshift
  refine ⟨hsum, ?_⟩
  change (∑' a, v a) ≤ C * ∑' a, ‖UnitAddTorus.mFourierCoeff f a‖ *
    ρ ^ (∑ j, |(a j : ℝ)|)
  rw [← (Equiv.addRight b).tsum_eq v, ← tsum_mul_left]
  exact hshift.tsum_le_tsum hle (hf.mul_left C)

end Stability.Selection
