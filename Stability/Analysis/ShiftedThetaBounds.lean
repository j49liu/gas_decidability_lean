import HGAS.Analysis.JacobiThetaHorizontalUniformBounds
import Mathlib.Tactic

/-!
# Weighted summability for shifted theta series

The shifted theta exponents in Step 1 of the revised manuscript's
`lem:bounds` need not be nonnegative.  Their positive quadratic leading
coefficient suffices: polynomial factors and exponential linear weights
preserve Gaussian summability.  The weighted result below retains the
absolute value of the exponent in the Fourier-frequency bound.
-/

noncomputable section

namespace Stability.Analysis.ShiftedThetaBounds

/-- A Gaussian with arbitrary linear and constant terms remains summable
after multiplication by a fixed power of the absolute integer index. -/
theorem summable_pow_mul_exp_quadratic
    {a : ℝ} (ha : 0 < a) (b c : ℝ) (d : ℕ) :
    Summable (fun n : ℤ ↦ |(n : ℝ)| ^ d *
      Real.exp (-a * (n : ℝ) ^ 2 + b * |(n : ℝ)| + c)) := by
  have h :=
    (summable_pow_mul_jacobiTheta₂_term_bound
      (b / (2 * Real.pi)) (div_pos ha Real.pi_pos) d).mul_right
      (Real.exp c)
  apply h.congr
  intro n
  simp only [Int.cast_abs]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  field_simp
  ring

/-- The added constant handles polynomial coefficients with nonzero
constant terms, including the theta-derivative factor `2 * |n| + 1`. -/
theorem summable_one_add_pow_mul_exp_quadratic
    {a : ℝ} (ha : 0 < a) (b c : ℝ) (d : ℕ) :
    Summable (fun n : ℤ ↦ (1 + |(n : ℝ)| ^ d) *
      Real.exp (-a * (n : ℝ) ^ 2 + b * |(n : ℝ)| + c)) := by
  have h₀ := summable_pow_mul_exp_quadratic ha b c 0
  simp only [pow_zero, one_mul] at h₀
  apply (h₀.add (summable_pow_mul_exp_quadratic ha b c d)).congr
  intro n
  ring

private theorem abs_quadratic_le
    {a : ℝ} (ha : 0 ≤ a) (b c x : ℝ) :
    |a * x ^ 2 + b * x + c| ≤ a * x ^ 2 + |b| * |x| + |c| := by
  calc
    |a * x ^ 2 + b * x + c| ≤ |a * x ^ 2 + b * x| + |c| := abs_add_le _ _
    _ ≤ |a * x ^ 2| + |b * x| + |c| := add_le_add (abs_add_le _ _) le_rfl
    _ = a * x ^ 2 + |b| * |x| + |c| := by
      rw [abs_of_nonneg (mul_nonneg ha (sq_nonneg x)), abs_mul]

/-- Weighted summability for an arbitrary positive-leading quadratic.
The exponent may be negative at finitely many indices.  The condition
`λ * ρ ^ A < 1` absorbs the quadratic Fourier weight, while arbitrary
linear frequency weights and polynomial coefficient factors are allowed.
All powers with real exponents are real powers. -/
theorem summable_weighted_quadratic
    {lam ρ a A : ℝ} (hlam : 0 < lam) (hρ : 1 ≤ ρ)
    (ha : 0 < a) (hA : 0 ≤ A) (hdecay : lam * ρ ^ A < 1)
    (b c B C : ℝ) (d : ℕ) :
    Summable (fun n : ℤ ↦
      (1 + |(n : ℝ)| ^ d) *
        lam ^ (a * (n : ℝ) ^ 2 + b * (n : ℝ) + c) *
        ρ ^ (A * |a * (n : ℝ) ^ 2 + b * (n : ℝ) + c| +
          B * |(n : ℝ)| + C)) := by
  have hρpos : 0 < ρ := zero_lt_one.trans_le hρ
  have hlogρ : 0 ≤ Real.log ρ := Real.log_nonneg hρ
  have hlog : Real.log lam + A * Real.log ρ < 0 := by
    have h := Real.log_neg (mul_pos hlam (Real.rpow_pos_of_pos hρpos A)) hdecay
    rwa [Real.log_mul hlam.ne' (Real.rpow_pos_of_pos hρpos A).ne',
      Real.log_rpow hρpos] at h
  have hlead : 0 < -(a * (Real.log lam + A * Real.log ρ)) :=
    neg_pos.mpr (mul_neg_of_pos_of_neg ha hlog)
  have hsum := summable_one_add_pow_mul_exp_quadratic hlead
    (|Real.log lam * b| + Real.log ρ * (A * |b| + B))
    (Real.log lam * c + Real.log ρ * (A * |c| + C)) d
  apply hsum.of_nonneg_of_le
  · intro n
    positivity
  · intro n
    rw [Real.rpow_def_of_pos hlam, Real.rpow_def_of_pos hρpos,
      mul_assoc, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have hquad := mul_le_mul_of_nonneg_left
      (abs_quadratic_le ha.le b c (n : ℝ)) (mul_nonneg hlogρ hA)
    have hlin : Real.log lam * b * (n : ℝ) ≤ |Real.log lam * b| * |(n : ℝ)| := by
      simpa only [abs_mul] using (le_abs_self (Real.log lam * b * (n : ℝ)))
    nlinarith

/-- The coefficient and frequency majorant for the manuscript's shifted
theta terms.  In particular, the term at `n = -1` has exponent `-1 / 4`
and is included in this summability statement. -/
theorem summable_shifted_theta_majorant
    {lam ρ : ℝ} (hlam : 0 < lam) (hρ : 1 ≤ ρ)
    (hdecay : lam * ρ ^ 4 < 1) (D : ℝ) :
    Summable (fun n : ℤ ↦
      (4 * (2 * |(n : ℝ)| + 1)) *
        lam ^ (((n : ℝ) + 1) ^ 2 - 1 / 4) *
        ρ ^ (4 * |((n : ℝ) + 1) ^ 2 - 1 / 4| +
          2 * (2 * |(n : ℝ)| + 1) * D)) := by
  have hdecay' : lam * ρ ^ (4 : ℝ) < 1 := by
    exact_mod_cast hdecay
  have h := summable_weighted_quadratic hlam hρ (a := 1) (A := 4)
    (by norm_num) (by norm_num) hdecay' 2 (3 / 4) (4 * D) (2 * D) 1
  have hs : Summable (fun n : ℤ ↦
      (1 + |(n : ℝ)|) *
        lam ^ (((n : ℝ) + 1) ^ 2 - 1 / 4) *
        ρ ^ (4 * |((n : ℝ) + 1) ^ 2 - 1 / 4| +
          2 * (2 * |(n : ℝ)| + 1) * D)) := by
    apply h.congr
    intro n
    rw [pow_one, show 1 * (n : ℝ) ^ 2 + 2 * (n : ℝ) + 3 / 4 =
      ((n : ℝ) + 1) ^ 2 - 1 / 4 by ring]
    congr 2
    ring
  apply (hs.mul_left 8).of_nonneg_of_le
  · intro n
    positivity
  · intro n
    have hcoeff : 4 * (2 * |(n : ℝ)| + 1) ≤ 8 * (1 + |(n : ℝ)|) := by
      linarith
    have hpower : 0 ≤ lam ^ (((n : ℝ) + 1) ^ 2 - 1 / 4) *
        ρ ^ (4 * |((n : ℝ) + 1) ^ 2 - 1 / 4| +
          2 * (2 * |(n : ℝ)| + 1) * D) := by positivity
    convert mul_le_mul_of_nonneg_right hcoeff hpower using 1 <;> ring

/-- Coefficient and frequency bounds imply absolute weighted summability.
This is the scalar estimate needed before collecting equal Fourier
frequencies; no injectivity of the frequency map is assumed. -/
theorem summable_shifted_theta_of_frequency_bound
    {lam ρ D : ℝ} (hlam : 0 < lam) (hρ : 1 ≤ ρ)
    (hdecay : lam * ρ ^ 4 < 1) (coeff : ℤ → ℂ) (freq : ℤ → ℝ)
    (hcoeff : ∀ n : ℤ, ‖coeff n‖ ≤ 4 * (2 * |(n : ℝ)| + 1))
    (hfreq : ∀ n : ℤ, freq n ≤
      4 * |((n : ℝ) + 1) ^ 2 - 1 / 4| + 2 * (2 * |(n : ℝ)| + 1) * D) :
    Summable (fun n : ℤ ↦ ‖coeff n‖ *
      lam ^ (((n : ℝ) + 1) ^ 2 - 1 / 4) * ρ ^ freq n) := by
  apply (summable_shifted_theta_majorant hlam hρ hdecay D).of_nonneg_of_le
  · intro n
    positivity
  · intro n
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right (hcoeff n) (by positivity)
    · exact Real.rpow_le_rpow_of_exponent_le hρ (hfreq n)
    · positivity
    · positivity

end Stability.Analysis.ShiftedThetaBounds
