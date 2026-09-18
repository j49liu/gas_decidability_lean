import HGAS.Analysis.CesaroExponentialSeries
import Mathlib.Tactic

/-!
# Resonance table for the unary theta moments

On a closed horocycle the three even theta characteristics have temporal
frequencies

```
             s n²                 (θ₃ and θ₄),
             s (n+1/2)²           (θ₂),
```

in units of the private nome clock.  The unary selector takes the mean
and the first Fourier moment, so it subtracts `r=0` or `r=1`.

This module proves the exact resonance table and combines it with the
general Cesàro extraction theorem.  In particular:

* the integer-square mean retains only `n=0`;
* the half-square mean retains nothing;
* reversed orientation `s=-1` has no first-moment resonance; and
* orientation `s=1` retains precisely `n=±1`.

The result begins after a recurrent orbit has been represented by its
absolutely summable theta expansion.  The separate global classification
is responsible for producing that representation.
-/

namespace HGAS.Modular

open Filter Topology

noncomputable section

/-- Integer-square frequency after twisting by the `r`-th private-clock
character. -/
def integerSquareMomentFrequency
    (Ω s : ℝ) (r n : ℤ) : ℝ :=
  Ω * (s * (n : ℝ) ^ 2 - (r : ℝ))

/-- Half-integer-square frequency after the same twist. -/
def halfSquareMomentFrequency
    (Ω s : ℝ) (r n : ℤ) : ℝ :=
  Ω * (s * ((n : ℝ) + 1 / 2) ^ 2 - (r : ℝ))

/-- The integer-square mean has only the constant resonance. -/
theorem integerSquareMeanFrequency_eq_zero_iff
    {Ω s : ℝ} (hΩ : Ω ≠ 0) (hs : s ≠ 0)
    (n : ℤ) :
    integerSquareMomentFrequency Ω s 0 n = 0 ↔
      n = 0 := by
  simp only [integerSquareMomentFrequency,
    Int.cast_zero, sub_zero, mul_eq_zero,
    hΩ, hs, pow_eq_zero_iff (by norm_num : 2 ≠ 0),
    Int.cast_eq_zero, false_or]

/-- No half-integer square is zero. -/
theorem intCast_add_half_ne_zero (n : ℤ) :
    (n : ℝ) + 1 / 2 ≠ 0 := by
  intro h
  have hn : (n : ℝ) = -(1 / 2 : ℝ) := by
    linarith
  have htwice : (2 * n : ℤ) = -1 := by
    exact_mod_cast (by linarith : (2 : ℝ) * n = -1)
  omega

/-- The half-integer theta characteristic has zero mean coefficient: no
index resonates with the untwisted mean. -/
theorem halfSquareMeanFrequency_ne_zero
    {Ω s : ℝ} (hΩ : Ω ≠ 0) (hs : s ≠ 0)
    (n : ℤ) :
    halfSquareMomentFrequency Ω s 0 n ≠ 0 := by
  simp only [halfSquareMomentFrequency,
    Int.cast_zero, sub_zero]
  exact mul_ne_zero hΩ
    (mul_ne_zero hs
      (pow_ne_zero 2 (intCast_add_half_ne_zero n)))

/-- Reversed orientation has no resonance in the first moment. -/
theorem integerSquareFirstFrequency_neg_ne_zero
    {Ω : ℝ} (hΩ : Ω ≠ 0) (n : ℤ) :
    integerSquareMomentFrequency Ω (-1) 1 n ≠ 0 := by
  unfold integerSquareMomentFrequency
  apply mul_ne_zero hΩ
  have hsquare : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
  norm_num
  nlinarith

/-- Forward unit orientation has exactly the two first-harmonic
resonances `n=1` and `n=-1`. -/
theorem integerSquareFirstFrequency_one_eq_zero_iff
    {Ω : ℝ} (hΩ : Ω ≠ 0) (n : ℤ) :
    integerSquareMomentFrequency Ω 1 1 n = 0 ↔
      n = 1 ∨ n = -1 := by
  rw [integerSquareMomentFrequency, mul_eq_zero,
    or_iff_right hΩ]
  norm_num
  rw [sub_eq_zero, sq_eq_one_iff]
  constructor <;> rintro (h | h)
  · left
    exact_mod_cast h
  · right
    exact_mod_cast h
  · left
    exact_mod_cast h
  · right
    exact_mod_cast h

/-- An absolutely summable integer-square exponential series. -/
def integerSquareMomentSeries
    (coefficient : ℤ → ℂ)
    (Ω s : ℝ) (r : ℤ) (t : ℝ) : ℂ :=
  HGAS.Analysis.exponentialSeries coefficient
    (integerSquareMomentFrequency Ω s r) t

/-- An absolutely summable half-integer-square exponential series. -/
def halfSquareMomentSeries
    (coefficient : ℤ → ℂ)
    (Ω s : ℝ) (r : ℤ) (t : ℝ) : ℂ :=
  HGAS.Analysis.exponentialSeries coefficient
    (halfSquareMomentFrequency Ω s r) t

/-- General Cesàro extraction for an integer-square unary moment. -/
theorem naturalCesaroMean_integerSquareMomentSeries_tendsto
    (coefficient : ℤ → ℂ)
    (hsum : Summable fun n ↦ ‖coefficient n‖)
    (Ω s : ℝ) (r : ℤ) :
    Tendsto
      (fun N ↦ HGAS.Analysis.naturalCesaroMean
        (integerSquareMomentSeries coefficient Ω s r) N)
      atTop
      (𝓝 (∑' n : ℤ,
        if integerSquareMomentFrequency Ω s r n = 0 then
          coefficient n
        else 0)) := by
  exact
    HGAS.Analysis.naturalCesaroMean_exponentialSeries_tendsto
      coefficient
      (integerSquareMomentFrequency Ω s r) hsum

/-- General Cesàro extraction for a half-integer-square unary moment. -/
theorem naturalCesaroMean_halfSquareMomentSeries_tendsto
    (coefficient : ℤ → ℂ)
    (hsum : Summable fun n ↦ ‖coefficient n‖)
    (Ω s : ℝ) (r : ℤ) :
    Tendsto
      (fun N ↦ HGAS.Analysis.naturalCesaroMean
        (halfSquareMomentSeries coefficient Ω s r) N)
      atTop
      (𝓝 (∑' n : ℤ,
        if halfSquareMomentFrequency Ω s r n = 0 then
          coefficient n
        else 0)) := by
  exact
    HGAS.Analysis.naturalCesaroMean_exponentialSeries_tendsto
      coefficient
      (halfSquareMomentFrequency Ω s r) hsum

/-- The mean of an integer-square expansion is its constant
coefficient. -/
theorem naturalCesaroMean_integerSquareMean_tendsto
    (coefficient : ℤ → ℂ)
    (hsum : Summable fun n ↦ ‖coefficient n‖)
    {Ω s : ℝ} (hΩ : Ω ≠ 0) (hs : s ≠ 0) :
    Tendsto
      (fun N ↦ HGAS.Analysis.naturalCesaroMean
        (integerSquareMomentSeries coefficient Ω s 0) N)
      atTop (𝓝 (coefficient 0)) := by
  convert
    naturalCesaroMean_integerSquareMomentSeries_tendsto
      coefficient hsum Ω s 0 using 1
  apply congrArg 𝓝
  simp_rw [integerSquareMeanFrequency_eq_zero_iff hΩ hs]
  exact (tsum_ite_eq 0 coefficient).symm

/-- The mean of a half-integer-square expansion is zero. -/
theorem naturalCesaroMean_halfSquareMean_tendsto_zero
    (coefficient : ℤ → ℂ)
    (hsum : Summable fun n ↦ ‖coefficient n‖)
    {Ω s : ℝ} (hΩ : Ω ≠ 0) (hs : s ≠ 0) :
    Tendsto
      (fun N ↦ HGAS.Analysis.naturalCesaroMean
        (halfSquareMomentSeries coefficient Ω s 0) N)
      atTop (𝓝 0) := by
  convert
    naturalCesaroMean_halfSquareMomentSeries_tendsto
      coefficient hsum Ω s 0 using 1
  apply congrArg 𝓝
  have hzero :
      (fun n : ℤ ↦
        if halfSquareMomentFrequency Ω s 0 n = 0 then
          coefficient n
        else 0) = 0 := by
    funext n
    simp [halfSquareMeanFrequency_ne_zero hΩ hs n]
  rw [hzero]
  exact (tsum_zero (α := ℂ) (β := ℤ)).symm

/-- Reversed orientation contributes zero to the first moment. -/
theorem naturalCesaroMean_integerSquareFirst_neg_tendsto_zero
    (coefficient : ℤ → ℂ)
    (hsum : Summable fun n ↦ ‖coefficient n‖)
    {Ω : ℝ} (hΩ : Ω ≠ 0) :
    Tendsto
      (fun N ↦ HGAS.Analysis.naturalCesaroMean
        (integerSquareMomentSeries coefficient Ω (-1) 1) N)
      atTop (𝓝 0) := by
  convert
    naturalCesaroMean_integerSquareMomentSeries_tendsto
      coefficient hsum Ω (-1) 1 using 1
  apply congrArg 𝓝
  have hzero :
      (fun n : ℤ ↦
        if integerSquareMomentFrequency Ω (-1) 1 n = 0 then
          coefficient n
        else 0) = 0 := by
    funext n
    simp [integerSquareFirstFrequency_neg_ne_zero hΩ n]
  rw [hzero]
  exact (tsum_zero (α := ℂ) (β := ℤ)).symm

/-- At forward unit orientation, the first moment retains exactly the two
indices `n=±1`. -/
theorem naturalCesaroMean_integerSquareFirst_one_tendsto
    (coefficient : ℤ → ℂ)
    (hsum : Summable fun n ↦ ‖coefficient n‖)
    {Ω : ℝ} (hΩ : Ω ≠ 0) :
    Tendsto
      (fun N ↦ HGAS.Analysis.naturalCesaroMean
        (integerSquareMomentSeries coefficient Ω 1 1) N)
      atTop
      (𝓝 (∑' n : ℤ,
        if n = 1 ∨ n = -1 then coefficient n else 0)) := by
  convert
    naturalCesaroMean_integerSquareMomentSeries_tendsto
      coefficient hsum Ω 1 1 using 1
  apply congrArg 𝓝
  apply tsum_congr
  intro n
  simp only [integerSquareFirstFrequency_one_eq_zero_iff hΩ]

end

end HGAS.Modular
