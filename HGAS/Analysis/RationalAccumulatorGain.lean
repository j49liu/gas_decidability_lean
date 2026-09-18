import HGAS.Foundation.FinitePolynomialCode
import Mathlib.Tactic

/-!
# A small positive rational accumulator gain

The finite-graph construction only requires the accumulator gain to be
positive and sufficiently small.  Since the compact compiler stores
rational coefficients, we record the elementary density argument in the
exact `RationalCode` representation.

For every positive chart budget `C` and nonnegative finite primitive
budget `S`, there is a code `κ` with positive decoded value and

```text
                         8 |κ|² S ≤ C.
```

This theorem is qualitative.  A later effective reduction may replace
the density choice by any computable rational upper bound for `S`.
-/

noncomputable section

namespace HGAS.Analysis

open HGAS

/-- Existence of a positive rational gain small enough for a prescribed
quadratic primitive budget. -/
theorem exists_positive_rationalCode_mul_sq_le
    {central budget : ℝ}
    (hcentral : 0 < central)
    (hbudget : 0 ≤ budget) :
    ∃ κ : RationalCode,
      0 < (RationalCode.decode κ : ℝ) ∧
      8 * |(RationalCode.decode κ : ℝ)| ^ 2 * budget ≤
        central := by
  by_cases hzero : budget = 0
  · refine ⟨RationalCode.one, ?_, ?_⟩
    · simp
    · calc
        8 * |(RationalCode.decode RationalCode.one : ℝ)| ^ 2 *
              budget =
            0 := by
              rw [hzero]
              norm_num
        _ ≤ central := hcentral.le
  · have hbudgetPos : 0 < budget :=
      lt_of_le_of_ne hbudget (Ne.symm hzero)
    let upper : ℝ :=
      min 1 (central / (8 * budget))
    have hupper : 0 < upper := by
      unfold upper
      exact lt_min (by norm_num)
        (div_pos hcentral (mul_pos (by norm_num) hbudgetPos))
    obtain ⟨q : ℚ, hq0, hqupper⟩ :=
      exists_pos_rat_lt hupper
    refine ⟨RationalCode.encode q, ?_, ?_⟩
    · simpa using hq0
    · have hq0' : 0 < (q : ℝ) := by exact_mod_cast hq0
      have hqOne : (q : ℝ) < 1 :=
        hqupper.trans_le (min_le_left _ _)
      have hqBudget :
          (q : ℝ) < central / (8 * budget) :=
        hqupper.trans_le (min_le_right _ _)
      have hqSq : (q : ℝ) ^ 2 ≤ (q : ℝ) := by
        nlinarith
      have hlinear :
          8 * (q : ℝ) * budget < central := by
        have hden : 0 < 8 * budget := by positivity
        have h := (lt_div_iff₀ hden).mp hqBudget
        nlinarith
      have hsquare :
          8 * (q : ℝ) ^ 2 * budget ≤
            8 * (q : ℝ) * budget := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hqSq (by norm_num))
          hbudget
      simpa only [RationalCode.decode_encode, Rat.cast_abs,
        abs_of_pos hq0'] using hsquare.trans hlinear.le

end HGAS.Analysis
