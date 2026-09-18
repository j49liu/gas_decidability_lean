import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Uniform lower bounds for affine complex exponentials

The Bloch formulas used later contain a nonzero constant times the
exponential of an affine complex function of real time.  Its modulus can
decay exponentially, but no faster.  This file records that elementary
estimate in a reusable form.

For

```
S(t) = C * exp (a + t * b),      C ≠ 0,
```

put

```
M = |log ‖C‖| + |re a| + |re b|.
```

Then, for every real `t`,

```
exp (-M * (1 + |t|)) ≤ ‖S(t)‖.
```

The symmetric `1 + |t|` form is convenient for two-sided escape
arguments; the one-sided `1+t` corollary is the form consumed by the
current theta-escape theorem.
-/

namespace HGAS.Analysis

open Complex Real

noncomputable section

/-- An explicit rate controlling the possible decay of a nonzero constant
times an affine complex exponential. -/
def affineComplexExponentialLoss (C a b : ℂ) : ℝ :=
  |Real.log ‖C‖| + |a.re| + |b.re|

theorem affineComplexExponentialLoss_nonneg
    (C a b : ℂ) :
    0 ≤ affineComplexExponentialLoss C a b := by
  unfold affineComplexExponentialLoss
  positivity

/-- A nonzero constant times an affine complex exponential has a global
two-sided exponential lower bound. -/
theorem exp_neg_affineComplexExponentialLoss_le_norm
    {C a b : ℂ}
    (hC : C ≠ 0) :
    ∀ t : ℝ,
      Real.exp
          (-affineComplexExponentialLoss C a b *
            (1 + |t|)) ≤
        ‖C * Complex.exp (a + (t : ℂ) * b)‖ := by
  intro t
  have hCnorm : 0 < ‖C‖ := norm_pos_iff.mpr hC
  have hlogLower :
      -|Real.log ‖C‖| ≤ Real.log ‖C‖ :=
    neg_abs_le _
  have haLower : -|a.re| ≤ a.re :=
    neg_abs_le _
  have hbLower : -|b.re| * |t| ≤ b.re * t := by
    have hmul :
        |b.re * t| ≤ |b.re| * |t| := by
      rw [abs_mul]
    simpa only [neg_mul] using (neg_le_of_abs_le hmul)
  have hexponent :
      -affineComplexExponentialLoss C a b *
          (1 + |t|) ≤
        Real.log ‖C‖ + (a + (t : ℂ) * b).re := by
    unfold affineComplexExponentialLoss
    simp only [add_re, mul_re, ofReal_re, ofReal_im,
      zero_mul, sub_zero]
    have ht : 0 ≤ |t| := abs_nonneg t
    have hlogAbs : 0 ≤ |Real.log ‖C‖| := abs_nonneg _
    have haAbs : 0 ≤ |a.re| := abs_nonneg _
    have hbAbs : 0 ≤ |b.re| := abs_nonneg _
    nlinarith
  apply Real.exp_le_exp.mpr at hexponent
  rw [Real.exp_add, Real.exp_log hCnorm] at hexponent
  simpa only [norm_mul, Complex.norm_exp] using hexponent

/-- One-sided version of
`exp_neg_affineComplexExponentialLoss_le_norm`, suitable on `t ≥ 0`. -/
theorem exp_neg_affineComplexExponentialLoss_one_add_le_norm
    {C a b : ℂ}
    (hC : C ≠ 0)
    {t : ℝ}
    (ht : 0 ≤ t) :
    Real.exp
          (-affineComplexExponentialLoss C a b *
            (1 + t)) ≤
        ‖C * Complex.exp (a + (t : ℂ) * b)‖ := by
  simpa [abs_of_nonneg ht] using
    exp_neg_affineComplexExponentialLoss_le_norm hC t

/-- The one-sided lower bound holds eventually at `+∞`. -/
theorem eventually_exp_neg_affineComplexExponentialLoss_one_add_le_norm
    {C a b : ℂ}
    (hC : C ≠ 0) :
    ∀ᶠ t : ℝ in Filter.atTop,
      Real.exp
          (-affineComplexExponentialLoss C a b *
            (1 + t)) ≤
        ‖C * Complex.exp (a + (t : ℂ) * b)‖ := by
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
  exact
    exp_neg_affineComplexExponentialLoss_one_add_le_norm
      hC ht

end

end HGAS.Analysis
