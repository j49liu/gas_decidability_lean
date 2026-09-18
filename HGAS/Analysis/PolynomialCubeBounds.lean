import HGAS.Analysis.MvPolynomialCalculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# Explicit coefficient bounds on the unit cube

This module supplies the quantitative estimate used by an exact dyadic-grid
certificate for strict polynomial positivity.

For a rational polynomial `p`, define

```
A(p) = ∑_{α ∈ support p} |p_α|,
L(p) = ∑ᵢ A(∂ᵢp).
```

On the finite-product unit cube, `|p(x)| ≤ A(p)` and the operator norm of
the derivative is at most `L(p)`.  The mean-value theorem therefore gives

```
|p(x)-p(y)| ≤ L(p) ‖x-y‖∞.
```

Both bounds are finite sums of absolute values of rational coefficients.
Thus later syntax modules can compute them exactly; this file isolates the
real-analysis proof of soundness.
-/

namespace HGAS

open MvPolynomial Set
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-- Sum of the absolute values of all nonzero rational coefficients,
viewed as a real number. -/
def polynomialCubeAbsBound
    (p : MvPolynomial (Fin n) ℚ) : ℝ :=
  ∑ e ∈ p.support, |algebraMap ℚ ℝ (p.coeff e)|

/-- Sum of the coefficient bounds of all formal partial derivatives. -/
def polynomialCubeGradientBound
    (p : MvPolynomial (Fin n) ℚ) : ℝ :=
  ∑ i : Fin n, polynomialCubeAbsBound (pderiv i p)

theorem polynomialCubeAbsBound_nonneg
    (p : MvPolynomial (Fin n) ℚ) :
    0 ≤ polynomialCubeAbsBound p := by
  exact Finset.sum_nonneg fun e he ↦ abs_nonneg _

theorem polynomialCubeGradientBound_nonneg
    (p : MvPolynomial (Fin n) ℚ) :
    0 ≤ polynomialCubeGradientBound p := by
  exact Finset.sum_nonneg fun i hi ↦
    polynomialCubeAbsBound_nonneg _

/-- Every monomial has absolute value at most one when every coordinate
does. -/
theorem abs_monomial_eval_le_one
    (e : Fin n →₀ ℕ) (x : Fin n → ℝ)
    (hx : ∀ i, |x i| ≤ 1) :
    |∏ i : Fin n, x i ^ e i| ≤ 1 := by
  rw [Finset.abs_prod]
  apply Finset.prod_le_one
  · intro i hi
    positivity
  · intro i hi
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (hx i)

/-- Coefficient `ℓ¹` bound for evaluation on the unit cube. -/
theorem abs_ratMvPolynomialEval_le_cubeAbsBound
    (p : MvPolynomial (Fin n) ℚ) (x : Fin n → ℝ)
    (hx : ∀ i, |x i| ≤ 1) :
    |ratMvPolynomialEval p x| ≤ polynomialCubeAbsBound p := by
  rw [ratMvPolynomialEval, ← MvPolynomial.eval₂_eq_eval_map]
  rw [MvPolynomial.eval₂_eq']
  calc
    |∑ e ∈ p.support,
        algebraMap ℚ ℝ (p.coeff e) *
          ∏ i : Fin n, x i ^ e i| ≤
        ∑ e ∈ p.support,
          |algebraMap ℚ ℝ (p.coeff e) *
            ∏ i : Fin n, x i ^ e i| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ p.support, |algebraMap ℚ ℝ (p.coeff e)| := by
      apply Finset.sum_le_sum
      intro e he
      rw [abs_mul]
      have hprod := abs_monomial_eval_le_one e x hx
      have hcoeff : 0 ≤ |algebraMap ℚ ℝ (p.coeff e)| := abs_nonneg _
      simpa using
        (mul_le_mul_of_nonneg_left hprod hcoeff)
    _ = polynomialCubeAbsBound p := rfl

/-- The derivative functional has the explicit coefficient bound on the
unit cube. -/
theorem norm_fderiv_ratMvPolynomialEval_le_cubeGradientBound
    (p : MvPolynomial (Fin n) ℚ) (x : Fin n → ℝ)
    (hx : ∀ i, |x i| ≤ 1) :
    ‖fderiv ℝ (ratMvPolynomialEval p) x‖ ≤
      polynomialCubeGradientBound p := by
  rw [(hasFDerivAt_ratMvPolynomialEval p x).fderiv]
  apply (ratMvPolynomialDifferential p x).opNorm_le_bound
    (polynomialCubeGradientBound_nonneg p)
  intro v
  rw [Real.norm_eq_abs, ratMvPolynomialDifferential_apply]
  calc
    |∑ i : Fin n,
        MvPolynomial.eval x
            (MvPolynomial.map (algebraMap ℚ ℝ) (pderiv i p)) *
          v i| ≤
        ∑ i : Fin n,
          |MvPolynomial.eval x
              (MvPolynomial.map (algebraMap ℚ ℝ) (pderiv i p)) *
            v i| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin n,
        polynomialCubeAbsBound (pderiv i p) * ‖v‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      apply mul_le_mul
      · simpa only [ratMvPolynomialEval] using
          abs_ratMvPolynomialEval_le_cubeAbsBound
            (pderiv i p) x hx
      · exact norm_le_pi_norm v i
      · exact abs_nonneg _
      · exact polynomialCubeAbsBound_nonneg _
    _ = polynomialCubeGradientBound p * ‖v‖ := by
      rw [polynomialCubeGradientBound, Finset.sum_mul]

/-- A point of the closed sup-norm unit ball has every coordinate in
`[-1,1]`. -/
theorem abs_apply_le_one_of_mem_closedUnitBall
    {x : Fin n → ℝ}
    (hx : x ∈ Metric.closedBall (0 : Fin n → ℝ) 1) :
    ∀ i, |x i| ≤ 1 := by
  intro i
  have hnorm : ‖x‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hx
  simpa [Real.norm_eq_abs] using
    (norm_le_pi_norm x i).trans hnorm

/-- Explicit Lipschitz estimate for rational polynomial evaluation on the
finite-product unit cube. -/
theorem norm_ratMvPolynomialEval_sub_le_cubeGradientBound
    (p : MvPolynomial (Fin n) ℚ)
    {x y : Fin n → ℝ}
    (hx : x ∈ Metric.closedBall (0 : Fin n → ℝ) 1)
    (hy : y ∈ Metric.closedBall (0 : Fin n → ℝ) 1) :
    ‖ratMvPolynomialEval p y - ratMvPolynomialEval p x‖ ≤
      polynomialCubeGradientBound p * ‖y - x‖ := by
  apply (convex_closedBall (0 : Fin n → ℝ) 1).norm_image_sub_le_of_norm_fderiv_le
    (𝕜 := ℝ)
    (s := Metric.closedBall (0 : Fin n → ℝ) 1)
    (f := ratMvPolynomialEval p)
  · intro z hz
    exact (contDiff_ratMvPolynomialEval p).differentiable
      (by simp) z
  · intro z hz
    exact norm_fderiv_ratMvPolynomialEval_le_cubeGradientBound
      p z (abs_apply_le_one_of_mem_closedUnitBall hz)
  · exact hx
  · exact hy

/-- Absolute-value form of the same estimate. -/
theorem abs_ratMvPolynomialEval_sub_le_cubeGradientBound
    (p : MvPolynomial (Fin n) ℚ)
    {x y : Fin n → ℝ}
    (hx : x ∈ Metric.closedBall (0 : Fin n → ℝ) 1)
    (hy : y ∈ Metric.closedBall (0 : Fin n → ℝ) 1) :
    |ratMvPolynomialEval p y - ratMvPolynomialEval p x| ≤
      polynomialCubeGradientBound p * ‖y - x‖ := by
  simpa [Real.norm_eq_abs] using
    norm_ratMvPolynomialEval_sub_le_cubeGradientBound p hx hy

end

end HGAS
