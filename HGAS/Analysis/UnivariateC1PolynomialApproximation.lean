import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic

/-!
# Simultaneous approximation of a function and its derivative

This file proves the one-dimensional `C¹` polynomial approximation theorem
in a form designed for later tensor-product arguments.  The proof is
particularly transparent: approximate the continuous derivative by
Weierstrass, take a polynomial antiderivative, and use the mean-value
inequality to control the value error.
-/

namespace HGAS

noncomputable section

open Set
open scoped Polynomial

/-- A coefficientwise antiderivative with zero constant term. -/
def polynomialAntiderivative (q : ℝ[X]) : ℝ[X] :=
  q.sum fun k a ↦
    _root_.Polynomial.C (a / (k + 1 : ℕ)) *
      _root_.Polynomial.X ^ (k + 1)

/-- Differentiating `antiderivative` recovers the original polynomial. -/
theorem polynomialAntiderivative_derivative (q : ℝ[X]) :
    (polynomialAntiderivative q).derivative = q := by
  classical
  rw [polynomialAntiderivative, _root_.Polynomial.sum]
  simp only [map_sum, _root_.Polynomial.derivative_mul,
    _root_.Polynomial.derivative_C, zero_mul,
    _root_.Polynomial.derivative_X_pow, zero_add]
  conv_rhs =>
    rw [← _root_.Polynomial.sum_C_mul_X_pow_eq q]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Nat.cast_add, Nat.cast_one]
  have hk1 : (k + 1 : ℝ) ≠ 0 := by positivity
  rw [Nat.add_sub_cancel]
  rw [← mul_assoc, ← _root_.Polynomial.C_mul,
    div_mul_cancel₀ _ hk1]

/-- The chosen antiderivative vanishes at the origin. -/
@[simp]
theorem polynomialAntiderivative_eval_zero (q : ℝ[X]) :
    (polynomialAntiderivative q).eval 0 = 0 := by
  classical
  rw [polynomialAntiderivative, _root_.Polynomial.eval_sum]
  rw [_root_.Polynomial.sum]
  simp

/-! ## The `C¹` approximation theorem on an interval -/

/-- A continuously differentiable real function on a compact interval can
be approximated, simultaneously with its derivative, by one polynomial.

The separate function `g` is the derivative of `f`.  Stating the theorem
this way avoids any endpoint convention for `derivWithin` and makes the
continuity hypothesis used by Weierstrass explicit. -/
theorem exists_polynomial_near_with_derivative
    {a b : ℝ} (hab : a ≤ b) (f g : ℝ → ℝ)
    (hg : ContinuousOn g (Icc a b))
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (g x) x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ[X],
      (∀ x ∈ Icc a b, |p.eval x - f x| < ε) ∧
      (∀ x ∈ Icc a b, |p.derivative.eval x - g x| < ε) := by
  let L : ℝ := |b - a|
  let δ : ℝ := ε / (2 * (1 + L))
  have hL : 0 ≤ L := abs_nonneg _
  have hden : 0 < 2 * (1 + L) := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have hδ_lt_ε : δ < ε := by
    dsimp only [δ]
    rw [div_lt_iff₀ hden]
    nlinarith
  have hδL_lt_ε : δ * L < ε := by
    dsimp only [δ]
    rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith
  obtain ⟨q, hq⟩ :=
    exists_polynomial_near_of_continuousOn a b g hg δ hδ
  let A : ℝ[X] := polynomialAntiderivative q
  let p : ℝ[X] :=
    A + _root_.Polynomial.C (f a - A.eval a)
  have hpderiv : p.derivative = q := by
    simp only [p, map_add, _root_.Polynomial.derivative_C, add_zero,
      A, polynomialAntiderivative_derivative]
  have hpa : p.eval a = f a := by
    simp only [p, _root_.Polynomial.eval_add,
      _root_.Polynomial.eval_C]
    ring
  refine ⟨p, ?_, ?_⟩
  · intro x hx
    let h : ℝ → ℝ := fun y ↦ p.eval y - f y
    have hh :
        ∀ y ∈ Icc a b,
          HasDerivAt h (q.eval y - g y) y := by
      intro y hy
      have hp' :
          HasDerivAt (fun z : ℝ ↦ p.eval z) (q.eval y) y := by
        simpa only [hpderiv] using
          (_root_.Polynomial.hasDerivAt p y)
      exact hp'.sub (hf y hy)
    have hdiff :
        ∀ y ∈ Icc a b, DifferentiableAt ℝ h y :=
      fun y hy ↦ (hh y hy).differentiableAt
    have hbound :
        ∀ y ∈ Icc a b, ‖deriv h y‖ ≤ δ := by
      intro y hy
      rw [(hh y hy).deriv, Real.norm_eq_abs]
      exact (hq y hy).le
    have hmv :
        ‖h x - h a‖ ≤ δ * ‖x - a‖ :=
      _root_.Convex.norm_image_sub_le_of_norm_deriv_le
        hdiff hbound (convex_Icc a b)
          (left_mem_Icc.mpr hab) hx
    have hxa : ‖x - a‖ ≤ L := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hx.1)]
      change x - a ≤ |b - a|
      rw [abs_of_nonneg (sub_nonneg.mpr hab)]
      linarith [hx.2]
    have hscaled : δ * ‖x - a‖ ≤ δ * L :=
      mul_le_mul_of_nonneg_left hxa hδ.le
    have hzero : h a = 0 := by
      simp only [h, hpa, sub_self]
    rw [hzero, sub_zero, Real.norm_eq_abs] at hmv
    exact lt_of_le_of_lt (hmv.trans hscaled) hδL_lt_ε
  · intro x hx
    rw [hpderiv]
    exact (hq x hx).trans hδ_lt_ε

end

end HGAS
