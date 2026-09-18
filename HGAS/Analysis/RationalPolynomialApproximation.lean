import HGAS.Analysis.StrictPolynomialPositivity
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic

/-!
# Rational approximation of real homogeneous polynomials

The converse Lyapunov theorem used in the upper-bound argument naturally
produces a polynomial with real coefficients.  A finite certificate search,
however, must enumerate rational data.  The passage between the two is
elementary but important: approximate the finitely many nonzero
coefficients independently by rationals.

Because only monomials already present in the real polynomial are retained,
homogeneity is preserved exactly.  The coefficientwise error controls the
uniform error on the coordinate unit cube.
-/

namespace HGAS

open MvPolynomial
open scoped BigOperators

noncomputable section

variable {n D : ℕ}

/-- Every real polynomial can be approximated uniformly on the coordinate
unit cube by a rational polynomial.  If the original polynomial is
homogeneous, the approximant has exactly the same homogeneous degree. -/
theorem exists_rational_homogeneous_polynomial_cube_approximation
    (p : MvPolynomial (Fin n) ℝ) (ε : ℝ) (hε : 0 < ε)
    (hp : p.IsHomogeneous D) :
    ∃ q : MvPolynomial (Fin n) ℚ,
      q.IsHomogeneous D ∧
      ∀ x : Fin n → ℝ, (∀ i, |x i| ≤ 1) →
        |ratMvPolynomialEval q x - MvPolynomial.eval x p| < ε := by
  let δ : ℝ := ε / (p.support.card + 1)
  have hcard : (0 : ℝ) < p.support.card + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hcard
  choose a ha using
    fun e : Fin n →₀ ℕ ↦ exists_rat_near (p.coeff e) hδ
  let q : MvPolynomial (Fin n) ℚ :=
    ∑ e ∈ p.support, monomial e (a e)
  have hqhom : q.IsHomogeneous D := by
    apply IsHomogeneous.sum p.support
      (fun e ↦ monomial e (a e)) D
    intro e he
    apply isHomogeneous_monomial
    rw [Finsupp.degree_eq_weight_one]
    exact hp (mem_support_iff.mp he)
  refine ⟨q, hqhom, ?_⟩
  intro x hx
  rw [show p = ∑ e ∈ p.support, monomial e (p.coeff e) by
    exact p.support_sum_monomial_coeff.symm]
  simp only [q, ratMvPolynomialEval, map_sum, map_monomial,
    eval_monomial]
  calc
    |(∑ e ∈ p.support,
        (a e : ℝ) * ∏ i ∈ e.support, x i ^ e i) -
      ∑ e ∈ p.support,
        p.coeff e * ∏ i ∈ e.support, x i ^ e i| =
        |∑ e ∈ p.support,
          ((a e : ℝ) - p.coeff e) *
            ∏ i ∈ e.support, x i ^ e i| := by
      congr 1
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro e he
      ring
    _ ≤ ∑ e ∈ p.support,
        |((a e : ℝ) - p.coeff e) *
          ∏ i ∈ e.support, x i ^ e i| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ p.support, δ := by
      apply Finset.sum_le_sum
      intro e he
      rw [abs_mul]
      have hmonomial :
          |∏ i ∈ e.support, x i ^ e i| ≤ 1 := by
        rw [Finset.abs_prod]
        apply Finset.prod_le_one
        · intro i hi
          positivity
        · intro i hi
          rw [abs_pow]
          exact pow_le_one₀ (abs_nonneg _) (hx i)
      have hcoeff : |(a e : ℝ) - p.coeff e| < δ := by
        simpa [abs_sub_comm] using ha e
      exact
        (mul_le_of_le_one_right (abs_nonneg _)
          hmonomial).trans hcoeff.le
    _ = p.support.card * δ := by simp
    _ < ε := by
      dsimp only [δ]
      have hcard_le :
          (p.support.card : ℝ) < p.support.card + 1 := by
        norm_num
      calc
        (p.support.card : ℝ) * (ε / (p.support.card + 1)) =
            ε * ((p.support.card : ℝ) /
              (p.support.card + 1)) := by ring
        _ < ε * 1 := by
          exact mul_lt_mul_of_pos_left
            ((div_lt_one hcard).2 hcard_le) hε
        _ = ε := mul_one ε

end

end HGAS
