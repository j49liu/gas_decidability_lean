import Stability.Simulation.PolynomialFraction

/-!
# Explicit positive common-denominator clearing

A finite family of polynomial fractions is cleared using the product of
its denominators. If each denominator is at least one, so is the product.
Every cleared numerator is a literal polynomial and equals the original
value multiplied by that same positive product. This applies jointly to
field coordinates and an output; it does not by itself assert a global
time-reparametrization theorem.
-/

namespace Stability.Simulation.PolynomialFraction

noncomputable section

open AbsFormula

variable {σ ι : Type*} [Fintype ι] [DecidableEq ι]

def commonDenominator (fs : ι → PolynomialFraction σ) : MvPolynomial σ ℚ :=
  ∏ i, (fs i).denominator

def clearedNumerator (fs : ι → PolynomialFraction σ) (i : ι) : MvPolynomial σ ℚ :=
  (fs i).numerator * ∏ j ∈ Finset.univ.erase i, (fs j).denominator

theorem denominator_mul_clearedNumerator (fs : ι → PolynomialFraction σ) (i : ι) :
    (fs i).denominator * clearedNumerator fs i =
      commonDenominator fs * (fs i).numerator := by
  unfold clearedNumerator commonDenominator
  rw [mul_left_comm, Finset.mul_prod_erase Finset.univ
    (fun j ↦ (fs j).denominator) (Finset.mem_univ i)]
  exact mul_comm _ _

omit [DecidableEq ι] in
/-- The common multiplier is positive on every state where the original
denominators satisfy their proved lower bounds. -/
theorem commonDenominator_one_le (fs : ι → PolynomialFraction σ) (x : σ → ℝ)
    (hden : ∀ i, 1 ≤ polynomialValue x (fs i).denominator) :
    1 ≤ polynomialValue x (commonDenominator fs) := by
  simp only [commonDenominator, polynomialValue, MvPolynomial.eval₂_prod]
  exact Finset.one_le_prod (fun i _ ↦ hden i)

/-- Clearing multiplies every coordinate value by the same explicit
positive clock factor, with no cancellation convention. -/
theorem clearedNumerator_value (fs : ι → PolynomialFraction σ) (x : σ → ℝ)
    (hden : ∀ i, 1 ≤ polynomialValue x (fs i).denominator) (i : ι) :
    polynomialValue x (clearedNumerator fs i) =
      polynomialValue x (commonDenominator fs) * value x (fs i) := by
  have h := congrArg (polynomialValue x) (denominator_mul_clearedNumerator fs i)
  simp only [polynomialValue, MvPolynomial.eval₂_mul] at h
  have hne : polynomialValue x (fs i).denominator ≠ 0 :=
    ne_of_gt (zero_lt_one.trans_le (hden i))
  unfold value
  rw [← mul_div_assoc]
  apply (eq_div_iff hne).mpr
  simpa only [polynomialValue, mul_comm] using h

omit [DecidableEq ι] in
theorem commonDenominator_totalDegree_le (fs : ι → PolynomialFraction σ) :
    (commonDenominator fs).totalDegree ≤ ∑ i, (fs i).denominator.totalDegree :=
  MvPolynomial.totalDegree_finsetProd _ _

theorem clearedNumerator_totalDegree_le (fs : ι → PolynomialFraction σ) (i : ι) :
    (clearedNumerator fs i).totalDegree ≤ (fs i).numerator.totalDegree +
      ∑ j ∈ Finset.univ.erase i, (fs j).denominator.totalDegree :=
  (MvPolynomial.totalDegree_mul _ _).trans
    (Nat.add_le_add_left (MvPolynomial.totalDegree_finsetProd _ _) _)

end

end Stability.Simulation.PolynomialFraction
