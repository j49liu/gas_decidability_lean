import Stability.Simulation.CompiledFormulaLift
import Stability.Simulation.RadicalDefectBounds

/-!
# Off-graph error bounds for the actual formula compiler

Each output has a constructed polynomial error weight. Division by the
precision power cannot enlarge the error, since the precision is at
least one. Summing the weights gives one polynomial, at least one,
that controls every member of the compiled formula family at every
auxiliary state. All triangularity and root equations are discharged
using the compiler's theorems.
-/

namespace Stability.Simulation.CompiledFormulaLift

noncomputable section

open AbsFormula RadicalDefectBounds

variable {σ : Type*} [Fintype σ]

def outputErrorWeight (L : MvPolynomial σ ℚ) (es : List (AbsFormula σ))
    (i : Fin es.length) : MvPolynomial (σ ⊕ Fin (finiteRadicalFamily L es).rootCount) ℚ :=
  polynomialWeight (finiteRadicalFamily L es).radicands (outputAt L es i).numerator

theorem outputErrorWeight_nonneg (L : MvPolynomial σ ℚ) (es : List (AbsFormula σ))
    (i : Fin es.length) (y : σ ⊕ Fin (finiteRadicalFamily L es).rootCount → ℝ) :
    0 ≤ polynomialValue y (outputErrorWeight L es i) :=
  polynomialWeight_nonneg _ _ y

/-- Error in a literal compiled rational output, without a graph condition. -/
theorem baseFraction_error_le (L : MvPolynomial σ ℚ) (es : List (AbsFormula σ))
    (x : σ → ℝ) (hL : 1 ≤ polynomialValue x L)
    (w : Fin (finiteRadicalFamily L es).rootCount → ℝ) (i : Fin es.length) :
    |PolynomialFraction.value (Sum.elim x w) (baseFraction L es i) -
      smoothEval (polynomialValue x L) x (es.get i)| ≤
      polynomialValue (Sum.elim x w) (outputErrorWeight L es i) *
        defectNorm (finiteRadicalFamily L es).radicands (Sum.elim x w) := by
  have hdiff := polynomial_error_le_weight_mul_norm (finiteRadicalFamily L es).radicands
    (finiteRadicalFamily_radicand_dependsBelow L es) x w (finiteRadicalRoots L es x)
    (fun r j ↦ finiteRadicalFamily_radicands_one_le L es x r hL j)
    (finiteRadicalRoots_equation L es x) (outputAt L es i).numerator
  rw [← outputAt_value L es x (zero_lt_one.trans_le hL) i]
  have hden : polynomialValue (Sum.elim x w)
      (MvPolynomial.rename Sum.inl L ^ (outputAt L es i).exponent) =
      polynomialValue x L ^ (outputAt L es i).exponent := by
    simp [polynomialValue, MvPolynomial.eval₂_rename, Function.comp_def]
  change |polynomialValue (Sum.elim x w)
      (RadicalProgram.squareRootsPolynomial (outputAt L es i).numerator) /
      polynomialValue (Sum.elim x w)
        (MvPolynomial.rename Sum.inl L ^ (outputAt L es i).exponent) -
      polynomialValue (Sum.elim x (finiteRadicalRoots L es x)) (outputAt L es i).numerator /
        polynomialValue x L ^ (outputAt L es i).exponent| ≤ _
  rw [RadicalProgram.squareRootsPolynomial_value, hden, ← sub_div, abs_div,
    abs_of_nonneg (pow_nonneg (zero_le_one.trans hL) _)]
  exact (div_le_self (abs_nonneg _) (one_le_pow₀ hL)).trans hdiff

def familyErrorWeight (L : MvPolynomial σ ℚ) (es : List (AbsFormula σ)) :
    MvPolynomial (σ ⊕ Fin (finiteRadicalFamily L es).rootCount) ℚ :=
  1 + ∑ i : Fin es.length, outputErrorWeight L es i

theorem familyErrorWeight_value (L : MvPolynomial σ ℚ) (es : List (AbsFormula σ))
    (y : σ ⊕ Fin (finiteRadicalFamily L es).rootCount → ℝ) :
    polynomialValue y (familyErrorWeight L es) =
      1 + ∑ i : Fin es.length, polynomialValue y (outputErrorWeight L es i) := by
  simp [familyErrorWeight, polynomialValue]

theorem familyErrorWeight_one_le (L : MvPolynomial σ ℚ) (es : List (AbsFormula σ))
    (y : σ ⊕ Fin (finiteRadicalFamily L es).rootCount → ℝ) :
    1 ≤ polynomialValue y (familyErrorWeight L es) := by
  rw [familyErrorWeight_value]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ ↦ outputErrorWeight_nonneg L es i y)

theorem outputErrorWeight_le_family (L : MvPolynomial σ ℚ) (es : List (AbsFormula σ))
    (y : σ ⊕ Fin (finiteRadicalFamily L es).rootCount → ℝ) (i : Fin es.length) :
    polynomialValue y (outputErrorWeight L es i) ≤ polynomialValue y (familyErrorWeight L es) := by
  rw [familyErrorWeight_value]
  exact (Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) ↦
    outputErrorWeight_nonneg L es j y) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)

theorem baseFraction_error_le_family (L : MvPolynomial σ ℚ) (es : List (AbsFormula σ))
    (x : σ → ℝ) (hL : 1 ≤ polynomialValue x L)
    (w : Fin (finiteRadicalFamily L es).rootCount → ℝ) (i : Fin es.length) :
    |PolynomialFraction.value (Sum.elim x w) (baseFraction L es i) -
      smoothEval (polynomialValue x L) x (es.get i)| ≤
      polynomialValue (Sum.elim x w) (familyErrorWeight L es) *
        defectNorm (finiteRadicalFamily L es).radicands (Sum.elim x w) :=
  (baseFraction_error_le L es x hL w i).trans
    (mul_le_mul_of_nonneg_right (outputErrorWeight_le_family L es (Sum.elim x w) i)
      (Real.sqrt_nonneg _))

end

end Stability.Simulation.CompiledFormulaLift
