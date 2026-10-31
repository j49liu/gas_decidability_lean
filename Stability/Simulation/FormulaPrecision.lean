import Stability.Simulation.FormulaResources
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# A common polynomial precision for a finite family of formulas

Each formula has a nonnegative polynomial error majorant `Vᵢ`.
The single precision `L = ε⁻¹ (1 + θ²) (1 + ∑ Vᵢ)` therefore makes
every smoothing error at most `ε / (1 + θ²)`. Along a unit-speed clock,
this bound has total mass less than `ε * π` on every finite interval.

These statements construct the precision and prove its error estimate;
they do not assume a previously supplied approximation bound.
-/

namespace Stability.Simulation.AbsFormula

noncomputable section

variable {σ ι : Type*} [Fintype ι]

/-- A strictly positive common majorant for all coordinate errors. -/
def commonErrorMajorant (formulas : ι → AbsFormula σ) : MvPolynomial σ ℚ :=
  1 + ∑ i, (majorants (formulas i)).2

/-- A rational polynomial precision, using the coordinate `clock` to
make the error integrable along a unit-speed clock trajectory. -/
def precisionPolynomial (formulas : ι → AbsFormula σ) (clock : σ) (ε : ℚ) :
    MvPolynomial σ ℚ :=
  MvPolynomial.C ε⁻¹ * (1 + MvPolynomial.X clock ^ 2) * commonErrorMajorant formulas

/-- A shape-dependent degree bound for a finite family of formulas. -/
def familyDegreeBound (formulas : ι → AbsFormula σ) : ℕ :=
  Finset.univ.sup (fun i ↦ majorantDegreeBound (formulas i))

theorem commonErrorMajorant_totalDegree_le (formulas : ι → AbsFormula σ) :
    (commonErrorMajorant formulas).totalDegree ≤ familyDegreeBound formulas := by
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le (by simp)
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  exact (majorants_totalDegree_le (formulas i)).2.trans
    (Finset.le_sup (f := fun i ↦ majorantDegreeBound (formulas i)) hi)

/-- Neither the precision coefficient nor any other rational constant
value affects this degree bound. -/
theorem precisionPolynomial_totalDegree_le (formulas : ι → AbsFormula σ)
    (clock : σ) (ε : ℚ) :
    (precisionPolynomial formulas clock ε).totalDegree ≤ 2 + familyDegreeBound formulas := by
  apply (MvPolynomial.totalDegree_mul _ _).trans
  apply Nat.add_le_add _ (commonErrorMajorant_totalDegree_le formulas)
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C, zero_add]
  exact (MvPolynomial.totalDegree_add _ _).trans (by simp)

theorem familyDegreeBound_eq_of_eraseConstants_eq
    {formulas other : ι → AbsFormula σ}
    (hshape : ∀ i, eraseConstants (formulas i) = eraseConstants (other i)) :
    familyDegreeBound formulas = familyDegreeBound other := by
  unfold familyDegreeBound
  congr 1
  funext i
  exact (resources_eq_of_eraseConstants_eq (hshape i)).1

theorem commonErrorMajorant_value (formulas : ι → AbsFormula σ) (x : σ → ℝ) :
    polynomialValue x (commonErrorMajorant formulas) =
      1 + ∑ i, polynomialValue x (majorants (formulas i)).2 := by
  simp [commonErrorMajorant, polynomialValue]

theorem one_le_commonErrorMajorant (formulas : ι → AbsFormula σ) (x : σ → ℝ) :
    1 ≤ polynomialValue x (commonErrorMajorant formulas) := by
  rw [commonErrorMajorant_value]
  have hnonneg : 0 ≤ ∑ i, polynomialValue x (majorants (formulas i)).2 :=
    Finset.sum_nonneg (fun i _ ↦ (majorants_correct (formulas i) x (L := 1) le_rfl).2.1)
  linarith

theorem errorMajorant_le_common (formulas : ι → AbsFormula σ) (x : σ → ℝ) (i : ι) :
    polynomialValue x (majorants (formulas i)).2 ≤
      polynomialValue x (commonErrorMajorant formulas) := by
  rw [commonErrorMajorant_value]
  have hsum := Finset.single_le_sum
    (fun j (_ : j ∈ Finset.univ) ↦
      (majorants_correct (formulas j) x (L := 1) le_rfl).2.1)
    (Finset.mem_univ i)
  linarith

theorem precisionPolynomial_value (formulas : ι → AbsFormula σ)
    (clock : σ) (ε : ℚ) (x : σ → ℝ) :
    polynomialValue x (precisionPolynomial formulas clock ε) =
      (ε : ℝ)⁻¹ * (1 + (x clock) ^ 2) * polynomialValue x (commonErrorMajorant formulas) := by
  simp [precisionPolynomial, polynomialValue]

/-- The constructed precision is at least one at every real state. -/
theorem one_le_precisionPolynomial (formulas : ι → AbsFormula σ)
    (clock : σ) {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1) (x : σ → ℝ) :
    1 ≤ polynomialValue x (precisionPolynomial formulas clock ε) := by
  have hεReal : (0 : ℝ) < ε := by exact_mod_cast hε
  have hεRealOne : (ε : ℝ) ≤ 1 := by exact_mod_cast hεOne
  have hinv : 1 ≤ (ε : ℝ)⁻¹ := (one_le_inv₀ hεReal).mpr hεRealOne
  rw [precisionPolynomial_value]
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hinv (by nlinarith [sq_nonneg (x clock)]))
    (one_le_commonErrorMajorant formulas x)

/-- The same polynomial precision controls every formula, including
states far from the discrete simulation set. -/
theorem smoothEval_error_le_clockTail (formulas : ι → AbsFormula σ)
    (clock : σ) {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1)
    (x : σ → ℝ) (i : ι) :
    |smoothEval (polynomialValue x (precisionPolynomial formulas clock ε)) x (formulas i) -
        eval x (formulas i)| ≤ (ε : ℝ) / (1 + (x clock) ^ 2) := by
  let L := polynomialValue x (precisionPolynomial formulas clock ε)
  let V := polynomialValue x (commonErrorMajorant formulas)
  have hL : 1 ≤ L := one_le_precisionPolynomial formulas clock hε hεOne x
  have hV : 1 ≤ V := one_le_commonErrorMajorant formulas x
  have hεReal : (0 : ℝ) < ε := by exact_mod_cast hε
  have hclock : 0 < 1 + (x clock) ^ 2 := by positivity
  have hmajorant := (majorants_correct (formulas i) x hL).2.2.2.2
  calc
    _ ≤ polynomialValue x (majorants (formulas i)).2 * L⁻¹ := hmajorant
    _ ≤ V * L⁻¹ := mul_le_mul_of_nonneg_right (errorMajorant_le_common formulas x i)
      (inv_nonneg.mpr (zero_le_one.trans hL))
    _ = (ε : ℝ) / (1 + (x clock) ^ 2) := by
      dsimp [L, V]
      rw [precisionPolynomial_value]
      field_simp [ne_of_gt hεReal, ne_of_gt hclock, ne_of_gt (zero_lt_one.trans_le hV)]
      exact div_self (ne_of_gt (zero_lt_one.trans_le hV))

/-- Exact finite-interval mass of the clock-tail error bound. -/
theorem integral_clockTail (ε offset a b : ℝ) :
    (∫ t in a..b, ε / (1 + (offset + t) ^ 2)) =
      ε * (Real.arctan (offset + b) - Real.arctan (offset + a)) := by
  simp_rw [div_eq_mul_inv]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_add_left (fun t : ℝ ↦ (1 + t ^ 2)⁻¹) offset]
  rw [integral_inv_one_add_sq]

/-- The perturbation budget is uniform in both the interval and the
initial clock offset. No nonnegative-offset hypothesis is needed. -/
theorem integral_clockTail_lt_pi {ε : ℝ} (hε : 0 < ε) (offset a b : ℝ) :
    (∫ t in a..b, ε / (1 + (offset + t) ^ 2)) < ε * Real.pi := by
  rw [integral_clockTail]
  apply mul_lt_mul_of_pos_left _ hε
  linarith [Real.arctan_lt_pi_div_two (offset + b),
    Real.neg_pi_div_two_lt_arctan (offset + a)]

end

end Stability.Simulation.AbsFormula
