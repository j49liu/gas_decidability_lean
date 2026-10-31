import Stability.Simulation.CompiledFormulaLift
import Stability.Simulation.TriangularLiftResources

/-!
# Degrees of the actual compiled formula lift

Squaring auxiliary variables doubles total degree at most. The selected
base fraction then has numerator degree bounded by the generated output
degree, and denominator degree bounded by precision degree times the
number of roots. These are bounds for the literal compiler output.
-/

namespace Stability.Simulation

noncomputable section

namespace RadicalProgram

variable {σ τ ι : Type*}

/-- Substitution by polynomials of degree at most `d` multiplies total
degree by at most `d`, including constant substitutions and the zero polynomial. -/
theorem bindPolynomial_totalDegree_le (f : σ → MvPolynomial τ ℚ)
    (p : MvPolynomial σ ℚ) {d : ℕ} (hf : ∀ i, (f i).totalDegree ≤ d) :
    (MvPolynomial.bind₁ f p).totalDegree ≤ d * p.totalDegree := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum p]
  rw [map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro e he
  rw [MvPolynomial.bind₁_monomial]
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C, zero_add]
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    (∑ i ∈ e.support, (f i ^ e i).totalDegree) ≤ ∑ i ∈ e.support, e i * d := by
      apply Finset.sum_le_sum
      intro i _
      exact (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hf i))
    _ = d * e.sum (fun _ n ↦ n) := by simp [Finsupp.sum, Finset.mul_sum, Nat.mul_comm]
    _ ≤ d * p.totalDegree := Nat.mul_le_mul_left d (MvPolynomial.le_totalDegree he)

theorem squareRootsPolynomial_totalDegree_le (p : MvPolynomial (σ ⊕ ι) ℚ) :
    (squareRootsPolynomial p).totalDegree ≤ 2 * p.totalDegree := by
  apply bindPolynomial_totalDegree_le
  intro i
  cases i <;> simp [squareRootVariable]

end RadicalProgram

namespace AbsFormula

variable {σ : Type*}

theorem extractRadicalFamily_exponents (L : MvPolynomial σ ℚ)
    (es : List (AbsFormula σ)) (start : ℕ) :
    ((extractRadicalFamily L es start).results.map PowerFraction.exponent) =
      es.map radicalCount := by
  induction es generalizing start with
  | nil => rfl
  | cons e es ih =>
      simp only [extractRadicalFamily, List.map_cons, extractRadicals_exponent, ih]

/-- The actual output denominator exponent list is exactly the list of
absolute-value counts, not merely an existence bound. -/
theorem finiteRadicalFamily_exponents (L : MvPolynomial σ ℚ) (es : List (AbsFormula σ)) :
    ((finiteRadicalFamily L es).outputs.map PowerFraction.exponent) =
      es.map radicalCount := by
  simpa only [finiteRadicalFamily, List.map_map, finiteFraction, Function.comp_def] using
    extractRadicalFamily_exponents L es 0

theorem liftRadicand_totalDegree_le (L : MvPolynomial σ ℚ) {d : ℕ}
    (hL : L.totalDegree ≤ d) (es : List (AbsFormula σ))
    (j : Fin (finiteRadicalFamily L es).rootCount) :
    (liftRadicand L es j).totalDegree ≤ 2 * radicalFamilyDegreeBound d es :=
  (RadicalProgram.squareRootsPolynomial_totalDegree_le _).trans
    (Nat.mul_le_mul_left 2 ((finiteRadicalFamily_totalDegree_le L hL es).1 j))

end AbsFormula

namespace CompiledFormulaLift

open AbsFormula PolynomialFraction

variable {σ : Type*}

theorem outputAt_numerator_totalDegree_le (L : MvPolynomial σ ℚ) {d : ℕ}
    (hL : L.totalDegree ≤ d) (es : List (AbsFormula σ)) (i : Fin es.length) :
    (outputAt L es i).numerator.totalDegree ≤ radicalFamilyDegreeBound d es :=
  (finiteRadicalFamily_totalDegree_le L hL es).2 _ (List.get_mem _ _)

theorem outputAt_exponent_le (L : MvPolynomial σ ℚ) (es : List (AbsFormula σ))
    (i : Fin es.length) : (outputAt L es i).exponent ≤ (finiteRadicalFamily L es).rootCount := by
  calc
    _ ≤ ((finiteRadicalFamily L es).outputs.map PowerFraction.exponent).sum :=
      List.le_sum_of_mem (List.mem_map.mpr ⟨outputAt L es i, List.get_mem _ _, rfl⟩)
    _ = (es.map radicalCount).sum := congrArg List.sum (finiteRadicalFamily_exponents L es)
    _ = _ := (finiteRadicalFamily_counts L es).1.symm

theorem baseFraction_numerator_totalDegree_le (L : MvPolynomial σ ℚ) {d : ℕ}
    (hL : L.totalDegree ≤ d) (es : List (AbsFormula σ)) (i : Fin es.length) :
    (baseFraction L es i).numerator.totalDegree ≤ 2 * radicalFamilyDegreeBound d es :=
  (RadicalProgram.squareRootsPolynomial_totalDegree_le _).trans
    (Nat.mul_le_mul_left 2 (outputAt_numerator_totalDegree_le L hL es i))

theorem baseFraction_denominator_totalDegree_le (L : MvPolynomial σ ℚ) {d : ℕ}
    (hL : L.totalDegree ≤ d) (es : List (AbsFormula σ)) (i : Fin es.length) :
    (baseFraction L es i).denominator.totalDegree ≤
      (finiteRadicalFamily L es).rootCount * d :=
  (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul
    (outputAt_exponent_le L es i) ((MvPolynomial.totalDegree_rename_le Sum.inl L).trans hL))

theorem baseFraction_degreesLE (L : MvPolynomial σ ℚ) {d : ℕ}
    (hL : L.totalDegree ≤ d) (es : List (AbsFormula σ)) (i : Fin es.length) :
    DegreesLE (baseFraction L es i)
      (max (2 * radicalFamilyDegreeBound d es) ((finiteRadicalFamily L es).rootCount * d)) :=
  ⟨(baseFraction_numerator_totalDegree_le L hL es i).trans (Nat.le_max_left _ _),
    (baseFraction_denominator_totalDegree_le L hL es i).trans (Nat.le_max_right _ _)⟩

end CompiledFormulaLift

end

end Stability.Simulation
