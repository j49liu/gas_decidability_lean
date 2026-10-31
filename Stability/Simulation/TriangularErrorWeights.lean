import Stability.Simulation.PolynomialEnvelope

/-!
# Explicit weights for triangular error propagation

If the j-th error is at most a common residual bound plus a nonnegative
linear combination of earlier errors, finite substitution gives a bound
Wⱼ times the residual. The Wⱼ are actual rational polynomials, defined
by the same triangular recursion; they are not chosen from an existence
statement. The construction also covers an empty system.
-/

namespace Stability.Simulation.TriangularErrorWeights

noncomputable section

open AbsFormula

variable {τ : Type*} {J : ℕ}

def step (C : Fin J → Fin J → MvPolynomial τ ℚ)
    (previous : Fin J → MvPolynomial τ ℚ) (j : Fin J) : MvPolynomial τ ℚ :=
  1 + ∑ i ∈ Finset.univ.filter (fun i : Fin J ↦ i.val < j.val), C j i * previous i

def weightPrefix (C : Fin J → Fin J → MvPolynomial τ ℚ) :
    ℕ → Fin J → MvPolynomial τ ℚ
  | 0 => fun _ ↦ 0
  | count + 1 =>
      let previous := weightPrefix C count
      if h : count < J then Function.update previous ⟨count, h⟩
        (step C previous ⟨count, h⟩) else previous

def weights (C : Fin J → Fin J → MvPolynomial τ ℚ) : Fin J → MvPolynomial τ ℚ :=
  weightPrefix C J

theorem prefix_succ_of_ne (C : Fin J → Fin J → MvPolynomial τ ℚ)
    (count : ℕ) (i : Fin J) (hi : i.val ≠ count) :
    weightPrefix C (count + 1) i = weightPrefix C count i := by
  change (if h : count < J then Function.update (weightPrefix C count) ⟨count, h⟩
    (step C (weightPrefix C count) ⟨count, h⟩) else weightPrefix C count) i = _
  split_ifs with h
  · apply Function.update_of_ne
    intro heq
    exact hi (congrArg Fin.val heq)
  · rfl

theorem prefix_eq_of_le (C : Fin J → Fin J → MvPolynomial τ ℚ)
    {a b : ℕ} (hab : a ≤ b) (i : Fin J) (hi : i.val < a) :
    weightPrefix C b i = weightPrefix C a i := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih => rw [prefix_succ_of_ne C b i (by omega), ih]

theorem weights_eq (C : Fin J → Fin J → MvPolynomial τ ℚ) (j : Fin J) :
    weights C j = 1 + ∑ i ∈ Finset.univ.filter (fun i : Fin J ↦ i.val < j.val),
      C j i * weights C i := by
  have hstep : weights C j = step C (weightPrefix C j.val) j := by
    rw [weights, prefix_eq_of_le C (a := j.val + 1) (by omega) j (by omega)]
    simp [weightPrefix, j.isLt]
  rw [hstep, step]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [weights, prefix_eq_of_le C j.isLt.le i (Finset.mem_filter.mp hi).2]

theorem weights_value (C : Fin J → Fin J → MvPolynomial τ ℚ)
    (y : τ → ℝ) (j : Fin J) :
    polynomialValue y (weights C j) =
      1 + ∑ i ∈ Finset.univ.filter (fun i : Fin J ↦ i.val < j.val),
        polynomialValue y (C j i) * polynomialValue y (weights C i) := by
  rw [weights_eq]
  simp [polynomialValue]

theorem weights_one_le (C : Fin J → Fin J → MvPolynomial τ ℚ)
    (y : τ → ℝ) (hC : ∀ j i, 0 ≤ polynomialValue y (C j i)) :
    ∀ j, 1 ≤ polynomialValue y (weights C j) := by
  apply Fin.strong_induction_on
  intro j ih
  rw [weights_value]
  apply le_add_of_nonneg_right
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hC j i) (zero_le_one.trans (ih i (Finset.mem_filter.mp hi).2))

/-- Triangular substitution with a common residual bound. No smallness
condition on the coefficients or the residual is needed. -/
theorem error_le_weight_mul (C : Fin J → Fin J → MvPolynomial τ ℚ)
    (y : τ → ℝ) (hC : ∀ j i, 0 ≤ polynomialValue y (C j i))
    (error : Fin J → ℝ) (E : ℝ)
    (herror : ∀ j, error j ≤ E +
      ∑ i ∈ Finset.univ.filter (fun i : Fin J ↦ i.val < j.val),
        polynomialValue y (C j i) * error i) :
    ∀ j, error j ≤ polynomialValue y (weights C j) * E := by
  apply Fin.strong_induction_on
  intro j ih
  apply (herror j).trans
  calc
    E + ∑ i ∈ Finset.univ.filter (fun i : Fin J ↦ i.val < j.val),
        polynomialValue y (C j i) * error i ≤
      E + ∑ i ∈ Finset.univ.filter (fun i : Fin J ↦ i.val < j.val),
        polynomialValue y (C j i) * (polynomialValue y (weights C i) * E) := by
      apply add_le_add_right
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (ih i (Finset.mem_filter.mp hi).2) (hC j i)
    _ = polynomialValue y (weights C j) * E := by
      rw [weights_value, add_mul, one_mul, Finset.sum_mul]
      simp only [mul_assoc]

end

end Stability.Simulation.TriangularErrorWeights
