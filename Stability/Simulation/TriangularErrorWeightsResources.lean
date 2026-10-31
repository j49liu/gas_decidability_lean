import Stability.Simulation.TriangularErrorWeights

/-!
# Degrees of the constructed triangular error weights

Every recursive substitution adds at most the common coefficient degree.
Thus the actual stored weights have degree at most root count times that
degree, without requiring a positive degree or a nonempty root family.
-/

namespace Stability.Simulation.TriangularErrorWeights

noncomputable section

variable {τ : Type*} {J : ℕ}

theorem step_totalDegree_le (C : Fin J → Fin J → MvPolynomial τ ℚ)
    (previous : Fin J → MvPolynomial τ ℚ) {c b : ℕ}
    (hC : ∀ j i, (C j i).totalDegree ≤ c)
    (hprevious : ∀ i, (previous i).totalDegree ≤ b) (j : Fin J) :
    (step C previous j).totalDegree ≤ c + b := by
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le (by simp)
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add (hC j i) (hprevious i))

theorem weightPrefix_totalDegree_le (C : Fin J → Fin J → MvPolynomial τ ℚ) {c : ℕ}
    (hC : ∀ j i, (C j i).totalDegree ≤ c) (count : ℕ) (j : Fin J) :
    (weightPrefix C count j).totalDegree ≤ count * c := by
  induction count generalizing j with
  | zero => simp [weightPrefix]
  | succ count ih =>
      unfold weightPrefix
      split_ifs with h
      · by_cases hj : j = ⟨count, h⟩
        · subst j
          rw [Function.update_self]
          exact (step_totalDegree_le C _ hC ih _).trans_eq (by ring)
        · rw [Function.update_of_ne hj]
          exact (ih j).trans (Nat.mul_le_mul_right c (Nat.le_succ count))
      · exact (ih j).trans (Nat.mul_le_mul_right c (Nat.le_succ count))

theorem weights_totalDegree_le (C : Fin J → Fin J → MvPolynomial τ ℚ) {c : ℕ}
    (hC : ∀ j i, (C j i).totalDegree ≤ c) (j : Fin J) :
    (weights C j).totalDegree ≤ J * c := weightPrefix_totalDegree_le C hC J j

end

end Stability.Simulation.TriangularErrorWeights
