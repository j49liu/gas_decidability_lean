import Stability.Simulation.RadicalMajorant

/-!
# Degrees of the constructed radical majorants

The bounds follow the actual polynomial prefix updates. The recurrence
depends only on the radicand degree and root count, not on coefficients.
Constant radicands retain a zero-degree budget, including at zero roots.
-/

namespace Stability.Simulation.RadicalMajorant

noncomputable section

open AbsFormula

variable {σ : Type*} [Fintype σ] {J : ℕ}

theorem radius_totalDegree_le (bounds : Fin J → MvPolynomial σ ℚ) {b : ℕ}
    (hbounds : ∀ i, (bounds i).totalDegree ≤ b) :
    (radius bounds).totalDegree ≤ 2 * (b + 1) := by
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · exact coordinateEnvelope_totalDegree_le.trans (by omega)
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro i _
    exact (MvPolynomial.totalDegree_pow _ _).trans
      ((Nat.mul_le_mul_left 2 (hbounds i)).trans (by omega))

theorem step_totalDegree_le (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (bounds : Fin J → MvPolynomial σ ℚ) {d b : ℕ}
    (hD : ∀ j, (D j).totalDegree ≤ d) (hbounds : ∀ i, (bounds i).totalDegree ≤ b)
    (j : Fin J) : (step D bounds j).totalDegree ≤ 2 * d * (b + 1) := by
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le (by simp)
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C, zero_add]
  exact (MvPolynomial.totalDegree_pow _ _).trans
    ((Nat.mul_le_mul (hD j) (radius_totalDegree_le bounds hbounds)).trans_eq (by ring))

/-- Preserve the previous entries and allow the newly computed majorant
degree; the zero degree case stays exactly zero. -/
def degreeStep (d b : ℕ) : ℕ := max b (2 * d * (b + 1))

def degreeBound (d : ℕ) : ℕ → ℕ
  | 0 => 0
  | count + 1 => degreeStep d (degreeBound d count)

@[simp]
theorem degreeBound_zero_degree (count : ℕ) : degreeBound 0 count = 0 := by
  induction count with
  | zero => rfl
  | succ count ih => simp [degreeBound, degreeStep, ih]

theorem boundPrefix_totalDegree_le (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ) {d : ℕ}
    (hD : ∀ j, (D j).totalDegree ≤ d) (count : ℕ) (j : Fin J) :
    (boundPrefix D count j).totalDegree ≤ degreeBound d count := by
  induction count generalizing j with
  | zero => simp [boundPrefix, degreeBound]
  | succ count ih =>
      unfold boundPrefix
      split_ifs with h
      · by_cases hj : j = ⟨count, h⟩
        · subst j
          rw [Function.update_self]
          exact (step_totalDegree_le D _ hD ih _).trans (Nat.le_max_right _ _)
        · rw [Function.update_of_ne hj]
          exact (ih j).trans (Nat.le_max_left _ _)
      · exact (ih j).trans (Nat.le_max_left _ _)

/-- Input-independent algebraic resources for every actual majorant. -/
theorem majorants_totalDegree_le (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ) {d : ℕ}
    (hD : ∀ j, (D j).totalDegree ≤ d) (j : Fin J) :
    (majorants D j).totalDegree ≤ degreeBound d J :=
  boundPrefix_totalDegree_le D hD J j

end

end Stability.Simulation.RadicalMajorant
