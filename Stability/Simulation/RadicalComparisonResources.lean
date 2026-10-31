import Stability.Simulation.RadicalComparison
import Stability.Simulation.RadicalMajorantResources

/-!
# Degrees of the actual radical comparison weights

Coefficient masses change coefficients but introduce no variables. The
degree growth comes only from the constructed root-majorant radius and
the displayed polynomial power in each coordinate comparison weight.
-/

namespace Stability.Simulation.RadicalComparison

noncomputable section

variable {σ : Type*} [Fintype σ] {J : ℕ}

def cubeDegreeBound (d J : ℕ) : ℕ :=
  2 * (max 2 (RadicalMajorant.degreeBound d J) + 1)

theorem rootBound_totalDegree_le (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ) {d : ℕ}
    (hD : ∀ j, (D j).totalDegree ≤ d) (i : Fin J) :
    (rootBound D i).totalDegree ≤ max 2 (RadicalMajorant.degreeBound d J) := by
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · simp
  · exact ((MvPolynomial.totalDegree_rename_le Sum.inl _).trans
      (RadicalMajorant.majorants_totalDegree_le D hD i)).trans (Nat.le_max_right _ _)

theorem cubeRadius_totalDegree_le (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ) {d : ℕ}
    (hD : ∀ j, (D j).totalDegree ≤ d) :
    (cubeRadius D).totalDegree ≤ cubeDegreeBound d J :=
  RadicalMajorant.radius_totalDegree_le (rootBound D) (rootBound_totalDegree_le D hD)

theorem weight_totalDegree_le (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (p : MvPolynomial (σ ⊕ Fin J) ℚ) {d degree : ℕ}
    (hD : ∀ j, (D j).totalDegree ≤ d) (hp : p.totalDegree ≤ degree) (i : Fin J) :
    (weight D p i).totalDegree ≤ degree * cubeDegreeBound d J := by
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C, zero_add]
  exact (MvPolynomial.totalDegree_pow _ _).trans
    (Nat.mul_le_mul hp (cubeRadius_totalDegree_le D hD))

end

end Stability.Simulation.RadicalComparison
