import Stability.Simulation.RadicalDefectBounds
import Stability.Simulation.RadicalComparisonResources
import Stability.Simulation.TriangularErrorWeightsResources
import Stability.Simulation.CompiledLiftResources

/-!
# Degrees of the actual quartic-defect error construction

The bounds apply to the constructed defect energy, triangular root-error
weights, and global polynomial-output weight. They use only root count,
radicand degree, and output degree; neither coefficients nor root values
enter the budgets. No penalty field is constructed in this module.
-/

namespace Stability.Simulation.RadicalDefectBounds

noncomputable section

variable {σ : Type*} [Fintype σ] {J : ℕ}

omit [Fintype σ] in
theorem defect_totalDegree_le (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ) {d : ℕ}
    (hD : ∀ j, (D j).totalDegree ≤ d) (j : Fin J) :
    (defect D j).totalDegree ≤ max 4 (2 * d) := by
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · simp
  · exact ((RadicalProgram.squareRootsPolynomial_totalDegree_le _).trans
      (Nat.mul_le_mul_left 2 (hD j))).trans (Nat.le_max_right _ _)

omit [Fintype σ] in
theorem defectEnergy_totalDegree_le (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ) {d : ℕ}
    (hD : ∀ j, (D j).totalDegree ≤ d) :
    (defectEnergy D).totalDegree ≤ 2 * max 4 (2 * d) := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j _
  exact (MvPolynomial.totalDegree_pow _ _).trans
    (Nat.mul_le_mul_left 2 (defect_totalDegree_le D hD j))

theorem coefficients_totalDegree_le (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ) {d : ℕ}
    (hD : ∀ j, (D j).totalDegree ≤ d) (j i : Fin J) :
    (coefficients D j i).totalDegree ≤ d * RadicalComparison.cubeDegreeBound d J :=
  RadicalComparison.weight_totalDegree_le D (D j) hD (hD j) i

theorem rootWeights_totalDegree_le (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ) {d : ℕ}
    (hD : ∀ j, (D j).totalDegree ≤ d) (j : Fin J) :
    (rootWeights D j).totalDegree ≤ J * (d * RadicalComparison.cubeDegreeBound d J) :=
  TriangularErrorWeights.weights_totalDegree_le (coefficients D)
    (coefficients_totalDegree_le D hD) j

theorem polynomialWeight_totalDegree_le (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (p : MvPolynomial (σ ⊕ Fin J) ℚ) {d degree : ℕ}
    (hD : ∀ j, (D j).totalDegree ≤ d) (hp : p.totalDegree ≤ degree) :
    (polynomialWeight D p).totalDegree ≤
      degree * RadicalComparison.cubeDegreeBound d J +
        J * (d * RadicalComparison.cubeDegreeBound d J) := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  exact (MvPolynomial.totalDegree_mul _ _).trans
    (Nat.add_le_add (RadicalComparison.weight_totalDegree_le D p hD hp i)
      (rootWeights_totalDegree_le D hD i))

end

end Stability.Simulation.RadicalDefectBounds
