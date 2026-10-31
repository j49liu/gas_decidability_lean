import Stability.Simulation.RadicalComparison
import Stability.Simulation.TriangularErrorWeights
import Stability.Simulation.RadicalInvariant

/-!
# Global error bounds from quartic defects

The auxiliary variables need not lie near the canonical root graph.
For each root, the quartic defect bounds the error relative to its
current radicand. The radicand's dependence on earlier roots adds a
triangular error term. Explicit polynomial substitution then bounds all
root errors, and every polynomial output error, by a polynomial weight
times the Euclidean norm of the quartic defects.
-/

namespace Stability.Simulation.RadicalDefectBounds

noncomputable section

open AbsFormula

variable {σ : Type*} {J : ℕ}

def defect (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ) (j : Fin J) :
    MvPolynomial (σ ⊕ Fin J) ℚ :=
  MvPolynomial.X (Sum.inr j) ^ 4 - RadicalProgram.squareRootsPolynomial (D j)

theorem defect_value (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (x : σ → ℝ) (w : Fin J → ℝ) (j : Fin J) :
    polynomialValue (Sum.elim x w) (defect D j) =
      w j ^ 4 - polynomialValue (Sum.elim x (fun i ↦ w i ^ 2)) (D j) := by
  simp only [defect, polynomialValue, MvPolynomial.eval₂_sub,
    MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X, Sum.elim_inr]
  rw [← polynomialValue, RadicalProgram.squareRootsPolynomial_value]
  rfl

def defectEnergy (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ) :
    MvPolynomial (σ ⊕ Fin J) ℚ := ∑ j, defect D j ^ 2

theorem defectEnergy_value (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (y : σ ⊕ Fin J → ℝ) :
    polynomialValue y (defectEnergy D) = ∑ j, polynomialValue y (defect D j) ^ 2 := by
  simp [defectEnergy, polynomialValue]

theorem defectEnergy_nonneg (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (y : σ ⊕ Fin J → ℝ) : 0 ≤ polynomialValue y (defectEnergy D) := by
  rw [defectEnergy_value]
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

def defectNorm (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (y : σ ⊕ Fin J → ℝ) : ℝ := Real.sqrt (polynomialValue y (defectEnergy D))

theorem abs_defect_le_norm (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (y : σ ⊕ Fin J → ℝ) (j : Fin J) :
    |polynomialValue y (defect D j)| ≤ defectNorm D y := by
  have hsingle : polynomialValue y (defect D j) ^ 2 ≤ polynomialValue y (defectEnergy D) := by
    rw [defectEnergy_value]
    exact Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) ↦
      sq_nonneg (polynomialValue y (defect D i))) (Finset.mem_univ j)
  have h := Real.sqrt_le_sqrt hsingle
  simpa only [Real.sqrt_sq_eq_abs] using h

variable [Fintype σ]

def coefficients (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ) (j i : Fin J) :
    MvPolynomial (σ ⊕ Fin J) ℚ := RadicalComparison.weight D (D j) i

def rootWeights (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ) :
    Fin J → MvPolynomial (σ ⊕ Fin J) ℚ :=
  TriangularErrorWeights.weights (coefficients D)

theorem rootWeights_one_le (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (y : σ ⊕ Fin J → ℝ) (j : Fin J) :
    1 ≤ polynomialValue y (rootWeights D j) :=
  TriangularErrorWeights.weights_one_le _ y
    (fun j i ↦ RadicalComparison.weight_nonneg D (D j) y i) j

/-- The actual root error satisfies a triangular inequality at every
state, not only in a neighborhood of the constraint graph. -/
theorem root_error_step (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (htri : ∀ j, RadicalProgram.FiniteDependsBelow (D j) j.val)
    (x : σ → ℝ) (w roots : Fin J → ℝ)
    (hD : ∀ r j, 1 ≤ polynomialValue (Sum.elim x r) (D j))
    (hroots : ∀ j, roots j = Real.sqrt (polynomialValue (Sum.elim x roots) (D j)))
    (j : Fin J) :
    |w j ^ 2 - roots j| ≤ |polynomialValue (Sum.elim x w) (defect D j)| +
      ∑ i ∈ Finset.univ.filter (fun i : Fin J ↦ i.val < j.val),
        polynomialValue (Sum.elim x w) (coefficients D j i) * |w i ^ 2 - roots i| := by
  let A := polynomialValue (Sum.elim x (fun i ↦ w i ^ 2)) (D j)
  let B := polynomialValue (Sum.elim x roots) (D j)
  have hlocal := abs_sq_sub_sqrt_le_quarticDefect (w := w j) (hD (fun i ↦ w i ^ 2) j)
  have hsqrt := two_mul_abs_sqrt_sub_le (hD (fun i ↦ w i ^ 2) j) (hD roots j)
  have hcomparison := RadicalComparison.polynomial_difference_le D htri x w roots hroots (D j)
  have hsum : (∑ i, polynomialValue (Sum.elim x w) (RadicalComparison.weight D (D j) i) *
      |w i ^ 2 - roots i|) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin J ↦ i.val < j.val),
        polynomialValue (Sum.elim x w) (coefficients D j i) * |w i ^ 2 - roots i| := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs with hi
    · rfl
    · rw [RadicalComparison.weight_eq_zero_of_dependsBelow D (htri j) i (by omega)]
      simp [polynomialValue]
  rw [hsum] at hcomparison
  have htriangle := abs_sub_le (w j ^ 2) (Real.sqrt A) (roots j)
  rw [hroots j] at htriangle
  rw [defect_value]
  change |w j ^ 2 - roots j| ≤ |w j ^ 4 - A| + _
  change |w j ^ 2 - Real.sqrt A| ≤ |w j ^ 4 - A| at hlocal
  change 2 * |Real.sqrt A - Real.sqrt B| ≤ |A - B| at hsqrt
  change |A - B| ≤ _ at hcomparison
  rw [hroots j]
  change |w j ^ 2 - Real.sqrt B| ≤ _
  nlinarith [abs_nonneg (Real.sqrt A - Real.sqrt B)]

theorem root_error_le_weight_mul_norm (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (htri : ∀ j, RadicalProgram.FiniteDependsBelow (D j) j.val)
    (x : σ → ℝ) (w roots : Fin J → ℝ)
    (hD : ∀ r j, 1 ≤ polynomialValue (Sum.elim x r) (D j))
    (hroots : ∀ j, roots j = Real.sqrt (polynomialValue (Sum.elim x roots) (D j)))
    (j : Fin J) :
    |w j ^ 2 - roots j| ≤ polynomialValue (Sum.elim x w) (rootWeights D j) *
      defectNorm D (Sum.elim x w) := by
  apply TriangularErrorWeights.error_le_weight_mul (coefficients D) (Sum.elim x w)
    (fun j i ↦ RadicalComparison.weight_nonneg D (D j) _ i)
    (fun i ↦ |w i ^ 2 - roots i|) (defectNorm D (Sum.elim x w)) _ j
  intro i
  exact (root_error_step D htri x w roots hD hroots i).trans
    (add_le_add_left (abs_defect_le_norm D (Sum.elim x w) i) _)

def polynomialWeight (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (p : MvPolynomial (σ ⊕ Fin J) ℚ) : MvPolynomial (σ ⊕ Fin J) ℚ :=
  ∑ i, RadicalComparison.weight D p i * rootWeights D i

theorem polynomialWeight_nonneg (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (p : MvPolynomial (σ ⊕ Fin J) ℚ) (y : σ ⊕ Fin J → ℝ) :
    0 ≤ polynomialValue y (polynomialWeight D p) := by
  simp only [polynomialWeight, polynomialValue, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul]
  exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (RadicalComparison.weight_nonneg D p y i)
    (zero_le_one.trans (rootWeights_one_le D y i))

/-- A constructed global polynomial error weight for any polynomial output. -/
theorem polynomial_error_le_weight_mul_norm (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (htri : ∀ j, RadicalProgram.FiniteDependsBelow (D j) j.val)
    (x : σ → ℝ) (w roots : Fin J → ℝ)
    (hD : ∀ r j, 1 ≤ polynomialValue (Sum.elim x r) (D j))
    (hroots : ∀ j, roots j = Real.sqrt (polynomialValue (Sum.elim x roots) (D j)))
    (p : MvPolynomial (σ ⊕ Fin J) ℚ) :
    |polynomialValue (Sum.elim x (fun i ↦ w i ^ 2)) p -
      polynomialValue (Sum.elim x roots) p| ≤
        polynomialValue (Sum.elim x w) (polynomialWeight D p) * defectNorm D (Sum.elim x w) := by
  apply (RadicalComparison.polynomial_difference_le D htri x w roots hroots p).trans
  calc
    _ ≤ ∑ i, polynomialValue (Sum.elim x w) (RadicalComparison.weight D p i) *
        (polynomialValue (Sum.elim x w) (rootWeights D i) * defectNorm D (Sum.elim x w)) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (root_error_le_weight_mul_norm D htri x w roots hD hroots i)
        (RadicalComparison.weight_nonneg D p _ i)
    _ = _ := by
      simp [polynomialWeight, polynomialValue, Finset.sum_mul, mul_assoc]

end

end Stability.Simulation.RadicalDefectBounds
