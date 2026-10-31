import Stability.Simulation.RadicalMajorant
import Stability.Simulation.PolynomialDifferenceBounds

/-!
# Polynomial comparison weights for the radical graph

The canonical roots have explicit polynomial majorants Sᵢ(x). Both wᵢ²
and the canonical root therefore lie below wᵢ² + Sᵢ(x). These bounds
give one polynomial cube radius for comparing any polynomial at the two
root assignments. Its coordinatewise difference weights use actual
formal partials, so a missing later root contributes exactly zero.
-/

namespace Stability.Simulation.RadicalComparison

noncomputable section

open AbsFormula

variable {σ : Type*} [Fintype σ] {J : ℕ}

def rootBound (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ) (i : Fin J) :
    MvPolynomial (σ ⊕ Fin J) ℚ :=
  MvPolynomial.X (Sum.inr i) ^ 2 + MvPolynomial.rename Sum.inl (RadicalMajorant.majorants D i)

def cubeRadius (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ) :
    MvPolynomial (σ ⊕ Fin J) ℚ := RadicalMajorant.radius (rootBound D)

theorem rootBound_value (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (x : σ → ℝ) (w : Fin J → ℝ) (i : Fin J) :
    polynomialValue (Sum.elim x w) (rootBound D i) =
      w i ^ 2 + polynomialValue x (RadicalMajorant.majorants D i) := by
  simp [rootBound, polynomialValue, MvPolynomial.eval₂_rename, Function.comp_def]

theorem cubeRadius_one_le (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (y : σ ⊕ Fin J → ℝ) : 1 ≤ polynomialValue y (cubeRadius D) :=
  RadicalMajorant.radius_one_le _ y

def weight (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (p : MvPolynomial (σ ⊕ Fin J) ℚ) (i : Fin J) :
    MvPolynomial (σ ⊕ Fin J) ℚ :=
  MvPolynomial.C (coefficientMass (MvPolynomial.pderiv (Sum.inr i) p)) *
    cubeRadius D ^ p.totalDegree

theorem weight_value (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (p : MvPolynomial (σ ⊕ Fin J) ℚ) (y : σ ⊕ Fin J → ℝ) (i : Fin J) :
    polynomialValue y (weight D p i) =
      (coefficientMass (MvPolynomial.pderiv (Sum.inr i) p) : ℝ) *
        polynomialValue y (cubeRadius D) ^ p.totalDegree := by
  simp [weight, polynomialValue]

theorem weight_nonneg (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (p : MvPolynomial (σ ⊕ Fin J) ℚ) (y : σ ⊕ Fin J → ℝ) (i : Fin J) :
    0 ≤ polynomialValue y (weight D p i) := by
  rw [weight_value]
  apply mul_nonneg
  · exact_mod_cast coefficientMass_nonneg (MvPolynomial.pderiv (Sum.inr i) p)
  · exact pow_nonneg (zero_le_one.trans (cubeRadius_one_le D y)) _

/-- Strict triangularity makes the corresponding comparison weight
identically zero, not merely small at the current state. -/
theorem weight_eq_zero_of_dependsBelow (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    {p : MvPolynomial (σ ⊕ Fin J) ℚ} {cut : ℕ}
    (hp : RadicalProgram.FiniteDependsBelow p cut) (i : Fin J) (hi : cut ≤ i.val) :
    weight D p i = 0 := by
  simp [weight, hp.pderiv_eq_zero i hi, coefficientMass]

/-- Every polynomial's actual root-substitution error is bounded by
the constructed polynomial weights times individual root errors. -/
theorem polynomial_difference_le (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (htri : ∀ j, RadicalProgram.FiniteDependsBelow (D j) j.val)
    (x : σ → ℝ) (w roots : Fin J → ℝ)
    (hroots : ∀ j, roots j = Real.sqrt (polynomialValue (Sum.elim x roots) (D j)))
    (p : MvPolynomial (σ ⊕ Fin J) ℚ) :
    |polynomialValue (Sum.elim x (fun i ↦ w i ^ 2)) p -
      polynomialValue (Sum.elim x roots) p| ≤
        ∑ i, polynomialValue (Sum.elim x w) (weight D p i) * |w i ^ 2 - roots i| := by
  have hmajorant := RadicalMajorant.abs_root_le_majorant D htri x roots hroots
  have hcanonical (i : Fin J) : |roots i| ≤
      polynomialValue (Sum.elim x w) (cubeRadius D) := by
    apply (hmajorant i).trans
    apply le_trans _ (RadicalMajorant.bound_le_radius (rootBound D) (Sum.elim x w) i)
    rw [rootBound_value]
    exact le_add_of_nonneg_left (sq_nonneg _)
  have hsquare (i : Fin J) : |w i ^ 2| ≤
      polynomialValue (Sum.elim x w) (cubeRadius D) := by
    apply le_trans _ (RadicalMajorant.bound_le_radius (rootBound D) (Sum.elim x w) i)
    rw [rootBound_value, abs_of_nonneg (sq_nonneg _)]
    exact le_add_of_nonneg_right (RadicalMajorant.prefix_nonneg D x J i)
  have hbase (i : σ) : |x i| ≤ polynomialValue (Sum.elim x w) (cubeRadius D) :=
    RadicalMajorant.abs_base_le_radius (rootBound D) (Sum.elim x w) (Sum.inl i)
  have h := abs_polynomialValue_sub_le_cube_of_degree_le p
    (Sum.elim x roots) (Sum.elim x (fun i ↦ w i ^ 2)) (cubeRadius_one_le D (Sum.elim x w))
    (by intro i; cases i with | inl i => exact hbase i | inr i => exact hcanonical i)
    (by intro i; cases i with | inl i => exact hbase i | inr i => exact hsquare i) le_rfl
  simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, sub_self,
    abs_zero, mul_zero, Finset.sum_const_zero, zero_add, weight_value] using h

end

end Stability.Simulation.RadicalComparison
