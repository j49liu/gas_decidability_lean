import Stability.Simulation.TriangularLiftInvariant

/-!
# Uniqueness of the tangent velocity on the quartic graph

At a point satisfying the quartic equations, the base velocity determines
every auxiliary velocity in order. Differentiating the j-th constraint
only involves earlier auxiliary velocities. Since its radicand is positive,
the corresponding root is nonzero and the differentiated equation has a
unique solution. This identifies the tangent field with the rational field
constructed by `TriangularLift`.
-/

namespace Stability.Simulation.TriangularLift

noncomputable section

open AbsFormula PolynomialFraction

variable {σ : Type*} [Fintype σ] {J : ℕ}

/-- A tangent vector satisfying the differentiated quartic constraints
is the actual constructed velocity. No invariant-flow premise is used. -/
theorem eq_realize_of_quartic_tangent
    (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (F : σ → PolynomialFraction (σ ⊕ Fin J))
    (htri : ∀ j, RadicalProgram.FiniteDependsBelow (D j) j.val)
    (x v : σ ⊕ Fin J → ℝ)
    (hF : ∀ i, 1 ≤ polynomialValue x (F i).denominator)
    (hD : ∀ i, 1 ≤ polynomialValue x (D i))
    (hbase : ∀ i, v (Sum.inl i) = value x (F i))
    (hquartic : ∀ j, x (Sum.inr j) ^ 4 = polynomialValue x (D j))
    (htangent : ∀ j, 4 * x (Sum.inr j) ^ 3 * v (Sum.inr j) =
      ∑ i, polynomialValue x (MvPolynomial.pderiv i (D j)) * v i) :
    v = realize D F x := by
  have hroot : ∀ j, v (Sum.inr j) = realize D F x (Sum.inr j) := by
    apply Fin.strong_induction_on
    intro j ih
    have hsum : (∑ i, polynomialValue x (MvPolynomial.pderiv i (D j)) * v i) =
        ∑ i, polynomialValue x (MvPolynomial.pderiv i (D j)) * value x (field D F i) := by
      apply Finset.sum_congr rfl
      intro i hi
      cases i with
      | inl i => rw [hbase i]; rfl
      | inr i =>
          by_cases hij : i.val < j.val
          · rw [ih i hij]; rfl
          · rw [(htri j).pderiv_eq_zero i (Nat.le_of_not_gt hij)]
            simp [polynomialValue]
    change v (Sum.inr j) = value x (rootVelocity D F j)
    rw [rootVelocity_value_eq D F htri x hF hD j]
    apply (eq_div_iff (by linarith [hD j] : (4 * polynomialValue x (D j)) ≠ 0)).mpr
    rw [← hsum, ← htangent j, ← hquartic j]
    ring
  funext i
  cases i with
  | inl i => exact hbase i
  | inr i => exact hroot i

end

end Stability.Simulation.TriangularLift
