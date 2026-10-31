import Stability.Simulation.PolynomialFractionResources
import Stability.Simulation.TriangularLift

/-!
# Degree growth of the actual triangular rational lift

The degree budget follows the same finite update recursion as the stored
fractions. It needs no denominator positivity or triangular-dependency
premise: those properties govern semantics, whereas this estimate counts
the literal algebraic operations, including all denominator factors.
-/

namespace Stability.Simulation.TriangularLift

noncomputable section

open PolynomialFraction

/-- One coarse degree budget for a root-velocity update in `N` total
coordinates with radicand degree at most `d`. -/
def degreeStep (N d b : ℕ) : ℕ := (N + 1) * (d + b) + 1

/-- The initial budget also bounds the base fractions; zero roots require
no updates and preserve that budget exactly. -/
def degreeBound (N d b : ℕ) : ℕ → ℕ
  | 0 => b
  | count + 1 => degreeStep N d (degreeBound N d b count)

theorem le_degreeStep (N d b : ℕ) : b ≤ degreeStep N d b := by
  unfold degreeStep
  nlinarith

theorem degreeBound_le_succ (N d b count : ℕ) :
    degreeBound N d b count ≤ degreeBound N d b (count + 1) := le_degreeStep _ _ _

theorem le_degreeBound (N d b count : ℕ) : b ≤ degreeBound N d b count := by
  induction count with
  | zero => rfl
  | succ count ih => exact ih.trans (degreeBound_le_succ N d b count)

variable {σ : Type*} [Fintype σ] {J : ℕ}

theorem rootStep_degreesLE (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (F : σ → PolynomialFraction (σ ⊕ Fin J))
    (roots : Fin J → PolynomialFraction (σ ⊕ Fin J)) {d b : ℕ}
    (hD : ∀ j, (D j).totalDegree ≤ d) (hF : ∀ i, DegreesLE (F i) b)
    (hroots : ∀ j, DegreesLE (roots j) b) (j : Fin J) :
    DegreesLE (rootStep D F roots j) (degreeStep (Fintype.card σ + J) d b) := by
  have hcombined : ∀ i, DegreesLE (Sum.elim F roots i) b := by
    intro i
    cases i with
    | inl i => exact hF i
    | inr i => exact hroots i
  have hdir := directional_degreesLE (D j) (Sum.elim F roots) (hD j) hcombined
  have hden : (MvPolynomial.C 4 * D j).totalDegree ≤ d := by
    calc
      _ ≤ (MvPolynomial.C (4 : ℚ) : MvPolynomial (σ ⊕ Fin J) ℚ).totalDegree +
          (D j).totalDegree := MvPolynomial.totalDegree_mul _ _
      _ = (D j).totalDegree := by simp
      _ ≤ d := hD j
  have hdiv := divPolynomial_degreesLE (MvPolynomial.C 4 * D j) hdir hden
  have hmul := mulPolynomial_degreesLE (MvPolynomial.X (Sum.inr j)) (d := 1) hdiv (by simp)
  apply hmul.mono
  simp only [Fintype.card_sum, Fintype.card_fin, degreeStep]
  nlinarith

/-- Every stage of the actual prefix construction obeys the scalar
resource recurrence, including unassigned zero coordinates. -/
theorem velocityPrefix_degreesLE (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (F : σ → PolynomialFraction (σ ⊕ Fin J)) {d b : ℕ}
    (hD : ∀ j, (D j).totalDegree ≤ d) (hF : ∀ i, DegreesLE (F i) b)
    (count : ℕ) (j : Fin J) : DegreesLE (velocityPrefix D F count j)
      (degreeBound (Fintype.card σ + J) d b count) := by
  induction count generalizing j with
  | zero => simp [velocityPrefix, DegreesLE, ofPolynomial, degreeBound]
  | succ count ih =>
      unfold velocityPrefix
      split_ifs with h
      · by_cases hj : j = ⟨count, h⟩
        · subst j
          rw [Function.update_self]
          exact rootStep_degreesLE D F _ hD
            (fun i ↦ (hF i).mono (le_degreeBound _ _ _ _)) ih _
        · rw [Function.update_of_ne hj]
          exact (ih j).mono (degreeBound_le_succ _ _ _ _)
      · exact (ih j).mono (degreeBound_le_succ _ _ _ _)

theorem rootVelocity_degreesLE (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (F : σ → PolynomialFraction (σ ⊕ Fin J)) {d b : ℕ}
    (hD : ∀ j, (D j).totalDegree ≤ d) (hF : ∀ i, DegreesLE (F i) b) (j : Fin J) :
    DegreesLE (rootVelocity D F j) (degreeBound (Fintype.card σ + J) d b J) :=
  velocityPrefix_degreesLE D F hD hF J j

theorem field_degreesLE (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (F : σ → PolynomialFraction (σ ⊕ Fin J)) {d b : ℕ}
    (hD : ∀ j, (D j).totalDegree ≤ d) (hF : ∀ i, DegreesLE (F i) b)
    (i : σ ⊕ Fin J) :
    DegreesLE (field D F i) (degreeBound (Fintype.card σ + J) d b J) := by
  cases i with
  | inl i => exact (hF i).mono (le_degreeBound _ _ _ _)
  | inr j => exact rootVelocity_degreesLE D F hD hF j

/-- Separate supplied base numerator and denominator bounds combine by
their maximum before the same explicit root recursion is applied. -/
theorem field_degreesLE_of_separate_bounds
    (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (F : σ → PolynomialFraction (σ ⊕ Fin J)) {d numeratorDegree denominatorDegree : ℕ}
    (hD : ∀ j, (D j).totalDegree ≤ d)
    (hnum : ∀ i, (F i).numerator.totalDegree ≤ numeratorDegree)
    (hden : ∀ i, (F i).denominator.totalDegree ≤ denominatorDegree)
    (i : σ ⊕ Fin J) :
    DegreesLE (field D F i)
      (degreeBound (Fintype.card σ + J) d (max numeratorDegree denominatorDegree) J) :=
  field_degreesLE D F hD (fun i ↦
    ⟨(hnum i).trans (Nat.le_max_left _ _), (hden i).trans (Nat.le_max_right _ _)⟩) i

end

end Stability.Simulation.TriangularLift
