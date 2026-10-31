import Stability.Simulation.RadicalDependencies
import Stability.Simulation.RationalDirectionalDerivative

/-!
# The recursively constructed rational radical lift

The j-th auxiliary velocity is w_j times the directional derivative of
D_j, divided by 4 D_j. Only earlier auxiliary velocities are available
when that fraction is constructed. Triangularity makes the missing
current and future partial derivatives zero, so the final field satisfies
the full chain-rule equation for every radicand.

All fractions and the finite recursion are explicit. The hypotheses on
radicands and input denominators are algebraic properties, not assumed
simulation or invariant-graph conclusions.
-/

namespace Stability.Simulation.TriangularLift

noncomputable section

open AbsFormula PolynomialFraction

variable {σ : Type*} [Fintype σ] {J : ℕ}

/-- One auxiliary velocity, using the velocities already constructed. -/
def rootStep (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (F : σ → PolynomialFraction (σ ⊕ Fin J))
    (roots : Fin J → PolynomialFraction (σ ⊕ Fin J)) (j : Fin J) :
    PolynomialFraction (σ ⊕ Fin J) :=
  mulPolynomial (MvPolynomial.X (Sum.inr j))
    (divPolynomial (directional (D j) (Sum.elim F roots)) (MvPolynomial.C 4 * D j))

/-- Construct the first `count` auxiliary fractions in their triangular order. -/
def velocityPrefix (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (F : σ → PolynomialFraction (σ ⊕ Fin J)) :
    ℕ → Fin J → PolynomialFraction (σ ⊕ Fin J)
  | 0 => fun _ ↦ ofPolynomial 0
  | count + 1 =>
      let previous := velocityPrefix D F count
      if h : count < J then
        Function.update previous ⟨count, h⟩ (rootStep D F previous ⟨count, h⟩)
      else previous

def rootVelocity (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (F : σ → PolynomialFraction (σ ⊕ Fin J)) : Fin J → PolynomialFraction (σ ⊕ Fin J) :=
  velocityPrefix D F J

/-- The actual rational field on the base and auxiliary coordinates. -/
def field (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (F : σ → PolynomialFraction (σ ⊕ Fin J)) :
    σ ⊕ Fin J → PolynomialFraction (σ ⊕ Fin J) := Sum.elim F (rootVelocity D F)

theorem velocityPrefix_succ_of_ne (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (F : σ → PolynomialFraction (σ ⊕ Fin J)) (count : ℕ) (i : Fin J)
    (hi : i.val ≠ count) : velocityPrefix D F (count + 1) i = velocityPrefix D F count i := by
  change (if h : count < J then Function.update (velocityPrefix D F count) ⟨count, h⟩
    (rootStep D F (velocityPrefix D F count) ⟨count, h⟩) else velocityPrefix D F count) i = _
  split_ifs with h
  · apply Function.update_of_ne
    intro heq
    exact hi (congrArg Fin.val heq)
  · rfl

theorem velocityPrefix_eq_of_le (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (F : σ → PolynomialFraction (σ ⊕ Fin J)) {a b : ℕ} (hab : a ≤ b)
    (i : Fin J) (hi : i.val < a) : velocityPrefix D F b i = velocityPrefix D F a i := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih => rw [velocityPrefix_succ_of_ne D F b i (by omega), ih]

theorem velocityPrefix_at (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (F : σ → PolynomialFraction (σ ⊕ Fin J)) (i : Fin J) :
    velocityPrefix D F (i.val + 1) i = rootStep D F (velocityPrefix D F i.val) i := by
  simp [velocityPrefix, i.isLt]

theorem rootVelocity_eq_prefix_step (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (F : σ → PolynomialFraction (σ ⊕ Fin J)) (i : Fin J) :
    rootVelocity D F i = rootStep D F (velocityPrefix D F i.val) i := by
  rw [rootVelocity, velocityPrefix_eq_of_le D F (a := i.val + 1)
    (by omega) i (by omega), velocityPrefix_at]

theorem rootStep_denominator_one_le (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (F : σ → PolynomialFraction (σ ⊕ Fin J))
    (roots : Fin J → PolynomialFraction (σ ⊕ Fin J)) (x : σ ⊕ Fin J → ℝ)
    (hF : ∀ i, 1 ≤ polynomialValue x (F i).denominator)
    (hroots : ∀ i, 1 ≤ polynomialValue x (roots i).denominator)
    (j : Fin J) (hD : 1 ≤ polynomialValue x (D j)) :
    1 ≤ polynomialValue x (rootStep D F roots j).denominator := by
  have hcombined : ∀ i, 1 ≤ polynomialValue x ((Sum.elim F roots) i).denominator := by
    intro i
    cases i with
    | inl i => exact hF i
    | inr i => exact hroots i
  have hdir := directional_denominator_one_le (D j) (Sum.elim F roots) x hcombined
  change 1 ≤ polynomialValue x
    ((directional (D j) (Sum.elim F roots)).denominator * (MvPolynomial.C 4 * D j))
  calc
    1 ≤ polynomialValue x (directional (D j) (Sum.elim F roots)).denominator *
        (4 * polynomialValue x (D j)) :=
      one_le_mul_of_one_le_of_one_le hdir (by linarith)
    _ = _ := by simp [polynomialValue]

theorem velocityPrefix_denominator_one_le (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (F : σ → PolynomialFraction (σ ⊕ Fin J)) (x : σ ⊕ Fin J → ℝ)
    (hF : ∀ i, 1 ≤ polynomialValue x (F i).denominator)
    (hD : ∀ i, 1 ≤ polynomialValue x (D i)) (count : ℕ) (i : Fin J) :
    1 ≤ polynomialValue x (velocityPrefix D F count i).denominator := by
  induction count generalizing i with
  | zero => simp [velocityPrefix, ofPolynomial, polynomialValue]
  | succ count ih =>
      unfold velocityPrefix
      split_ifs with h
      · by_cases hi : i = ⟨count, h⟩
        · subst i
          rw [Function.update_self]
          exact rootStep_denominator_one_le D F _ x hF (fun j ↦ ih j) _ (hD _)
        · rw [Function.update_of_ne hi]
          exact ih i
      · exact ih i

theorem field_denominator_one_le (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (F : σ → PolynomialFraction (σ ⊕ Fin J)) (x : σ ⊕ Fin J → ℝ)
    (hF : ∀ i, 1 ≤ polynomialValue x (F i).denominator)
    (hD : ∀ i, 1 ≤ polynomialValue x (D i)) (i : σ ⊕ Fin J) :
    1 ≤ polynomialValue x (field D F i).denominator := by
  cases i with
  | inl i => exact hF i
  | inr i => exact velocityPrefix_denominator_one_le D F x hF hD J i

theorem value_rootStep (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (F : σ → PolynomialFraction (σ ⊕ Fin J))
    (roots : Fin J → PolynomialFraction (σ ⊕ Fin J)) (x : σ ⊕ Fin J → ℝ)
    (hF : ∀ i, 1 ≤ polynomialValue x (F i).denominator)
    (hroots : ∀ i, 1 ≤ polynomialValue x (roots i).denominator) (j : Fin J) :
    value x (rootStep D F roots j) = x (Sum.inr j) *
      (∑ i, polynomialValue x (MvPolynomial.pderiv i (D j)) *
        value x (Sum.elim F roots i)) / (4 * polynomialValue x (D j)) := by
  have hcombined : ∀ i, 1 ≤ polynomialValue x ((Sum.elim F roots) i).denominator := by
    intro i
    cases i with
    | inl i => exact hF i
    | inr i => exact hroots i
  rw [rootStep, value_mulPolynomial, value_divPolynomial,
    value_directional _ _ x hcombined]
  simp [polynomialValue, mul_div_assoc]

/-- The fully assembled field obeys each full directional-derivative
equation. Later auxiliary velocities disappear by triangularity. -/
theorem rootVelocity_value_eq (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (F : σ → PolynomialFraction (σ ⊕ Fin J))
    (htri : ∀ j, RadicalProgram.FiniteDependsBelow (D j) j.val)
    (x : σ ⊕ Fin J → ℝ)
    (hF : ∀ i, 1 ≤ polynomialValue x (F i).denominator)
    (hD : ∀ i, 1 ≤ polynomialValue x (D i)) (j : Fin J) :
    value x (rootVelocity D F j) = x (Sum.inr j) *
      (∑ i, polynomialValue x (MvPolynomial.pderiv i (D j)) * value x (field D F i)) /
        (4 * polynomialValue x (D j)) := by
  rw [rootVelocity_eq_prefix_step, value_rootStep D F _ x hF
    (velocityPrefix_denominator_one_le D F x hF hD j.val)]
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  cases i with
  | inl i => rfl
  | inr i =>
      by_cases hij : i.val < j.val
      · have heq := velocityPrefix_eq_of_le D F (a := j.val) (b := J)
          (Nat.le_of_lt j.isLt) i hij
        change _ * value x (velocityPrefix D F j.val i) =
          _ * value x (velocityPrefix D F J i)
        rw [heq]
      · rw [(htri j).pderiv_eq_zero i (Nat.le_of_not_gt hij)]
        simp [polynomialValue]

end

end Stability.Simulation.TriangularLift
