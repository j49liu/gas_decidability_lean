import Stability.Simulation.CompiledFormulaLift
import Stability.Simulation.TriangularLiftTangent

/-!
# Lifting trajectories to the canonical radical graph

The graph is the actual output of the finite root evaluator, not a chosen
solution of polynomial equations. It is smooth and satisfies every quartic
constraint. Differentiating these identities and using triangular tangent
uniqueness shows that any trajectory of the smoothed base formulas lifts
to a trajectory of the constructed rational field.
-/

namespace Stability.Simulation.CompiledFormulaLift

noncomputable section

open AbsFormula PolynomialFraction

variable {σ : Type*} [Fintype σ]

/-- Canonical positive fourth-root graph produced by the formula compiler. -/
def graph (L : MvPolynomial σ ℚ) (es : List (AbsFormula σ)) (x : σ → ℝ) :
    σ ⊕ Fin (finiteRadicalFamily L es).rootCount → ℝ :=
  Sum.elim x (finiteLiftRoots L es x)

theorem contDiff_graph (L : MvPolynomial σ ℚ) (es : List (AbsFormula σ))
    (hL : ∀ x : σ → ℝ, 1 ≤ polynomialValue x L) :
    ContDiff ℝ ⊤ (graph L es) := by
  rw [contDiff_pi]
  intro i
  cases i with
  | inl i => exact (ContinuousLinearMap.proj i : (σ → ℝ) →L[ℝ] ℝ).contDiff
  | inr i => exact (contDiff_pi.mp (contDiff_finiteLiftRoots L es hL)) i

/-- An actual smoothed base trajectory has the actual rational lifted
velocity on the explicitly generated graph. The proof neither assumes a
lifted solution nor infers existence from invariance. -/
theorem hasDerivAt_graph (L : MvPolynomial σ ℚ) (es : List (AbsFormula σ))
    (component : σ → Fin es.length) (hL : ∀ x : σ → ℝ, 1 ≤ polynomialValue x L)
    {x : ℝ → σ → ℝ} {t : ℝ}
    (hx : HasDerivAt x (fun i ↦ smoothEval (polynomialValue (x t) L)
      (x t) (es.get (component i))) t) :
    HasDerivAt (fun u ↦ graph L es (x u))
      (realize L es component (graph L es (x t))) t := by
  have hdiff : DifferentiableAt ℝ (fun u ↦ graph L es (x u)) t :=
    ((contDiff_graph L es hL).differentiable (by simp)).differentiableAt.comp t
      hx.differentiableAt
  have hd := hdiff.hasDerivAt
  apply hd.congr_deriv
  apply TriangularLift.eq_realize_of_quartic_tangent (liftRadicand L es)
    (fun i ↦ baseFraction L es (component i)) (liftRadicand_dependsBelow L es)
  · intro i
    exact baseFraction_denominator_one_le L es (component i) _ (hL _)
  · exact radicand_one_le L es hL _
  · intro i
    have hi := (hasDerivAt_pi.mp hd) (Sum.inl i)
    have hxi := (hasDerivAt_pi.mp hx) i
    exact (hi.unique hxi).trans
      (baseFraction_value_on_graph L es (x t) (hL (x t)) (component i)).symm
  · intro j
    exact finiteLiftRoots_fourth L es (x t) (hL (x t)) j
  · intro j
    have hpow := ((hasDerivAt_pi.mp hd) (Sum.inr j)).pow 4
    change HasDerivAt (fun u ↦ graph L es (x u) (Sum.inr j) ^ 4)
      (4 * graph L es (x t) (Sum.inr j) ^ 3 *
        deriv (fun u ↦ graph L es (x u)) t (Sum.inr j)) t at hpow
    have hpoly := hasDerivAt_polynomialValue (liftRadicand L es j) (hasDerivAt_pi.mp hd)
    have heq : (fun u ↦ graph L es (x u) (Sum.inr j) ^ 4) =
        (fun u ↦ polynomialValue (graph L es (x u)) (liftRadicand L es j)) := by
      funext u
      exact finiteLiftRoots_fourth L es (x u) (hL (x u)) j
    rw [heq] at hpow
    exact hpow.unique hpoly

/-- The derivative of the graph map sends the actual smoothed base
velocity to the actual lifted velocity. An affine test curve identifies
this derivative without imposing any condition on a time domain. -/
theorem fderiv_graph_apply_baseField (L : MvPolynomial σ ℚ) (es : List (AbsFormula σ))
    (component : σ → Fin es.length) (hL : ∀ x : σ → ℝ, 1 ≤ polynomialValue x L)
    (x : σ → ℝ) :
    fderiv ℝ (graph L es) x
      (fun i ↦ smoothEval (polynomialValue x L) x (es.get (component i))) =
      realize L es component (graph L es x) := by
  let v : σ → ℝ := fun i ↦ smoothEval (polynomialValue x L) x (es.get (component i))
  let line : ℝ → σ → ℝ := fun t ↦ x + t • v
  have hline : HasDerivAt line v 0 := by
    simpa only [zero_add, one_smul] using (hasDerivAt_const (0 : ℝ) x).add
      ((hasDerivAt_id (0 : ℝ)).smul_const v)
  have hzero : line 0 = x := by simp [line]
  have hconstructed := hasDerivAt_graph L es component hL
    (x := line) (t := 0) (by simpa only [hzero] using hline)
  have hcomposed := (((contDiff_graph L es hL).differentiable
    (by simp)).differentiableAt (x := line 0)).hasFDerivAt.comp_hasDerivAt 0 hline
  simpa only [hzero] using hcomposed.unique hconstructed

/-- The graph transfer also holds at one-sided endpoints, including
time zero of the repository's global forward-trajectory predicate. -/
theorem hasDerivWithinAt_graph (L : MvPolynomial σ ℚ) (es : List (AbsFormula σ))
    (component : σ → Fin es.length) (hL : ∀ x : σ → ℝ, 1 ≤ polynomialValue x L)
    {x : ℝ → σ → ℝ} {t : ℝ} {domain : Set ℝ}
    (hx : HasDerivWithinAt x (fun i ↦ smoothEval (polynomialValue (x t) L)
      (x t) (es.get (component i))) domain t) :
    HasDerivWithinAt (fun u ↦ graph L es (x u))
      (realize L es component (graph L es (x t))) domain t := by
  have h := (((contDiff_graph L es hL).differentiable
    (by simp)).differentiableAt (x := x t)).hasFDerivAt.comp_hasDerivWithinAt t hx
  rw [fderiv_graph_apply_baseField L es component hL (x t)] at h
  exact h

end

end Stability.Simulation.CompiledFormulaLift
