import Stability.Simulation.FormulaPrecision
import HGAS.Veronese.CoordinateFieldSmoothness
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Smoothness of formulas with positive precision

The smoothed absolute value has a strictly positive radicand whenever
the precision is nonzero. Structural induction therefore proves
smoothness of every smoothed formula. The common polynomial precision
then gives a globally smooth approximation on the entire state space.
-/

namespace Stability.Simulation.AbsFormula

noncomputable section

variable {σ : Type*}

/-- Absolute-value formulas are continuous under continuous coordinate
substitution, even though they need not be differentiable. -/
theorem continuous_eval
    {E : Type*} [TopologicalSpace E] {x : E → σ → ℝ}
    (hx : ∀ i, Continuous (fun z ↦ x z i)) (e : AbsFormula σ) :
    Continuous (fun z ↦ eval (x z) e) := by
  induction e with
  | coordinate i => exact hx i
  | constant c => exact continuous_const
  | add e f he hf => exact he.add hf
  | mul e f he hf => exact he.mul hf
  | abs e he => exact he.abs

/-- Smooth coordinates and a smooth nonvanishing precision give a smooth
evaluation. This composition theorem is independent of the dimension of
the parameter space and of the particular polynomial precision. -/
theorem contDiff_smoothEval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : E → σ → ℝ} {L : E → ℝ}
    (hx : ∀ i, ContDiff ℝ ⊤ (fun z ↦ x z i))
    (hL : ContDiff ℝ ⊤ L) (hLne : ∀ z, L z ≠ 0)
    (e : AbsFormula σ) :
    ContDiff ℝ ⊤ (fun z ↦ smoothEval (L z) (x z) e) := by
  induction e with
  | coordinate i => exact hx i
  | constant c => exact contDiff_const
  | add e f he hf => exact he.add hf
  | mul e f he hf => exact he.mul hf
  | abs e he =>
    apply ((he.pow 2).add ((hL.inv hLne).pow 2)).sqrt
    intro z
    have hpositive : 0 < (L z)⁻¹ ^ 2 := sq_pos_of_ne_zero (inv_ne_zero (hLne z))
    exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) hpositive)

/-- The explicit precision polynomial smooths every formula globally.
No invariant region or bounded-state hypothesis is needed. -/
theorem contDiff_smoothEval_precisionPolynomial
    {ι : Type*} [Fintype ι] [Fintype σ]
    (formulas : ι → AbsFormula σ) (clock : σ)
    {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1) (e : AbsFormula σ) :
    ContDiff ℝ ⊤ (fun x : σ → ℝ ↦
      smoothEval (polynomialValue x (precisionPolynomial formulas clock ε)) x e) := by
  apply contDiff_smoothEval
  · intro i
    exact (ContinuousLinearMap.proj i : (σ → ℝ) →L[ℝ] ℝ).contDiff
  · exact HGAS.contDiff_eval₂Hom_rational_real_fintype _
  · intro x
    exact ne_of_gt (zero_lt_one.trans_le
      (one_le_precisionPolynomial formulas clock hε hεOne x))

/-- The entire finite family is a smooth vector-valued map. -/
theorem contDiff_smoothedFamily
    {ι : Type*} [Fintype ι] [Fintype σ]
    (formulas : ι → AbsFormula σ) (clock : σ)
    {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1) :
    ContDiff ℝ ⊤ (fun x : σ → ℝ ↦ fun i ↦
      smoothEval (polynomialValue x (precisionPolynomial formulas clock ε)) x (formulas i)) := by
  rw [contDiff_pi]
  intro i
  exact contDiff_smoothEval_precisionPolynomial formulas clock hε hεOne (formulas i)

end

end Stability.Simulation.AbsFormula
