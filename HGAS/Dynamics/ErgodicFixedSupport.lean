import HGAS.Dynamics.ErgodicInvariantProbability
import Mathlib.MeasureTheory.Measure.Typeclasses.ZeroOne

/-!
# Ergodic probabilities supported on fixed points

An ergodic invariant probability cannot distribute mass among several
stationary states.  More precisely, if almost every point is fixed by the
flow, then every measurable set is invariant modulo null sets.  Ergodicity
therefore makes the underlying measure a nonzero zero--one measure, and the
standard-Borel zero--one theorem identifies it with a Dirac mass.

This is the form needed for the polynomial controller: recurrence first
shows that every invariant probability is concentrated on the finite set of
controller equilibria, all of which are fixed points; ergodicity then
selects one equilibrium.
-/

noncomputable section

open Filter MeasureTheory Set

namespace HGAS.Dynamics

variable {X : Type*} [TopologicalSpace X]
  [MeasurableSpace X] [BorelSpace X]
  [StandardBorelSpace X]

/-- An ergodic invariant probability which is almost surely supported on
fixed points of the flow is a Dirac measure. -/
theorem exists_eq_dirac_of_isErgodicInvariantProbability_ae_fixed
    {ϕ : Flow ℝ X}
    (μ : ProbabilityMeasure X)
    (hμ : IsErgodicInvariantProbability ϕ μ)
    (hfixed :
      ∀ᵐ x ∂(μ : Measure X),
        InvariantProbabilityMeasure.IsFlowFixedPoint ϕ x) :
    ∃ x : X, (μ : Measure X) = Measure.dirac x := by
  letI : IsZeroOneMeasure (μ : Measure X) :=
    ⟨by
      intro s hs
      apply hμ.zero_or_one hs
      intro t
      filter_upwards [hfixed] with x hx
      exact congrArg (fun y : X ↦ y ∈ s) (hx t)⟩
  have hne : (μ : Measure X) ≠ 0 := by
    intro hzero
    have huniv :=
      congrArg (fun ν : Measure X ↦ ν Set.univ) hzero
    simp at huniv
  letI : NeZero (μ : Measure X) := ⟨hne⟩
  exact IsZeroOneMeasure.exists_eq_dirac

/-- Probability-measure formulation of the fixed-support classification. -/
theorem exists_eq_diracProba_of_isErgodicInvariantProbability_ae_fixed
    {ϕ : Flow ℝ X}
    (μ : ProbabilityMeasure X)
    (hμ : IsErgodicInvariantProbability ϕ μ)
    (hfixed :
      ∀ᵐ x ∂(μ : Measure X),
        InvariantProbabilityMeasure.IsFlowFixedPoint ϕ x) :
    ∃ x : X, μ = MeasureTheory.diracProba x := by
  obtain ⟨x, hx⟩ :=
    exists_eq_dirac_of_isErgodicInvariantProbability_ae_fixed
      μ hμ hfixed
  refine ⟨x, ProbabilityMeasure.toMeasure_injective ?_⟩
  simpa [MeasureTheory.diracProba] using hx

end HGAS.Dynamics
