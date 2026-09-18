import HGAS.Dynamics.ErgodicMaximizer
import HGAS.Dynamics.UniformNegativeBlocks

/-!
# Ergodic realization of the maximal invariant average

`ErgodicMaximizer` proves, independently of the particular definition of
the maximum, that a bounded continuous observable has an ergodic
maximizing invariant probability.  This short bridge identifies its
average with the attained value `maximalInvariantAverage` used in the GAS
development.
-/

noncomputable section

open MeasureTheory Set
open scoped BoundedContinuousFunction

namespace HGAS.Dynamics

variable {K : Type*} [MetricSpace K] [MeasurableSpace K]
  [BorelSpace K] [CompactSpace K] [Nonempty K]

/-- The chosen ergodic maximizing probability realizes the
`maximalInvariantAverage` value. -/
theorem ergodicMaximizingInvariantProbabilityMeasure_average_eq
    (ϕ : Flow ℝ K) (f : K →ᵇ ℝ) :
    observableAverage f
        (ergodicMaximizingInvariantProbabilityMeasure ϕ f).measure =
      maximalInvariantAverage ϕ f := by
  apply le_antisymm
  · exact
      invariantAverage_le_maximalInvariantAverage
        ϕ f
        (ergodicMaximizingInvariantProbabilityMeasure ϕ f).measure
        (ergodicMaximizingInvariantProbabilityMeasure ϕ f).invariant
  · exact
      ergodicMaximizingInvariantProbabilityMeasure_isMaxOn
        ϕ f
        (maximizingInvariantProbability_invariant ϕ f)

/-- Bundled existence statement in the vocabulary used by the compact
sign reduction: an ergodic invariant probability has average exactly the
maximal invariant average. -/
theorem exists_ergodicInvariantProbability_average_eq_maximal
    (ϕ : Flow ℝ K) (f : K →ᵇ ℝ) :
    ∃ μ : InvariantProbabilityMeasure ϕ,
      IsErgodicInvariantProbability ϕ μ.measure ∧
        observableAverage f μ.measure =
          maximalInvariantAverage ϕ f := by
  exact
    ⟨ergodicMaximizingInvariantProbabilityMeasure ϕ f,
      ergodicMaximizingInvariantProbabilityMeasure_ergodic ϕ f,
      ergodicMaximizingInvariantProbabilityMeasure_average_eq ϕ f⟩

/-- An upper bound checked only on ergodic invariant probabilities bounds
the attained maximal invariant average. -/
theorem maximalInvariantAverage_le_of_forall_ergodic
    (ϕ : Flow ℝ K) (f : K →ᵇ ℝ) {c : ℝ}
    (hbound :
      ∀ μ : InvariantProbabilityMeasure ϕ,
        IsErgodicInvariantProbability ϕ μ.measure →
          observableAverage f μ.measure ≤ c) :
    maximalInvariantAverage ϕ f ≤ c := by
  rw [←
    ergodicMaximizingInvariantProbabilityMeasure_average_eq
      ϕ f]
  exact
    hbound
      (ergodicMaximizingInvariantProbabilityMeasure ϕ f)
      (ergodicMaximizingInvariantProbabilityMeasure_ergodic
        ϕ f)

end HGAS.Dynamics
