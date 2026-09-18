import HGAS.Dynamics.InvariantComponentAverage
import HGAS.Dynamics.UniformNegativeBlocks

/-!
# Maximal averages determined by a unique factor marginal

Suppose every invariant probability of a compact source flow has the same
pushforward `ν` under a continuous equivariant factor map.  Then every
observable which factors through that map has one and the same invariant
average, so its maximal invariant average is exactly its `ν`-average.

This elementary lemma is the reusable measure-theoretic bridge between the
radical-clock Haar-marginal theorem and the arithmetic detector integral.
-/

namespace HGAS.Dynamics

open Function MeasureTheory
open scoped BoundedContinuousFunction

noncomputable section

variable {X Y : Type*}
  [MetricSpace X] [CompactSpace X] [Nonempty X]
  [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- If every source invariant probability has one prescribed factor
marginal, then the maximal average of every pulled-back factor observable
is its average against that marginal. -/
theorem maximalInvariantAverage_compContinuous_eq_of_uniqueFactorMarginal
    {ϕ : Flow ℝ X} {ψ : Flow ℝ Y}
    (q : X → Y) (hq : Continuous q)
    (hequiv : ∀ t : ℝ, Function.Semiconj q (ϕ t) (ψ t))
    (ν : ProbabilityMeasure Y)
    (hunique :
      ∀ μ : InvariantProbabilityMeasure ϕ,
        (μ.mapEquivariant q hq hequiv).measure = ν)
    (a : Y →ᵇ ℝ) :
    maximalInvariantAverage ϕ
        (a.compContinuous ⟨q, hq⟩) =
      observableAverage a ν := by
  let μmax : InvariantProbabilityMeasure ϕ :=
    ⟨maximizingInvariantProbability ϕ
        (a.compContinuous ⟨q, hq⟩),
      maximizingInvariantProbability_invariant ϕ
        (a.compContinuous ⟨q, hq⟩)⟩
  change
    observableAverage (a.compContinuous ⟨q, hq⟩)
        μmax.measure =
      observableAverage a ν
  rw [← observableAverage_mapEquivariant
    μmax q hq hequiv a, hunique μmax]

omit [CompactSpace X] [Nonempty X] in
/-- In particular, all invariant averages of a pulled-back factor
observable equal the same prescribed value. -/
theorem observableAverage_compContinuous_eq_of_uniqueFactorMarginal
    {ϕ : Flow ℝ X} {ψ : Flow ℝ Y}
    (q : X → Y) (hq : Continuous q)
    (hequiv : ∀ t : ℝ, Function.Semiconj q (ϕ t) (ψ t))
    (ν : ProbabilityMeasure Y)
    (hunique :
      ∀ μ : InvariantProbabilityMeasure ϕ,
        (μ.mapEquivariant q hq hequiv).measure = ν)
    (a : Y →ᵇ ℝ)
    (μ : InvariantProbabilityMeasure ϕ) :
    observableAverage
        (a.compContinuous ⟨q, hq⟩) μ.measure =
      observableAverage a ν := by
  rw [← observableAverage_mapEquivariant
    μ q hq hequiv a, hunique μ]

end

end HGAS.Dynamics
