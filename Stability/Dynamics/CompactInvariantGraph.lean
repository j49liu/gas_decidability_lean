import HGAS.Dynamics.KrylovBogolyubov
import HGAS.Dynamics.InvariantComponentAverage

/-!
# Invariant probabilities carried by compact graph images

A continuous map from a nonempty compact space has a compact image.
If the ambient flow preserves that image, restricting the flow and
applying Krylov--Bogolyubov produces a probability supported there.
The parameter map need not be injective or equivariant in the same time.
-/

namespace Stability.Dynamics

noncomputable section

open HGAS.Dynamics MeasureTheory Set
open scoped BoundedContinuousFunction

variable {X A : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace A] [CompactSpace A] [Nonempty A]

/-- A compact invariant image carries an ambient invariant probability
giving the image full mass and preserving every pointwise reward bound. -/
theorem exists_invariantProbability_on_compact_range
    (flow : Flow ℝ X) (graph : A → X) (hgraph : Continuous graph)
    (hinvariant : ∀ t a, flow t (graph a) ∈ range graph)
    (reward : X →ᵇ ℝ) (lower : ℝ) (hlower : ∀ a, lower ≤ reward (graph a)) :
    ∃ μ : InvariantProbabilityMeasure flow,
      (μ.measure : Measure X) (range graph) = 1 ∧
        lower ≤ observableAverage reward μ.measure := by
  have hcompact : IsCompact (range graph) := isCompact_range hgraph
  have hinv : IsInvariant flow (range graph) := by
    rintro t _ ⟨a, rfl⟩
    exact hinvariant t a
  letI : CompactSpace (range graph) := isCompact_iff_compactSpace.mp hcompact
  letI : Nonempty (range graph) := ⟨⟨graph (Classical.choice inferInstance), mem_range_self _⟩⟩
  let ν := Classical.choice (nonempty_invariantProbabilityMeasure (flow.restrict hinv))
  refine ⟨ν.mapSubtype hinv, ?_, ?_⟩
  · change (Measure.map Subtype.val (ν.measure : Measure (range graph))) (range graph) = 1
    rw [Measure.map_apply measurable_subtype_coe hcompact.isClosed.measurableSet]
    simp
  · rw [observableAverage_mapSubtype]
    unfold observableAverage
    have hpoint : ∀ᵐ x : range graph ∂(ν.measure : Measure (range graph)),
        lower ≤ subtypeObservable reward (range graph) x := by
      filter_upwards with x
      obtain ⟨a, ha⟩ := x.property
      change lower ≤ reward x.val
      rw [← ha]
      exact hlower a
    calc
      lower = ∫ _ : range graph, lower ∂(ν.measure : Measure (range graph)) := by simp
      _ ≤ ∫ x : range graph, subtypeObservable reward (range graph) x
          ∂(ν.measure : Measure (range graph)) :=
        integral_mono_ae (integrable_const _)
          ((subtypeObservable reward _).integrable _) hpoint

end

end Stability.Dynamics
