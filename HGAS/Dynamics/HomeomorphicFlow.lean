import HGAS.Dynamics.UniformNegativeBlocks
import Mathlib.Tactic

/-!
# Transporting flows and invariant averages through homeomorphisms

This module packages a standard reusable construction.  A homeomorphism
`e : X ≃ₜ Y` pulls a flow on `Y` back to `X` by

```
e⁻¹ ∘ ψₜ ∘ e.
```

Invariant probabilities push forward in both directions, their observable
averages are unchanged, and therefore attained maximal invariant averages
are preserved.
-/

namespace HGAS

open Function MeasureTheory Set
open scoped BoundedContinuousFunction

noncomputable section

namespace Flow

variable {τ X Y : Type*}
  [TopologicalSpace τ] [AddMonoid τ] [ContinuousAdd τ]
  [TopologicalSpace X] [TopologicalSpace Y]

/-- Pull a flow back through a homeomorphism. -/
def pullbackHomeomorph
    (e : X ≃ₜ Y) (ψ : Flow τ Y) : Flow τ X where
  toFun t x := e.symm (ψ t (e x))
  cont' := by
    fun_prop
  map_add' t₁ t₂ x := by
    simp [ψ.map_add]
  map_zero' x := by
    simp

@[simp]
theorem pullbackHomeomorph_apply
    (e : X ≃ₜ Y) (ψ : Flow τ Y) (t : τ) (x : X) :
    pullbackHomeomorph e ψ t x =
      e.symm (ψ t (e x)) :=
  rfl

/-- The defining homeomorphism semiconjugates the pullback flow to the
original flow. -/
theorem semiconj_pullbackHomeomorph
    (e : X ≃ₜ Y) (ψ : Flow τ Y) (t : τ) :
    Function.Semiconj e
      (pullbackHomeomorph e ψ t) (ψ t) := by
  intro x
  simp

/-- The inverse homeomorphism semiconjugates the original flow to its
pullback. -/
theorem semiconj_symm_pullbackHomeomorph
    (e : X ≃ₜ Y) (ψ : Flow τ Y) (t : τ) :
    Function.Semiconj e.symm
      (ψ t) (pullbackHomeomorph e ψ t) := by
  intro y
  simp

end Flow

namespace Dynamics.InvariantProbabilityMeasure

variable {X Y : Type*}
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- Push an invariant probability from a pullback flow to the original
flow. -/
def mapHomeomorph
    (e : X ≃ₜ Y) (ψ : Flow ℝ Y)
    (μ : InvariantProbabilityMeasure
      (Flow.pullbackHomeomorph e ψ)) :
    InvariantProbabilityMeasure ψ :=
  μ.mapEquivariant e e.continuous
    (Flow.semiconj_pullbackHomeomorph e ψ)

/-- Pull an invariant probability of the original flow back through the
homeomorphism. -/
def comapHomeomorph
    (e : X ≃ₜ Y) (ψ : Flow ℝ Y)
    (μ : InvariantProbabilityMeasure ψ) :
    InvariantProbabilityMeasure
      (Flow.pullbackHomeomorph e ψ) :=
  μ.mapEquivariant e.symm e.symm.continuous
    (Flow.semiconj_symm_pullbackHomeomorph e ψ)

@[simp]
theorem mapHomeomorph_measure
    (e : X ≃ₜ Y) (ψ : Flow ℝ Y)
    (μ : InvariantProbabilityMeasure
      (Flow.pullbackHomeomorph e ψ)) :
    (mapHomeomorph e ψ μ).measure =
      μ.measure.map e.continuous.measurable.aemeasurable :=
  rfl

@[simp]
theorem comapHomeomorph_measure
    (e : X ≃ₜ Y) (ψ : Flow ℝ Y)
    (μ : InvariantProbabilityMeasure ψ) :
    (comapHomeomorph e ψ μ).measure =
      μ.measure.map e.symm.continuous.measurable.aemeasurable :=
  rfl

end Dynamics.InvariantProbabilityMeasure

namespace Dynamics

variable {X Y : Type*}
  [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- Observable pullback through a homeomorphism. -/
def pullbackObservable
    (e : X ≃ₜ Y) (a : Y →ᵇ ℝ) : X →ᵇ ℝ :=
  a.compContinuous ⟨e, e.continuous⟩

omit [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace Y] [BorelSpace Y] in
@[simp]
theorem pullbackObservable_apply
    (e : X ≃ₜ Y) (a : Y →ᵇ ℝ) (x : X) :
    pullbackObservable e a x = a (e x) :=
  rfl

/-- Pushing an invariant probability through the homeomorphism preserves
the corresponding observable average. -/
theorem observableAverage_mapHomeomorph
    (e : X ≃ₜ Y) (ψ : Flow ℝ Y)
    (a : Y →ᵇ ℝ)
    (μ : InvariantProbabilityMeasure
      (Flow.pullbackHomeomorph e ψ)) :
    observableAverage a
        (InvariantProbabilityMeasure.mapHomeomorph e ψ μ).measure =
      observableAverage (pullbackObservable e a) μ.measure := by
  unfold observableAverage
  rw [InvariantProbabilityMeasure.mapHomeomorph_measure]
  change
    (∫ y : Y, a y
        ∂Measure.map (fun x : X ↦ e x) (μ.measure : Measure X)) =
      ∫ x : X, pullbackObservable e a x ∂(μ.measure : Measure X)
  rw [integral_map
    (f := fun y : Y ↦ a y)
    (φ := fun x : X ↦ e x)
    e.continuous.measurable.aemeasurable
    a.continuous.aestronglyMeasurable]
  rfl

/-- Pulling an invariant probability back through the homeomorphism also
preserves the corresponding observable average. -/
theorem observableAverage_comapHomeomorph
    (e : X ≃ₜ Y) (ψ : Flow ℝ Y)
    (a : Y →ᵇ ℝ)
    (μ : InvariantProbabilityMeasure ψ) :
    observableAverage (pullbackObservable e a)
        (InvariantProbabilityMeasure.comapHomeomorph e ψ μ).measure =
      observableAverage a μ.measure := by
  unfold observableAverage
  rw [InvariantProbabilityMeasure.comapHomeomorph_measure]
  change
    (∫ x : X, pullbackObservable e a x
        ∂Measure.map (fun y : Y ↦ e.symm y)
          (μ.measure : Measure Y)) =
      ∫ y : Y, a y ∂(μ.measure : Measure Y)
  rw [integral_map
    (f := fun x : X ↦ pullbackObservable e a x)
    (φ := fun y : Y ↦ e.symm y)
    e.symm.continuous.measurable.aemeasurable
    (pullbackObservable e a).continuous.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [] with y
  simp

/-- Maximal invariant averages are invariant under topological conjugacy. -/
theorem maximalInvariantAverage_pullbackHomeomorph
    [CompactSpace X] [Nonempty X]
    [CompactSpace Y] [Nonempty Y]
    (e : X ≃ₜ Y) (ψ : Flow ℝ Y)
    (a : Y →ᵇ ℝ) :
    maximalInvariantAverage
        (Flow.pullbackHomeomorph e ψ)
        (pullbackObservable e a) =
      maximalInvariantAverage ψ a := by
  apply le_antisymm
  · let μX : InvariantProbabilityMeasure
        (Flow.pullbackHomeomorph e ψ) :=
      ⟨maximizingInvariantProbability
          (Flow.pullbackHomeomorph e ψ)
          (pullbackObservable e a),
        maximizingInvariantProbability_invariant
          (Flow.pullbackHomeomorph e ψ)
          (pullbackObservable e a)⟩
    have hle :=
      invariantAverage_le_maximalInvariantAverage
        ψ a
        (InvariantProbabilityMeasure.mapHomeomorph e ψ μX).measure
        (InvariantProbabilityMeasure.mapHomeomorph e ψ μX).invariant
    rw [observableAverage_mapHomeomorph] at hle
    exact hle
  · let μY : InvariantProbabilityMeasure ψ :=
      ⟨maximizingInvariantProbability ψ a,
        maximizingInvariantProbability_invariant ψ a⟩
    have hle :=
      invariantAverage_le_maximalInvariantAverage
        (Flow.pullbackHomeomorph e ψ)
        (pullbackObservable e a)
        (InvariantProbabilityMeasure.comapHomeomorph e ψ μY).measure
        (InvariantProbabilityMeasure.comapHomeomorph e ψ μY).invariant
    rw [observableAverage_comapHomeomorph] at hle
    exact hle

end Dynamics

end

end HGAS
