import HGAS.Dynamics.InvariantProbability
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Tactic

/-!
# Restricting an invariant probability to a full-measure invariant set

An invariant probability on an ambient flow can be transported to the
subtype of any measurable invariant set having full measure.  This is the
measure-theoretic bridge used when a compactified invariant measure gives
full mass to its finite affine chart.

The construction uses the pullback measure along the subtype inclusion.
Full measure makes that pullback a probability; invariance follows by
pushing both sides back through the measurable embedding.
-/

noncomputable section

open Function MeasureTheory Set

namespace HGAS.Dynamics

variable {X : Type*} [TopologicalSpace X]
  [MeasurableSpace X] [BorelSpace X]

namespace InvariantProbabilityMeasure

variable {ϕ : Flow ℝ X}

/-- Pull an invariant probability back to a measurable invariant set of
full measure. -/
def restrictToFullMeasureInvariant
    (μ : InvariantProbabilityMeasure ϕ)
    {s : Set X} (hs : MeasurableSet s)
    (hfull : (μ.measure : Measure X) s = 1)
    (hinv : IsInvariant ϕ s) :
    InvariantProbabilityMeasure (ϕ.restrict hinv) := by
  have hae : ∀ᵐ x ∂(μ.measure : Measure X), x ∈ s := by
    apply (ae_mem_iff_measure_eq hs.nullMeasurableSet).2
    simpa only [measure_univ] using hfull
  let ν : ProbabilityMeasure s :=
    ⟨Measure.comap ((↑) : s → X) (μ.measure : Measure X),
      (MeasurableEmbedding.subtype_coe hs).isProbabilityMeasure_comap
        (by simpa only [Subtype.range_coe] using hae)⟩
  refine ⟨ν, ?_⟩
  intro t
  apply ProbabilityMeasure.toMeasure_injective
  change
    Measure.map ((ϕ.restrict hinv) t)
        (Measure.comap ((↑) : s → X) (μ.measure : Measure X)) =
      Measure.comap ((↑) : s → X) (μ.measure : Measure X)
  apply (MeasurableEmbedding.subtype_coe hs).map_injective
  rw [Measure.map_map measurable_subtype_coe
    ((ϕ.restrict hinv).continuous_toFun t).measurable]
  rw [map_comap_subtype_coe hs]
  have hrestrict :
      (μ.measure : Measure X).restrict s =
        (μ.measure : Measure X) :=
    Measure.restrict_eq_self_of_ae_mem hae
  rw [hrestrict]
  rw [show
      ((↑) : s → X) ∘ ((ϕ.restrict hinv) t) =
        (ϕ t) ∘ ((↑) : s → X) by
      funext x
      rfl]
  rw [← Measure.map_map
    ((ϕ.continuous_toFun t).measurable)
    measurable_subtype_coe]
  rw [map_comap_subtype_coe hs, hrestrict,
    μ.map_time_toMeasure t]

@[simp]
theorem restrictToFullMeasureInvariant_measure
    (μ : InvariantProbabilityMeasure ϕ)
    {s : Set X} (hs : MeasurableSet s)
    (hfull : (μ.measure : Measure X) s = 1)
    (hinv : IsInvariant ϕ s) :
    ((μ.restrictToFullMeasureInvariant hs hfull hinv).measure :
      Measure s) =
      Measure.comap ((↑) : s → X) (μ.measure : Measure X) := by
  simp [restrictToFullMeasureInvariant]

/-- Pushing the restricted probability back to the ambient space recovers
the original full-measure probability. -/
theorem map_restrictToFullMeasureInvariant_measure
    (μ : InvariantProbabilityMeasure ϕ)
    {s : Set X} (hs : MeasurableSet s)
    (hfull : (μ.measure : Measure X) s = 1)
    (hinv : IsInvariant ϕ s) :
    Measure.map ((↑) : s → X)
        ((μ.restrictToFullMeasureInvariant hs hfull hinv).measure :
          Measure s) =
      (μ.measure : Measure X) := by
  rw [restrictToFullMeasureInvariant_measure,
    map_comap_subtype_coe hs]
  exact Measure.restrict_eq_self_of_ae_mem <|
    (ae_mem_iff_measure_eq hs.nullMeasurableSet).2 <| by
      simpa only [measure_univ] using hfull

end InvariantProbabilityMeasure

end HGAS.Dynamics

end
