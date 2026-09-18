import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Recovering a measure supported on a measurable section

Suppose `π : X → B` has a measurable section `ι : B → X`.  Any measure on
`X` supported on the section is uniquely determined by its `π`-marginal:

```
                    μ = ι₊ (π₊ μ).
```

For the compact accumulator, `ι` is the infinity graph.  Once the finite
chart has zero mass, this lemma turns support on the infinity graph into
the exact product/graph measure asserted in the reduction.
-/

noncomputable section

open Function MeasureTheory Set

namespace HGAS.Dynamics

variable {X B : Type*}
  [MeasurableSpace X] [MeasurableSpace B]

/-- A measure supported on a measurable section is the pushforward of its
marginal along that section. -/
theorem measure_eq_map_section_of_ae_mem_range
    (μ : Measure X)
    (π : X → B) (hπ : Measurable π)
    (ι : B → X) (hι : Measurable ι)
    (hsection : Function.LeftInverse π ι)
    (hsupport : ∀ᵐ x ∂μ, x ∈ Set.range ι) :
    Measure.map ι (Measure.map π μ) = μ := by
  rw [Measure.map_map hι hπ]
  have hae :
      (ι ∘ π) =ᵐ[μ] id := by
    filter_upwards [hsupport] with x hx
    obtain ⟨b, rfl⟩ := hx
    simp only [comp_apply, hsection b, id_eq]
  rw [Measure.map_congr hae]
  simp

/-- Probability-measure version of
`measure_eq_map_section_of_ae_mem_range`. -/
theorem probabilityMeasure_eq_map_section_of_ae_mem_range
    (μ : ProbabilityMeasure X)
    (π : X → B) (hπ : Measurable π)
    (ι : B → X) (hι : Measurable ι)
    (hsection : Function.LeftInverse π ι)
    (hsupport : ∀ᵐ x ∂(μ : Measure X), x ∈ Set.range ι) :
    μ =
      (μ.map hπ.aemeasurable).map hι.aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_map]
  exact (measure_eq_map_section_of_ae_mem_range
    (μ : Measure X) π hπ ι hι hsection hsupport).symm

/-- If the complement of a null set is exactly the range of a section,
then the measure is the section pushforward of its marginal. -/
theorem measure_eq_map_section_of_compl_eq_range
    (μ : Measure X)
    {s : Set X} (hnull : μ s = 0)
    (π : X → B) (hπ : Measurable π)
    (ι : B → X) (hι : Measurable ι)
    (hsection : Function.LeftInverse π ι)
    (hcompl : sᶜ = Set.range ι) :
    Measure.map ι (Measure.map π μ) = μ := by
  apply measure_eq_map_section_of_ae_mem_range
    μ π hπ ι hι hsection
  have hnot : ∀ᵐ x ∂μ, x ∉ s :=
    measure_eq_zero_iff_ae_notMem.mp hnull
  filter_upwards [hnot] with x hx
  rw [← hcompl]
  exact hx

end HGAS.Dynamics

end
