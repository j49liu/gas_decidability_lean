import HGAS.Dynamics.InvariantProbability
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Tactic

/-!
# Conditioning an invariant probability on an invariant set

If a measurable invariant set has positive mass, the normalized restriction
of an invariant probability to that set is again an invariant probability
for the restricted flow.  This is the positive-mass counterpart of
`InvariantFullMeasureRestriction`.

It is useful for decomposing a compactified skew-product measure into its
finite-chart and infinity parts.
-/

noncomputable section

open Function MeasureTheory Set

namespace HGAS.Dynamics

variable {X : Type*} [TopologicalSpace X]
  [MeasurableSpace X] [BorelSpace X]

namespace InvariantProbabilityMeasure

variable {ϕ : Flow ℝ X}

omit [MeasurableSpace X] [BorelSpace X] in
/-- A two-sided flow carries an invariant set onto itself, not merely into
itself. -/
theorem preimage_eq_of_isInvariant
    {s : Set X} (hinv : IsInvariant ϕ s) (t : ℝ) :
    (ϕ t) ⁻¹' s = s := by
  ext x
  constructor
  · intro hx
    have hback := hinv (-t) hx
    simpa [← ϕ.map_add] using hback
  · intro hx
    exact hinv t hx

/-- The restriction of an invariant measure to an invariant measurable set
is invariant as a finite measure. -/
theorem map_restrict_invariant
    (μ : InvariantProbabilityMeasure ϕ)
    {s : Set X} (hs : MeasurableSet s)
    (hinv : IsInvariant ϕ s) (t : ℝ) :
    Measure.map (ϕ t) ((μ.measure : Measure X).restrict s) =
      (μ.measure : Measure X).restrict s := by
  have hrestrictMap :=
    Measure.restrict_map
      (μ := (μ.measure : Measure X))
      (ϕ.continuous_toFun t).measurable hs
  rw [μ.map_time_toMeasure t,
    preimage_eq_of_isInvariant hinv t] at hrestrictMap
  exact hrestrictMap.symm

/-- Normalize the restriction to a positive-mass invariant measurable set
and pull it back to the subtype. -/
def restrictToPositiveInvariant
    (μ : InvariantProbabilityMeasure ϕ)
    {s : Set X} (hs : MeasurableSet s)
    (hpos : (μ.measure : Measure X) s ≠ 0)
    (hinv : IsInvariant ϕ s) :
    InvariantProbabilityMeasure (ϕ.restrict hinv) := by
  letI : Nonempty s :=
    ⟨(nonempty_of_measure_ne_zero hpos).some,
      (nonempty_of_measure_ne_zero hpos).some_mem⟩
  let m : FiniteMeasure s :=
    ⟨Measure.comap ((↑) : s → X) (μ.measure : Measure X),
      ⟨by
        rw [comap_subtype_coe_apply hs]
        rw [image_univ, Subtype.range_coe]
        exact (measure_ne_top (μ.measure : Measure X) s).lt_top⟩⟩
  have hmne : m ≠ 0 := by
    intro hm
    have hmMeasure :
        (m : Measure s) = 0 :=
      congrArg FiniteMeasure.toMeasure hm
    have huniv := congrArg (fun ν : Measure s ↦ ν Set.univ)
      hmMeasure
    change
      Measure.comap ((↑) : s → X)
          (μ.measure : Measure X) Set.univ =
        0 at huniv
    rw [comap_subtype_coe_apply hs, image_univ,
      Subtype.range_coe] at huniv
    exact hpos huniv
  let ν : ProbabilityMeasure s := m.normalize
  refine ⟨ν, ?_⟩
  intro t
  apply ProbabilityMeasure.toMeasure_injective
  simp only [timePushforward, ProbabilityMeasure.toMeasure_map]
  change
    Measure.map ((ϕ.restrict hinv) t) (ν : Measure s) =
      (ν : Measure s)
  rw [show (ν : Measure s) = m.mass⁻¹ • (m : Measure s) by
    exact FiniteMeasure.toMeasure_normalize_eq_of_nonzero m hmne]
  rw [Measure.map_smul]
  congr 1
  apply (MeasurableEmbedding.subtype_coe hs).map_injective
  rw [Measure.map_map measurable_subtype_coe
    ((ϕ.restrict hinv).continuous_toFun t).measurable]
  rw [show
      ((↑) : s → X) ∘ ((ϕ.restrict hinv) t) =
        (ϕ t) ∘ ((↑) : s → X) by
      funext x
      rfl]
  rw [← Measure.map_map
    (ϕ.continuous_toFun t).measurable
    measurable_subtype_coe]
  change
    Measure.map (ϕ t)
        (Measure.map ((↑) : s → X)
          (Measure.comap ((↑) : s → X)
            (μ.measure : Measure X))) =
      Measure.map ((↑) : s → X)
        (Measure.comap ((↑) : s → X)
          (μ.measure : Measure X))
  rw [map_comap_subtype_coe hs, map_restrict_invariant μ hs hinv t]

end InvariantProbabilityMeasure

end HGAS.Dynamics

end
