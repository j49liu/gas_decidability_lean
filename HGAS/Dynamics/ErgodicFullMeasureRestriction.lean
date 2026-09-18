import HGAS.Dynamics.ErgodicInvariantProbability
import HGAS.Dynamics.InvariantFullMeasureRestriction
import HGAS.Dynamics.InvariantPositiveRestriction
import Mathlib.Tactic

/-!
# Ergodicity on a full-measure invariant subtype

Restricting an invariant probability to a measurable invariant set of full
measure preserves ergodicity.  The invariant-measure construction itself
is in `InvariantFullMeasureRestriction`; this file supplies the zero--one
law needed by pointwise ergodic arguments on the restricted flow.
-/

noncomputable section

open Function MeasureTheory Set

namespace HGAS.Dynamics

variable {X : Type*} [TopologicalSpace X]
  [MeasurableSpace X] [BorelSpace X]
  {ϕ : Flow ℝ X}

namespace IsErgodicInvariantProbability

/-- A measurable invariant set of positive mass has full mass under an
ergodic invariant probability. -/
theorem measure_eq_one_of_ne_zero_of_isInvariant
    {μ : ProbabilityMeasure X}
    (hμ : IsErgodicInvariantProbability ϕ μ)
    {s : Set X} (hs : MeasurableSet s)
    (hinv : IsInvariant ϕ s)
    (hpos : (μ : Measure X) s ≠ 0) :
    (μ : Measure X) s = 1 := by
  rcases hμ.zero_or_one_of_isInvariant hs hinv with hzero | hone
  · exact (hpos hzero).elim
  · exact hone

/-- An ergodic invariant probability remains ergodic after restriction to
a measurable invariant set of full measure. -/
theorem restrictToFullMeasureInvariant
    (μ : InvariantProbabilityMeasure ϕ)
    (hμ : IsErgodicInvariantProbability ϕ μ.measure)
    {s : Set X} (hs : MeasurableSet s)
    (hfull : (μ.measure : Measure X) s = 1)
    (hinv : IsInvariant ϕ s) :
    IsErgodicInvariantProbability
      (ϕ.restrict hinv)
      (μ.restrictToFullMeasureInvariant hs hfull hinv).measure := by
  let ν : InvariantProbabilityMeasure (ϕ.restrict hinv) :=
    μ.restrictToFullMeasureInvariant hs hfull hinv
  refine ⟨ν.invariant, ?_⟩
  intro A hA hAInvariant
  let B : Set X := ((↑) : s → X) '' A
  have hB : MeasurableSet B :=
    (MeasurableEmbedding.subtype_coe hs).measurableSet_image' hA
  have hmem (x : s) :
      ((x : X) ∈ B) ↔ x ∈ A := by
    constructor
    · rintro ⟨y, hy, hxy⟩
      have : y = x := Subtype.ext hxy
      simpa only [this] using hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hBInvariant :
      ∀ t : ℝ,
        (ϕ t) ⁻¹' B =ᵐ[(μ.measure : Measure X)] B := by
    intro t
    rw [← μ.map_restrictToFullMeasureInvariant_measure
      hs hfull hinv]
    change
      ∀ᵐ x ∂Measure.map ((↑) : s → X)
          ((μ.restrictToFullMeasureInvariant
            hs hfull hinv).measure : Measure s),
        (ϕ t x ∈ B) = (x ∈ B)
    rw [(MeasurableEmbedding.subtype_coe hs).ae_map_iff]
    filter_upwards [hAInvariant t] with x hx
    rw [show
      ϕ t (x : X) =
        (((ϕ.restrict hinv) t x : s) : X) from rfl]
    simpa only [hmem] using hx
  have hmass :
      ((ν.measure : ProbabilityMeasure s) : Measure s) A =
        (μ.measure : Measure X) B := by
    change
      ((μ.restrictToFullMeasureInvariant
          hs hfull hinv).measure : Measure s) A =
        (μ.measure : Measure X) B
    rw [InvariantProbabilityMeasure.restrictToFullMeasureInvariant_measure]
    exact comap_subtype_coe_apply hs (μ.measure : Measure X) A
  rcases hμ.zero_or_one hB hBInvariant with hzero | hone
  · left
    rw [hmass]
    exact hzero
  · right
    rw [hmass]
    exact hone

end IsErgodicInvariantProbability

namespace InvariantProbabilityMeasure

/-- When the invariant set has full mass, the normalized positive-mass
restriction and the direct full-measure pullback have the same underlying
probability. -/
theorem restrictToPositiveInvariant_measure_eq_of_full
    (μ : InvariantProbabilityMeasure ϕ)
    {s : Set X} (hs : MeasurableSet s)
    (hfull : (μ.measure : Measure X) s = 1)
    (hpos : (μ.measure : Measure X) s ≠ 0)
    (hinv : IsInvariant ϕ s) :
    (μ.restrictToPositiveInvariant hs hpos hinv).measure =
      (μ.restrictToFullMeasureInvariant hs hfull hinv).measure := by
  letI : Nonempty s :=
    ⟨(nonempty_of_measure_ne_zero hpos).some,
      (nonempty_of_measure_ne_zero hpos).some_mem⟩
  apply ProbabilityMeasure.toMeasure_injective
  rw [restrictToFullMeasureInvariant_measure]
  unfold restrictToPositiveInvariant
  dsimp only
  let m : FiniteMeasure s :=
    ⟨Measure.comap ((↑) : s → X) (μ.measure : Measure X),
      ⟨by
        rw [comap_subtype_coe_apply hs, image_univ,
          Subtype.range_coe]
        exact (measure_ne_top (μ.measure : Measure X) s).lt_top⟩⟩
  have hmne : m ≠ 0 := by
    intro hm
    have hmMeasure :
        (m : Measure s) = 0 :=
      congrArg FiniteMeasure.toMeasure hm
    have huniv :=
      congrArg (fun ν : Measure s ↦ ν Set.univ) hmMeasure
    change
      Measure.comap ((↑) : s → X)
          (μ.measure : Measure X) Set.univ =
        0 at huniv
    rw [comap_subtype_coe_apply hs, image_univ,
      Subtype.range_coe] at huniv
    exact hpos huniv
  change (m.normalize : Measure s) =
    Measure.comap ((↑) : s → X) (μ.measure : Measure X)
  rw [m.toMeasure_normalize_eq_of_nonzero hmne]
  have hmass : m.mass = 1 := by
    change
      (Measure.comap ((↑) : s → X)
        (μ.measure : Measure X) Set.univ).toNNReal = 1
    rw [comap_subtype_coe_apply hs, image_univ,
      Subtype.range_coe, hfull]
    norm_num
  rw [hmass]
  simp [m]

end InvariantProbabilityMeasure

namespace IsErgodicInvariantProbability

/-- The positive-mass restriction of an ergodic invariant probability to
an invariant measurable set is ergodic.  Ergodicity first upgrades
positive mass to full mass, after which the two restriction
constructions coincide. -/
theorem restrictToPositiveInvariant
    (μ : InvariantProbabilityMeasure ϕ)
    (hμ : IsErgodicInvariantProbability ϕ μ.measure)
    {s : Set X} (hs : MeasurableSet s)
    (hpos : (μ.measure : Measure X) s ≠ 0)
    (hinv : IsInvariant ϕ s) :
    IsErgodicInvariantProbability
      (ϕ.restrict hinv)
      (μ.restrictToPositiveInvariant hs hpos hinv).measure := by
  have hfull :
      (μ.measure : Measure X) s = 1 :=
    hμ.measure_eq_one_of_ne_zero_of_isInvariant hs hinv hpos
  have hfullErgodic :=
    hμ.restrictToFullMeasureInvariant μ hs hfull hinv
  rw [InvariantProbabilityMeasure.restrictToPositiveInvariant_measure_eq_of_full
    μ hs hfull hpos hinv]
  exact hfullErgodic

end IsErgodicInvariantProbability

end HGAS.Dynamics

end
