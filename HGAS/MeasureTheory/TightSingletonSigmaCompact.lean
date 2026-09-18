import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.Topology.Compactness.SigmaCompact

/-!
# Tightness of one finite measure on a sigma-compact space

This module records a small tightness lemma in a form convenient for
noncompact homogeneous spaces.

Let `X` be a sigma-compact Hausdorff space equipped with its Borel
measurable structure.  Choose Mathlib's increasing compact exhaustion
`compactCovering X n`.  Its complements decrease to the empty set, so
continuity from above for a finite measure `μ` gives

```text
  μ ((compactCovering X n)ᶜ) → 0.
```

Consequently the singleton family `{μ}` is uniformly tight.  This avoids
introducing a complete metric merely to invoke the more familiar Polish
space tightness theorem.
-/

namespace HGAS.MeasureTheory

open Filter Function _root_.MeasureTheory Set Topology

noncomputable section

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
variable [BorelSpace X] [T2Space X] [SigmaCompactSpace X]

/-- Every finite Borel measure on a sigma-compact Hausdorff space is a
tight singleton family. -/
theorem isTightMeasureSet_singleton_of_sigmaCompact
    (μ : Measure X) [IsFiniteMeasure μ] :
    IsTightMeasureSet {μ} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  have hlim :
      Tendsto
        (fun n : ℕ ↦ μ (compactCovering X n)ᶜ)
        atTop (𝓝 0) := by
    have h :=
      tendsto_measure_iInter_atTop
        (μ := μ)
        (s := fun n : ℕ ↦ (compactCovering X n)ᶜ)
        (fun n ↦
          (isCompact_compactCovering X n).isClosed.measurableSet.compl.nullMeasurableSet)
        (fun _ _ hmn ↦
          compl_subset_compl.mpr
            (compactCovering_subset X hmn))
        ⟨0, measure_ne_top μ _⟩
    simpa only [Function.comp_apply, ← compl_iUnion,
      iUnion_compactCovering, compl_univ, measure_empty] using h
  obtain ⟨n, hn⟩ :=
    (hlim.eventually (Iio_mem_nhds hε)).exists
  exact
    ⟨compactCovering X n,
      isCompact_compactCovering X n,
      by simpa using hn.le⟩

end

end HGAS.MeasureTheory
