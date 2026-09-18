import Mathlib.MeasureTheory.Measure.Tight

/-!
# Tightness of finite families from tight singletons

Uniform nonescape estimates usually control only the tail of a sequence
of measures.  To recover tightness of the whole sequence one must also
absorb finitely many initial measures into a compact set.

The lemma in this file isolates the elementary finite-union step.  It is
stated without any finiteness or regularity assumption on the measures:
the only input is tightness of each singleton family.  This makes the
lemma useful in settings where singleton tightness is obtained by
different arguments.
-/

namespace HGAS.MeasureTheory

open _root_.MeasureTheory Set

/-- A finite set of measures is tight if each of its singleton subsets
is tight. -/
theorem isTightMeasureSet_of_finite_of_singletons
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {S : Set (Measure X)}
    (hS : S.Finite)
    (hsingleton :
      ∀ μ ∈ S, IsTightMeasureSet ({μ} : Set (Measure X))) :
    IsTightMeasureSet S := by
  induction S, hS using Set.Finite.induction_on with
  | empty =>
      rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
      intro ε hε
      exact ⟨∅, isCompact_empty, by simp⟩
  | @insert μ S hμ hS ih =>
      rw [insert_eq]
      exact
        (hsingleton μ (mem_insert μ S)).union
          (ih (fun ν hν ↦
            hsingleton ν (mem_insert_of_mem μ hν)))

end HGAS.MeasureTheory
