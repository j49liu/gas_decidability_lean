import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Tactic

/-!
# Measure bounds for a disjoint family of excursions

This file isolates the countable-additivity bookkeeping used by the
horocycle cusp argument.  An inner family is compared term by term with
a pairwise-disjoint measurable outer family inside an observation
window.  There are two forms:

* every index satisfies the comparison;
* one distinguished index is exceptional and is paid for by a finite
  additive constant.

The lemmas are measure-theoretic and make no reference to modular
geometry.
-/

namespace HGAS.MeasureTheory

open Function _root_.MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {α ι : Type*} [MeasurableSpace α] [Countable ι]

/-- Summing a termwise comparison against pairwise-disjoint outer sets
costs at most the measure of the observation window. -/
theorem measure_iUnion_inter_le_mul_of_pairwise
    (μ : Measure α)
    (inner outer : ι → Set α)
    (W : Set α) (q : ℝ≥0∞)
    (hW : MeasurableSet W)
    (houterDisjoint : Pairwise (Disjoint on outer))
    (houterMeasurable : ∀ i, MeasurableSet (outer i))
    (hterm :
      ∀ i,
        μ (inner i ∩ W) ≤ q * μ (outer i ∩ W)) :
    μ (⋃ i, inner i ∩ W) ≤ q * μ W := by
  calc
    μ (⋃ i, inner i ∩ W) ≤
        ∑' i, μ (inner i ∩ W) :=
      measure_iUnion_le _
    _ ≤ ∑' i, q * μ (outer i ∩ W) :=
      ENNReal.tsum_le_tsum hterm
    _ = q * ∑' i, μ (outer i ∩ W) :=
      ENNReal.tsum_mul_left
    _ = q * μ (⋃ i, outer i ∩ W) := by
      congr 1
      rw [measure_iUnion]
      · intro i j hij
        exact
          (houterDisjoint hij).mono
            inter_subset_left inter_subset_left
      · intro i
        exact (houterMeasurable i).inter hW
    _ ≤ q * μ W := by
      gcongr
      exact iUnion_subset fun i ↦ inter_subset_right

/-- The same estimate with one distinguished exceptional excursion.
Its entire clipped measure is absorbed into the additive constant `B`.
-/
theorem measure_iUnion_inter_le_add_mul_of_one_exception
    (μ : Measure α)
    (inner outer : ι → Set α)
    (W : Set α) (q B : ℝ≥0∞)
    (e : ι)
    (hW : MeasurableSet W)
    (houterDisjoint : Pairwise (Disjoint on outer))
    (houterMeasurable : ∀ i, MeasurableSet (outer i))
    (hexception : μ (inner e ∩ W) ≤ B)
    (hterm :
      ∀ i, i ≠ e →
        μ (inner i ∩ W) ≤ q * μ (outer i ∩ W)) :
    μ (⋃ i, inner i ∩ W) ≤ B + q * μ W := by
  classical
  let J := {i : ι // i ≠ e}
  have hsubset :
      (⋃ i, inner i ∩ W) ⊆
        (inner e ∩ W) ∪
          ⋃ j : J, inner j.1 ∩ W := by
    intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    by_cases hie : i = e
    · left
      simpa only [hie] using hxi
    · right
      exact mem_iUnion.mpr ⟨⟨i, hie⟩, hxi⟩
  calc
    μ (⋃ i, inner i ∩ W) ≤
        μ ((inner e ∩ W) ∪
          ⋃ j : J, inner j.1 ∩ W) :=
      measure_mono hsubset
    _ ≤ μ (inner e ∩ W) +
          μ (⋃ j : J, inner j.1 ∩ W) :=
      measure_union_le _ _
    _ ≤ B + q * μ W := by
      gcongr
      exact
        measure_iUnion_inter_le_mul_of_pairwise
          μ (fun j : J ↦ inner j.1)
          (fun j : J ↦ outer j.1)
          W q hW
          (by
            intro i j hij
            exact houterDisjoint
              (fun h ↦ hij (Subtype.ext h)))
          (fun j ↦ houterMeasurable j.1)
          (fun j ↦ hterm j.1 j.2)

end

end HGAS.MeasureTheory
