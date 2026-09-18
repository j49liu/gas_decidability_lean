import HGAS.Modular.GammaTwoCuspExcursionMeasure
import Mathlib.Tactic

/-!
# Orienting primitive rows along a nonperiodic horocycle

The primitive rows `v` and `-v` define the same cusp excursion.  Along a
nonperiodic horocycle their first moving coordinate `C` is nonzero, so
there is a unique choice of sign for which `C > 0`.  Indexing by these
positively oriented rows removes the only duplication in the excursion
family.

At the reference cutoff `1/3`, the resulting outer excursions are
pairwise disjoint and still cover every primitive-row short time.
-/

namespace HGAS.Modular

open Function Set

noncomputable section

/-- Negation preserves primitivity. -/
def negPrimitiveIntegralRow
    (v : PrimitiveIntegralRow) :
    PrimitiveIntegralRow :=
  ⟨-v.1, by
    rw [EisensteinSeries.mem_gammaSet_one]
    exact
      ((EisensteinSeries.mem_gammaSet_one v.1).mp v.2).neg_neg⟩

@[simp]
theorem negPrimitiveIntegralRow_coe
    (v : PrimitiveIntegralRow) :
    (negPrimitiveIntegralRow v).1 = -v.1 :=
  rfl

@[simp]
theorem primitiveIntegralRowMul_neg
    (v : PrimitiveIntegralRow)
    (g : RealModularFrame) :
    primitiveIntegralRowMul (negPrimitiveIntegralRow v) g =
      -primitiveIntegralRowMul v g :=
  primitiveIntegralRowMul_eq_neg_of_row_eq_neg rfl g

@[simp]
theorem primitiveRowShortTimes_neg
    (δ : ℝ) (g : RealModularFrame)
    (v : PrimitiveIntegralRow) :
    primitiveRowShortTimes δ g
        (negPrimitiveIntegralRow v) =
      primitiveRowShortTimes δ g v :=
  primitiveRowShortTimes_eq_of_row_eq_neg rfl δ g

/-- Primitive rows oriented by positivity of their constant first
coordinate along the horocycle through `g`. -/
abbrev PositivePrimitiveRowAt
    (g : RealModularFrame) :=
  {v : PrimitiveIntegralRow //
    0 < primitiveIntegralRowMul v g 0}

/-- The reference `1/3` excursions indexed by positively oriented rows
are pairwise disjoint. -/
theorem pairwise_disjoint_positivePrimitiveRowShortTimes_one_third
    (g : RealModularFrame) :
    Pairwise
      (Disjoint on
        (fun v : PositivePrimitiveRowAt g ↦
          primitiveRowShortTimes (1 / 3 : ℝ) g v.1)) := by
  intro v w hvw
  change
    Disjoint
      (primitiveRowShortTimes (1 / 3 : ℝ) g v.1)
      (primitiveRowShortTimes (1 / 3 : ℝ) g w.1)
  rw [Set.disjoint_iff_inter_eq_empty]
  apply not_nonempty_iff_eq_empty.mp
  intro hinter
  obtain ⟨t, htv, htw⟩ := hinter
  have hrows :=
    primitiveIntegralRows_eq_or_eq_neg_of_both_short
      v.1 w.1 (g * upperUnipotent t) htv htw
  rcases hrows with heq | hneg
  · apply hvw
    apply Subtype.ext
    exact Subtype.ext heq.symm
  · have hmul :=
      primitiveIntegralRowMul_eq_neg_of_row_eq_neg hneg g
    have hcoord :=
      congrFun hmul 0
    simp only [Pi.neg_apply] at hcoord
    nlinarith [v.2, w.2]

/-- Every primitive row can be represented by a positively oriented row
when the horocycle is nonperiodic. -/
theorem exists_positivePrimitiveRowAt_shortTimes_eq
    (g : RealModularFrame)
    (hnonperiodic :
      ¬ IsPeriodicHorocyclePoint 1
        (gammaTwoFrameQuotientMk g))
    (δ : ℝ) (v : PrimitiveIntegralRow) :
    ∃ w : PositivePrimitiveRowAt g,
      primitiveRowShortTimes δ g w.1 =
        primitiveRowShortTimes δ g v := by
  have hCne :
      primitiveIntegralRowMul v g 0 ≠ 0 :=
    primitiveIntegralRowMul_fst_ne_zero_of_nonperiodic
      g hnonperiodic v
  rcases lt_or_gt_of_ne hCne with hCneg | hCpos
  · let w0 := negPrimitiveIntegralRow v
    have hwpos :
        0 < primitiveIntegralRowMul w0 g 0 := by
      have hmul := primitiveIntegralRowMul_neg v g
      have hcoord := congrFun hmul 0
      dsimp only [w0]
      rw [hcoord]
      exact neg_pos.mpr hCneg
    exact ⟨⟨w0, hwpos⟩,
      primitiveRowShortTimes_neg δ g v⟩
  · exact ⟨⟨v, hCpos⟩, rfl⟩

/-- Positively oriented rows cover exactly the same short-time set as all
primitive rows. -/
theorem iUnion_positivePrimitiveRowShortTimes
    (g : RealModularFrame)
    (hnonperiodic :
      ¬ IsPeriodicHorocyclePoint 1
        (gammaTwoFrameQuotientMk g))
    (δ : ℝ) :
    (⋃ v : PositivePrimitiveRowAt g,
        primitiveRowShortTimes δ g v.1) =
      ⋃ v : PrimitiveIntegralRow,
        primitiveRowShortTimes δ g v := by
  apply le_antisymm
  · intro t ht
    obtain ⟨v, htv⟩ := mem_iUnion.mp ht
    exact mem_iUnion.mpr ⟨v.1, htv⟩
  · intro t ht
    obtain ⟨v, htv⟩ := mem_iUnion.mp ht
    obtain ⟨w, hw⟩ :=
      exists_positivePrimitiveRowAt_shortTimes_eq
        g hnonperiodic δ v
    exact mem_iUnion.mpr ⟨w, hw.symm ▸ htv⟩

end

end HGAS.Modular
