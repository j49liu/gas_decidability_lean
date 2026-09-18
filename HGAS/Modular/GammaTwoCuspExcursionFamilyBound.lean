import HGAS.MeasureTheory.DisjointExcursionFamily
import HGAS.Modular.GammaTwoOrientedPrimitiveRows
import Mathlib.Tactic

/-!
# The uniform finite-time cusp-excursion bound

This file assembles the interval geometry into the quantitative estimate
used for nonescape.  For a nonperiodic frame `g` and a cutoff
`0 < δ ≤ 1/6`, let `Badδ(g)` be the union of times at which some
primitive row of `g u(t)` has length below `δ`.

There is a finite, orbit-dependent initial cost `B`, but the coefficient
of the observation time is uniform:

```text
  volume (Badδ(g) ∩ (0,T]) ≤ B + (12δ) T.
```

Only the single reference excursion that may contain time zero
contributes to `B`.  All other inner excursions are controlled by their
pairwise-disjoint outer `1/3` excursions.
-/

namespace HGAS.Modular

open Function _root_.MeasureTheory Set
open scoped ENNReal

noncomputable section

private theorem primitiveRowShortTimes_eq_empty_of_not_short
    {δ : ℝ} (g : RealModularFrame)
    (v : PrimitiveIntegralRow)
    (hnot :
      ¬ primitiveIntegralRowMul v g 0 ^ 2 < δ ^ 2) :
    primitiveRowShortTimes δ g v = ∅ := by
  rw [primitiveRowShortTimes_eq_affine]
  ext t
  simp only [affineRowShortTimes, mem_setOf_eq,
    mem_empty_iff_false, iff_false]
  intro ht
  exact hnot
    ((le_add_of_nonneg_right
      (sq_nonneg
        (primitiveIntegralRowMul v g 0 * t +
          primitiveIntegralRowMul v g 1))).trans_lt ht)

/-- Every primitive-row excursion has finite Lebesgue length when its
constant first coordinate is nonzero. -/
theorem volume_primitiveRowShortTimes_lt_top
    {δ : ℝ} (g : RealModularFrame)
    (v : PrimitiveIntegralRow)
    (hC :
      primitiveIntegralRowMul v g 0 ≠ 0) :
    volume (primitiveRowShortTimes δ g v) < ∞ := by
  by_cases hshort :
      primitiveIntegralRowMul v g 0 ^ 2 < δ ^ 2
  · rw [primitiveRowShortTimes_eq_affine,
      volume_affineRowShortTimes hC hshort]
    exact ENNReal.ofReal_lt_top
  · rw [primitiveRowShortTimes_eq_empty_of_not_short
      g v hshort, measure_empty]
    exact ENNReal.zero_lt_top

/-- Termwise comparison of one noninitial `δ`-excursion with its
reference `1/3` excursion. -/
theorem volume_positivePrimitiveRowShortTimes_inter_le
    {δ : ℝ} (hδ : 0 < δ)
    (hδle : δ ≤ 1 / 6)
    (g : RealModularFrame)
    (v : PositivePrimitiveRowAt g)
    (T : ℝ)
    (hzero :
      0 ∉ primitiveRowShortTimes
        (1 / 3 : ℝ) g v.1) :
    volume
        (primitiveRowShortTimes δ g v.1 ∩
          Ioc 0 T) ≤
      ENNReal.ofReal (12 * δ) *
        volume
          (primitiveRowShortTimes
            (1 / 3 : ℝ) g v.1 ∩
              Ioc 0 T) := by
  let C := primitiveIntegralRowMul v.1 g 0
  let D := primitiveIntegralRowMul v.1 g 1
  have hC : C ≠ 0 := ne_of_gt v.2
  by_cases hshort : C ^ 2 < δ ^ 2
  · have hδthird : δ ≤ (1 / 3 : ℝ) := by
      norm_num at hδle ⊢
      linarith
    have houter : C ^ 2 < (1 / 3 : ℝ) ^ 2 :=
      hshort.trans_le
        ((sq_le_sq₀ hδ.le (by norm_num)).mpr hδthird)
    let c := affineRowExcursionCenter C D
    let r := affineRowExcursionRadius C δ
    let R := affineRowExcursionRadius C (1 / 3 : ℝ)
    let k := δ / (1 / 3 : ℝ)
    have hRpos : 0 < R :=
      affineRowExcursionRadius_pos hC houter
    have hrk : r ≤ k * R :=
      affineRowExcursionRadius_le_scaled
        hC hδ (by norm_num) hδthird hshort
    have hk : 0 ≤ k := (div_pos hδ (by norm_num)).le
    have hkle : k ≤ (1 / 2 : ℝ) := by
      dsimp only [k]
      norm_num at hδle ⊢
      linarith
    have hkone : k ≤ 1 := hkle.trans (by norm_num)
    have hrR : r ≤ R :=
      hrk.trans
        (by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right hkone hRpos.le)
    rw [primitiveRowShortTimes_eq_affine,
      affineRowShortTimes_eq_Ioo hC hshort]
    rw [primitiveRowShortTimes_eq_affine,
      affineRowShortTimes_eq_Ioo hC houter] at hzero ⊢
    have hbound :=
      volume_inner_Ioo_inter_Ioc_le
        (c := c) (r := r) (R := R)
        (k := k) (T := T)
        hRpos hrR hk hkle hrk hzero
    have hcoeff : 4 * k = 12 * δ := by
      dsimp only [k]
      ring
    rwa [hcoeff] at hbound
  · rw [primitiveRowShortTimes_eq_empty_of_not_short
      g v.1 hshort, empty_inter, measure_empty]
    exact bot_le

/-- Uniform linear bound for the union of all primitive-row short
times.  The additive constant is finite but may depend on the starting
frame. -/
theorem exists_finite_initialCost_volume_iUnion_shortTimes_le
    {δ : ℝ} (hδ : 0 < δ)
    (hδle : δ ≤ 1 / 6)
    (g : RealModularFrame) :
    ∃ B : ℝ≥0∞, B < ∞ ∧
      ∀ T : ℝ,
        volume
            (⋃ v : PositivePrimitiveRowAt g,
              primitiveRowShortTimes δ g v.1 ∩
                Ioc 0 T) ≤
          B + ENNReal.ofReal (12 * δ) *
            ENNReal.ofReal T := by
  let outer : PositivePrimitiveRowAt g → Set ℝ :=
    fun v ↦ primitiveRowShortTimes
      (1 / 3 : ℝ) g v.1
  let inner : PositivePrimitiveRowAt g → Set ℝ :=
    fun v ↦ primitiveRowShortTimes δ g v.1
  have hpairwise : Pairwise (Disjoint on outer) :=
    pairwise_disjoint_positivePrimitiveRowShortTimes_one_third g
  have houterMeasurable :
      ∀ v, MeasurableSet (outer v) :=
    fun v ↦
      (isOpen_primitiveRowShortTimes
        (1 / 3 : ℝ) g v.1).measurableSet
  by_cases hexception :
      ∃ e : PositivePrimitiveRowAt g,
        0 ∈ outer e
  · obtain ⟨e, he⟩ := hexception
    let B : ℝ≥0∞ := volume (inner e)
    have hBfinite : B < ∞ := by
      exact volume_primitiveRowShortTimes_lt_top
        g e.1 (ne_of_gt e.2)
    refine ⟨B, hBfinite, ?_⟩
    intro T
    have hbound :=
      HGAS.MeasureTheory.measure_iUnion_inter_le_add_mul_of_one_exception
        volume inner outer (Ioc 0 T)
        (ENNReal.ofReal (12 * δ)) B e
        measurableSet_Ioc hpairwise houterMeasurable
        (measure_mono inter_subset_left)
        (fun v hve ↦ ?_)
    · simpa only [inner, outer, Real.volume_Ioc,
        sub_zero] using hbound
    · apply volume_positivePrimitiveRowShortTimes_inter_le
        hδ hδle g v T
      intro hvzero
      have hdisjoint : Disjoint (outer v) (outer e) :=
        hpairwise (fun h ↦ hve h)
      exact Set.disjoint_left.mp hdisjoint hvzero he
  · refine ⟨0, ENNReal.zero_lt_top, ?_⟩
    intro T
    have hbound :=
      HGAS.MeasureTheory.measure_iUnion_inter_le_mul_of_pairwise
        volume inner outer (Ioc 0 T)
        (ENNReal.ofReal (12 * δ))
        measurableSet_Ioc hpairwise houterMeasurable
        (fun v ↦
          volume_positivePrimitiveRowShortTimes_inter_le
            hδ hδle g v T
            (fun hv ↦ hexception ⟨v, hv⟩))
    simpa only [inner, outer, Real.volume_Ioc,
      sub_zero, zero_add] using hbound

end

end HGAS.Modular
