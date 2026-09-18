import HGAS.Modular.GammaTwoOrientedPrimitiveRows
import HGAS.Modular.HorocycleShearingAlgebra
import Mathlib.Tactic

/-!
# Thick-part recurrence of nonperiodic level-two geodesic rays

This module proves the deterministic recurrence fact used to choose the
"good times" in the elementary Dani--Smillie argument.

For a primitive integral row `v`, write

```text
  v g = (C,D).
```

Along the positive geodesic ray its squared length is

```text
  ‖v g a(t)‖² = C² exp(t) + D² exp(-t).
```

If the positive horocycle through `Γ(2)g` is nonperiodic, then `C ≠ 0`
for every primitive row.  Consequently the interval of sufficiently
short geodesic times associated to any fixed row is bounded above.

At the cutoff `1/3`, two distinct oriented primitive rows cannot be
short at the same time.  Their short-time sets are therefore pairwise
disjoint open subsets of the real line.  If every point of a half-line
were a short time for some row, connectedness of the half-line would
force one fixed row to remain short throughout that half-line, contrary
to its boundedness.  Thus the geodesic ray has arbitrarily late times
at which every primitive row has length at least `1/3`.  The explicit
Mahler criterion places all these return points in one compact core.

The proof is entirely elementary: it uses only matrix multiplication,
the integer-determinant separation lemma, connectedness of real
intervals, and the previously proved level-two Mahler compactness
criterion.
-/

namespace HGAS.Modular

open Filter Function Matrix Set Topology
open scoped MatrixGroups

noncomputable section

@[simp]
theorem primitiveIntegralRowMul_geodesicFrame_fst
    (v : PrimitiveIntegralRow) (g : RealModularFrame) (t : ℝ) :
    primitiveIntegralRowMul v (g * geodesicFrame t) 0 =
      primitiveIntegralRowMul v g 0 * Real.exp (t / 2) := by
  simp [primitiveIntegralRowMul,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
    Fin.sum_univ_two]
  ring

@[simp]
theorem primitiveIntegralRowMul_geodesicFrame_snd
    (v : PrimitiveIntegralRow) (g : RealModularFrame) (t : ℝ) :
    primitiveIntegralRowMul v (g * geodesicFrame t) 1 =
      primitiveIntegralRowMul v g 1 * Real.exp (-t / 2) := by
  simp [primitiveIntegralRowMul,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
    Fin.sum_univ_two]
  ring

theorem primitiveIntegralRowNormSq_geodesicFrame
    (v : PrimitiveIntegralRow) (g : RealModularFrame) (t : ℝ) :
    primitiveIntegralRowNormSq v (g * geodesicFrame t) =
      primitiveIntegralRowMul v g 0 ^ 2 * Real.exp t +
        primitiveIntegralRowMul v g 1 ^ 2 * Real.exp (-t) := by
  rw [primitiveIntegralRowNormSq,
    primitiveIntegralRowMul_geodesicFrame_fst,
    primitiveIntegralRowMul_geodesicFrame_snd]
  have hplus : Real.exp (t / 2) ^ 2 = Real.exp t := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hminus : Real.exp (-t / 2) ^ 2 = Real.exp (-t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [mul_pow, mul_pow, hplus, hminus]

def primitiveRowGeodesicShortTimes
    (δ : ℝ) (g : RealModularFrame)
    (v : PrimitiveIntegralRow) : Set ℝ :=
  {t |
    primitiveIntegralRowNormSq v
      (g * geodesicFrame t) < δ ^ 2}

theorem isOpen_primitiveRowGeodesicShortTimes
    (δ : ℝ) (g : RealModularFrame)
    (v : PrimitiveIntegralRow) :
    IsOpen (primitiveRowGeodesicShortTimes δ g v) := by
  rw [primitiveRowGeodesicShortTimes]
  apply isOpen_lt
  · rw [show
      (fun t ↦ primitiveIntegralRowNormSq v
        (g * geodesicFrame t)) =
      (fun t ↦
        primitiveIntegralRowMul v g 0 ^ 2 * Real.exp t +
          primitiveIntegralRowMul v g 1 ^ 2 * Real.exp (-t)) by
        funext t
        exact primitiveIntegralRowNormSq_geodesicFrame v g t]
    fun_prop
  · fun_prop

theorem pairwise_disjoint_positivePrimitiveRowGeodesicShortTimes_one_third
    (g : RealModularFrame) :
    Pairwise
      (Disjoint on
        (fun v : PositivePrimitiveRowAt g ↦
          primitiveRowGeodesicShortTimes
            (1 / 3 : ℝ) g v.1)) := by
  intro v w hvw
  change
    Disjoint
      (primitiveRowGeodesicShortTimes (1 / 3 : ℝ) g v.1)
      (primitiveRowGeodesicShortTimes (1 / 3 : ℝ) g w.1)
  rw [Set.disjoint_left]
  intro t htv htw
  have hrows :=
    primitiveIntegralRows_eq_or_eq_neg_of_both_short
      v.1 w.1 (g * geodesicFrame t) htv htw
  rcases hrows with heq | hneg
  · apply hvw
    apply Subtype.ext
    exact Subtype.ext heq.symm
  · have hmul :=
      primitiveIntegralRowMul_eq_neg_of_row_eq_neg hneg g
    have hcoord := congrFun hmul 0
    simp only [Pi.neg_apply] at hcoord
    nlinarith [v.2, w.2]

theorem primitiveRowGeodesicShortTimes_bddAbove
    {δ : ℝ} (g : RealModularFrame)
    (v : PositivePrimitiveRowAt g) :
    BddAbove
      (primitiveRowGeodesicShortTimes δ g v.1) := by
  let C : ℝ := primitiveIntegralRowMul v.1 g 0
  have hC : 0 < C := v.2
  have hlim :
      Tendsto (fun t : ℝ ↦ C ^ 2 * Real.exp t)
        atTop atTop := by
    exact Real.tendsto_exp_atTop.const_mul_atTop
      (sq_pos_of_pos hC)
  have hevent :
      ∀ᶠ t : ℝ in atTop,
        δ ^ 2 < C ^ 2 * Real.exp t :=
    hlim.eventually (eventually_gt_atTop (δ ^ 2))
  obtain ⟨B, hB⟩ := (eventually_atTop.1 hevent)
  refine ⟨B, ?_⟩
  intro t ht
  by_contra hBt
  have htB : B ≤ t := le_of_not_ge hBt
  have hlarge := hB t htB
  have hshort : primitiveIntegralRowNormSq v.1
      (g * geodesicFrame t) < δ ^ 2 := ht
  rw [primitiveIntegralRowNormSq_geodesicFrame] at hshort
  have hnonneg :
      0 ≤ primitiveIntegralRowMul v.1 g 1 ^ 2 *
        Real.exp (-t) := mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  dsimp only [C] at hlarge
  nlinarith

@[simp]
theorem primitiveRowGeodesicShortTimes_neg
    (δ : ℝ) (g : RealModularFrame)
    (v : PrimitiveIntegralRow) :
    primitiveRowGeodesicShortTimes δ g
        (negPrimitiveIntegralRow v) =
      primitiveRowGeodesicShortTimes δ g v := by
  ext t
  simp only [primitiveRowGeodesicShortTimes, mem_setOf_eq,
    primitiveIntegralRowNormSq]
  have hmul :=
    primitiveIntegralRowMul_neg v (g * geodesicFrame t)
  rw [hmul]
  simp only [Pi.neg_apply, neg_sq]

theorem exists_positivePrimitiveRowAt_geodesicShortTimes_eq
    (g : RealModularFrame)
    (hnonperiodic :
      ¬ IsPeriodicHorocyclePoint 1
        (gammaTwoFrameQuotientMk g))
    (δ : ℝ) (v : PrimitiveIntegralRow) :
    ∃ w : PositivePrimitiveRowAt g,
      primitiveRowGeodesicShortTimes δ g w.1 =
        primitiveRowGeodesicShortTimes δ g v := by
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
    exact
      ⟨⟨w0, hwpos⟩,
        primitiveRowGeodesicShortTimes_neg δ g v⟩
  · exact ⟨⟨v, hCpos⟩, rfl⟩

/-- A nonperiodic positive horocycle has arbitrarily late geodesic
times at which every primitive row has length at least `1/3`. -/
theorem exists_geodesic_thick_return_time_ge
    (g : RealModularFrame)
    (hnonperiodic :
      ¬ IsPeriodicHorocyclePoint 1
        (gammaTwoFrameQuotientMk g))
    (L₀ : ℝ) :
    ∃ L : ℝ, L₀ ≤ L ∧
      HasPrimitiveRowLowerBound (1 / 3 : ℝ)
        (g * geodesicFrame L) := by
  by_contra hreturn
  push Not at hreturn
  let S : PositivePrimitiveRowAt g → Set ℝ :=
    fun v ↦
      primitiveRowGeodesicShortTimes
        (1 / 3 : ℝ) g v.1
  have hcover :
      Ici L₀ ⊆ ⋃ v : PositivePrimitiveRowAt g, S v := by
    intro L hL
    have hnot := hreturn L hL
    rw [HasPrimitiveRowLowerBound] at hnot
    push Not at hnot
    obtain ⟨v, hv⟩ := hnot
    obtain ⟨w, hw⟩ :=
      exists_positivePrimitiveRowAt_geodesicShortTimes_eq
        g hnonperiodic (1 / 3 : ℝ) v
    apply mem_iUnion.mpr
    refine ⟨w, ?_⟩
    change L ∈ primitiveRowGeodesicShortTimes
      (1 / 3 : ℝ) g w.1
    rw [hw]
    exact hv
  obtain ⟨v₀, hv₀⟩ :=
    mem_iUnion.mp (hcover (by simp : L₀ ∈ Ici L₀))
  let U : Set ℝ := S v₀
  let V : Set ℝ :=
    ⋃ (v : PositivePrimitiveRowAt g),
      ⋃ (_ : v ≠ v₀), S v
  have hUopen : IsOpen U :=
    isOpen_primitiveRowGeodesicShortTimes
      (1 / 3 : ℝ) g v₀.1
  have hVopen : IsOpen V := by
    dsimp only [V]
    apply isOpen_iUnion
    intro v
    apply isOpen_iUnion
    intro _
    exact
      isOpen_primitiveRowGeodesicShortTimes
        (1 / 3 : ℝ) g v.1
  have hUV : Disjoint U V := by
    rw [Set.disjoint_left]
    intro L hLU hLV
    obtain ⟨v, hv⟩ := mem_iUnion.mp hLV
    obtain ⟨hvv₀, hLv⟩ := mem_iUnion.mp hv
    have hpair :=
      pairwise_disjoint_positivePrimitiveRowGeodesicShortTimes_one_third
        g hvv₀
    exact Set.disjoint_left.mp hpair hLv hLU
  have hcoverUV : Ici L₀ ⊆ U ∪ V := by
    intro L hL
    obtain ⟨v, hLv⟩ := mem_iUnion.mp (hcover hL)
    by_cases hv : v = v₀
    · left
      simpa only [U, S, hv] using hLv
    · right
      apply mem_iUnion.mpr
      refine ⟨v, mem_iUnion.mpr ⟨hv, ?_⟩⟩
      exact hLv
  have htailU : Ici L₀ ⊆ U :=
    isPreconnected_Ici.subset_left_of_subset_union
      hUopen hVopen hUV hcoverUV
      ⟨L₀, by simp, by simpa only [U, S] using hv₀⟩
  obtain ⟨B, hB⟩ :=
    primitiveRowGeodesicShortTimes_bddAbove
      (δ := (1 / 3 : ℝ)) g v₀
  let L : ℝ := max L₀ (B + 1)
  have hLmem : L ∈ U :=
    htailU (le_max_left L₀ (B + 1))
  have hLB : L ≤ B :=
    hB (by simpa only [U, S] using hLmem)
  have hBL : B < L :=
    (lt_add_one B).trans_le (le_max_right L₀ (B + 1))
  exact (not_le_of_gt hBL) hLB

/-- Sequence form of thick-part geodesic recurrence. -/
theorem exists_tendsto_geodesic_thick_return_times
    (g : RealModularFrame)
    (hnonperiodic :
      ¬ IsPeriodicHorocyclePoint 1
        (gammaTwoFrameQuotientMk g)) :
    ∃ L : ℕ → ℝ,
      Tendsto L atTop atTop ∧
      ∀ n,
        HasPrimitiveRowLowerBound (1 / 3 : ℝ)
          (g * geodesicFrame (L n)) := by
  choose L hLge hLthick using
    fun n : ℕ ↦
      exists_geodesic_thick_return_time_ge
        g hnonperiodic (n : ℝ)
  refine ⟨L, ?_, hLthick⟩
  exact
    tendsto_atTop_mono hLge
      tendsto_natCast_atTop_atTop

/-- The returned quotient points lie in one explicit compact Mahler
core. -/
theorem exists_tendsto_geodesic_mahler_return_times
    (g : RealModularFrame)
    (hnonperiodic :
      ¬ IsPeriodicHorocyclePoint 1
        (gammaTwoFrameQuotientMk g)) :
    ∃ L : ℕ → ℝ,
      Tendsto L atTop atTop ∧
      ∀ n,
        gammaTwoFrameQuotientMk
            (g * geodesicFrame (L n)) ∈
          gammaTwoMahlerCompactCore (1 / 3 : ℝ) := by
  obtain ⟨L, hLtop, hLthick⟩ :=
    exists_tendsto_geodesic_thick_return_times
      g hnonperiodic
  refine ⟨L, hLtop, ?_⟩
  intro n
  exact gammaTwoFrameQuotientMk_mem_mahlerCompactCore
    (by norm_num) _ (hLthick n)

/-- Quotient-intrinsic form of thick-part recurrence: every nonperiodic
positive horocycle base point has a sequence of positive-geodesic times
tending to infinity whose images remain in the fixed `1/3` Mahler
core. -/
theorem exists_tendsto_gammaTwoGeodesic_mahler_return_times
    (q : GammaTwoFrameQuotient)
    (hnonperiodic :
      ¬ IsPeriodicHorocyclePoint 1 q) :
    ∃ L : ℕ → ℝ,
      Tendsto L atTop atTop ∧
      ∀ n,
        gammaTwoFrameRightMul
            (geodesicFrame (L n)) q ∈
          gammaTwoMahlerCompactCore (1 / 3 : ℝ) := by
  induction q using Quotient.inductionOn with
  | _ g =>
      obtain ⟨L, hLtop, hLcore⟩ :=
        exists_tendsto_geodesic_mahler_return_times
          g hnonperiodic
      refine ⟨L, hLtop, ?_⟩
      intro n
      exact hLcore n

end

end HGAS.Modular
