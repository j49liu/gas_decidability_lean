import HGAS.Modular.GammaTwoPrimitiveRowSeparation
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic

/-!
# Cusp excursions as disjoint nested intervals

For fixed real numbers `C ≠ 0` and `D`, the inequality

```text
  C² + (Ct + D)² < δ²
```

cuts out an open interval in the time variable.  Its center is `-D/C`
and its radius is

```text
  sqrt (δ² - C²) / |C|.
```

The primitive-row dynamics identifies precisely these intervals with
the times at which a lattice row is shorter than `δ`.  At the reference
cutoff `1/3`, distinct intervals are disjoint: an intersection would give
two simultaneously short primitive rows, and the integer-determinant
lemma says that the rows differ by sign and hence define the same
interval.
-/

namespace HGAS.Modular

open Matrix _root_.MeasureTheory Set
open scoped ENNReal MatrixGroups

noncomputable section

/-- Times at which the affine row `(C, Ct + D)` is shorter than `δ`. -/
def affineRowShortTimes
    (C D δ : ℝ) : Set ℝ :=
  {t | C ^ 2 + (C * t + D) ^ 2 < δ ^ 2}

theorem isOpen_affineRowShortTimes
    (C D δ : ℝ) :
    IsOpen (affineRowShortTimes C D δ) := by
  apply isOpen_lt
  · fun_prop
  · fun_prop

/-- Center of an affine row excursion. -/
def affineRowExcursionCenter
    (C D : ℝ) : ℝ :=
  -D / C

/-- Radius of an affine row excursion.  The useful case has
`C² < δ²`, so the square-root argument is positive. -/
def affineRowExcursionRadius
    (C δ : ℝ) : ℝ :=
  Real.sqrt (δ ^ 2 - C ^ 2) / |C|

theorem affineRowExcursionRadius_pos
    {C δ : ℝ} (hC : C ≠ 0)
    (hshort : C ^ 2 < δ ^ 2) :
    0 < affineRowExcursionRadius C δ := by
  exact div_pos
    (Real.sqrt_pos.2 (sub_pos.2 hshort))
    (abs_pos.2 hC)

theorem affineRowExcursionRadius_sq
    {C δ : ℝ} (hshort : C ^ 2 < δ ^ 2) :
    affineRowExcursionRadius C δ ^ 2 =
      (δ ^ 2 - C ^ 2) / C ^ 2 := by
  rw [affineRowExcursionRadius, div_pow, sq_abs,
    Real.sq_sqrt (sub_nonneg.2 hshort.le)]

/-- Exact interval description of one nondegenerate affine-row
excursion. -/
theorem affineRowShortTimes_eq_Ioo
    {C D δ : ℝ} (hC : C ≠ 0)
    (hshort : C ^ 2 < δ ^ 2) :
    affineRowShortTimes C D δ =
      Ioo
        (affineRowExcursionCenter C D -
          affineRowExcursionRadius C δ)
        (affineRowExcursionCenter C D +
          affineRowExcursionRadius C δ) := by
  let c := affineRowExcursionCenter C D
  let R := affineRowExcursionRadius C δ
  have hR : 0 < R :=
    affineRowExcursionRadius_pos hC hshort
  have hR2 :
      R ^ 2 = (δ ^ 2 - C ^ 2) / C ^ 2 :=
    affineRowExcursionRadius_sq hshort
  have hCsq : 0 < C ^ 2 := sq_pos_of_ne_zero hC
  have hlin (t : ℝ) :
      C * t + D = C * (t - c) := by
    dsimp only [c, affineRowExcursionCenter]
    field_simp [hC]
    ring
  ext t
  simp only [affineRowShortTimes, mem_setOf_eq, mem_Ioo]
  rw [hlin]
  have hequiv :
      C ^ 2 + (C * (t - c)) ^ 2 < δ ^ 2 ↔
        (t - c) ^ 2 < R ^ 2 := by
    rw [mul_pow]
    constructor <;> intro h
    · have hscale :
          C ^ 2 * R ^ 2 = δ ^ 2 - C ^ 2 := by
        rw [hR2]
        field_simp [hC]
      nlinarith
    · have hscale :
          C ^ 2 * R ^ 2 = δ ^ 2 - C ^ 2 := by
        rw [hR2]
        field_simp [hC]
      nlinarith
  rw [hequiv]
  constructor
  · intro hsq
    have habs : |t - c| < R :=
      abs_lt_of_sq_lt_sq hsq hR.le
    exact ⟨by linarith [abs_lt.mp habs |>.1],
      by linarith [abs_lt.mp habs |>.2]⟩
  · rintro ⟨hleft, hright⟩
    have habs : |t - c| < R :=
      abs_lt.mpr ⟨by linarith, by linarith⟩
    exact (sq_lt_sq.mpr
      (by simpa only [abs_of_pos hR] using habs))

/-- Full Lebesgue length of one affine-row excursion. -/
theorem volume_affineRowShortTimes
    {C D δ : ℝ} (hC : C ≠ 0)
    (hshort : C ^ 2 < δ ^ 2) :
    volume (affineRowShortTimes C D δ) =
      ENNReal.ofReal
        (2 * affineRowExcursionRadius C δ) := by
  rw [affineRowShortTimes_eq_Ioo hC hshort,
    Real.volume_Ioo]
  congr 1
  ring

/-- Times at which a primitive lattice row of `g u(t)` is shorter than
`δ`. -/
def primitiveRowShortTimes
    (δ : ℝ) (g : RealModularFrame)
    (v : PrimitiveIntegralRow) : Set ℝ :=
  {t |
    primitiveIntegralRowNormSq v
      (g * upperUnipotent t) < δ ^ 2}

/-- Primitive-row short times are the corresponding affine short-time
set. -/
theorem primitiveRowShortTimes_eq_affine
    (δ : ℝ) (g : RealModularFrame)
    (v : PrimitiveIntegralRow) :
    primitiveRowShortTimes δ g v =
      affineRowShortTimes
        (primitiveIntegralRowMul v g 0)
        (primitiveIntegralRowMul v g 1) δ := by
  ext t
  simp only [primitiveRowShortTimes, mem_setOf_eq,
    primitiveIntegralRowNormSq, affineRowShortTimes]
  rw [primitiveIntegralRowMul_upperUnipotent_fst,
    primitiveIntegralRowMul_upperUnipotent_snd]

theorem isOpen_primitiveRowShortTimes
    (δ : ℝ) (g : RealModularFrame)
    (v : PrimitiveIntegralRow) :
    IsOpen (primitiveRowShortTimes δ g v) := by
  rw [primitiveRowShortTimes_eq_affine]
  exact isOpen_affineRowShortTimes _ _ _

theorem primitiveIntegralRowMul_eq_neg_of_row_eq_neg
    {v w : PrimitiveIntegralRow}
    (hneg : w.1 = -v.1)
    (g : RealModularFrame) :
    primitiveIntegralRowMul w g =
      -primitiveIntegralRowMul v g := by
  funext j
  simp only [primitiveIntegralRowMul, hneg, Pi.neg_apply,
    Int.cast_neg]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Opposite primitive rows determine the same short-time set. -/
theorem primitiveRowShortTimes_eq_of_row_eq_neg
    {v w : PrimitiveIntegralRow}
    (hneg : w.1 = -v.1)
    (δ : ℝ) (g : RealModularFrame) :
    primitiveRowShortTimes δ g w =
      primitiveRowShortTimes δ g v := by
  ext t
  simp only [primitiveRowShortTimes, mem_setOf_eq,
    primitiveIntegralRowNormSq]
  have hmul :=
    primitiveIntegralRowMul_eq_neg_of_row_eq_neg
      hneg (g * upperUnipotent t)
  rw [hmul]
  simp only [Pi.neg_apply, neg_sq]

/-- At cutoff `1/3`, two primitive-row excursion intervals are either
identical or disjoint. -/
theorem primitiveRowShortTimes_one_third_eq_or_disjoint
    (g : RealModularFrame)
    (v w : PrimitiveIntegralRow) :
    primitiveRowShortTimes (1 / 3 : ℝ) g v =
        primitiveRowShortTimes (1 / 3 : ℝ) g w ∨
      Disjoint
        (primitiveRowShortTimes (1 / 3 : ℝ) g v)
        (primitiveRowShortTimes (1 / 3 : ℝ) g w) := by
  by_cases hinter :
      (primitiveRowShortTimes (1 / 3 : ℝ) g v ∩
        primitiveRowShortTimes (1 / 3 : ℝ) g w).Nonempty
  · obtain ⟨t, htv, htw⟩ := hinter
    have hrows :=
      primitiveIntegralRows_eq_or_eq_neg_of_both_short
        v w (g * upperUnipotent t) htv htw
    rcases hrows with heq | hneg
    · left
      congr 1
      exact Subtype.ext heq.symm
    · left
      exact
        (primitiveRowShortTimes_eq_of_row_eq_neg
          hneg (1 / 3 : ℝ) g).symm
  · right
    rw [Set.disjoint_iff_inter_eq_empty]
    exact not_nonempty_iff_eq_empty.mp hinter

end

end HGAS.Modular
