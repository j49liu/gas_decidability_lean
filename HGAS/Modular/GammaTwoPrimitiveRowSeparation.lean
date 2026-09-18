import HGAS.Modular.GammaTwoPrimitiveRowDynamics
import Mathlib.Tactic

/-!
# Separation of primitive lattice-row excursions

At a fixed time, two genuinely different primitive lattice directions
cannot both be very short.  In dimension two this is an elementary
integer-determinant argument:

* the determinant of two integral rows is an integer;
* right multiplication by a unimodular real frame preserves it;
* if both resulting rows have all coordinates smaller than `1/3`, the
  determinant has absolute value less than one;
* hence that integer determinant vanishes;
* two primitive integral rows with determinant zero differ only by sign.

This is the separation input that makes the cusp excursions disjoint
after identifying `v` and `-v`.
-/

namespace HGAS.Modular

open Matrix Set
open scoped MatrixGroups

noncomputable section

/-- The integral determinant of two primitive row vectors. -/
def primitiveIntegralRowDet
    (v w : PrimitiveIntegralRow) : ℤ :=
  v.1 0 * w.1 1 - v.1 1 * w.1 0

/-- Vanishing determinant makes two primitive integral rows equal up to
sign. -/
theorem primitiveIntegralRows_eq_or_eq_neg_of_det_eq_zero
    (v w : PrimitiveIntegralRow)
    (hdet : primitiveIntegralRowDet v w = 0) :
    w.1 = v.1 ∨ w.1 = -v.1 := by
  have hv :
      IsCoprime (v.1 0) (v.1 1) :=
    (EisensteinSeries.mem_gammaSet_one v.1).mp v.2
  have hw :
      IsCoprime (w.1 0) (w.1 1) :=
    (EisensteinSeries.mem_gammaSet_one w.1).mp w.2
  obtain ⟨r, s, hrs⟩ := hv
  let k : ℤ := r * w.1 0 + s * w.1 1
  have hcross :
      v.1 0 * w.1 1 = v.1 1 * w.1 0 := by
    exact sub_eq_zero.mp hdet
  have hk0 : k * v.1 0 = w.1 0 := by
    dsimp only [k]
    calc
      (r * w.1 0 + s * w.1 1) * v.1 0 =
          w.1 0 * (r * v.1 0 + s * v.1 1) := by
            linear_combination s * hcross
      _ = w.1 0 := by rw [hrs, mul_one]
  have hk1 : k * v.1 1 = w.1 1 := by
    dsimp only [k]
    calc
      (r * w.1 0 + s * w.1 1) * v.1 1 =
          w.1 1 * (r * v.1 0 + s * v.1 1) := by
            linear_combination -r * hcross
      _ = w.1 1 := by rw [hrs, mul_one]
  obtain ⟨p, q, hpq⟩ := hw
  have hkunit : IsUnit k := by
    rw [isUnit_iff_dvd_one]
    refine ⟨p * v.1 0 + q * v.1 1, ?_⟩
    calc
      1 = p * w.1 0 + q * w.1 1 := hpq.symm
      _ = k * (p * v.1 0 + q * v.1 1) := by
            rw [← hk0, ← hk1]
            ring
  rcases Int.isUnit_iff.mp hkunit with hk | hk
  · left
    funext i
    fin_cases i
    · simpa [hk] using hk0.symm
    · simpa [hk] using hk1.symm
  · right
    funext i
    fin_cases i
    · simpa [hk] using hk0.symm
    · simpa [hk] using hk1.symm

/-- The real determinant of the two lattice rows is their original
integral determinant, because the frame has determinant one. -/
theorem primitiveIntegralRowMul_det
    (v w : PrimitiveIntegralRow)
    (g : RealModularFrame) :
    primitiveIntegralRowMul v g 0 *
          primitiveIntegralRowMul w g 1 -
        primitiveIntegralRowMul v g 1 *
          primitiveIntegralRowMul w g 0 =
      (primitiveIntegralRowDet v w : ℝ) := by
  have hg :
      g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.2
  simp only [primitiveIntegralRowMul,
    Fin.sum_univ_two, primitiveIntegralRowDet]
  push_cast
  calc
    ((v.1 0 : ℝ) * g 0 0 + (v.1 1 : ℝ) * g 1 0) *
          ((w.1 0 : ℝ) * g 0 1 + (w.1 1 : ℝ) * g 1 1) -
        ((v.1 0 : ℝ) * g 0 1 + (v.1 1 : ℝ) * g 1 1) *
          ((w.1 0 : ℝ) * g 0 0 + (w.1 1 : ℝ) * g 1 0) =
        ((v.1 0 : ℝ) * (w.1 1 : ℝ) -
            (v.1 1 : ℝ) * (w.1 0 : ℝ)) *
          (g 0 0 * g 1 1 - g 0 1 * g 1 0) := by
            ring
    _ = (v.1 0 : ℝ) * (w.1 1 : ℝ) -
          (v.1 1 : ℝ) * (w.1 0 : ℝ) := by
            rw [hg, mul_one]

/-- A real coordinate is smaller than `1/3` in absolute value if it is
one coordinate of a vector whose squared norm is below `(1/3)²`. -/
private theorem abs_lt_one_third_of_sq_add_sq_lt
    {x y : ℝ}
    (h : x ^ 2 + y ^ 2 < (1 / 3 : ℝ) ^ 2) :
    |x| < (1 / 3 : ℝ) := by
  have hsq : |x| ^ 2 < (1 / 3 : ℝ) ^ 2 := by
    rw [sq_abs]
    nlinarith [sq_nonneg y]
  nlinarith [abs_nonneg x, sq_nonneg (|x| + (1 / 3 : ℝ))]

/-- Two primitive rows that are simultaneously shorter than `1/3`
differ only by sign. -/
theorem primitiveIntegralRows_eq_or_eq_neg_of_both_short
    (v w : PrimitiveIntegralRow)
    (g : RealModularFrame)
    (hv :
      primitiveIntegralRowNormSq v g <
        (1 / 3 : ℝ) ^ 2)
    (hw :
      primitiveIntegralRowNormSq w g <
        (1 / 3 : ℝ) ^ 2) :
    w.1 = v.1 ∨ w.1 = -v.1 := by
  let C := primitiveIntegralRowMul v g 0
  let D := primitiveIntegralRowMul v g 1
  let E := primitiveIntegralRowMul w g 0
  let F := primitiveIntegralRowMul w g 1
  have hC : |C| < (1 / 3 : ℝ) := by
    apply abs_lt_one_third_of_sq_add_sq_lt
    exact hv
  have hD : |D| < (1 / 3 : ℝ) := by
    apply abs_lt_one_third_of_sq_add_sq_lt
    simpa only [add_comm] using hv
  have hE : |E| < (1 / 3 : ℝ) := by
    apply abs_lt_one_third_of_sq_add_sq_lt
    exact hw
  have hF : |F| < (1 / 3 : ℝ) := by
    apply abs_lt_one_third_of_sq_add_sq_lt
    simpa only [add_comm] using hw
  have hCE : |C * F - D * E| < 1 := by
    calc
      |C * F - D * E| ≤ |C * F| + |D * E| :=
        abs_sub _ _
      _ = |C| * |F| + |D| * |E| := by
        rw [abs_mul, abs_mul]
      _ < (1 / 3 : ℝ) * (1 / 3) +
            (1 / 3) * (1 / 3) := by
        gcongr
      _ < 1 := by norm_num
  have hdetabs :
      |(primitiveIntegralRowDet v w : ℝ)| < 1 := by
    rw [← primitiveIntegralRowMul_det v w g]
    exact hCE
  have hdet : primitiveIntegralRowDet v w = 0 := by
    by_contra hne
    have hone :
        (1 : ℝ) ≤
          |(primitiveIntegralRowDet v w : ℝ)| := by
      have honeInt :
          (1 : ℤ) ≤ |primitiveIntegralRowDet v w| :=
        Int.one_le_abs hne
      exact_mod_cast honeInt
    exact (not_lt_of_ge hone) hdetabs
  exact
    primitiveIntegralRows_eq_or_eq_neg_of_det_eq_zero
      v w hdet

end

end HGAS.Modular
