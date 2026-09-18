import HGAS.Modular.GammaTwoCuspExcursionIntervals
import Mathlib.Tactic

/-!
# Quantitative length estimates for nested cusp excursions

Shrinking the row-length cutoff from `δ₀` to `δ ≤ δ₀` leaves the center
of every excursion fixed and shrinks its radius by at least the factor
`δ / δ₀`.  A small elementary interval lemma then controls an inner
excursion clipped by a finite observation window, provided the
corresponding outer interval does not cross the left endpoint.

The constants are intentionally generous.  For a radius ratio at most
`k ≤ 1/2`, the clipped inner length is at most `4k` times the clipped
outer length.  This robust estimate avoids any delicate endpoint cases
and is sufficient for nonescape of mass.
-/

namespace HGAS.Modular

open _root_.MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Shrinking the cutoff shrinks every nonempty affine excursion by at
least the same relative factor. -/
theorem affineRowExcursionRadius_le_scaled
    {C δ δ₀ : ℝ}
    (hC : C ≠ 0)
    (hδ : 0 < δ) (hδ₀ : 0 < δ₀)
    (hδle : δ ≤ δ₀)
    (hshort : C ^ 2 < δ ^ 2) :
    affineRowExcursionRadius C δ ≤
      (δ / δ₀) * affineRowExcursionRadius C δ₀ := by
  have houter : C ^ 2 < δ₀ ^ 2 :=
    hshort.trans_le
      ((sq_le_sq₀ hδ.le hδ₀.le).mpr hδle)
  have hr :
      0 ≤ affineRowExcursionRadius C δ :=
    (affineRowExcursionRadius_pos hC hshort).le
  have hR :
      0 ≤ affineRowExcursionRadius C δ₀ :=
    (affineRowExcursionRadius_pos hC houter).le
  have hscale : 0 ≤ δ / δ₀ :=
    (div_pos hδ hδ₀).le
  rw [← sq_le_sq₀ hr (mul_nonneg hscale hR)]
  rw [mul_pow,
    affineRowExcursionRadius_sq hshort,
    affineRowExcursionRadius_sq houter]
  have hδsq : δ ^ 2 ≤ δ₀ ^ 2 :=
    (sq_le_sq₀ hδ.le hδ₀.le).mpr hδle
  have hCsq : 0 < C ^ 2 := sq_pos_of_ne_zero hC
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hCsq hCsq).mpr
  have hprod :
      C ^ 2 * δ ^ 2 ≤ C ^ 2 * δ₀ ^ 2 :=
    mul_le_mul_of_nonneg_left hδsq (sq_nonneg C)
  field_simp [hC, hδ₀.ne']
  nlinarith

/-- Lebesgue measure of an open interval clipped by `(0,T]`.  Endpoint
choices are immaterial for Lebesgue measure. -/
theorem volume_Ioo_inter_Ioc
    (a b T : ℝ) :
    volume (Ioo a b ∩ Ioc 0 T) =
      ENNReal.ofReal (min b T - max a 0) := by
  by_cases hbT : b ≤ T
  · rw [Ioo_inter_Ioc_of_left_le hbT,
      Real.volume_Ioo, min_eq_left hbT]
  · have hTb : T < b := lt_of_not_ge hbT
    rw [Ioo_inter_Ioc_of_right_lt hTb,
      Real.volume_Ioc, min_eq_right hTb.le]

/-- A clipped concentric inner interval is controlled by its outer
interval when the outer interval does not cross time zero.

The hypotheses `r ≤ kR` and `k ≤ 1/2` imply that the inner interval has
length at most `2kR`, while any observation window meeting it sees at
least `R-r ≥ R/2` of the outer interval. -/
theorem volume_inner_Ioo_inter_Ioc_le
    {c r R k T : ℝ}
    (hR : 0 < R)
    (hrR : r ≤ R)
    (hk : 0 ≤ k) (hkle : k ≤ 1 / 2)
    (hrk : r ≤ k * R)
    (hzero : 0 ∉ Ioo (c - R) (c + R)) :
    volume (Ioo (c - r) (c + r) ∩ Ioc 0 T) ≤
      ENNReal.ofReal (4 * k) *
        volume (Ioo (c - R) (c + R) ∩ Ioc 0 T) := by
  rw [volume_Ioo_inter_Ioc,
    volume_Ioo_inter_Ioc]
  have horient :
      c + R ≤ 0 ∨ 0 ≤ c - R := by
    simpa only [mem_Ioo, not_and_or, not_lt, or_comm] using hzero
  rcases horient with hleft | hright
  · have hinnerRight : c + r ≤ 0 := by
      nlinarith
    have hinnerNonpos :
        min (c + r) T - max (c - r) 0 ≤ 0 := by
      have hmin : min (c + r) T ≤ 0 :=
        (min_le_left _ _).trans hinnerRight
      have hmax : 0 ≤ max (c - r) 0 :=
        le_max_right _ _
      linarith
    rw [ENNReal.ofReal_eq_zero.mpr hinnerNonpos]
    exact bot_le
  · have hinnerLeft : 0 ≤ c - r := by
      nlinarith
    rw [max_eq_left hinnerLeft, max_eq_left hright]
    let Lin : ℝ := min (c + r) T - (c - r)
    let Lout : ℝ := min (c + R) T - (c - R)
    change
      ENNReal.ofReal Lin ≤
        ENNReal.ofReal (4 * k) * ENNReal.ofReal Lout
    by_cases hLin : Lin ≤ 0
    · rw [ENNReal.ofReal_eq_zero.mpr hLin]
      exact bot_le
    · have hLinpos : 0 < Lin := lt_of_not_ge hLin
      have hminmono :
          min (c + r) T ≤ min (c + R) T := by
        exact min_le_min_right T (by linarith)
      have hLinle : Lin ≤ 2 * r := by
        dsimp only [Lin]
        have := min_le_left (c + r) T
        linarith
      have hLoutLower : R - r ≤ Lout := by
        dsimp only [Lin] at hLinpos
        dsimp only [Lout]
        linarith
      have hkR : k * R ≤ (1 / 2 : ℝ) * R :=
        mul_le_mul_of_nonneg_right hkle hR.le
      have hrhalf : r ≤ (1 / 2 : ℝ) * R :=
        hrk.trans hkR
      have hhalf : (1 / 2 : ℝ) * R ≤ R - r :=
        by nlinarith
      have hhalfOut : (1 / 2 : ℝ) * R ≤ Lout :=
        hhalf.trans hLoutLower
      have hinnerScale : Lin ≤ 2 * k * R := by
        calc
          Lin ≤ 2 * r := hLinle
          _ ≤ 2 * (k * R) :=
            mul_le_mul_of_nonneg_left hrk (by norm_num)
          _ = 2 * k * R := by ring
      have hfactor : 0 ≤ 4 * k := by positivity
      have houterScale :
          2 * k * R ≤ (4 * k) * Lout := by
        have :=
          mul_le_mul_of_nonneg_left hhalfOut hfactor
        nlinarith
      rw [← ENNReal.ofReal_mul hfactor]
      exact ENNReal.ofReal_le_ofReal
        (hinnerScale.trans houterScale)

end

end HGAS.Modular
