import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Conserved ratios for auxiliary radical variables

If `w' = w D' / (4 D)` and `D` stays positive, then `w^4 / D`
is constant. An initially exact constraint `w^4 = D` therefore persists,
and `w^2` equals the nonnegative square root of `D`.

These are finite-solution-segment statements for the scalar equation used
in the triangular radical lift (Lemma 5.2 of the cited source proof).
The chain rule identifying `D'` in the full triangular system and the
construction of that system are separate obligations.
-/

namespace Stability.Simulation

open Set MeasureTheory

/-- Direct differentiation of the ratio gives zero. The variable `w`
may vanish or be negative; only the denominator must be nonzero. -/
theorem hasDerivAt_radicalRatio_zero
    {w D : ℝ → ℝ} {t rate : ℝ} (hDne : D t ≠ 0)
    (hw : HasDerivAt w (w t * rate / (4 * D t)) t)
    (hD : HasDerivAt D rate t) :
    HasDerivAt (fun s ↦ w s ^ 4 / D s) 0 t := by
  convert (hw.pow 4).div hD hDne using 1
  simp only [Pi.pow_apply]
  field_simp
  ring

/-- The ratio is conserved throughout any supplied closed interval with
positive denominator. No global solution or continuity of its derivative
is assumed. -/
theorem radicalRatio_eq_initial
    {a b : ℝ} {w D rate : ℝ → ℝ}
    (hw : ContinuousOn w (Icc a b)) (hD : ContinuousOn D (Icc a b))
    (hDpos : ∀ t ∈ Icc a b, 0 < D t)
    (hdw : ∀ t ∈ Ioo a b, HasDerivAt w (w t * rate t / (4 * D t)) t)
    (hdD : ∀ t ∈ Ioo a b, HasDerivAt D (rate t) t)
    {t : ℝ} (ht : t ∈ Icc a b) :
    w t ^ 4 / D t = w a ^ 4 / D a := by
  have hcont : ContinuousOn (fun s ↦ w s ^ 4 / D s) (Icc a b) :=
    (hw.pow 4).div hD (fun s hs ↦ ne_of_gt (hDpos s hs))
  have hderiv : ∀ s ∈ Ioo a t,
      HasDerivAt (fun s ↦ w s ^ 4 / D s) 0 s := by
    intro s hs
    have hsFull : s ∈ Ioo a b := ⟨hs.1, hs.2.trans_le ht.2⟩
    exact hasDerivAt_radicalRatio_zero
      (ne_of_gt (hDpos s (Ioo_subset_Icc_self hsFull)))
      (hdw s hsFull) (hdD s hsFull)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    (hcont.mono (Icc_subset_Icc le_rfl ht.2)) hderiv
    (intervalIntegrable_const (c := (0 : ℝ)))
  simp only [intervalIntegral.integral_zero] at hFTC
  linarith

/-- Exact radical constraints are preserved by the actual scalar lift
equation. The dynamics need not drive inexact constraints to zero. -/
theorem radicalDefect_zero_of_initial
    {a b : ℝ} {w D rate : ℝ → ℝ}
    (hw : ContinuousOn w (Icc a b)) (hD : ContinuousOn D (Icc a b))
    (hDpos : ∀ t ∈ Icc a b, 0 < D t)
    (hdw : ∀ t ∈ Ioo a b, HasDerivAt w (w t * rate t / (4 * D t)) t)
    (hdD : ∀ t ∈ Ioo a b, HasDerivAt D (rate t) t)
    (hinitial : w a ^ 4 = D a)
    {t : ℝ} (ht : t ∈ Icc a b) : w t ^ 4 = D t := by
  have hratio := radicalRatio_eq_initial hw hD hDpos hdw hdD ht
  rw [hinitial, div_self (ne_of_gt (hDpos a ⟨le_rfl, ht.1.trans ht.2⟩))] at hratio
  exact (div_eq_one_iff_eq (ne_of_gt (hDpos t ht))).mp hratio

/-- Squaring the auxiliary variable selects the nonnegative square-root
branch. A bare variable constrained only by its square would not do so. -/
theorem sq_eq_sqrt_of_fourth_eq {w D : ℝ} (h : w ^ 4 = D) :
    w ^ 2 = Real.sqrt D := by
  rw [← h, show w ^ 4 = (w ^ 2) ^ 2 by ring, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (sq_nonneg w)]

/-- Even far from the constraint, the radical error is bounded by the
quartic defect when the radicand is at least one. -/
theorem abs_sq_sub_sqrt_le_quarticDefect {w D : ℝ} (hD : 1 ≤ D) :
    |w ^ 2 - Real.sqrt D| ≤ |w ^ 4 - D| := by
  have hDnonneg : 0 ≤ D := zero_le_one.trans hD
  have hsqrt : 1 ≤ Real.sqrt D := by
    simpa using Real.sqrt_le_sqrt hD
  have hfactor : w ^ 4 - D = (w ^ 2 - Real.sqrt D) * (w ^ 2 + Real.sqrt D) := by
    nlinarith [Real.sq_sqrt hDnonneg]
  rw [hfactor, abs_mul, abs_of_nonneg (by positivity : 0 ≤ w ^ 2 + Real.sqrt D)]
  exact le_mul_of_one_le_right (abs_nonneg _) (by nlinarith [sq_nonneg w])

/-- Square root is one-half Lipschitz on radicands at least one.
The factorized proof includes equality of the two radicands. -/
theorem two_mul_abs_sqrt_sub_le {D E : ℝ} (hD : 1 ≤ D) (hE : 1 ≤ E) :
    2 * |Real.sqrt D - Real.sqrt E| ≤ |D - E| := by
  have hDnonneg : 0 ≤ D := zero_le_one.trans hD
  have hEnonneg : 0 ≤ E := zero_le_one.trans hE
  have hrootD : 1 ≤ Real.sqrt D := by simpa using Real.sqrt_le_sqrt hD
  have hrootE : 1 ≤ Real.sqrt E := by simpa using Real.sqrt_le_sqrt hE
  have hfactor : D - E = (Real.sqrt D - Real.sqrt E) * (Real.sqrt D + Real.sqrt E) := by
    nlinarith [Real.sq_sqrt hDnonneg, Real.sq_sqrt hEnonneg]
  rw [hfactor, abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt D + Real.sqrt E)]
  nlinarith [abs_nonneg (Real.sqrt D - Real.sqrt E)]

end Stability.Simulation
