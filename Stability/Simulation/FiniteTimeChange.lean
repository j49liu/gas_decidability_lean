import HGAS.Dynamics.StateTimeChange
import Mathlib.Topology.Order.ProjIcc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Positive changes of time on finite solution segments

A continuous positive speed on a compact time interval extends constantly
at both endpoints. Its integral clock is an order isomorphism of the real
line, even when the original state-dependent clock would have finite range.
Only finite trajectories are reparametrized; no global completeness is claimed.
-/

namespace Stability.TimeChange

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

/-- Extend a finite-interval speed constantly beyond both endpoints. -/
def extendedSpeed {T : ℝ} (hT : 0 ≤ T) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  w (projIcc 0 T hT t)

theorem extendedSpeed_of_mem {T : ℝ} (hT : 0 ≤ T) (w : ℝ → ℝ)
    {t : ℝ} (ht : t ∈ Icc 0 T) : extendedSpeed hT w t = w t := by
  simp only [extendedSpeed, projIcc_of_mem hT ht]

/-- The constant endpoint extension gives a genuine global positive
clock from merely finite-interval positivity and continuity. -/
theorem positiveIntegralClock_extendedSpeed {T : ℝ} (hT : 0 ≤ T) {w : ℝ → ℝ}
    (hw : ContinuousOn w (Icc 0 T)) (hpositive : ∀ t ∈ Icc 0 T, 0 < w t) :
    HGAS.PositiveIntegralClock (extendedSpeed hT w) := by
  have hcont : Continuous (extendedSpeed hT w) := hw.restrict.comp continuous_projIcc
  refine ⟨hcont, fun t ↦ hpositive _ (projIcc 0 T hT t).property, ?_, ?_⟩
  · apply HGAS.integralClock_tendsto_atTop_of_eventually_ge hcont
      (hpositive T ⟨hT, le_rfl⟩)
    filter_upwards [eventually_ge_atTop T] with t ht
    simp only [extendedSpeed, projIcc_of_right_le hT ht, le_refl]
  · apply HGAS.integralClock_tendsto_atBot_of_eq_const_nonpos
      (hpositive 0 ⟨le_rfl, hT⟩)
    intro t ht
    simp only [extendedSpeed, projIcc_of_le_left hT ht]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A supplied finite solution can be accelerated by any continuous speed
positive on its image. The integral of the correspondingly accelerated
output is exactly preserved, including a zero-length segment. -/
theorem exists_accelerated_segment {F : E → E} {Q g : E → ℝ}
    {T : ℝ} (hT : 0 ≤ T) {x : ℝ → E}
    (hx : ContinuousOn x (Icc 0 T))
    (hQ : ContinuousOn (fun t ↦ Q (x t)) (Icc 0 T))
    (hg : ContinuousOn (fun t ↦ g (x t)) (Icc 0 T))
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt x (F (x t)) t)
    (hpositive : ∀ t ∈ Icc 0 T, 0 < Q (x t)) :
    ∃ S ≥ 0, ∃ z : ℝ → E,
      ContinuousOn z (Icc 0 S) ∧ z 0 = x 0 ∧ z S = x T ∧
      MapsTo z (Icc 0 S) (x '' Icc 0 T) ∧
      (∀ t ∈ Ioo 0 S, HasDerivAt z (Q (z t) • F (z t)) t) ∧
      (∫ t in 0..S, Q (z t) * g (z t)) = ∫ t in 0..T, g (x t) := by
  let w : ℝ → ℝ := fun t ↦ (Q (x t))⁻¹
  have hw : ContinuousOn w (Icc 0 T) :=
    hQ.inv₀ (fun t ht ↦ ne_of_gt (hpositive t ht))
  have hclock := positiveIntegralClock_extendedSpeed hT hw
    (fun t ht ↦ inv_pos.mpr (hpositive t ht))
  let e := HGAS.PositiveIntegralClock.orderIso hclock
  let S := e T
  let z : ℝ → E := fun t ↦ x (e.symm t)
  have he0 : e 0 = 0 := HGAS.PositiveIntegralClock.orderIso_zero hclock
  have hi0 : e.symm 0 = 0 := HGAS.PositiveIntegralClock.symm_zero hclock
  have hiS : e.symm S = T := e.symm_apply_apply T
  have hS : 0 ≤ S := by simpa only [he0] using e.monotone hT
  have hmaps : MapsTo e.symm (Icc 0 S) (Icc 0 T) := by
    intro t ht
    exact ⟨by simpa only [hi0] using e.symm.monotone ht.1,
      by simpa only [hiS] using e.symm.monotone ht.2⟩
  have hmapsOpen : MapsTo e.symm (Ioo 0 S) (Ioo 0 T) := by
    intro t ht
    exact ⟨by simpa only [hi0] using e.symm.strictMono ht.1,
      by simpa only [hiS] using e.symm.strictMono ht.2⟩
  have hzin : ContinuousOn z (Icc 0 S) := hx.comp e.symm.continuous.continuousOn hmaps
  have hdInverse (t : ℝ) :
      HasDerivAt (fun t ↦ e.symm t) (extendedSpeed hT w (e.symm t))⁻¹ t :=
    HGAS.PositiveIntegralClock.symm_hasDerivAt hclock t
  have hdValue (t : ℝ) (ht : t ∈ Icc 0 S) :
      (extendedSpeed hT w (e.symm t))⁻¹ = Q (z t) := by
    rw [extendedSpeed_of_mem hT w (hmaps ht)]
    exact inv_inv _
  refine ⟨S, hS, z, hzin, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [z, hi0]
  · simp only [z, hiS]
  · intro t ht
    exact ⟨e.symm t, hmaps ht, rfl⟩
  · intro t ht
    have hcomp := (hderiv (e.symm t) (hmapsOpen ht)).scomp t (hdInverse t)
    simpa only [hdValue t (Ioo_subset_Icc_self ht)] using hcomp
  · have hcontinuous : Continuous (fun t ↦ (extendedSpeed hT w (e.symm t))⁻¹) :=
      (hclock.continuous.comp e.symm.continuous).inv₀
        (fun t ↦ ne_of_gt (hclock.positive (e.symm t)))
    have houtput : ContinuousOn (fun t ↦ g (x t)) ((fun t ↦ e.symm t) '' uIcc 0 S) := by
      apply hg.mono
      rintro _ ⟨t, ht, rfl⟩
      rw [uIcc_of_le hS] at ht
      exact hmaps ht
    have hchange := intervalIntegral.integral_comp_mul_deriv'
      (fun t _ ↦ hdInverse t) hcontinuous.continuousOn houtput
    simp only [hi0, hiS, Function.comp_apply] at hchange
    rw [← hchange]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hS] at ht
    change Q (z t) * g (z t) = g (z t) * (extendedSpeed hT w (e.symm t))⁻¹
    rw [hdValue t ht]
    exact mul_comm _ _

/-- Reversing a positive acceleration preserves the corresponding output
integral. Positivity is needed only on the supplied finite curve image. -/
theorem exists_decelerated_segment {F : E → E} {Q g : E → ℝ}
    {T : ℝ} (hT : 0 ≤ T) {x : ℝ → E}
    (hx : ContinuousOn x (Icc 0 T))
    (hQ : ContinuousOn (fun t ↦ Q (x t)) (Icc 0 T))
    (hg : ContinuousOn (fun t ↦ g (x t)) (Icc 0 T))
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt x (Q (x t) • F (x t)) t)
    (hpositive : ∀ t ∈ Icc 0 T, 0 < Q (x t)) :
    ∃ S ≥ 0, ∃ z : ℝ → E,
      ContinuousOn z (Icc 0 S) ∧ z 0 = x 0 ∧ z S = x T ∧
      MapsTo z (Icc 0 S) (x '' Icc 0 T) ∧
      (∀ t ∈ Ioo 0 S, HasDerivAt z (F (z t)) t) ∧
      (∫ t in 0..S, g (z t)) = ∫ t in 0..T, Q (x t) * g (x t) := by
  obtain ⟨S, hS, z, hz, hz0, hzS, himage, hdz, hint⟩ :=
    exists_accelerated_segment (F := fun y ↦ Q y • F y) (Q := fun y ↦ (Q y)⁻¹)
      (g := fun y ↦ Q y * g y) hT hx
      (hQ.inv₀ (fun t ht ↦ ne_of_gt (hpositive t ht))) (hQ.mul hg) hderiv
      (fun t ht ↦ inv_pos.mpr (hpositive t ht))
  have hzPositive (t : ℝ) (ht : t ∈ Icc 0 S) : 0 < Q (z t) := by
    obtain ⟨r, hr, heq⟩ := himage ht
    rw [← heq]
    exact hpositive r hr
  refine ⟨S, hS, z, hz, hz0, hzS, himage, ?_, ?_⟩
  · intro t ht
    simpa only [smul_smul, inv_mul_cancel₀ (ne_of_gt (hzPositive t (Ioo_subset_Icc_self ht))),
      one_smul] using hdz t ht
  · have heq : (∫ t in 0..S, (Q (z t))⁻¹ * (Q (z t) * g (z t))) =
        ∫ t in 0..S, g (z t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hS] at ht
      change (Q (z t))⁻¹ * (Q (z t) * g (z t)) = g (z t)
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (hzPositive t ht)), one_mul]
    exact heq.symm.trans hint

/-- General-endpoint version of finite acceleration, normalized to a
new interval beginning at zero. -/
theorem exists_accelerated_segment_Icc {F : E → E} {Q g : E → ℝ}
    {a b : ℝ} (hab : a ≤ b) {x : ℝ → E}
    (hx : ContinuousOn x (Icc a b))
    (hQ : ContinuousOn (fun t ↦ Q (x t)) (Icc a b))
    (hg : ContinuousOn (fun t ↦ g (x t)) (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt x (F (x t)) t)
    (hpositive : ∀ t ∈ Icc a b, 0 < Q (x t)) :
    ∃ S ≥ 0, ∃ z : ℝ → E,
      ContinuousOn z (Icc 0 S) ∧ z 0 = x a ∧ z S = x b ∧
      MapsTo z (Icc 0 S) (x '' Icc a b) ∧
      (∀ t ∈ Ioo 0 S, HasDerivAt z (Q (z t) • F (z t)) t) ∧
      (∫ t in 0..S, Q (z t) * g (z t)) = ∫ t in a..b, g (x t) := by
  have hshift : MapsTo (fun t ↦ a + t) (Icc 0 (b - a)) (Icc a b) := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hshiftOpen : MapsTo (fun t ↦ a + t) (Ioo 0 (b - a)) (Ioo a b) := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hcont : Continuous (fun t : ℝ ↦ a + t) := continuous_const.add continuous_id
  have hd : ∀ t ∈ Ioo 0 (b - a), HasDerivAt (fun r ↦ x (a + r)) (F (x (a + t))) t := by
    intro t ht
    simpa only [one_smul] using
      (hderiv (a + t) (hshiftOpen ht)).scomp t ((hasDerivAt_id t).const_add a)
  obtain ⟨S, hS, z, hz, hz0, hzS, himage, hdz, hint⟩ :=
    exists_accelerated_segment (sub_nonneg.mpr hab) (hx.comp hcont.continuousOn hshift)
      (hQ.comp hcont.continuousOn hshift) (hg.comp hcont.continuousOn hshift) hd
      (fun t ht ↦ hpositive (a + t) (hshift ht))
  refine ⟨S, hS, z, hz, ?_, ?_, ?_, hdz, ?_⟩
  · simpa only [Function.comp_apply, add_zero] using hz0
  · simpa only [Function.comp_apply, add_sub_cancel] using hzS
  · intro t ht
    obtain ⟨r, hr, heq⟩ := himage ht
    exact ⟨a + r, hshift hr, heq⟩
  · refine hint.trans ?_
    simpa only [add_zero, add_sub_cancel] using
      (intervalIntegral.integral_comp_add_left (fun t ↦ g (x t)) a (a := 0) (b := b - a))

/-- General-endpoint version of reversing a positive time acceleration. -/
theorem exists_decelerated_segment_Icc {F : E → E} {Q g : E → ℝ}
    {a b : ℝ} (hab : a ≤ b) {x : ℝ → E}
    (hx : ContinuousOn x (Icc a b))
    (hQ : ContinuousOn (fun t ↦ Q (x t)) (Icc a b))
    (hg : ContinuousOn (fun t ↦ g (x t)) (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt x (Q (x t) • F (x t)) t)
    (hpositive : ∀ t ∈ Icc a b, 0 < Q (x t)) :
    ∃ S ≥ 0, ∃ z : ℝ → E,
      ContinuousOn z (Icc 0 S) ∧ z 0 = x a ∧ z S = x b ∧
      MapsTo z (Icc 0 S) (x '' Icc a b) ∧
      (∀ t ∈ Ioo 0 S, HasDerivAt z (F (z t)) t) ∧
      (∫ t in 0..S, g (z t)) = ∫ t in a..b, Q (x t) * g (x t) := by
  obtain ⟨S, hS, z, hz, hz0, hzS, himage, hdz, hint⟩ :=
    exists_accelerated_segment_Icc (F := fun y ↦ Q y • F y) (Q := fun y ↦ (Q y)⁻¹)
      (g := fun y ↦ Q y * g y) hab hx
      (hQ.inv₀ (fun t ht ↦ ne_of_gt (hpositive t ht))) (hQ.mul hg) hderiv
      (fun t ht ↦ inv_pos.mpr (hpositive t ht))
  have hzPositive (t : ℝ) (ht : t ∈ Icc 0 S) : 0 < Q (z t) := by
    obtain ⟨r, hr, heq⟩ := himage ht
    rw [← heq]
    exact hpositive r hr
  refine ⟨S, hS, z, hz, hz0, hzS, himage, ?_, ?_⟩
  · intro t ht
    simpa only [smul_smul, inv_mul_cancel₀ (ne_of_gt (hzPositive t (Ioo_subset_Icc_self ht))),
      one_smul] using hdz t ht
  · have heq : (∫ t in 0..S, (Q (z t))⁻¹ * (Q (z t) * g (z t))) =
        ∫ t in 0..S, g (z t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hS] at ht
      change (Q (z t))⁻¹ * (Q (z t) * g (z t)) = g (z t)
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (hzPositive t ht)), one_mul]
    exact heq.symm.trans hint

end

end Stability.TimeChange
