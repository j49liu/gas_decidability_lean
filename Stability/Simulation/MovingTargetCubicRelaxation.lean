import Stability.Simulation.CubicRelaxation
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Unforced cubic relaxation toward a bounded moving target

Reference: the unforced moving-target estimate in Lemma 4.1,
https://arxiv.org/html/2609.22058v2#S4. The proof starts from the actual
scalar differential equation.

The squared positive part makes the no-crossing argument valid even at
zero excess. The final estimate imposes no initial sign or size condition.
Continuity of the prescribed target is unnecessary for this estimate once
the derivative equation is supplied. Existence and additive forcing are
not established here.
-/

namespace Stability.Simulation

open Set Filter MeasureTheory
open scoped Topology

/-- The squared positive part is differentiable even where the positive
part itself is not differentiable. -/
theorem hasDerivAt_sq_max_zero (x : ℝ) :
    HasDerivAt (fun u : ℝ ↦ (max u 0) ^ 2) (2 * max x 0) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [max_eq_right hx.le, mul_zero]
    apply (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hx] with u hu
    simp [max_eq_right (show u ≤ 0 from hu.le)]
  · rw [max_self, mul_zero]
    apply hasDerivAt_iff_tendsto_slope.mpr
    have hslope : slope (fun u : ℝ ↦ (max u 0) ^ 2) 0 = fun u ↦ max u 0 := by
      funext u
      rw [slope_def_field]
      simp only [max_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        sub_zero]
      by_cases hu : 0 ≤ u
      · rw [max_eq_left hu]
        by_cases hu0 : u = 0
        · simp [hu0]
        · field_simp
      · simp [max_eq_right (le_of_not_ge hu)]
    rw [hslope]
    have hcont : Continuous (fun u : ℝ ↦ max u 0) :=
      continuous_id.max continuous_const
    simpa only [max_self] using
      (hcont.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  · rw [max_eq_left hx.le]
    have hd : HasDerivAt (fun u : ℝ ↦ u ^ 2) (2 * x) x := by
      simpa using (hasDerivAt_id x).pow 2
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx] with u hu
    rw [max_eq_left (show 0 ≤ u from hu.le)]

/-- If a function cannot increase while positive, its squared positive
part cannot increase anywhere, including at zero crossings. -/
theorem sq_posPart_antitoneOn_of_deriv_nonpos_on_pos
    {a b : ℝ} {w w' : ℝ → ℝ}
    (hw : ContinuousOn w (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt w (w' t) t)
    (hdecay : ∀ t ∈ Ioo a b, 0 < w t → w' t ≤ 0) :
    AntitoneOn (fun t ↦ (max (w t) 0) ^ 2) (Icc a b) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos
    (f' := fun t ↦ (2 * max (w t) 0) * w' t) (convex_Icc a b)
    ((hw.sup continuousOn_const).pow 2) ?_ ?_
  · intro t ht
    rw [interior_Icc] at ht
    exact ((hasDerivAt_sq_max_zero (w t)).comp t (hderiv t ht)).hasDerivWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    by_cases hp : 0 < w t
    · exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (hdecay t ht hp)
    · simp [max_eq_right (le_of_not_gt hp)]

/-- A function whose derivative is nonpositive whenever it is positive
cannot cross from nonpositive to positive on a solution segment. -/
theorem nonpos_of_nonpos_of_deriv_nonpos_on_pos
    {a b : ℝ} {w w' : ℝ → ℝ}
    (hw : ContinuousOn w (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt w (w' t) t)
    (hdecay : ∀ t ∈ Ioo a b, 0 < w t → w' t ≤ 0)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (hst : s ≤ t) (hs0 : w s ≤ 0) :
    w t ≤ 0 := by
  have hbound := sq_posPart_antitoneOn_of_deriv_nonpos_on_pos
    hw hderiv hdecay hs ht hst
  change (max (w t) 0) ^ 2 ≤ (max (w s) 0) ^ 2 at hbound
  rw [max_eq_right hs0, zero_pow (by decide : 2 ≠ 0)] at hbound
  have hzero : max (w t) 0 = 0 :=
    sq_eq_zero_iff.mp (le_antisymm hbound (sq_nonneg _))
  exact (le_max_left (w t) 0).trans_eq hzero

/-- Cubic decay imposed only on positive excess still gives the uniform
one-sided relaxation bound, without any initial sign restriction. -/
theorem lt_inv_sqrt_integral_of_cubic_decay_on_pos
    {a b : ℝ} {w w' rate : ℝ → ℝ}
    (hab : a ≤ b)
    (hw : ContinuousOn w (Icc a b))
    (hrate : ContinuousOn rate (Icc a b))
    (hnonneg : ∀ t ∈ Icc a b, 0 ≤ rate t)
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt w (w' t) t)
    (hdecay : ∀ t ∈ Ioo a b, 0 < w t →
      w' t ≤ -(rate t) * (w t) ^ 3)
    (hgain : 0 < ∫ t in a..b, rate t) :
    w b < (Real.sqrt (2 * (∫ t in a..b, rate t)))⁻¹ := by
  have hboundpos : 0 < (Real.sqrt (2 * (∫ t in a..b, rate t)))⁻¹ := by
    apply inv_pos.mpr
    apply Real.sqrt_pos.mpr
    positivity
  by_cases hb : 0 < w b
  · have hnonpos : ∀ t ∈ Ioo a b, 0 < w t → w' t ≤ 0 := by
      intro t ht hp
      refine (hdecay t ht hp).trans ?_
      exact mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (hnonneg t (Ioo_subset_Icc_self ht))) (by positivity)
    have hpositive : ∀ t ∈ Icc a b, 0 < w t := by
      intro t ht
      by_contra hn
      have hfinal := nonpos_of_nonpos_of_deriv_nonpos_on_pos hw hderiv hnonpos
        ht (right_mem_Icc.mpr hab) ht.2 (le_of_not_gt hn)
      exact (not_lt_of_ge hfinal) hb
    exact lt_inv_sqrt_integral_of_cubic_decay hab hw hrate hpositive hderiv
      (fun t ht ↦ hdecay t ht (hpositive t (Ioo_subset_Icc_self ht))) hgain
  · exact (le_of_not_gt hb).trans_lt hboundpos

/-- Uniform relaxation toward a moving target constrained to a fixed
interval. The bound holds for every initial value and both error signs. -/
theorem abs_sub_lt_radius_add_inv_sqrt_integral_of_cubic_relaxation
    {a b center radius : ℝ} {y target rate : ℝ → ℝ}
    (hab : a ≤ b)
    (hy : ContinuousOn y (Icc a b))
    (hrate : ContinuousOn rate (Icc a b))
    (hnonneg : ∀ t ∈ Icc a b, 0 ≤ rate t)
    (htarget : ∀ t ∈ Icc a b, |target t - center| ≤ radius)
    (hderiv : ∀ t ∈ Ioo a b,
      HasDerivAt y (rate t * (target t - y t) ^ 3) t)
    (hgain : 0 < ∫ t in a..b, rate t) :
    |y b - center| < radius + (Real.sqrt (2 * (∫ t in a..b, rate t)))⁻¹ := by
  have hupper : y b - (center + radius) <
      (Real.sqrt (2 * (∫ t in a..b, rate t)))⁻¹ := by
    apply lt_inv_sqrt_integral_of_cubic_decay_on_pos hab
      (hy.sub continuousOn_const) hrate hnonneg
      (fun t ht ↦ (hderiv t ht).sub_const (center + radius)) ?_ hgain
    intro t ht _
    have htbound := (abs_le.mp (htarget t (Ioo_subset_Icc_self ht))).2
    have hcube : (target t - y t) ^ 3 ≤ (center + radius - y t) ^ 3 :=
      (show Odd (3 : ℕ) by decide).pow_le_pow.mpr (by linarith)
    have hscaled := mul_le_mul_of_nonneg_left hcube
      (hnonneg t (Ioo_subset_Icc_self ht))
    nlinarith
  have hlower : center - radius - y b <
      (Real.sqrt (2 * (∫ t in a..b, rate t)))⁻¹ := by
    apply lt_inv_sqrt_integral_of_cubic_decay_on_pos hab
      (continuousOn_const.sub hy) hrate hnonneg
      (fun t ht ↦ (hderiv t ht).const_sub (center - radius)) ?_ hgain
    intro t ht _
    have htbound := (abs_le.mp (htarget t (Ioo_subset_Icc_self ht))).1
    have hcube : (center - radius - y t) ^ 3 ≤ (target t - y t) ^ 3 :=
      (show Odd (3 : ℕ) by decide).pow_le_pow.mpr (by linarith)
    have hscaled := mul_le_mul_of_nonneg_left hcube
      (hnonneg t (Ioo_subset_Icc_self ht))
    nlinarith
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

end Stability.Simulation
