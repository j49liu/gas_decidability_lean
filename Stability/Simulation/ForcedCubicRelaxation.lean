import Stability.Simulation.MovingTargetCubicRelaxation

/-!
# Cubic relaxation with moving targets and integrable forcing

Reference: the finite-solution-segment estimates in Lemma 4.1,
https://arxiv.org/html/2609.22058v2#S4.

The bounds follow from the actual scalar equation. The cumulative integral of the
absolute forcing moves both comparison barriers outward and costs exactly
one forcing-mass term. No restriction is placed on the initial value.

All solution estimates concern a supplied finite closed interval. This
file proves bounds on such segments, not existence or continuation.
-/

namespace Stability.Simulation

open Set Filter MeasureTheory
open scoped Topology

/-- The accumulated absolute forcing between two times. -/
noncomputable def forcingMass (forcing : ℝ → ℝ) (a t : ℝ) : ℝ :=
  ∫ s in a..t, |forcing s|

@[simp] theorem forcingMass_self (forcing : ℝ → ℝ) (a : ℝ) :
    forcingMass forcing a a = 0 := by
  simp [forcingMass]

@[simp] theorem forcingMass_neg (forcing : ℝ → ℝ) (a t : ℝ) :
    forcingMass (fun s ↦ -forcing s) a t = forcingMass forcing a t := by
  simp [forcingMass]

/-- Absolute forcing has nonnegative accumulated mass in forward time. -/
theorem forcingMass_nonneg (forcing : ℝ → ℝ) {a t : ℝ} (hat : a ≤ t) :
    0 ≤ forcingMass forcing a t :=
  intervalIntegral.integral_nonneg_of_forall hat fun _ ↦ abs_nonneg _

/-- The accumulated forcing is continuous on a closed interval where the
forcing is continuous. -/
theorem continuousOn_forcingMass {a b : ℝ} {forcing : ℝ → ℝ}
    (hab : a ≤ b) (hforcing : ContinuousOn forcing (Icc a b)) :
    ContinuousOn (forcingMass forcing a) (Icc a b) := by
  have hint : IntegrableOn (fun t ↦ |forcing t|) (uIcc a b) := by
    simpa only [uIcc_of_le hab] using hforcing.abs.integrableOn_Icc
  simpa only [forcingMass, uIcc_of_le hab] using
    intervalIntegral.continuousOn_primitive_interval hint

/-- The cumulative absolute forcing has derivative equal to its integrand
at interior times; only closed-interval continuity is required. -/
theorem hasDerivAt_forcingMass {a b : ℝ} {forcing : ℝ → ℝ}
    (hforcing : ContinuousOn forcing (Icc a b))
    {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (forcingMass forcing a) |forcing t| t := by
  have hcont : ContinuousOn (fun s ↦ |forcing s|) (Ioo a b) :=
    hforcing.abs.mono Ioo_subset_Icc_self
  have hint : IntervalIntegrable (fun s ↦ |forcing s|) volume a t :=
    (hforcing.abs.mono (Icc_subset_Icc le_rfl ht.2.le)).intervalIntegrable_of_Icc ht.1.le
  exact intervalIntegral.integral_hasDerivAt_right hint
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hcont t ht)
    ((hcont t ht).continuousAt (isOpen_Ioo.mem_nhds ht))

/-- Restricting a continuous forcing to a shorter forward interval cannot
increase its accumulated absolute mass. -/
theorem forcingMass_le {a b : ℝ} {forcing : ℝ → ℝ}
    (hforcing : ContinuousOn forcing (Icc a b))
    {t : ℝ} (ht : t ∈ Icc a b) :
    forcingMass forcing a t ≤ forcingMass forcing a b := by
  exact intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
    (Eventually.of_forall fun _ ↦ abs_nonneg _)
    (hforcing.abs.intervalIntegrable_of_Icc (ht.1.trans ht.2))

private theorem upper_excess_deriv_le_cubic
    {value target rate forcing mass upper : ℝ}
    (hrate : 0 ≤ rate) (htarget : target ≤ upper) (hmass : 0 ≤ mass) :
    rate * (target - value) ^ 3 + forcing - |forcing| ≤
      -rate * (value - upper - mass) ^ 3 := by
  have hcube : (target - value) ^ 3 ≤ (upper + mass - value) ^ 3 :=
    (show Odd (3 : ℕ) by decide).pow_le_pow.mpr (by linarith)
  have hscaled := mul_le_mul_of_nonneg_left hcube hrate
  have hforcing := le_abs_self forcing
  nlinarith

/-- An upper bound on the moving target yields an upper relaxation estimate,
with one cumulative absolute-forcing term and no initial-value restriction. -/
theorem lt_upper_add_inv_sqrt_integral_add_forcingMass
    {a b upper : ℝ} {y target rate forcing : ℝ → ℝ}
    (hab : a ≤ b)
    (hy : ContinuousOn y (Icc a b))
    (hrate : ContinuousOn rate (Icc a b))
    (hforcing : ContinuousOn forcing (Icc a b))
    (hnonneg : ∀ t ∈ Icc a b, 0 ≤ rate t)
    (htarget : ∀ t ∈ Icc a b, target t ≤ upper)
    (hderiv : ∀ t ∈ Ioo a b,
      HasDerivAt y (rate t * (target t - y t) ^ 3 + forcing t) t)
    (hgain : 0 < ∫ t in a..b, rate t) :
    y b < upper + (Real.sqrt (2 * (∫ t in a..b, rate t)))⁻¹ +
      forcingMass forcing a b := by
  have hbound := lt_inv_sqrt_integral_of_cubic_decay_on_pos hab
    ((hy.sub continuousOn_const).sub (continuousOn_forcingMass hab hforcing))
    hrate hnonneg
    (fun t ht ↦ ((hderiv t ht).sub_const upper).sub (hasDerivAt_forcingMass hforcing ht))
    (fun t ht _ ↦ upper_excess_deriv_le_cubic
      (hnonneg t (Ioo_subset_Icc_self ht))
      (htarget t (Ioo_subset_Icc_self ht)) (forcingMass_nonneg forcing ht.1.le)) hgain
  change y b - upper - forcingMass forcing a b <
    (Real.sqrt (2 * (∫ t in a..b, rate t)))⁻¹ at hbound
  linarith

/-- A lower bound on the moving target yields the one-sided estimate in
Lemma 4.1(ii), again without an initial-value restriction. -/
theorem lower_sub_inv_sqrt_integral_sub_forcingMass_lt
    {a b lower : ℝ} {y target rate forcing : ℝ → ℝ}
    (hab : a ≤ b)
    (hy : ContinuousOn y (Icc a b))
    (hrate : ContinuousOn rate (Icc a b))
    (hforcing : ContinuousOn forcing (Icc a b))
    (hnonneg : ∀ t ∈ Icc a b, 0 ≤ rate t)
    (htarget : ∀ t ∈ Icc a b, lower ≤ target t)
    (hderiv : ∀ t ∈ Ioo a b,
      HasDerivAt y (rate t * (target t - y t) ^ 3 + forcing t) t)
    (hgain : 0 < ∫ t in a..b, rate t) :
    lower - (Real.sqrt (2 * (∫ t in a..b, rate t)))⁻¹ -
      forcingMass forcing a b < y b := by
  have hnegderiv : ∀ t ∈ Ioo a b,
      HasDerivAt (fun s ↦ -y s)
        (rate t * (-target t - -y t) ^ 3 + -forcing t) t := by
    intro t ht
    convert (hderiv t ht).neg using 1
    ring
  have hbound := lt_upper_add_inv_sqrt_integral_add_forcingMass hab
    hy.neg hrate hforcing.neg hnonneg
    (fun t ht ↦ neg_le_neg (htarget t ht)) hnegderiv hgain
  simp only [forcingMass_neg] at hbound
  linarith

/-- The two-sided forced moving-target estimate of Lemma 4.1(i). The
initial state is arbitrary, and the forcing enters with coefficient one. -/
theorem abs_sub_lt_radius_add_inv_sqrt_integral_add_forcingMass
    {a b center radius : ℝ} {y target rate forcing : ℝ → ℝ}
    (hab : a ≤ b)
    (hy : ContinuousOn y (Icc a b))
    (hrate : ContinuousOn rate (Icc a b))
    (hforcing : ContinuousOn forcing (Icc a b))
    (hnonneg : ∀ t ∈ Icc a b, 0 ≤ rate t)
    (htarget : ∀ t ∈ Icc a b, |target t - center| ≤ radius)
    (hderiv : ∀ t ∈ Ioo a b,
      HasDerivAt y (rate t * (target t - y t) ^ 3 + forcing t) t)
    (hgain : 0 < ∫ t in a..b, rate t) :
    |y b - center| < radius + (Real.sqrt (2 * (∫ t in a..b, rate t)))⁻¹ +
      forcingMass forcing a b := by
  have hupper : ∀ t ∈ Icc a b, target t ≤ center + radius := by
    intro t ht
    have h := (abs_le.mp (htarget t ht)).2
    linarith
  have hlower : ∀ t ∈ Icc a b, center - radius ≤ target t := by
    intro t ht
    have h := (abs_le.mp (htarget t ht)).1
    linarith
  have hu := lt_upper_add_inv_sqrt_integral_add_forcingMass
    hab hy hrate hforcing hnonneg hupper hderiv hgain
  have hl := lower_sub_inv_sqrt_integral_sub_forcingMass_lt
    hab hy hrate hforcing hnonneg hlower hderiv hgain
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- If both the initial value and the moving target lie below `upper`,
the solution stays below `upper` plus the accumulated absolute forcing.
No positive-gain assumption is required. -/
theorem le_upper_add_forcingMass
    {a b upper : ℝ} {y target rate forcing : ℝ → ℝ}
    (hab : a ≤ b)
    (hy : ContinuousOn y (Icc a b))
    (hforcing : ContinuousOn forcing (Icc a b))
    (hnonneg : ∀ t ∈ Icc a b, 0 ≤ rate t)
    (hinitial : y a ≤ upper)
    (htarget : ∀ t ∈ Icc a b, target t ≤ upper)
    (hderiv : ∀ t ∈ Ioo a b,
      HasDerivAt y (rate t * (target t - y t) ^ 3 + forcing t) t)
    {t : ℝ} (ht : t ∈ Icc a b) :
    y t ≤ upper + forcingMass forcing a t := by
  have hnonpos : ∀ s ∈ Ioo a b, 0 < y s - upper - forcingMass forcing a s →
      rate s * (target s - y s) ^ 3 + forcing s - |forcing s| ≤ 0 := by
    intro s hs hp
    refine (upper_excess_deriv_le_cubic
      (hnonneg s (Ioo_subset_Icc_self hs))
      (htarget s (Ioo_subset_Icc_self hs)) (forcingMass_nonneg forcing hs.1.le)).trans ?_
    exact mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (hnonneg s (Ioo_subset_Icc_self hs))) (by positivity)
  have hinitial' : y a - upper - forcingMass forcing a a ≤ 0 := by
    simpa only [forcingMass_self, sub_zero, sub_nonpos] using hinitial
  have hbound := nonpos_of_nonpos_of_deriv_nonpos_on_pos
    ((hy.sub continuousOn_const).sub (continuousOn_forcingMass hab hforcing))
    (fun s hs ↦ ((hderiv s hs).sub_const upper).sub (hasDerivAt_forcingMass hforcing hs))
    hnonpos (left_mem_Icc.mpr hab) ht ht.1 hinitial'
  change y t - upper - forcingMass forcing a t ≤ 0 at hbound
  linarith

/-- A common bound on the initial value and target bounds the solution up
to its accumulated absolute forcing, even when the gain vanishes. -/
theorem abs_le_bound_add_forcingMass
    {a b bound : ℝ} {y target rate forcing : ℝ → ℝ}
    (hab : a ≤ b)
    (hy : ContinuousOn y (Icc a b))
    (hforcing : ContinuousOn forcing (Icc a b))
    (hnonneg : ∀ t ∈ Icc a b, 0 ≤ rate t)
    (hinitial : |y a| ≤ bound)
    (htarget : ∀ t ∈ Icc a b, |target t| ≤ bound)
    (hderiv : ∀ t ∈ Ioo a b,
      HasDerivAt y (rate t * (target t - y t) ^ 3 + forcing t) t)
    {t : ℝ} (ht : t ∈ Icc a b) :
    |y t| ≤ bound + forcingMass forcing a t := by
  have hu := le_upper_add_forcingMass hab hy hforcing hnonneg
    (abs_le.mp hinitial).2 (fun s hs ↦ (abs_le.mp (htarget s hs)).2) hderiv ht
  have hnegderiv : ∀ s ∈ Ioo a b,
      HasDerivAt (fun r ↦ -y r)
        (rate s * (-target s - -y s) ^ 3 + -forcing s) s := by
    intro s hs
    convert (hderiv s hs).neg using 1
    ring
  have hneginit : -y a ≤ bound := by
    have h := (abs_le.mp hinitial).1
    linarith
  have hnegtarget : ∀ s ∈ Icc a b, -target s ≤ bound := by
    intro s hs
    have h := (abs_le.mp (htarget s hs)).1
    linarith
  have hl := le_upper_add_forcingMass hab hy.neg hforcing.neg hnonneg
    hneginit hnegtarget hnegderiv ht
  simp only [forcingMass_neg] at hl
  exact abs_le.mpr ⟨by linarith, hu⟩

/-- The finite-segment bound in Lemma 4.1(iii), expressed using any uniform
bound on the target. This theorem does not assert continuation. -/
theorem abs_le_max_initial_target_add_total_forcingMass
    {a b targetBound : ℝ} {y target rate forcing : ℝ → ℝ}
    (hab : a ≤ b)
    (hy : ContinuousOn y (Icc a b))
    (hforcing : ContinuousOn forcing (Icc a b))
    (hnonneg : ∀ t ∈ Icc a b, 0 ≤ rate t)
    (htarget : ∀ t ∈ Icc a b, |target t| ≤ targetBound)
    (hderiv : ∀ t ∈ Ioo a b,
      HasDerivAt y (rate t * (target t - y t) ^ 3 + forcing t) t)
    {t : ℝ} (ht : t ∈ Icc a b) :
    |y t| ≤ max |y a| targetBound + forcingMass forcing a b := by
  have hbound := abs_le_bound_add_forcingMass hab hy hforcing hnonneg
    (le_max_left |y a| targetBound)
    (fun s hs ↦ (htarget s hs).trans (le_max_right |y a| targetBound)) hderiv ht
  exact hbound.trans (add_le_add le_rfl (forcingMass_le hforcing ht))

end Stability.Simulation
