import HGAS.Dynamics.Stability
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.ExtendFrom
import Mathlib.Tactic

/-!
# Positive state-dependent changes of time

This module develops the analytic infrastructure for replacing an
autonomous vector field `F` by

```
x ↦ a x • F x,
```

where the scalar speed `a` is nonnegative and vanishes only at the common
equilibrium.  The global GAS equivalence is proved later in this file.  The
first sections are independently reusable:

* integral clocks and their differentiable inverse;
* compact-interval uniqueness for `C¹` autonomous fields in proper normed
  spaces;
* noncollision with an equilibrium; and
* conversion of a trajectory by a positive integral clock.

All clock statements are ordinary theorems.  No existence, uniqueness, or
continuation principle is introduced as an axiom.
-/

namespace HGAS

open Filter Function Metric Set
open scoped NNReal Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## Integral clocks -/

/-- The clock whose instantaneous speed is `w`. -/
def integralClock (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, w s

@[simp]
theorem integralClock_zero (w : ℝ → ℝ) :
    integralClock w 0 = 0 := by
  simp [integralClock]

/-- A continuous clock speed is the derivative of its integral clock. -/
theorem integralClock_hasDerivAt
    {w : ℝ → ℝ} (hw : Continuous w) (t : ℝ) :
    HasDerivAt (integralClock w) (w t) t := by
  simpa only [integralClock] using
    (hw.integral_hasStrictDerivAt 0 t).hasDerivAt

/-- An integral clock with continuous speed is continuous. -/
theorem integralClock_continuous
    {w : ℝ → ℝ} (hw : Continuous w) :
    Continuous (integralClock w) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (integralClock_hasDerivAt hw t).continuousAt

/-- A continuous, everywhere positive speed gives a strictly increasing
clock. -/
theorem integralClock_strictMono
    {w : ℝ → ℝ} (hw : Continuous w) (hwpos : ∀ t, 0 < w t) :
    StrictMono (integralClock w) := by
  intro s t hst
  have hdiff :
      integralClock w t - integralClock w s =
        ∫ u in s..t, w u := by
    simpa only [integralClock] using
      intervalIntegral.integral_interval_sub_left
        (hw.intervalIntegrable 0 t)
        (hw.intervalIntegrable 0 s)
  have hpos :
      0 < ∫ u in s..t, w u :=
    intervalIntegral.intervalIntegral_pos_of_pos
      (hw.intervalIntegrable s t) hwpos hst
  linarith

/-- A continuous positive clock speed bounded below by a positive constant
eventually produces a clock tending to `+∞`. -/
theorem integralClock_tendsto_atTop_of_eventually_ge
    {w : ℝ → ℝ} (hw : Continuous w)
    {c : ℝ} (hc : 0 < c)
    (hge : ∀ᶠ t in atTop, c ≤ w t) :
    Tendsto (integralClock w) atTop atTop := by
  obtain ⟨T, hT⟩ := eventually_atTop.1 hge
  apply tendsto_atTop_atTop.2
  intro M
  let U : ℝ :=
    max T (T + (M - integralClock w T) / c)
  refine ⟨U, ?_⟩
  intro t ht
  have hTt : T ≤ t :=
    le_trans (le_max_left _ _) ht
  have hwlower : ∀ u ∈ Icc T t, c ≤ w u := by
    intro u hu
    exact hT u hu.1
  have hintegral :
      c * (t - T) ≤ ∫ u in T..t, w u := by
    have hconst :
        (∫ _u in T..t, c) = c * (t - T) := by
      simp [mul_comm]
    rw [← hconst]
    exact intervalIntegral.integral_mono_on hTt
      (continuous_const.intervalIntegrable T t)
      (hw.intervalIntegrable T t) hwlower
  have hclock :
      integralClock w t =
        integralClock w T + ∫ u in T..t, w u := by
    symm
    simpa only [integralClock] using
      intervalIntegral.integral_add_adjacent_intervals
        (hw.intervalIntegrable 0 T)
        (hw.intervalIntegrable T t)
  have htU :
      T + (M - integralClock w T) / c ≤ t :=
    le_trans (le_max_right _ _) ht
  have hlinear :
      M ≤ integralClock w T + c * (t - T) := by
    have hquotient :
        (M - integralClock w T) / c ≤ t - T := by
      linarith
    have hmul :=
      mul_le_mul_of_nonneg_left hquotient hc.le
    have hcancel :
        c * ((M - integralClock w T) / c) =
          M - integralClock w T := by
      field_simp [hc.ne']
    rw [hcancel] at hmul
    linarith
  rw [hclock]
  exact hlinear.trans
    (by
      simpa [add_comm] using
        add_le_add_left hintegral (integralClock w T))

/-- If a clock speed is a fixed positive constant on nonpositive time,
then its integral clock tends to `-∞` at `-∞`. -/
theorem integralClock_tendsto_atBot_of_eq_const_nonpos
    {w : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hw : ∀ t, t ≤ 0 → w t = c) :
    Tendsto (integralClock w) atBot atBot := by
  have heq :
      integralClock w =ᶠ[atBot] fun t ↦ c * t := by
    filter_upwards [eventually_le_atBot (0 : ℝ)] with t ht
    rw [integralClock]
    calc
      (∫ s in (0 : ℝ)..t, w s) =
          ∫ _s in (0 : ℝ)..t, c := by
        apply intervalIntegral.integral_congr
        intro s hs
        apply hw s
        rw [Set.uIcc_of_ge ht] at hs
        exact hs.2
      _ = c * t := by simp [mul_comm]
  exact ((tendsto_const_mul_atBot_of_pos hc).2 tendsto_id).congr' heq.symm

/-- The data making an integral clock a global orientation-preserving
diffeomorphic reparametrization of the real line. -/
structure PositiveIntegralClock (w : ℝ → ℝ) : Prop where
  continuous : Continuous w
  positive : ∀ t, 0 < w t
  tendsto_atTop : Tendsto (integralClock w) atTop atTop
  tendsto_atBot : Tendsto (integralClock w) atBot atBot

namespace PositiveIntegralClock

/-- A positive integral clock as an order isomorphism of `ℝ`. -/
noncomputable def orderIso {w : ℝ → ℝ}
    (hclock : PositiveIntegralClock w) : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (integralClock w)
    (integralClock_strictMono hclock.continuous hclock.positive)
    ((integralClock_continuous hclock.continuous).surjective
      hclock.tendsto_atTop hclock.tendsto_atBot)

@[simp]
theorem orderIso_apply {w : ℝ → ℝ}
    (hclock : PositiveIntegralClock w) (t : ℝ) :
    orderIso (w := w) hclock t = integralClock w t :=
  rfl

@[simp]
theorem orderIso_zero {w : ℝ → ℝ}
    (hclock : PositiveIntegralClock w) :
    orderIso (w := w) hclock 0 = 0 := by
  exact integralClock_zero w

@[simp]
theorem symm_zero {w : ℝ → ℝ}
    (hclock : PositiveIntegralClock w) :
    (orderIso (w := w) hclock).symm 0 = 0 := by
  apply (orderIso (w := w) hclock).injective
  simp

/-- The inverse clock has reciprocal instantaneous speed. -/
theorem symm_hasDerivAt {w : ℝ → ℝ}
    (hclock : PositiveIntegralClock w) (τ : ℝ) :
    HasDerivAt (fun s ↦ (orderIso (w := w) hclock).symm s)
      (w ((orderIso (w := w) hclock).symm τ))⁻¹ τ := by
  apply
    (integralClock_hasDerivAt hclock.continuous
      ((orderIso (w := w) hclock).symm τ)).of_local_left_inverse
      (orderIso (w := w) hclock).symm.continuous.continuousAt
      (ne_of_gt (hclock.positive _))
  exact Eventually.of_forall fun s ↦ by
    simpa only [orderIso_apply] using
      (orderIso (w := w) hclock).apply_symm_apply s

/-- The inverse of a positive clock preserves nonnegative time. -/
theorem symm_nonneg {w : ℝ → ℝ}
    (hclock : PositiveIntegralClock w) {τ : ℝ} (hτ : 0 ≤ τ) :
    0 ≤ (orderIso (w := w) hclock).symm τ := by
  rw [← symm_zero hclock]
  exact (orderIso (w := w) hclock).symm.monotone hτ

/-- The inverse of a positive clock tends to `+∞`. -/
theorem symm_tendsto_atTop {w : ℝ → ℝ}
    (hclock : PositiveIntegralClock w) :
    Tendsto (fun τ ↦ (orderIso (w := w) hclock).symm τ) atTop atTop :=
  (orderIso (w := w) hclock).symm.tendsto_atTop

end PositiveIntegralClock

/-! ## The inverse below a hypothetical finite clock limit -/

/-- A positive integral clock whose positive-time end has a finite limit.
This structure is used only in contradiction arguments proving that the
clock range is actually unbounded. -/
structure FinitePositiveIntegralClock
    (w : ℝ → ℝ) (L : ℝ) : Prop where
  continuous : Continuous w
  positive : ∀ t, 0 < w t
  tendsto_atTop : Tendsto (integralClock w) atTop (𝓝 L)
  tendsto_atBot : Tendsto (integralClock w) atBot atBot

namespace FinitePositiveIntegralClock

theorem strictMono {w : ℝ → ℝ} {L : ℝ}
    (hclock : FinitePositiveIntegralClock w L) :
    StrictMono (integralClock w) :=
  integralClock_strictMono hclock.continuous hclock.positive

/-- Every finite clock value lies strictly below its limit at `+∞`. -/
theorem apply_lt_limit {w : ℝ → ℝ} {L : ℝ}
    (hclock : FinitePositiveIntegralClock w L) (t : ℝ) :
    integralClock w t < L := by
  have hmono := strictMono (w := w) (L := L) hclock
  have hstep : integralClock w t < integralClock w (t + 1) :=
    hmono (by linarith)
  have hupper : integralClock w (t + 1) ≤ L := by
    apply ge_of_tendsto hclock.tendsto_atTop
    filter_upwards [eventually_ge_atTop (t + 1)] with s hs
    exact hmono.monotone hs
  exact hstep.trans_le hupper

/-- The finite clock, regarded as a map into the open interval below its
limit. -/
def toIio {w : ℝ → ℝ} {L : ℝ}
    (hclock : FinitePositiveIntegralClock w L) (t : ℝ) : Iio L :=
  ⟨integralClock w t, apply_lt_limit (w := w) (L := L) hclock t⟩

theorem toIio_strictMono {w : ℝ → ℝ} {L : ℝ}
    (hclock : FinitePositiveIntegralClock w L) :
    StrictMono (toIio (w := w) (L := L) hclock) := by
  intro s t hst
  exact strictMono (w := w) (L := L) hclock hst

/-- A finite positive clock maps `ℝ` onto the whole interval `(-∞, L)`. -/
theorem toIio_surjective {w : ℝ → ℝ} {L : ℝ}
    (hclock : FinitePositiveIntegralClock w L) :
    Function.Surjective (toIio (w := w) (L := L) hclock) := by
  rintro ⟨y, hyL⟩
  obtain ⟨s, hs⟩ :
      ∃ s : ℝ, integralClock w s ≤ y := by
    have hevent :
        ∀ᶠ s in atBot, integralClock w s ≤ y :=
      hclock.tendsto_atBot (eventually_le_atBot y)
    exact hevent.exists
  obtain ⟨t, ht⟩ :
      ∃ t : ℝ, y ≤ integralClock w t := by
    have hevent :
        ∀ᶠ t in atTop, y < integralClock w t :=
      hclock.tendsto_atTop (Ioi_mem_nhds hyL)
    obtain ⟨t, ht⟩ := hevent.exists
    exact ⟨t, ht.le⟩
  have hy :
      y ∈ Set.range (integralClock w) :=
    intermediate_value_univ s t
      (integralClock_continuous hclock.continuous) ⟨hs, ht⟩
  obtain ⟨u, hu⟩ := hy
  refine ⟨u, ?_⟩
  apply Subtype.ext
  exact hu

/-- The order isomorphism from physical time to the finite clock range. -/
noncomputable def orderIso {w : ℝ → ℝ} {L : ℝ}
    (hclock : FinitePositiveIntegralClock w L) : ℝ ≃o Iio L :=
  StrictMono.orderIsoOfSurjective
    (toIio (w := w) (L := L) hclock)
    (toIio_strictMono (w := w) (L := L) hclock)
    (toIio_surjective (w := w) (L := L) hclock)

@[simp]
theorem orderIso_apply_val {w : ℝ → ℝ} {L : ℝ}
    (hclock : FinitePositiveIntegralClock w L) (t : ℝ) :
    (orderIso (w := w) (L := L) hclock t : ℝ) = integralClock w t :=
  rfl

/-- A total inverse below `L`; its arbitrary value at and above `L` is
irrelevant. -/
noncomputable def inverse {w : ℝ → ℝ} {L : ℝ}
    (hclock : FinitePositiveIntegralClock w L) (s : ℝ) : ℝ :=
  if hs : s < L then
    (orderIso (w := w) (L := L) hclock).symm ⟨s, hs⟩
  else 0

theorem inverse_of_lt {w : ℝ → ℝ} {L : ℝ}
    (hclock : FinitePositiveIntegralClock w L)
    {s : ℝ} (hs : s < L) :
    inverse (w := w) (L := L) hclock s =
      (orderIso (w := w) (L := L) hclock).symm ⟨s, hs⟩ := by
  simp [inverse, hs]

/-- The clock applied to its finite-range inverse is the identity. -/
theorem apply_inverse {w : ℝ → ℝ} {L : ℝ}
    (hclock : FinitePositiveIntegralClock w L)
    {s : ℝ} (hs : s < L) :
    integralClock w (inverse (w := w) (L := L) hclock s) = s := by
  rw [inverse_of_lt (w := w) (L := L) hclock hs]
  simpa only [← orderIso_apply_val (w := w) (L := L) hclock] using
    congrArg Subtype.val
      ((orderIso (w := w) (L := L) hclock).apply_symm_apply ⟨s, hs⟩)

/-- The finite-range inverse applied to a clock value is the identity. -/
theorem inverse_apply {w : ℝ → ℝ} {L : ℝ}
    (hclock : FinitePositiveIntegralClock w L) (t : ℝ) :
    inverse (w := w) (L := L) hclock (integralClock w t) = t := by
  rw [inverse_of_lt (w := w) (L := L) hclock
    (apply_lt_limit (w := w) (L := L) hclock t)]
  exact (orderIso (w := w) (L := L) hclock).symm_apply_apply t

/-- The finite positive-time clock limit is itself positive. -/
theorem limit_pos {w : ℝ → ℝ} {L : ℝ}
    (hclock : FinitePositiveIntegralClock w L) :
    0 < L := by
  simpa only [integralClock_zero] using
    apply_lt_limit (w := w) (L := L) hclock 0

@[simp]
theorem inverse_zero {w : ℝ → ℝ} {L : ℝ}
    (hclock : FinitePositiveIntegralClock w L) :
    inverse (w := w) (L := L) hclock 0 = 0 := by
  simpa only [integralClock_zero] using
    inverse_apply (w := w) (L := L) hclock 0

/-- Below the finite endpoint, the inverse clock is monotone. -/
theorem inverse_mono_of_lt {w : ℝ → ℝ} {L : ℝ}
    (hclock : FinitePositiveIntegralClock w L)
    {s t : ℝ} (hs : s < L) (ht : t < L) (hst : s ≤ t) :
    inverse (w := w) (L := L) hclock s ≤
      inverse (w := w) (L := L) hclock t := by
  rw [inverse_of_lt (w := w) (L := L) hclock hs,
    inverse_of_lt (w := w) (L := L) hclock ht]
  exact (orderIso (w := w) (L := L) hclock).symm.monotone hst

/-- Nonnegative finite clock time corresponds to nonnegative physical
time. -/
theorem inverse_nonneg {w : ℝ → ℝ} {L : ℝ}
    (hclock : FinitePositiveIntegralClock w L)
    {s : ℝ} (hs0 : 0 ≤ s) (hsL : s < L) :
    0 ≤ inverse (w := w) (L := L) hclock s := by
  rw [← inverse_zero (w := w) (L := L) hclock]
  exact inverse_mono_of_lt (w := w) (L := L) hclock
    (limit_pos (w := w) (L := L) hclock) hsL hs0

/-- Positive finite clock time corresponds to positive physical time. -/
theorem inverse_pos {w : ℝ → ℝ} {L : ℝ}
    (hclock : FinitePositiveIntegralClock w L)
    {s : ℝ} (hs0 : 0 < s) (hsL : s < L) :
    0 < inverse (w := w) (L := L) hclock s := by
  rw [← inverse_zero (w := w) (L := L) hclock,
    inverse_of_lt (w := w) (L := L) hclock
      (limit_pos (w := w) (L := L) hclock),
    inverse_of_lt (w := w) (L := L) hclock hsL]
  exact (orderIso (w := w) (L := L) hclock).symm.strictMono hs0

/-- The finite-range inverse is continuous at every point below `L`. -/
theorem inverse_continuousAt {w : ℝ → ℝ} {L : ℝ}
    (hclock : FinitePositiveIntegralClock w L)
    {s : ℝ} (hs : s < L) :
    ContinuousAt (inverse (w := w) (L := L) hclock) s := by
  let q : ℝ := (s + L) / 2
  have hsq : s < q := by
    dsimp only [q]
    linarith
  have hqL : q < L := by
    dsimp only [q]
    linarith
  let r : ℝ → Iio L :=
    fun y ↦ ⟨min y q, lt_of_le_of_lt (min_le_right _ _) hqL⟩
  let g : ℝ → ℝ :=
    fun y ↦ (orderIso (w := w) (L := L) hclock).symm (r y)
  have hg : Continuous g := by
    dsimp only [g, r]
    fun_prop
  have heq :
      inverse (w := w) (L := L) hclock =ᶠ[𝓝 s] g := by
    filter_upwards [Iio_mem_nhds hsq] with y hy
    have hyL : y < L := hy.trans hqL
    rw [inverse_of_lt (w := w) (L := L) hclock hyL]
    apply congrArg (orderIso (w := w) (L := L) hclock).symm
    apply Subtype.ext
    have hyq : y ≤ q := le_of_lt hy
    simp [r, min_eq_left hyq]
  exact hg.continuousAt.congr_of_eventuallyEq heq

/-- Derivative of the finite-range inverse. -/
theorem inverse_hasDerivAt {w : ℝ → ℝ} {L : ℝ}
    (hclock : FinitePositiveIntegralClock w L)
    {s : ℝ} (hs : s < L) :
    HasDerivAt (inverse (w := w) (L := L) hclock)
      (w (inverse (w := w) (L := L) hclock s))⁻¹ s := by
  apply
    (integralClock_hasDerivAt hclock.continuous
      (inverse (w := w) (L := L) hclock s)).of_local_left_inverse
      (inverse_continuousAt (w := w) (L := L) hclock hs)
      (ne_of_gt (hclock.positive _))
  filter_upwards [Iio_mem_nhds hs] with y hy
  exact apply_inverse (w := w) (L := L) hclock hy

/-- The inverse clock goes to `+∞` as its argument approaches the finite
limit from below. -/
theorem inverse_tendsto_atTop {w : ℝ → ℝ} {L : ℝ}
    (hclock : FinitePositiveIntegralClock w L) :
    Tendsto (inverse (w := w) (L := L) hclock)
      (𝓝[Iio L] L) atTop := by
  apply Filter.tendsto_atTop.2
  intro T
  have hCT : integralClock w T < L :=
    apply_lt_limit (w := w) (L := L) hclock T
  filter_upwards
    [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hCT),
      self_mem_nhdsWithin] with s hsT hsL
  have hslt : s < L := hsL
  rw [inverse_of_lt (w := w) (L := L) hclock hslt]
  have hsub :
      (⟨integralClock w T, hCT⟩ : Iio L) ≤ ⟨s, hslt⟩ :=
    hsT.le
  simpa only [
    ← orderIso_apply_val (w := w) (L := L) hclock,
    (orderIso (w := w) (L := L) hclock).symm_apply_apply] using
      (orderIso (w := w) (L := L) hclock).symm.monotone hsub

end FinitePositiveIntegralClock

/-! ## Compact-interval uniqueness for `C¹` fields -/

section Uniqueness

variable [ProperSpace E]

/-- Two solutions of a `C¹` autonomous ODE that agree at the left endpoint
agree throughout a compact interval.

The proof extracts a single closed ball containing both compact trajectory
images.  A `C¹` field is Lipschitz on that compact convex ball, so Mathlib's
Gronwall uniqueness theorem applies. -/
theorem ode_solution_unique_Icc_right_of_contDiff
    {F : E → E} (hF : ContDiff ℝ 1 F)
    {γ η : ℝ → E} {a b : ℝ}
    (hγc : ContinuousOn γ (Icc a b))
    (hγd : ∀ t ∈ Ico a b,
      HasDerivWithinAt γ (F (γ t)) (Ici t) t)
    (hηc : ContinuousOn η (Icc a b))
    (hηd : ∀ t ∈ Ico a b,
      HasDerivWithinAt η (F (η t)) (Ici t) t)
    (heq : γ a = η a) :
    EqOn γ η (Icc a b) := by
  have hcompact :
      IsCompact (γ '' Icc a b ∪ η '' Icc a b) :=
    (isCompact_Icc.image_of_continuousOn hγc).union
      (isCompact_Icc.image_of_continuousOn hηc)
  obtain ⟨R, hR⟩ :=
    hcompact.isBounded.subset_closedBall (0 : E)
  obtain ⟨K, hK⟩ :=
    hF.contDiffOn.exists_lipschitzOnWith one_ne_zero
      (convex_closedBall (0 : E) R) (isCompact_closedBall (0 : E) R)
  apply ODE_solution_unique_of_mem_Icc_right
    (v := fun _ ↦ F) (s := fun _ ↦ closedBall (0 : E) R)
    (K := K) (a := a) (b := b)
  · intro t ht
    exact hK
  · exact hγc
  · exact hγd
  · intro t ht
    exact hR (Or.inl ⟨t, Ico_subset_Icc_self ht, rfl⟩)
  · exact hηc
  · exact hηd
  · intro t ht
    exact hR (Or.inr ⟨t, Ico_subset_Icc_self ht, rfl⟩)
  · exact heq

/-- Backward version of compact-interval uniqueness: agreement at the
right endpoint determines both trajectories on the whole interval. -/
theorem ode_solution_unique_Icc_left_of_contDiff
    {F : E → E} (hF : ContDiff ℝ 1 F)
    {γ η : ℝ → E} {a b : ℝ}
    (hγc : ContinuousOn γ (Icc a b))
    (hγd : ∀ t ∈ Ioc a b,
      HasDerivWithinAt γ (F (γ t)) (Iic t) t)
    (hηc : ContinuousOn η (Icc a b))
    (hηd : ∀ t ∈ Ioc a b,
      HasDerivWithinAt η (F (η t)) (Iic t) t)
    (heq : γ b = η b) :
    EqOn γ η (Icc a b) := by
  have hcompact :
      IsCompact (γ '' Icc a b ∪ η '' Icc a b) :=
    (isCompact_Icc.image_of_continuousOn hγc).union
      (isCompact_Icc.image_of_continuousOn hηc)
  obtain ⟨R, hR⟩ :=
    hcompact.isBounded.subset_closedBall (0 : E)
  obtain ⟨K, hK⟩ :=
    hF.contDiffOn.exists_lipschitzOnWith one_ne_zero
      (convex_closedBall (0 : E) R) (isCompact_closedBall (0 : E) R)
  apply ODE_solution_unique_of_mem_Icc_left
    (v := fun _ ↦ F) (s := fun _ ↦ closedBall (0 : E) R)
    (K := K) (a := a) (b := b)
  · intro t ht
    exact hK
  · exact hγc
  · exact hγd
  · intro t ht
    exact hR (Or.inl ⟨t, Ioc_subset_Icc_self ht, rfl⟩)
  · exact hηc
  · exact hηd
  · intro t ht
    exact hR (Or.inr ⟨t, Ioc_subset_Icc_self ht, rfl⟩)
  · exact heq

/-- Forward trajectories of a `C¹` autonomous field with the same initial
state agree at every nonnegative time.  This is the global-on-the-common-
domain consequence of compact-interval uniqueness. -/
theorem IsForwardTrajectory.eqOn_Ici_of_contDiff
    {F : E → E} (hF : ContDiff ℝ 1 F)
    {x₀ : E} {γ η : ℝ → E}
    (hγ : IsForwardTrajectory F γ x₀)
    (hη : IsForwardTrajectory F η x₀) :
    EqOn γ η (Ici (0 : ℝ)) := by
  intro t ht
  have heqOn :=
    ode_solution_unique_Icc_right_of_contDiff
      (γ := γ) (η := η) (a := 0) (b := t) hF
      (hγ.2.continuousOn.mono Icc_subset_Ici_self)
      (by
        intro s hs
        exact (hγ.2 s hs.1).mono
          (Ici_subset_Ici.mpr hs.1))
      (hη.2.continuousOn.mono Icc_subset_Ici_self)
      (by
        intro s hs
        exact (hη.2 s hs.1).mono
          (Ici_subset_Ici.mpr hs.1))
      (hγ.1.trans hη.1.symm)
  exact heqOn ⟨ht, le_rfl⟩

/-- A forward trajectory of a `C¹` field cannot meet an equilibrium in
finite positive time unless it starts there. -/
theorem IsForwardTrajectory.ne_equilibrium
    {F : E → E} (hF : ContDiff ℝ 1 F)
    {xEq x₀ : E} (hEq : F xEq = 0)
    {γ : ℝ → E} (hγ : IsForwardTrajectory F γ x₀)
    (hx₀ : x₀ ≠ xEq) {t : ℝ} (ht : 0 ≤ t) :
    γ t ≠ xEq := by
  intro hhit
  by_cases ht0 : t = 0
  · subst t
    exact hx₀ (hγ.1.symm.trans hhit)
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  let η : ℝ → E := fun _ ↦ xEq
  have heqOn :=
    ode_solution_unique_Icc_left_of_contDiff
      (γ := γ) (η := η) (a := 0) (b := t) hF
      (hγ.2.continuousOn.mono Icc_subset_Ici_self)
      (by
        intro s hs
        exact
          ((hγ.2 s hs.1.le).hasDerivAt
            (Ici_mem_nhds hs.1)).hasDerivWithinAt)
      continuous_const.continuousOn
      (by
        intro s hs
        show HasDerivWithinAt η (F (η s)) (Iic s) s
        simpa only [η, hEq] using
          (hasDerivAt_const (x := s) (c := xEq)).hasDerivWithinAt)
      (by
        show γ t = η t
        simpa only [η] using hhit)
  have hzero : γ 0 = xEq :=
    heqOn ⟨le_rfl, ht⟩
  exact hx₀ (hγ.1.symm.trans hzero)

end Uniqueness

/-! ## State-scaled fields and forward extensions -/

/-- Multiplication of a vector field by a scalar state-dependent speed. -/
def timeScaledField (a : E → ℝ) (F : E → E) : E → E :=
  fun x ↦ a x • F x

/-- A scalar multiplication of two `C¹` maps is `C¹`. -/
theorem timeScaledField_contDiff
    {a : E → ℝ} {F : E → E}
    (ha : ContDiff ℝ 1 a) (hF : ContDiff ℝ 1 F) :
    ContDiff ℝ 1 (timeScaledField a F) := by
  exact ha.smul hF

/-- The constant curve through an equilibrium is a forward trajectory. -/
theorem IsForwardTrajectory.const_of_equilibrium
    {F : E → E} {xEq : E} (hEq : F xEq = 0) :
    IsForwardTrajectory F (fun _ ↦ xEq) xEq := by
  refine ⟨rfl, ?_⟩
  intro t _ht
  simpa only [hEq] using
    (hasDerivWithinAt_const (x := t) (c := xEq)
      (s := Ici (0 : ℝ)))

/-- Extend the forward-time part of a curve to negative time by keeping
its value at time zero. -/
def forwardExtension (γ : ℝ → E) (t : ℝ) : E :=
  γ (max t 0)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
@[simp]
theorem forwardExtension_zero (γ : ℝ → E) :
    forwardExtension γ 0 = γ 0 := by
  simp [forwardExtension]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem forwardExtension_of_nonneg
    (γ : ℝ → E) {t : ℝ} (ht : 0 ≤ t) :
    forwardExtension γ t = γ t := by
  simp [forwardExtension, max_eq_left ht]

omit [NormedSpace ℝ E] in
/-- A curve continuous on nonnegative time has a continuous constant
extension to negative time. -/
theorem continuous_forwardExtension
    {γ : ℝ → E} (hγ : ContinuousOn γ (Ici 0)) :
    Continuous (forwardExtension γ) := by
  rw [← continuousOn_univ]
  simpa only [forwardExtension, Function.comp_def] using
    hγ.comp (continuous_id.max continuous_const).continuousOn
      (fun t _ ↦ le_max_right t 0)

/-! ## The reciprocal clock along an attractive base trajectory -/

/-- The speed used to pass from a trajectory of `F` to a trajectory of
`a • F`. -/
def reciprocalStateClockWeight
    (a : E → ℝ) (γ : ℝ → E) (t : ℝ) : ℝ :=
  (a (forwardExtension γ t))⁻¹

/-- The speed used to pass from a trajectory of `a • F` back to a
trajectory of `F`. -/
def stateClockWeight
    (a : E → ℝ) (γ : ℝ → E) (t : ℝ) : ℝ :=
  a (forwardExtension γ t)

/-- Epsilon-time global attraction is exactly convergence at `atTop`. -/
theorem GloballyAttractive.tendsto_atTop
    {F : E → E} {xEq x₀ : E} {γ : ℝ → E}
    (hattr : GloballyAttractive F xEq)
    (hγ : IsForwardTrajectory F γ x₀) :
    Tendsto γ atTop (𝓝 xEq) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T, hT, hafter⟩ := hattr x₀ γ hγ ε hε
  exact ⟨T, hafter⟩

section ProperTimeChange

variable [ProperSpace E]

/-- Along a nonzero trajectory of a `C¹` field, the reciprocal state
weight is continuous and strictly positive. -/
theorem reciprocalStateClockWeight_continuous_positive
    {a : E → ℝ} {F : E → E}
    (ha : Continuous a) (ha_nonneg : ∀ x, 0 ≤ a x)
    (ha_zero : ∀ x, a x = 0 ↔ x = 0)
    (hF : ContDiff ℝ 1 F) (hF0 : F 0 = 0)
    {x₀ : E} (hx₀ : x₀ ≠ 0)
    {γ : ℝ → E} (hγ : IsForwardTrajectory F γ x₀) :
    Continuous (reciprocalStateClockWeight a γ) ∧
      ∀ t, 0 < reciprocalStateClockWeight a γ t := by
  have hγne : ∀ t : ℝ, 0 ≤ t → γ t ≠ 0 := by
    intro t ht
    exact hγ.ne_equilibrium hF hF0 hx₀ ht
  have hfwd_ne : ∀ t : ℝ, forwardExtension γ t ≠ 0 := by
    intro t
    exact hγne (max t 0) (le_max_right t 0)
  have hapos : ∀ t : ℝ, 0 < a (forwardExtension γ t) := by
    intro t
    exact lt_of_le_of_ne (ha_nonneg _)
      (Ne.symm ((ha_zero _).not.mpr (hfwd_ne t)))
  constructor
  · exact
      (ha.comp (continuous_forwardExtension hγ.2.continuousOn)).inv₀
        fun t ↦ ne_of_gt (hapos t)
  · intro t
    exact inv_pos.mpr (hapos t)

omit [NormedSpace ℝ E] [ProperSpace E] in
/-- If the base trajectory converges to the origin, its reciprocal clock
has unbounded positive-time range. -/
theorem reciprocalStateClockWeight_tendsto_atTop
    {a : E → ℝ} (ha : Continuous a) (ha0 : a 0 = 0)
    {γ : ℝ → E} (hγcont : ContinuousOn γ (Ici 0))
    (hγlim : Tendsto γ atTop (𝓝 0))
    (hpos : ∀ t, 0 < reciprocalStateClockWeight a γ t) :
    Tendsto (integralClock (reciprocalStateClockWeight a γ))
      atTop atTop := by
  have hfwd_eq : forwardExtension γ =ᶠ[atTop] γ := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact forwardExtension_of_nonneg γ ht
  have hfwd_lim : Tendsto (forwardExtension γ) atTop (𝓝 0) :=
    hγlim.congr' hfwd_eq.symm
  have halim :
      Tendsto (fun t ↦ a (forwardExtension γ t)) atTop (𝓝 0) := by
    simpa only [ha0] using ha.continuousAt.tendsto.comp hfwd_lim
  have hsmall :
      ∀ᶠ t in atTop, a (forwardExtension γ t) < 1 :=
    halim (Iio_mem_nhds zero_lt_one)
  have hge :
      ∀ᶠ t in atTop, 1 ≤ reciprocalStateClockWeight a γ t := by
    filter_upwards [hsmall] with t ht
    have hapos : 0 < a (forwardExtension γ t) := by
      exact inv_pos.mp (hpos t)
    exact (one_le_inv₀ hapos).2 ht.le
  have hcontinuous :
      Continuous (reciprocalStateClockWeight a γ) := by
    have hane : ∀ t, a (forwardExtension γ t) ≠ 0 :=
      fun t ↦ ne_of_gt (inv_pos.mp (hpos t))
    exact
      (ha.comp (continuous_forwardExtension hγcont)).inv₀ hane
  exact integralClock_tendsto_atTop_of_eventually_ge
    hcontinuous zero_lt_one hge

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] in
/-- The reciprocal clock tends to `-∞` on negative time because its
forward extension is constant there. -/
theorem reciprocalStateClockWeight_tendsto_atBot
    {a : E → ℝ} {x₀ : E} {γ : ℝ → E}
    (hγ0 : γ 0 = x₀) (hapos : 0 < a x₀) :
    Tendsto (integralClock (reciprocalStateClockWeight a γ))
      atBot atBot := by
  apply integralClock_tendsto_atBot_of_eq_const_nonpos (inv_pos.mpr hapos)
  intro t ht
  simp [reciprocalStateClockWeight, forwardExtension,
    max_eq_right ht, hγ0]

/-- The reciprocal integral clock along a nonzero attractive trajectory
is a global positive clock. -/
theorem reciprocalStateClock
    {a : E → ℝ} {F : E → E}
    (ha : Continuous a) (ha_nonneg : ∀ x, 0 ≤ a x)
    (ha_zero : ∀ x, a x = 0 ↔ x = 0)
    (hF : ContDiff ℝ 1 F) (hF0 : F 0 = 0)
    {x₀ : E} (hx₀ : x₀ ≠ 0)
    {γ : ℝ → E} (hγ : IsForwardTrajectory F γ x₀)
    (hγlim : Tendsto γ atTop (𝓝 0)) :
    PositiveIntegralClock (reciprocalStateClockWeight a γ) := by
  obtain ⟨hcontinuous, hpositive⟩ :=
    reciprocalStateClockWeight_continuous_positive
      ha ha_nonneg ha_zero hF hF0 hx₀ hγ
  have hapos : 0 < a x₀ :=
    lt_of_le_of_ne (ha_nonneg x₀)
      (Ne.symm ((ha_zero x₀).not.mpr hx₀))
  exact
    { continuous := hcontinuous
      positive := hpositive
      tendsto_atTop :=
        reciprocalStateClockWeight_tendsto_atTop
          ha ((ha_zero 0).2 rfl) hγ.2.continuousOn hγlim hpositive
      tendsto_atBot :=
        reciprocalStateClockWeight_tendsto_atBot hγ.1 hapos }

/-! ## The direct clock along a state-scaled trajectory -/

/-- Along a nonzero trajectory of the state-scaled field, the direct state
weight is continuous and strictly positive.  The only possible zero of the
speed is the equilibrium, and `C¹` uniqueness prevents a nonzero trajectory
from reaching that equilibrium in finite time. -/
theorem stateClockWeight_continuous_positive
    {a : E → ℝ} {F : E → E}
    (ha : ContDiff ℝ 1 a) (ha_nonneg : ∀ x, 0 ≤ a x)
    (ha_zero : ∀ x, a x = 0 ↔ x = 0)
    (hF : ContDiff ℝ 1 F)
    {x₀ : E} (hx₀ : x₀ ≠ 0)
    {γ : ℝ → E}
    (hγ : IsForwardTrajectory (timeScaledField a F) γ x₀) :
    Continuous (stateClockWeight a γ) ∧
      ∀ t, 0 < stateClockWeight a γ t := by
  have hscaled : ContDiff ℝ 1 (timeScaledField a F) :=
    timeScaledField_contDiff ha hF
  have hscaled0 : timeScaledField a F 0 = 0 := by
    simp [timeScaledField, (ha_zero 0).2 rfl]
  have hγne : ∀ t : ℝ, 0 ≤ t → γ t ≠ 0 := by
    intro t ht
    exact hγ.ne_equilibrium hscaled hscaled0 hx₀ ht
  have hfwd_ne : ∀ t : ℝ, forwardExtension γ t ≠ 0 := by
    intro t
    exact hγne (max t 0) (le_max_right t 0)
  have hapos : ∀ t : ℝ, 0 < a (forwardExtension γ t) := by
    intro t
    exact lt_of_le_of_ne (ha_nonneg _)
      (Ne.symm ((ha_zero _).not.mpr (hfwd_ne t)))
  constructor
  · exact
      ha.continuous.comp
        (continuous_forwardExtension hγ.2.continuousOn)
  · exact hapos

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] in
/-- The direct state clock tends to `-∞` on negative time because its
forward extension is constant there. -/
theorem stateClockWeight_tendsto_atBot
    {a : E → ℝ} {x₀ : E} {γ : ℝ → E}
    (hγ0 : γ 0 = x₀) (hapos : 0 < a x₀) :
    Tendsto (integralClock (stateClockWeight a γ))
      atBot atBot := by
  apply integralClock_tendsto_atBot_of_eq_const_nonpos hapos
  intro t ht
  simp [stateClockWeight, forwardExtension, max_eq_right ht, hγ0]

/-! ## Reparametrizing trajectories by global clocks -/

omit [ProperSpace E] in
/-- A base trajectory reparametrized by the inverse reciprocal clock is a
trajectory of the state-scaled field. -/
theorem IsForwardTrajectory.reparametrize_to_timeScaledField
    {a : E → ℝ} {F : E → E} {x₀ : E} {γ : ℝ → E}
    (hγ : IsForwardTrajectory F γ x₀)
    (hclock :
      PositiveIntegralClock (reciprocalStateClockWeight a γ)) :
    IsForwardTrajectory (timeScaledField a F)
      (fun τ ↦ γ
        ((PositiveIntegralClock.orderIso hclock).symm τ)) x₀ := by
  let B : ℝ → ℝ :=
    fun τ ↦ (PositiveIntegralClock.orderIso hclock).symm τ
  have hB0 : B 0 = 0 :=
    PositiveIntegralClock.symm_zero hclock
  refine ⟨by simp only [B, hB0, hγ.1], ?_⟩
  intro t ht
  have hBt : 0 ≤ B t :=
    PositiveIntegralClock.symm_nonneg hclock ht
  have hBmaps : MapsTo B (Ici 0) (Ici 0) := by
    intro s hs
    exact PositiveIntegralClock.symm_nonneg hclock hs
  have hcomp :=
    (hγ.2 (B t) hBt).scomp t
      (PositiveIntegralClock.symm_hasDerivAt hclock t).hasDerivWithinAt
      hBmaps
  simpa only [B, reciprocalStateClockWeight,
    forwardExtension_of_nonneg γ hBt, timeScaledField, inv_inv] using hcomp

omit [ProperSpace E] in
/-- A state-scaled trajectory reparametrized by the inverse direct clock is
a trajectory of the original field. -/
theorem IsForwardTrajectory.reparametrize_from_timeScaledField
    {a : E → ℝ} {F : E → E} {x₀ : E} {γ : ℝ → E}
    (hγ : IsForwardTrajectory (timeScaledField a F) γ x₀)
    (hclock : PositiveIntegralClock (stateClockWeight a γ)) :
    IsForwardTrajectory F
      (fun τ ↦ γ
        ((PositiveIntegralClock.orderIso hclock).symm τ)) x₀ := by
  let B : ℝ → ℝ :=
    fun τ ↦ (PositiveIntegralClock.orderIso hclock).symm τ
  have hB0 : B 0 = 0 :=
    PositiveIntegralClock.symm_zero hclock
  refine ⟨by simp only [B, hB0, hγ.1], ?_⟩
  intro t ht
  have hBt : 0 ≤ B t :=
    PositiveIntegralClock.symm_nonneg hclock ht
  have hBmaps : MapsTo B (Ici 0) (Ici 0) := by
    intro s hs
    exact PositiveIntegralClock.symm_nonneg hclock hs
  have hcomp :=
    (hγ.2 (B t) hBt).scomp t
      (PositiveIntegralClock.symm_hasDerivAt hclock t).hasDerivWithinAt
      hBmaps
  have hapos : 0 < a (γ (B t)) := by
    simpa only [B, stateClockWeight,
      forwardExtension_of_nonneg γ hBt] using hclock.positive (B t)
  simpa only [B, stateClockWeight,
    forwardExtension_of_nonneg γ hBt, timeScaledField, smul_smul,
    inv_mul_cancel₀ (ne_of_gt hapos), one_smul] using hcomp

/-! ## Excluding a finite endpoint for the direct clock -/

omit [ProperSpace E] in
/-- Below a hypothetical finite clock endpoint, inverse-clock
reparametrization of a state-scaled trajectory solves the original ODE.
The statement is deliberately local: it is useful independently of the
contradiction argument below. -/
theorem IsForwardTrajectory.finite_reparametrize_from_timeScaledField_hasDerivAt
    {a : E → ℝ} {F : E → E} {x₀ : E} {γ : ℝ → E} {L : ℝ}
    (hγ : IsForwardTrajectory (timeScaledField a F) γ x₀)
    (hclock :
      FinitePositiveIntegralClock (stateClockWeight a γ) L)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) L) :
    HasDerivAt
      (fun τ ↦ γ (FinitePositiveIntegralClock.inverse hclock τ))
      (F (γ (FinitePositiveIntegralClock.inverse hclock s))) s := by
  let B : ℝ → ℝ :=
    FinitePositiveIntegralClock.inverse hclock
  have hBpos : 0 < B s :=
    FinitePositiveIntegralClock.inverse_pos hclock hs.1 hs.2
  have hBnonneg : 0 ≤ B s := hBpos.le
  have hηderiv :
      HasDerivAt γ
        (timeScaledField a F (γ (B s))) (B s) :=
    (hγ.2 (B s) hBnonneg).hasDerivAt
      (Ici_mem_nhds hBpos)
  have hcomp :=
    hηderiv.scomp s
      (FinitePositiveIntegralClock.inverse_hasDerivAt hclock hs.2)
  have hapos : 0 < a (γ (B s)) := by
    simpa only [B, stateClockWeight,
      forwardExtension_of_nonneg γ hBnonneg] using
        hclock.positive (B s)
  simpa only [B, stateClockWeight,
    forwardExtension_of_nonneg γ hBnonneg, timeScaledField, smul_smul,
    inv_mul_cancel₀ (ne_of_gt hapos), one_smul] using hcomp

/-- The inverse-clock reparametrization below a hypothetical finite
endpoint. -/
def finiteClockReparam
    {w : ℝ → ℝ} {L : ℝ}
    (hclock : FinitePositiveIntegralClock w L)
    (γ : ℝ → E) (s : ℝ) : E :=
  γ (FinitePositiveIntegralClock.inverse hclock s)

/-- Fill in both endpoints of the finite-clock orbit by their one-sided
limits.  In the application, these values are respectively the initial
state and the equilibrium. -/
def finiteClockOrbit
    {w : ℝ → ℝ} {L : ℝ}
    (hclock : FinitePositiveIntegralClock w L)
    (γ : ℝ → E) : ℝ → E :=
  extendFrom (Ioo (0 : ℝ) L) (finiteClockReparam hclock γ)

omit [ProperSpace E] in
/-- The finite-clock reparametrization is continuous in the open clock
interval. -/
theorem finiteClockReparam_continuousOn
    {a : E → ℝ} {F : E → E} {x₀ : E} {γ : ℝ → E} {L : ℝ}
    (hγ : IsForwardTrajectory (timeScaledField a F) γ x₀)
    (hclock :
      FinitePositiveIntegralClock (stateClockWeight a γ) L) :
    ContinuousOn (finiteClockReparam hclock γ) (Ioo 0 L) := by
  intro s hs
  exact
    (hγ.finite_reparametrize_from_timeScaledField_hasDerivAt
      hclock hs).continuousAt.continuousWithinAt

omit [ProperSpace E] in
/-- At the left endpoint the finite-clock reparametrization tends to its
initial state. -/
theorem finiteClockReparam_tendsto_zero
    {a : E → ℝ} {F : E → E} {x₀ : E} {γ : ℝ → E} {L : ℝ}
    (hγ : IsForwardTrajectory (timeScaledField a F) γ x₀)
    (hclock :
      FinitePositiveIntegralClock (stateClockWeight a γ) L) :
    Tendsto (finiteClockReparam hclock γ)
      (𝓝[>] (0 : ℝ)) (𝓝 x₀) := by
  let B : ℝ → ℝ :=
    FinitePositiveIntegralClock.inverse hclock
  have hBlim_nhds : Tendsto B (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [B, FinitePositiveIntegralClock.inverse_zero hclock] using
      (FinitePositiveIntegralClock.inverse_continuousAt hclock
        (FinitePositiveIntegralClock.limit_pos hclock)).mono_left
          inf_le_left
  have hBnonneg : ∀ᶠ s in 𝓝[>] (0 : ℝ), B s ∈ Ici (0 : ℝ) := by
    filter_upwards
      [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds
          (Iio_mem_nhds
            (FinitePositiveIntegralClock.limit_pos hclock))] with s hs0 hsL
    exact FinitePositiveIntegralClock.inverse_nonneg
      hclock hs0.le hsL
  have hBlim :
      Tendsto B (𝓝[>] (0 : ℝ)) (𝓝[Ici (0 : ℝ)] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      B hBlim_nhds hBnonneg
  have hηcont :
      Tendsto γ (𝓝[Ici (0 : ℝ)] 0) (𝓝 (γ 0)) :=
    hγ.2.continuousOn 0 (by simp)
  have hηlim := hηcont.comp hBlim
  simpa only [finiteClockReparam, B, hγ.1] using hηlim

omit [NormedSpace ℝ E] [ProperSpace E] in
/-- If the physical trajectory converges to the origin, then the
finite-clock reparametrization converges to the origin at the putative
right endpoint. -/
theorem finiteClockReparam_tendsto_limit
    {w : ℝ → ℝ} {L : ℝ}
    (hclock : FinitePositiveIntegralClock w L)
    {γ : ℝ → E} (hγlim : Tendsto γ atTop (𝓝 0)) :
    Tendsto (finiteClockReparam hclock γ)
      (𝓝[<] L) (𝓝 0) := by
  exact hγlim.comp
    (FinitePositiveIntegralClock.inverse_tendsto_atTop hclock)

omit [ProperSpace E] in
/-- The endpoint-filled finite-clock orbit is continuous on its closed
clock interval. -/
theorem finiteClockOrbit_continuousOn
    {a : E → ℝ} {F : E → E} {x₀ : E} {γ : ℝ → E} {L : ℝ}
    (hγ : IsForwardTrajectory (timeScaledField a F) γ x₀)
    (hclock :
      FinitePositiveIntegralClock (stateClockWeight a γ) L)
    (hγlim : Tendsto γ atTop (𝓝 0)) :
    ContinuousOn (finiteClockOrbit hclock γ) (Icc 0 L) := by
  exact continuousOn_Icc_extendFrom_Ioo
    (finiteClockReparam_continuousOn hγ hclock)
    (finiteClockReparam_tendsto_zero hγ hclock)
    (finiteClockReparam_tendsto_limit hclock hγlim)

omit [ProperSpace E] in
/-- In the open interval, endpoint filling does not change the
inverse-clock reparametrization. -/
theorem finiteClockOrbit_eq_reparam
    {a : E → ℝ} {F : E → E} {x₀ : E} {γ : ℝ → E} {L : ℝ}
    (hγ : IsForwardTrajectory (timeScaledField a F) γ x₀)
    (hclock :
      FinitePositiveIntegralClock (stateClockWeight a γ) L)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) L) :
    finiteClockOrbit hclock γ s =
      finiteClockReparam hclock γ s := by
  exact extendFrom_extends
    (finiteClockReparam_continuousOn hγ hclock) s hs

omit [ProperSpace E] in
/-- The filled orbit starts at the original initial state. -/
theorem finiteClockOrbit_zero
    {a : E → ℝ} {F : E → E} {x₀ : E} {γ : ℝ → E} {L : ℝ}
    (hγ : IsForwardTrajectory (timeScaledField a F) γ x₀)
    (hclock :
      FinitePositiveIntegralClock (stateClockWeight a γ) L) :
    finiteClockOrbit hclock γ 0 = x₀ := by
  rw [finiteClockOrbit]
  apply extendFrom_eq
  · rw [closure_Ioo
      (ne_of_lt (FinitePositiveIntegralClock.limit_pos hclock))]
    exact
      ⟨le_rfl,
        (FinitePositiveIntegralClock.limit_pos hclock).le⟩
  · rw [nhdsWithin_Ioo_eq_nhdsGT
      (FinitePositiveIntegralClock.limit_pos hclock)]
    exact finiteClockReparam_tendsto_zero hγ hclock

omit [NormedSpace ℝ E] [ProperSpace E] in
/-- At the putative finite right endpoint, the filled orbit has reached
the limiting equilibrium. -/
theorem finiteClockOrbit_limit
    {w : ℝ → ℝ} {γ : ℝ → E} {L : ℝ}
    (hclock : FinitePositiveIntegralClock w L)
    (hγlim : Tendsto γ atTop (𝓝 0)) :
    finiteClockOrbit hclock γ L = 0 := by
  rw [finiteClockOrbit]
  apply extendFrom_eq
  · rw [closure_Ioo
      (ne_of_lt (FinitePositiveIntegralClock.limit_pos hclock))]
    exact
      ⟨(FinitePositiveIntegralClock.limit_pos hclock).le,
        le_rfl⟩
  · rw [nhdsWithin_Ioo_eq_nhdsLT
      (FinitePositiveIntegralClock.limit_pos hclock)]
    exact finiteClockReparam_tendsto_limit hclock hγlim

omit [ProperSpace E] in
/-- At every interior clock time, the endpoint-filled orbit solves the
original ODE. -/
theorem finiteClockOrbit_hasDerivAt
    {a : E → ℝ} {F : E → E} {x₀ : E} {γ : ℝ → E} {L : ℝ}
    (hγ : IsForwardTrajectory (timeScaledField a F) γ x₀)
    (hclock :
      FinitePositiveIntegralClock (stateClockWeight a γ) L)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) L) :
    HasDerivAt (finiteClockOrbit hclock γ)
      (F (finiteClockOrbit hclock γ s)) s := by
  have hraw :=
    hγ.finite_reparametrize_from_timeScaledField_hasDerivAt
      hclock hs
  have heq :
      finiteClockOrbit hclock γ =ᶠ[𝓝 s]
        finiteClockReparam hclock γ := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with u hu
    exact finiteClockOrbit_eq_reparam hγ hclock hu
  have hderiv := hraw.congr_of_eventuallyEq heq
  simpa only [finiteClockOrbit_eq_reparam hγ hclock hs] using hderiv

omit [ProperSpace E] in
/-- The filled orbit also solves the original ODE at the right endpoint,
with a left derivative.  This is the analytic continuation step: interior
derivatives are `F` evaluated on the orbit, and both the orbit and those
derivatives have limits at the endpoint. -/
theorem finiteClockOrbit_hasDerivWithinAt_limit
    {a : E → ℝ} {F : E → E} {x₀ : E} {γ : ℝ → E} {L : ℝ}
    (hF : Continuous F)
    (hγ : IsForwardTrajectory (timeScaledField a F) γ x₀)
    (hclock :
      FinitePositiveIntegralClock (stateClockWeight a γ) L)
    (hγlim : Tendsto γ atTop (𝓝 0)) :
    HasDerivWithinAt (finiteClockOrbit hclock γ)
      (F (finiteClockOrbit hclock γ L)) (Iic L) L := by
  let ζ : ℝ → E := finiteClockOrbit hclock γ
  have hL : 0 < L :=
    FinitePositiveIntegralClock.limit_pos hclock
  have hdiff : DifferentiableOn ℝ ζ (Ioo 0 L) := by
    intro s hs
    exact
      (finiteClockOrbit_hasDerivAt hγ hclock hs).differentiableAt
        |>.differentiableWithinAt
  have hcontWithin :
      ContinuousWithinAt ζ (Ioo 0 L) L := by
    exact
      (finiteClockOrbit_continuousOn hγ hclock hγlim L
        ⟨hL.le, le_rfl⟩).mono Ioo_subset_Icc_self
  have hζlim : Tendsto ζ (𝓝[<] L) (𝓝 0) := by
    have hrawlim :=
      finiteClockReparam_tendsto_limit hclock hγlim
    apply hrawlim.congr'
    filter_upwards
      [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hL)] with s hsL hs0
    exact (finiteClockOrbit_eq_reparam hγ hclock ⟨hs0, hsL⟩).symm
  have hderivEq :
      (fun s ↦ deriv ζ s) =ᶠ[𝓝[<] L]
        fun s ↦ F (ζ s) := by
    filter_upwards
      [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hL)] with s hsL hs0
    exact (finiteClockOrbit_hasDerivAt hγ hclock
      ⟨hs0, hsL⟩).deriv
  have hderivLim :
      Tendsto (fun s ↦ deriv ζ s) (𝓝[<] L) (𝓝 (F 0)) := by
    exact (hF.continuousAt.tendsto.comp hζlim).congr' hderivEq.symm
  have hend :=
    hasDerivWithinAt_Iic_of_tendsto_deriv
      hdiff hcontWithin (Ioo_mem_nhdsLT hL) hderivLim
  simpa only [ζ, finiteClockOrbit_limit hclock hγlim] using hend

/-- A nonzero state-scaled trajectory converging to the origin cannot have
a direct clock with a finite positive-time endpoint.  Otherwise its
inverse-clock orbit would solve the original `C¹` ODE on a compact interval
and reach the equilibrium at the right endpoint; backward uniqueness would
force the entire orbit, including its nonzero initial state, to be zero. -/
theorem no_finite_stateClock_limit
    {a : E → ℝ} {F : E → E} {x₀ : E} {γ : ℝ → E} {L : ℝ}
    (hF : ContDiff ℝ 1 F) (hF0 : F 0 = 0)
    (hx₀ : x₀ ≠ 0)
    (hγ : IsForwardTrajectory (timeScaledField a F) γ x₀)
    (hγlim : Tendsto γ atTop (𝓝 0))
    (hclock :
      FinitePositiveIntegralClock (stateClockWeight a γ) L) :
    False := by
  let ζ : ℝ → E := finiteClockOrbit hclock γ
  let η : ℝ → E := fun _ ↦ 0
  have hL : 0 < L :=
    FinitePositiveIntegralClock.limit_pos hclock
  have heqOn :=
    ode_solution_unique_Icc_left_of_contDiff
      (F := F) (γ := ζ) (η := η) (a := 0) (b := L) hF
      (finiteClockOrbit_continuousOn hγ hclock hγlim)
      (by
        intro s hs
        by_cases hsL : s = L
        · subst s
          exact finiteClockOrbit_hasDerivWithinAt_limit
            hF.continuous hγ hclock hγlim
        · exact
            (finiteClockOrbit_hasDerivAt hγ hclock
              ⟨hs.1, lt_of_le_of_ne hs.2 hsL⟩).hasDerivWithinAt)
      continuous_const.continuousOn
      (by
        intro s _hs
        show HasDerivWithinAt η (F (η s)) (Iic s) s
        simpa only [η, hF0] using
          (hasDerivAt_const (x := s) (c := (0 : E))).hasDerivWithinAt)
      (by
        show ζ L = η L
        simpa only [ζ, η] using finiteClockOrbit_limit hclock hγlim)
  have hzero : ζ 0 = 0 :=
    heqOn ⟨le_rfl, hL.le⟩
  apply hx₀
  rw [← finiteClockOrbit_zero hγ hclock]
  exact hzero

/-- For a nonzero state-scaled trajectory converging to the origin, the
direct clock has unbounded positive-time range.  Monotonicity gives only
two possibilities: divergence to `+∞`, or convergence to a finite limit.
The preceding backward-uniqueness argument excludes the latter. -/
theorem stateClockWeight_tendsto_atTop
    {a : E → ℝ} {F : E → E}
    (ha : ContDiff ℝ 1 a) (ha_nonneg : ∀ x, 0 ≤ a x)
    (ha_zero : ∀ x, a x = 0 ↔ x = 0)
    (hF : ContDiff ℝ 1 F) (hF0 : F 0 = 0)
    {x₀ : E} (hx₀ : x₀ ≠ 0)
    {γ : ℝ → E}
    (hγ : IsForwardTrajectory (timeScaledField a F) γ x₀)
    (hγlim : Tendsto γ atTop (𝓝 0)) :
    Tendsto (integralClock (stateClockWeight a γ))
      atTop atTop := by
  obtain ⟨hcontinuous, hpositive⟩ :=
    stateClockWeight_continuous_positive
      ha ha_nonneg ha_zero hF hx₀ hγ
  have hmono :
      Monotone (integralClock (stateClockWeight a γ)) :=
    (integralClock_strictMono hcontinuous hpositive).monotone
  rcases tendsto_atTop_of_monotone hmono with htop | ⟨L, hfinite⟩
  · exact htop
  · exfalso
    have hapos : 0 < a x₀ := by
      exact lt_of_le_of_ne (ha_nonneg x₀)
        (Ne.symm ((ha_zero x₀).not.mpr hx₀))
    exact no_finite_stateClock_limit hF hF0 hx₀ hγ hγlim
      { continuous := hcontinuous
        positive := hpositive
        tendsto_atTop := hfinite
        tendsto_atBot :=
          stateClockWeight_tendsto_atBot hγ.1 hapos }

/-- The direct integral clock along a nonzero attractive state-scaled
trajectory is a global positive clock. -/
theorem stateClock
    {a : E → ℝ} {F : E → E}
    (ha : ContDiff ℝ 1 a) (ha_nonneg : ∀ x, 0 ≤ a x)
    (ha_zero : ∀ x, a x = 0 ↔ x = 0)
    (hF : ContDiff ℝ 1 F) (hF0 : F 0 = 0)
    {x₀ : E} (hx₀ : x₀ ≠ 0)
    {γ : ℝ → E}
    (hγ : IsForwardTrajectory (timeScaledField a F) γ x₀)
    (hγlim : Tendsto γ atTop (𝓝 0)) :
    PositiveIntegralClock (stateClockWeight a γ) := by
  obtain ⟨hcontinuous, hpositive⟩ :=
    stateClockWeight_continuous_positive
      ha ha_nonneg ha_zero hF hx₀ hγ
  have hapos : 0 < a x₀ := by
    exact lt_of_le_of_ne (ha_nonneg x₀)
      (Ne.symm ((ha_zero x₀).not.mpr hx₀))
  exact
    { continuous := hcontinuous
      positive := hpositive
      tendsto_atTop :=
        stateClockWeight_tendsto_atTop
          ha ha_nonneg ha_zero hF hF0 hx₀ hγ hγlim
      tendsto_atBot :=
        stateClockWeight_tendsto_atBot hγ.1 hapos }

/-! ## GAS invariance under positive state-dependent time change -/

/-- Multiplying a `C¹` vector field by a nonnegative `C¹` scalar which
vanishes exactly at the GAS equilibrium preserves global asymptotic
stability.

The proof uses a canonical trajectory obtained from the original GAS
system.  Its reciprocal clock is automatically global because the scalar
speed tends to zero along an attractive trajectory.  Compact-interval
uniqueness then identifies every trajectory of the scaled field with this
canonical reparametrization. -/
theorem GloballyAsymptoticallyStable.timeScaledField
    {a : E → ℝ} {F : E → E}
    (hgas : GloballyAsymptoticallyStable F 0)
    (ha : ContDiff ℝ 1 a)
    (ha_nonneg : ∀ x, 0 ≤ a x)
    (ha_zero : ∀ x, a x = 0 ↔ x = 0)
    (hF : ContDiff ℝ 1 F) :
    GloballyAsymptoticallyStable (HGAS.timeScaledField a F) 0 := by
  have hscaledC1 : ContDiff ℝ 1 (HGAS.timeScaledField a F) :=
    timeScaledField_contDiff ha hF
  have hscaled0 : HGAS.timeScaledField a F 0 = 0 := by
    simp [HGAS.timeScaledField, (ha_zero 0).2 rfl]
  refine
    { equilibrium := hscaled0
      forwardComplete := ?_
      stable := ?_
      attractive := ?_ }
  · intro x₀
    by_cases hx₀ : x₀ = 0
    · subst x₀
      exact
        ⟨fun _ ↦ 0,
          IsForwardTrajectory.const_of_equilibrium hscaled0⟩
    · obtain ⟨γ, hγ⟩ := hgas.forwardComplete x₀
      have hγlim : Tendsto γ atTop (𝓝 0) :=
        hgas.attractive.tendsto_atTop hγ
      let hclock :
          PositiveIntegralClock
            (reciprocalStateClockWeight a γ) :=
        reciprocalStateClock ha.continuous ha_nonneg ha_zero
          hF hgas.equilibrium hx₀ hγ hγlim
      exact
        ⟨fun t ↦ γ
            ((PositiveIntegralClock.orderIso hclock).symm t),
          hγ.reparametrize_to_timeScaledField hclock⟩
  · intro ε hε
    obtain ⟨δ, hδ, hstay⟩ := hgas.stable ε hε
    refine ⟨δ, hδ, ?_⟩
    intro x₀ hxclose η hη t ht
    by_cases hx₀ : x₀ = 0
    · subst x₀
      have hconst :
          IsForwardTrajectory (HGAS.timeScaledField a F)
            (fun _ ↦ (0 : E)) 0 :=
        IsForwardTrajectory.const_of_equilibrium hscaled0
      have heq : η t = 0 :=
        hη.eqOn_Ici_of_contDiff hscaledC1 hconst ht
      rw [heq, dist_self]
      exact hε
    · obtain ⟨γ, hγ⟩ := hgas.forwardComplete x₀
      have hγlim : Tendsto γ atTop (𝓝 0) :=
        hgas.attractive.tendsto_atTop hγ
      let hclock :
          PositiveIntegralClock
            (reciprocalStateClockWeight a γ) :=
        reciprocalStateClock ha.continuous ha_nonneg ha_zero
          hF hgas.equilibrium hx₀ hγ hγlim
      let θ : ℝ → E :=
        fun s ↦ γ ((PositiveIntegralClock.orderIso hclock).symm s)
      have hθ :
          IsForwardTrajectory (HGAS.timeScaledField a F) θ x₀ :=
        hγ.reparametrize_to_timeScaledField hclock
      have heq : η t = θ t :=
        hη.eqOn_Ici_of_contDiff hscaledC1 hθ ht
      have hBnonneg :
          0 ≤ (PositiveIntegralClock.orderIso hclock).symm t :=
        PositiveIntegralClock.symm_nonneg hclock ht
      rw [heq]
      exact hstay x₀ hxclose γ hγ
        ((PositiveIntegralClock.orderIso hclock).symm t) hBnonneg
  · intro x₀ η hη ε hε
    by_cases hx₀ : x₀ = 0
    · subst x₀
      have hconst :
          IsForwardTrajectory (HGAS.timeScaledField a F)
            (fun _ ↦ (0 : E)) 0 :=
        IsForwardTrajectory.const_of_equilibrium hscaled0
      refine ⟨0, le_rfl, ?_⟩
      intro t ht
      have heq : η t = 0 :=
        hη.eqOn_Ici_of_contDiff hscaledC1 hconst ht
      rw [heq, dist_self]
      exact hε
    · obtain ⟨γ, hγ⟩ := hgas.forwardComplete x₀
      have hγlim : Tendsto γ atTop (𝓝 0) :=
        hgas.attractive.tendsto_atTop hγ
      let hclock :
          PositiveIntegralClock
            (reciprocalStateClockWeight a γ) :=
        reciprocalStateClock ha.continuous ha_nonneg ha_zero
          hF hgas.equilibrium hx₀ hγ hγlim
      let θ : ℝ → E :=
        fun s ↦ γ ((PositiveIntegralClock.orderIso hclock).symm s)
      have hθ :
          IsForwardTrajectory (HGAS.timeScaledField a F) θ x₀ :=
        hγ.reparametrize_to_timeScaledField hclock
      obtain ⟨Tbase, hTbase, hafter⟩ :=
        hgas.attractive x₀ γ hγ ε hε
      have hevent :
          ∀ᶠ t in atTop,
            Tbase ≤ (PositiveIntegralClock.orderIso hclock).symm t :=
        PositiveIntegralClock.symm_tendsto_atTop hclock
          (eventually_ge_atTop Tbase)
      obtain ⟨T, hT⟩ := eventually_atTop.1 hevent
      refine ⟨max T 0, le_max_right T 0, ?_⟩
      intro t ht
      have hTt : T ≤ t :=
        le_trans (le_max_left T 0) ht
      have heq : η t = θ t :=
        hη.eqOn_Ici_of_contDiff hscaledC1 hθ
          (le_trans (le_max_right T 0) ht)
      rw [heq]
      exact hafter
        ((PositiveIntegralClock.orderIso hclock).symm t)
        (hT t hTt)

/-- Conversely, GAS of the state-scaled field implies GAS of the original
field, provided the original field has the same equilibrium.  The delicate
point is forward completeness: the direct clock might a priori cover only
a finite interval.  `stateClock` rules this out using attraction and
backward uniqueness. -/
theorem GloballyAsymptoticallyStable.of_timeScaledField
    {a : E → ℝ} {F : E → E}
    (hgas :
      GloballyAsymptoticallyStable (HGAS.timeScaledField a F) 0)
    (ha : ContDiff ℝ 1 a)
    (ha_nonneg : ∀ x, 0 ≤ a x)
    (ha_zero : ∀ x, a x = 0 ↔ x = 0)
    (hF : ContDiff ℝ 1 F) (hF0 : F 0 = 0) :
    GloballyAsymptoticallyStable F 0 := by
  have hscaledC1 : ContDiff ℝ 1 (HGAS.timeScaledField a F) :=
    timeScaledField_contDiff ha hF
  refine
    { equilibrium := hF0
      forwardComplete := ?_
      stable := ?_
      attractive := ?_ }
  · intro x₀
    by_cases hx₀ : x₀ = 0
    · subst x₀
      exact
        ⟨fun _ ↦ 0,
          IsForwardTrajectory.const_of_equilibrium hF0⟩
    · obtain ⟨γ, hγ⟩ := hgas.forwardComplete x₀
      have hγlim : Tendsto γ atTop (𝓝 0) :=
        hgas.attractive.tendsto_atTop hγ
      let hclock :
          PositiveIntegralClock (stateClockWeight a γ) :=
        stateClock ha ha_nonneg ha_zero hF hF0
          hx₀ hγ hγlim
      exact
        ⟨fun t ↦ γ
            ((PositiveIntegralClock.orderIso hclock).symm t),
          hγ.reparametrize_from_timeScaledField hclock⟩
  · intro ε hε
    obtain ⟨δ, hδ, hstay⟩ := hgas.stable ε hε
    refine ⟨δ, hδ, ?_⟩
    intro x₀ hxclose γ hγ t ht
    by_cases hx₀ : x₀ = 0
    · subst x₀
      have hconst :
          IsForwardTrajectory F (fun _ ↦ (0 : E)) 0 :=
        IsForwardTrajectory.const_of_equilibrium hF0
      have heq : γ t = 0 :=
        hγ.eqOn_Ici_of_contDiff hF hconst ht
      rw [heq, dist_self]
      exact hε
    · obtain ⟨η, hη⟩ := hgas.forwardComplete x₀
      have hηlim : Tendsto η atTop (𝓝 0) :=
        hgas.attractive.tendsto_atTop hη
      let hclock :
          PositiveIntegralClock (stateClockWeight a η) :=
        stateClock ha ha_nonneg ha_zero hF hF0
          hx₀ hη hηlim
      let ξ : ℝ → E :=
        fun s ↦ η ((PositiveIntegralClock.orderIso hclock).symm s)
      have hξ : IsForwardTrajectory F ξ x₀ :=
        hη.reparametrize_from_timeScaledField hclock
      have heq : γ t = ξ t :=
        hγ.eqOn_Ici_of_contDiff hF hξ ht
      have hBnonneg :
          0 ≤ (PositiveIntegralClock.orderIso hclock).symm t :=
        PositiveIntegralClock.symm_nonneg hclock ht
      rw [heq]
      exact hstay x₀ hxclose η hη
        ((PositiveIntegralClock.orderIso hclock).symm t) hBnonneg
  · intro x₀ γ hγ ε hε
    by_cases hx₀ : x₀ = 0
    · subst x₀
      have hconst :
          IsForwardTrajectory F (fun _ ↦ (0 : E)) 0 :=
        IsForwardTrajectory.const_of_equilibrium hF0
      refine ⟨0, le_rfl, ?_⟩
      intro t ht
      have heq : γ t = 0 :=
        hγ.eqOn_Ici_of_contDiff hF hconst ht
      rw [heq, dist_self]
      exact hε
    · obtain ⟨η, hη⟩ := hgas.forwardComplete x₀
      have hηlim : Tendsto η atTop (𝓝 0) :=
        hgas.attractive.tendsto_atTop hη
      let hclock :
          PositiveIntegralClock (stateClockWeight a η) :=
        stateClock ha ha_nonneg ha_zero hF hF0
          hx₀ hη hηlim
      let ξ : ℝ → E :=
        fun s ↦ η ((PositiveIntegralClock.orderIso hclock).symm s)
      have hξ : IsForwardTrajectory F ξ x₀ :=
        hη.reparametrize_from_timeScaledField hclock
      obtain ⟨Tscaled, hTscaled, hafter⟩ :=
        hgas.attractive x₀ η hη ε hε
      have hevent :
          ∀ᶠ t in atTop,
            Tscaled ≤ (PositiveIntegralClock.orderIso hclock).symm t :=
        PositiveIntegralClock.symm_tendsto_atTop hclock
          (eventually_ge_atTop Tscaled)
      obtain ⟨T, hT⟩ := eventually_atTop.1 hevent
      refine ⟨max T 0, le_max_right T 0, ?_⟩
      intro t ht
      have hTt : T ≤ t :=
        le_trans (le_max_left T 0) ht
      have heq : γ t = ξ t :=
        hγ.eqOn_Ici_of_contDiff hF hξ
          (le_trans (le_max_right T 0) ht)
      rw [heq]
      exact hafter
        ((PositiveIntegralClock.orderIso hclock).symm t)
        (hT t hTt)

/-- Positive state-dependent time rescaling preserves and reflects GAS.
The scalar may vanish at the equilibrium, but nowhere else. -/
theorem globallyAsymptoticallyStable_timeScaledField_iff
    {a : E → ℝ} {F : E → E}
    (ha : ContDiff ℝ 1 a)
    (ha_nonneg : ∀ x, 0 ≤ a x)
    (ha_zero : ∀ x, a x = 0 ↔ x = 0)
    (hF : ContDiff ℝ 1 F) (hF0 : F 0 = 0) :
    GloballyAsymptoticallyStable (HGAS.timeScaledField a F) 0 ↔
      GloballyAsymptoticallyStable F 0 := by
  constructor
  · intro hgas
    exact hgas.of_timeScaledField
      ha ha_nonneg ha_zero hF hF0
  · intro hgas
    exact hgas.timeScaledField
      ha ha_nonneg ha_zero hF

end ProperTimeChange

end

end HGAS
