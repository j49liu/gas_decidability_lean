import HGAS.Dynamics.PositiveMeanTimeReparametrization
import HGAS.Dynamics.FlowPointwiseErgodic
import HGAS.Dynamics.PositiveIntegralClockUniformLower

/-!
# Full real horizons for bounded orbit averages

Integer-horizon convergence of a bounded continuous observable implies
convergence at all real horizons. A positive clock then transfers full
speed-weighted means to ordinary time by an exact ratio identity.

These are the horizon-normalization steps in Section 9,
Lemma `lem:selectedorbit`.
-/

noncomputable section

namespace Stability.Selection

open HGAS HGAS.Dynamics Filter MeasureTheory Topology
open scoped BoundedContinuousFunction

variable {X : Type*} [TopologicalSpace X]

/-- The discrepancy between a real horizon and the next integer horizon
is controlled by the observable's uniform bound. -/
theorem dist_realMean_integerMean_le
    (ϕ : Flow ℝ X) (f : X →ᵇ ℝ) {T : ℝ} (hT : 1 ≤ T) (x : X) :
    dist (T⁻¹ * orbitIntegral ϕ f T x)
      (integerOrbitAverageObservable ϕ f (⌊T⌋₊ + 1) x) ≤ 2 * ‖f‖ / T := by
  let N : ℝ := (⌊T⌋₊ : ℝ) + 1
  let I := orbitIntegral ϕ f T x
  let J := orbitIntegral ϕ f (N - T) (ϕ T x)
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hTltN : T < N := Nat.lt_floor_add_one T
  have hNpos : 0 < N := hTpos.trans hTltN
  have hdelta : 0 ≤ N - T := sub_nonneg.mpr hTltN.le
  have hdelta_le : N - T ≤ 1 := by
    have hfloor := Nat.floor_le hTpos.le
    dsimp [N]
    linarith
  have hI : |I| ≤ ‖f‖ * T := by
    simpa only [I, Real.norm_eq_abs, abs_of_pos hTpos] using norm_orbitIntegral_le ϕ f T x
  have hJ : |J| ≤ ‖f‖ * (N - T) := by
    simpa only [J, Real.norm_eq_abs, abs_of_nonneg hdelta] using
      norm_orbitIntegral_le ϕ f (N - T) (ϕ T x)
  have hdecomp : orbitIntegral ϕ f N x = I + J := by
    simpa only [add_sub_cancel, I, J] using orbitIntegral_add ϕ f T (N - T) x
  have heq : T⁻¹ * orbitIntegral ϕ f T x -
      integerOrbitAverageObservable ϕ f (⌊T⌋₊ + 1) x =
      ((N - T) / (T * N)) * I - (1 / N) * J := by
    rw [integerOrbitAverageObservable_apply]
    simp only [Nat.cast_add, Nat.cast_one]
    change T⁻¹ * I - N⁻¹ * orbitIntegral ϕ f N x = _
    rw [hdecomp]
    field_simp
    ring
  have hcoeff : 0 ≤ (N - T) / (T * N) := by positivity
  have hinv : 0 ≤ (1 / N : ℝ) := by positivity
  have hfrac : (N - T) / N ≤ 1 / T := by
    rw [div_le_div_iff₀ hNpos hTpos]
    calc
      (N - T) * T ≤ 1 * T := mul_le_mul_of_nonneg_right hdelta_le hTpos.le
      _ ≤ 1 * N := by linarith
  rw [Real.dist_eq, heq]
  calc
    _ ≤ |((N - T) / (T * N)) * I| + |(1 / N) * J| := abs_sub _ _
    _ = ((N - T) / (T * N)) * |I| + (1 / N) * |J| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hcoeff, abs_of_nonneg hinv]
    _ ≤ ((N - T) / (T * N)) * (‖f‖ * T) + (1 / N) * (‖f‖ * (N - T)) :=
      add_le_add (mul_le_mul_of_nonneg_left hI hcoeff) (mul_le_mul_of_nonneg_left hJ hinv)
    _ = 2 * ‖f‖ * ((N - T) / N) := by field_simp; ring
    _ ≤ 2 * ‖f‖ * (1 / T) := mul_le_mul_of_nonneg_left hfrac (by positivity)
    _ = 2 * ‖f‖ / T := by ring

/-- Positive-integer convergence of a bounded continuous orbit observable
implies the full real-horizon limit. -/
theorem realMean_tendsto_of_integerMean
    (ϕ : Flow ℝ X) (f : X →ᵇ ℝ) (x : X) {c : ℝ}
    (hmean : Tendsto (fun n : ℕ ↦ integerOrbitAverageObservable ϕ f (n + 1) x)
      atTop (𝓝 c)) :
    Tendsto (fun T : ℝ ↦ T⁻¹ * orbitIntegral ϕ f T x) atTop (𝓝 c) := by
  have hinteger : Tendsto (fun T : ℝ ↦
      integerOrbitAverageObservable ϕ f (⌊T⌋₊ + 1) x) atTop (𝓝 c) :=
    hmean.comp tendsto_nat_floor_atTop
  have herror : Tendsto (fun T : ℝ ↦ 2 * ‖f‖ / T) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.const_mul (2 * ‖f‖))
  have hdist : Tendsto (fun T : ℝ ↦ dist (T⁻¹ * orbitIntegral ϕ f T x)
      (integerOrbitAverageObservable ϕ f (⌊T⌋₊ + 1) x)) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg)
      (Filter.eventually_atTop.2 ⟨1, fun T hT ↦ dist_realMean_integerMean_le ϕ f hT x⟩) herror
  exact tendsto_of_tendsto_of_dist hinteger (by simpa only [dist_comm] using hdist)

/-- Full speed and weighted-observable means give a full ordinary-time
mean. Only positivity and globality of the actual clock are required. -/
theorem inverseClock_fullMean_tendsto_ratio
    {w f : ℝ → ℝ} (hclock : PositiveIntegralClock w) (hf : Continuous f)
    {c d : ℝ} (hc : c ≠ 0)
    (hspeed : Tendsto (fun T : ℝ ↦ T⁻¹ * integralClock w T) atTop (𝓝 c))
    (hweighted : Tendsto (fun T : ℝ ↦ T⁻¹ * ∫ t in (0 : ℝ)..T, f t * w t)
      atTop (𝓝 d)) :
    Tendsto (fun H : ℝ ↦ H⁻¹ * ∫ t in (0 : ℝ)..H, f (hclock.orderIso.symm t))
      atTop (𝓝 (d / c)) := by
  have hratio := (hweighted.div hspeed hc).comp hclock.symm_tendsto_atTop
  apply hratio.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
  have hT : hclock.orderIso.symm H ≠ 0 := by
    intro hzero
    have h := congrArg hclock.orderIso hzero
    exact hH.ne' (by simpa only [OrderIso.apply_symm_apply,
      PositiveIntegralClock.orderIso_zero] using h)
  have hid := inverseClockAverage_eq_ratio hclock hf hT
  have hclockH : integralClock w (hclock.orderIso.symm H) = H :=
    hclock.orderIso.apply_symm_apply H
  simpa only [hclockH, Function.comp_apply, Pi.div_apply] using hid.symm

/-- Positive means for the forward and reflected speed make the unmodified
clock global. This concerns speed genericity, not reverse recurrence. -/
theorem positiveIntegralClock_of_twoSidedMean
    {w : ℝ → ℝ} (hw : Continuous w) (hwpos : ∀ t, 0 < w t)
    {c : ℝ} (hc : 0 < c)
    (hforward : Tendsto (fun T : ℝ ↦ T⁻¹ * integralClock w T) atTop (𝓝 c))
    (hreverse : Tendsto (fun T : ℝ ↦ T⁻¹ * integralClock (fun t ↦ w (-t)) T)
      atTop (𝓝 c)) : PositiveIntegralClock w := by
  have htop := integralClock_tendsto_atTop_of_positive_integerMean hw hwpos hc
    (hforward.comp positiveIntegerHorizon_tendsto_atTop)
  have hrevTop := integralClock_tendsto_atTop_of_positive_integerMean
    (hw.comp continuous_neg) (fun t ↦ hwpos (-t)) hc
    (hreverse.comp positiveIntegerHorizon_tendsto_atTop)
  refine ⟨hw, hwpos, htop, ?_⟩
  have hbot := (tendsto_neg_atTop_atBot.comp hrevTop).comp tendsto_neg_atBot_atTop
  simpa only [Function.comp_def, integralClock_reflect, neg_neg] using hbot

/-- For a continuous integrand, an eventual bound on averages extends to
all horizons `H ≥ 1`; the omitted finite interval is compact. -/
theorem forwardMean_bounded_on_ge_one
    {f : ℝ → ℝ} (hf : Continuous f) (B : ℝ)
    (hbound : ∀ᶠ H : ℝ in atTop, H⁻¹ * (∫ t in (0 : ℝ)..H, f t) ≤ B) :
    ∃ C : ℝ, ∀ H : ℝ, 1 ≤ H → H⁻¹ * (∫ t in (0 : ℝ)..H, f t) ≤ C := by
  obtain ⟨A, hA⟩ := Filter.eventually_atTop.mp hbound
  have hint : Continuous (fun H : ℝ ↦ ∫ t in (0 : ℝ)..H, f t) :=
    continuous_iff_continuousAt.mpr fun H ↦ (integralClock_hasDerivAt hf H).continuousAt
  have hc : ContinuousOn (fun H : ℝ ↦ H⁻¹ * ∫ t in (0 : ℝ)..H, f t) (Set.Icc 1 A) :=
    (continuousOn_id.inv₀ (fun H hH ↦ (zero_lt_one.trans_le hH.1).ne')).mul hint.continuousOn
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hc
  refine ⟨max C B, fun H hH ↦ ?_⟩
  by_cases hHA : H ≤ A
  · exact (hC ⟨H, ⟨hH, hHA⟩, rfl⟩).trans (le_max_left _ _)
  · exact (hA H (le_of_not_ge hHA)).trans (le_max_right _ _)

end Stability.Selection
