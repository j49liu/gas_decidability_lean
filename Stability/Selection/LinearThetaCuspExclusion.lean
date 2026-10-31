import Stability.Selection.LinearCuspDivergence
import HGAS.Modular.RealFrameHorocycleUnaryAmplitude
import HGAS.Modular.GammaTwoScaledPointwiseEquidistribution
import HGAS.Modular.ExplicitGammaTwoHaarCompactTests
import Mathlib.Data.Real.Sqrt

/-!
# Ordinary-time exclusion of nonperiodic horocycles by linear theta growth

The revised manuscript's Proposition `prop:modselect`, Step 2, excludes
nonclosed horocycles using bounded ordinary-time growth averages. We take
the square root of the existing continuous `H₄²` observable, obtaining a
continuous quotient observable equal to the linear theta amplitude.

The critical first-moment cusp theorem proves that this observable has
infinite Haar integral. The unconditional signed-speed pointwise horocycle
theorem then forces its forward averages to diverge on every nonperiodic
orbit. No source invariant probability, reverse recurrence, or
compactification clock is assumed.

This file proves the quotient-orbit exclusion. Applying it to a complete
ordinary-time modular trajectory still requires that trajectory's frame
reconstruction and the comparison with its stated growth bound.
-/

noncomputable section

namespace Stability.Selection

open Filter MeasureTheory Set Topology HGAS.Modular HGAS.Dynamics
open scoped ENNReal NNReal CompactlySupported

/-- A continuous linear theta amplitude, descended through the existing
square observable. The scale records the absolute horocycle speed. -/
def gammaTwoLinearThetaObservable (a : ℝ≥0) : C(GammaTwoFrameQuotient, ℝ) :=
  ⟨fun q ↦ Real.sqrt (gammaTwoScaledH4SquareNormPower a 1 q),
    Real.continuous_sqrt.comp (gammaTwoScaledH4SquareNormPower a 1).continuous⟩

theorem gammaTwoLinearThetaObservable_nonneg (a : ℝ≥0) (q : GammaTwoFrameQuotient) :
    0 ≤ gammaTwoLinearThetaObservable a q := Real.sqrt_nonneg _

/-- On a representative, the observable is exactly the linear amplitude,
not the square used in the published compactification argument. -/
theorem gammaTwoLinearThetaObservable_mk (a : ℝ≥0) (g : RealModularFrame) :
    gammaTwoLinearThetaObservable a (gammaTwoFrameQuotientMk g) =
      (a : ℝ) * realModularFrameHeight g * ‖H₄ (realModularFrameBasePoint g)‖ := by
  change Real.sqrt (gammaTwoScaledH4SquareNormPower a 1 (gammaTwoFrameQuotientMk g)) = _
  rw [gammaTwoScaledH4SquareNormPower_mk]
  norm_num only [mul_one, Real.sqrt_sq_eq_abs]
  apply abs_of_nonneg
  exact mul_nonneg (mul_nonneg a.coe_nonneg (realModularFrameBasePoint g).im_pos.le)
    (norm_nonneg _)

/-- Taking square roots of the existing square cusp bound gives a linear
height lower bound, with the same positive scale. -/
theorem exists_gammaTwoLinearThetaObservable_cuspLowerBound
    {Y : ℝ} (hY : 1 < Y) (a : ℝ≥0) (ha : a ≠ 0) :
    ∃ Ytail : ℝ, 0 < Ytail ∧ ∀ q : GammaTwoFrameQuotient,
      (gammaTwoScaledThetaCuspHalf a : ℝ≥0∞) *
        cuspTailHeightPower Ytail 1 (gammaTwoExplicitCuspHeight Y q) ≤
      ENNReal.ofReal (gammaTwoLinearThetaObservable a q) := by
  obtain ⟨Ytail, hYtail, hbound⟩ :=
    exists_gammaTwoScaledH4SquareNormPower_cuspLowerBound hY a ha 1
  refine ⟨Ytail, hYtail, ?_⟩
  intro q
  by_cases hq : Ytail ≤ gammaTwoExplicitCuspHeight Y q
  · have hheight : 0 ≤ gammaTwoExplicitCuspHeight Y q := (hYtail.trans_le hq).le
    have hmem : gammaTwoExplicitCuspHeight Y q ∈ Ici Ytail := hq
    have hR := gammaTwoScaledH4SquareNormPower_nonneg a 1 q
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hbound q)
    simp only [mul_one, cuspTailHeightPower, indicator_of_mem hmem, cuspHeightPower,
      max_eq_left hheight, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.coe_toReal, ENNReal.toReal_ofReal (sq_nonneg _),
      ENNReal.toReal_ofReal hR] at hreal
    have hsquare : ((gammaTwoScaledThetaCuspHalf a : ℝ) *
        gammaTwoExplicitCuspHeight Y q) ^ 2 ≤ gammaTwoScaledH4SquareNormPower a 1 q := by
      nlinarith [hreal]
    have hlinear := Real.le_sqrt_of_sq_le hsquare
    simp only [cuspTailHeightPower, indicator_of_mem hmem, cuspHeightPower,
      pow_one, max_eq_left hheight]
    rw [ENNReal.coe_nnreal_eq, ← ENNReal.ofReal_mul (gammaTwoScaledThetaCuspHalf a).coe_nonneg]
    exact ENNReal.ofReal_le_ofReal hlinear
  · have hnotmem : gammaTwoExplicitCuspHeight Y q ∉ Ici Ytail := hq
    simp only [cuspTailHeightPower, indicator_of_notMem hnotmem, mul_zero]
    exact bot_le

/-- The concrete linear theta observable has infinite Haar integral for
every nonzero scale. This includes the critical linear-growth case. -/
theorem gammaTwoLinearThetaObservable_lintegral_eq_top
    (a : ℝ≥0) (ha : a ≠ 0) :
    ∫⁻ q, ENNReal.ofReal (gammaTwoLinearThetaObservable a q)
      ∂(gammaTwoFrameHaarProbability : Measure GammaTwoFrameQuotient) = ∞ := by
  obtain ⟨Ytail, _, hbound⟩ :=
    exists_gammaTwoLinearThetaObservable_cuspLowerBound (Y := 2) (by norm_num) a ha
  obtain ⟨c, hc, hcusp⟩ :=
    exists_gammaTwoFrameHaarProbability_cuspMarginal_unconditional 2 (by norm_num)
  have hdiv := lintegral_scaled_cuspTailHeight_one_eq_top_of_cusp_marginal
    (gammaTwoFrameHaarProbability : Measure GammaTwoFrameQuotient)
    (gammaTwoExplicitCuspHeight 2) (measurable_gammaTwoExplicitCuspHeight (by norm_num))
    2 Ytail c hc hcusp (gammaTwoScaledThetaCuspHalf a)
    (gammaTwoScaledThetaCuspHalf_ne_zero ha)
  exact top_unique (hdiv ▸ lintegral_mono hbound)

/-- Nonperiodic horocycles have divergent forward linear-theta averages
at every nonzero signed speed. -/
theorem linearThetaAverage_tendsto_atTop_of_nonperiodic
    (a : ℝ≥0) (ha : a ≠ 0) {s : ℝ} (hs : s ≠ 0)
    (q : GammaTwoFrameQuotient) (hq : ¬ IsPeriodicHorocyclePoint 1 q) :
    Tendsto (fun n ↦ forwardContinuousOrbitAverage
      (scaledGammaTwoHorocycleFlow s) (gammaTwoLinearThetaObservable a) n q)
      atTop atTop := by
  apply forwardContinuousOrbitAverage_tendsto_atTop_of_generic
    (scaledGammaTwoHorocycleFlow s) gammaTwoFrameHaarProbability
    (gammaTwoLinearThetaObservable a)
  · intro B
    exact exists_compactlySupportedContinuous_minorant_integral_gt
      (gammaTwoFrameHaarProbability : Measure GammaTwoFrameQuotient)
      (gammaTwoLinearThetaObservable a) (gammaTwoLinearThetaObservable_nonneg a)
      (gammaTwoLinearThetaObservable_lintegral_eq_top a ha) B
  · exact gammaTwoPointwiseScaledHorocycleEquidistribution_unconditional
      gammaTwoFrameHaarProbability gammaTwoFrameHaarProbability_rightInvariant q hq hs

/-- An eventual upper bound on ordinary-time forward linear-theta
averages forces a periodic horocycle. This form tolerates the finite
initial interval introduced by a positive constant time rescaling. -/
theorem periodic_of_eventually_bounded_linearThetaAverage
    (a : ℝ≥0) (ha : a ≠ 0) {s : ℝ} (hs : s ≠ 0)
    (q : GammaTwoFrameQuotient) (B : ℝ)
    (hbound : ∀ᶠ n : ℕ in atTop, forwardContinuousOrbitAverage
      (scaledGammaTwoHorocycleFlow s) (gammaTwoLinearThetaObservable a) n q ≤ B) :
    IsPeriodicHorocyclePoint 1 q := by
  by_contra hq
  have hdiv := linearThetaAverage_tendsto_atTop_of_nonperiodic a ha hs q hq
  obtain ⟨n, hn, hnBound⟩ := ((hdiv.eventually (eventually_gt_atTop B)).and hbound).exists
  exact (not_lt_of_ge hnBound) hn

/-- A bound on all positive integer horizons is sufficient in particular. -/
theorem periodic_of_bounded_linearThetaAverage
    (a : ℝ≥0) (ha : a ≠ 0) {s : ℝ} (hs : s ≠ 0)
    (q : GammaTwoFrameQuotient) (B : ℝ)
    (hbound : ∀ n : ℕ, forwardContinuousOrbitAverage
      (scaledGammaTwoHorocycleFlow s) (gammaTwoLinearThetaObservable a) n q ≤ B) :
    IsPeriodicHorocyclePoint 1 q :=
  periodic_of_eventually_bounded_linearThetaAverage a ha hs q B
    (Eventually.of_forall hbound)

/-- Along a reconstructed normalized modular trajectory, the linear
quotient observable is exactly the norm of its `C` coordinate. -/
theorem gammaTwoLinearThetaObservable_eq_unaryC_norm
    {z : ℝ → UnaryModularState ℂ} {T : ℝ → UpperHalfPlane}
    (hz : IsScaledUnaryModularTrajectory modularIndependentVariableClock z)
    (hB : ∀ t, UnaryModularState.B (z t) ≠ 0)
    (hlambda : ∀ t, UnaryModularState.lambdaCoordinate (z t) = canonicalLambda (T t))
    (g : RealModularFrame) (s : ℝ)
    (hframe : ∀ t, T t = realModularFrameBasePoint (g * upperUnipotent (s * t)))
    (t : ℝ) :
    gammaTwoLinearThetaObservable (horocycleSpeedNorm s)
      (scaledGammaTwoHorocycleFlow s t (gammaTwoFrameQuotientMk g)) = ‖(z t).C‖ := by
  change Real.sqrt (gammaTwoScaledH4SquareNormPower (horocycleSpeedNorm s) 1
    (scaledGammaTwoHorocycleFlow s t (gammaTwoFrameQuotientMk g))) = _
  rw [gammaTwoScaledH4SquareNormPower_eq_unaryC_norm_pow hz hB hlambda g s hframe]
  norm_num only [mul_one, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

/-- Ordinary-time bounded coordinate moments of any real order `μ ≥ 1`
exclude nonperiodic reconstructed modular horocycles. The proof uses
`x ≤ 1 + x^μ` for `x ≥ 0`, so the critical case `μ = 1` is included.

The trajectory is already normalized to the modular independent-variable
clock, and its frame representation is an explicit hypothesis. Neither
reverse recurrence nor a selected invariant measure is required. -/
theorem periodic_of_bounded_unaryC_rpow_average
    {z : ℝ → UnaryModularState ℂ} {T : ℝ → UpperHalfPlane}
    (hz : IsScaledUnaryModularTrajectory modularIndependentVariableClock z)
    (hB : ∀ t, UnaryModularState.B (z t) ≠ 0)
    (hlambda : ∀ t, UnaryModularState.lambdaCoordinate (z t) = canonicalLambda (T t))
    (g : RealModularFrame) {s : ℝ} (hs : s ≠ 0)
    (hframe : ∀ t, T t = realModularFrameBasePoint (g * upperUnipotent (s * t)))
    {μ : ℝ} (hμ : 1 ≤ μ) (B : ℝ)
    (hbound : ∀ᶠ n : ℕ in atTop,
      (n + 1 : ℝ)⁻¹ * (∫ t in (0 : ℝ)..(n + 1 : ℝ), ‖(z t).C‖ ^ μ) ≤ B) :
    IsPeriodicHorocyclePoint 1 (gammaTwoFrameQuotientMk g) := by
  apply periodic_of_eventually_bounded_linearThetaAverage (horocycleSpeedNorm s)
    (horocycleSpeedNorm_ne_zero hs) hs (gammaTwoFrameQuotientMk g) (1 + B)
  filter_upwards [hbound] with n hnBound
  have hT : (0 : ℝ) < (n + 1 : ℝ) := by positivity
  have hcont := hz.continuous_C.norm
  have hpowcont : Continuous (fun t ↦ ‖(z t).C‖ ^ μ) :=
    (Real.continuous_rpow_const (zero_le_one.trans hμ)).comp hcont
  have hpoint : ∀ t, ‖(z t).C‖ ≤ 1 + ‖(z t).C‖ ^ μ := by
    intro t
    by_cases hsmall : ‖(z t).C‖ ≤ 1
    · exact hsmall.trans (le_add_of_nonneg_right (Real.rpow_nonneg (norm_nonneg _) _))
    · have hlarge := Real.self_le_rpow_of_one_le (le_of_not_ge hsmall) hμ
      linarith
  have hint : (∫ t in (0 : ℝ)..(n + 1 : ℝ), ‖(z t).C‖) ≤
      ∫ t in (0 : ℝ)..(n + 1 : ℝ), 1 + ‖(z t).C‖ ^ μ :=
    intervalIntegral.integral_mono_on hT.le (hcont.intervalIntegrable _ _)
      ((continuous_const.add hpowcont).intervalIntegrable _ _) (fun t _ ↦ hpoint t)
  rw [intervalIntegral.integral_add (continuous_const.intervalIntegrable _ _)
    (hpowcont.intervalIntegrable _ _), intervalIntegral.integral_const] at hint
  simp only [sub_zero, smul_eq_mul, mul_one] at hint
  have hnormalized := mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hT.le)
  rw [mul_add, inv_mul_cancel₀ hT.ne'] at hnormalized
  unfold forwardContinuousOrbitAverage
  simp_rw [gammaTwoLinearThetaObservable_eq_unaryC_norm hz hB hlambda g s hframe]
  exact hnormalized.trans (add_le_add le_rfl hnBound)

end Stability.Selection
