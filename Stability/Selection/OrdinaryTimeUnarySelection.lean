import Stability.Selection.OrdinaryTimeClosedFrame
import Stability.Selection.OrdinaryTimeGenericity
import HGAS.Modular.ClosedUnaryHorocycleChartExactAmplitude
import HGAS.Modular.FiniteClosedCuspCanonicalRootSeed
import HGAS.Modular.HorizontalThetaFirstMoment
import HGAS.Analysis.CesaroConstantTimeRescaling

/-!
# Ordinary-time selection of the canonical unary trajectory

The two raw coordinate means select the infinity cusp and unit speed.
The first harmonic then determines the height and phase. Together with
the closed-frame theorem, this gives the unary conclusion directly from
the normalized linked ODE, forward recurrence, residuals, full forward
means, and a bounded moment of real order at least one.

This is the unary part of Proposition `prop:modselect` in Section 8.
The subsequent Jacobi/Bloch selection and the normalization of a general
physical clock are not assertions of this module.
-/

noncomputable section

namespace Stability.Selection

open HGAS HGAS.Modular Filter MeasureTheory Topology

/-- The two forward coordinate means normalize a differentiable closed
chart and identify the complete unary state on a unit-speed line. -/
theorem exists_unitHorizontalCanonical_of_closedFrame_means
    {κZ : ℂ} {z : ℝ → LinkedJacobiState ℂ}
    (hz : IsScaledLinkedJacobiTrajectory κZ modularIndependentVariableClock z)
    {T : ℝ → UpperHalfPlane}
    (c : ClosedUnaryHorocycleChart (fun t ↦ (z t).unary) T)
    (hB : ∀ t, UnaryModularState.B (z t).unary ≠ 0)
    (hlambda : ∀ t, UnaryModularState.lambdaCoordinate (z t).unary = canonicalLambda (T t))
    (hdiff : ∀ t, ∃ v : ℂ, HasDerivAt (fun u : ℝ ↦ (T u : ℂ)) v t)
    (hresidual : ∀ t (r : LinkedJacobiResidualIndex), linkedJacobiResidual r (z t) = 0)
    {H : ℕ → ℝ} (hH : Tendsto H atTop atTop)
    (hY : Tendsto (fun n ↦ HGAS.Analysis.cesaroMeanAt
      (fun t ↦ (z t).unary.Y) (H n)) atTop (𝓝 1))
    (hp4 : Tendsto (fun n ↦ HGAS.Analysis.cesaroMeanAt
      (fun t ↦ (z t).jacobi.p4) (H n)) atTop (𝓝 1)) :
    ∃ x y : ℝ, ∃ hy : 0 < y,
      (∀ t, (z t).unary = canonicalUnaryTheta (horizontalLine x y 1 hy t)) ∧
      (∀ t, (z t).jacobi.p4 = theta₄ (horizontalLine x y 1 hy t) ^ 2) := by
  let x := c.horizontalization.cuspNormalized.upperLeft *
    c.horizontalization.cuspNormalized.upperRight
  let y := c.horizontalization.cuspNormalized.upperLeft ^ 2
  let s := y * c.orbitSpeed
  let q := cuspQuarticAmplitude c.cuspLabel s
  have hy : 0 < y := sq_pos_of_ne_zero c.horizontalization.cuspNormalized.upperLeft_ne_zero
  have hs : s ≠ 0 := c.horizontalSpeed_ne_zero
  have hamp : ∀ t, HasCuspQuarticAmplitude c.cuspLabel (z t).unary
      (horizontalLine x y s hy t) q := by
    intro t
    have h := c.hasCuspQuarticAmplitude hz.unary hB hlambda hdiff t
    rw [c.horizontalModulus_eq] at h
    exact h
  obtain ⟨selection⟩ := finiteClosedCuspMeanSelection c.cuspLabel z hz
    x y s hy hs q (hamp 0).1 hamp hresidual hH hY hp4
  have hsOne : s = 1 := by
    have hcomplex : (s : ℂ) = 1 := by
      simpa [q, cuspQuarticAmplitude, selection.cusp_eq_infinity] using selection.q_eq_one
    exact_mod_cast hcomplex
  refine ⟨x, y, hy, finiteClosedSelection_unary_eq_canonical hz selection hsOne hresidual, ?_⟩
  intro t
  simpa only [hsOne] using selection.p4_eq_theta₄_sq t

/-- Forward recurrence, the residuals, the three elementary selector
means, and bounded full-state moments already give a canonical unary
trajectory at an initially unspecified positive height. -/
theorem exists_unitHorizontalCanonical_of_recurrent_selector_limits
    {κZ : ℂ} {z : ℝ → LinkedJacobiState ℂ}
    (hz : IsScaledLinkedJacobiTrajectory κZ modularIndependentVariableClock z)
    {t₀ : ℝ}
    (hrec : ForwardRecurrentAt (fun t ↦ LinkedJacobiPolynomialCode.point (z t)) t₀)
    (hresidual : ∀ t (r : LinkedJacobiResidualIndex), linkedJacobiResidual r (z t) = 0)
    (χ : ℝ → ℂ)
    (hY : Tendsto (HGAS.Analysis.cesaroMeanAt (unaryMeanObservable z)) atTop (𝓝 0))
    (hp4 : Tendsto (HGAS.Analysis.cesaroMeanAt (rootP4MeanObservable z)) atTop (𝓝 0))
    (hp2 : Tendsto (HGAS.Analysis.cesaroMeanAt (rootP2MeanObservable z χ)) atTop (𝓝 0))
    {μ : ℝ} (hμ : 1 ≤ μ) (B : ℝ)
    (hgrowth : ∀ᶠ H : ℝ in atTop,
      H⁻¹ * (∫ t in (0 : ℝ)..H, ‖LinkedJacobiPolynomialCode.point (z t)‖ ^ μ) ≤ B) :
    ∃ x y : ℝ, ∃ hy : 0 < y,
      (∀ t, (z t).unary = canonicalUnaryTheta (horizontalLine x y 1 hy t)) ∧
      (∀ t, (z t).jacobi.p4 = theta₄ (horizontalLine x y 1 hy t) ^ 2) := by
  obtain ⟨_, _, hB, T, _, hlambda, hdiff, ⟨c⟩⟩ :=
    exists_closedFrame_of_recurrent_linked_selector_limits
      hz hrec hresidual χ hY hp4 hp2 hμ B hgrowth
  have htimes : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  apply exists_unitHorizontalCanonical_of_closedFrame_means hz c
    (hz.unary.B_ne_zero hB) hlambda hdiff hresidual htimes
  · exact HGAS.Analysis.tendsto_cesaroMeanAt_of_sub_const_tendsto_zero
      hz.unary.continuous_Y 1 htimes (hY.comp htimes)
  · exact HGAS.Analysis.tendsto_cesaroMeanAt_of_sub_const_tendsto_zero
      hz.jacobi.continuous_p4 1 htimes (hp4.comp htimes)

/-- The selected coefficient records the horizontal phase explicitly. -/
theorem theta3HorizontalCoefficient_one_at_gaugeHeight (x : ℝ) :
    theta3HorizontalCoefficient x thetaGaugeHeight thetaGaugeHeight_pos 1 =
      (1 / 256 : ℂ) * Complex.exp ((Real.pi * x : ℝ) * Complex.I) := by
  unfold theta3HorizontalCoefficient theta₃Term
  have harg : (Real.pi : ℂ) * Complex.I * (1 : ℂ) ^ 2 *
      (horizontalLine x thetaGaugeHeight 0 thetaGaugeHeight_pos 0 : ℂ) =
      (-Real.pi * thetaGaugeHeight : ℝ) + (Real.pi * x : ℝ) * Complex.I := by
    apply Complex.ext <;> simp [horizontalLine, Complex.mul_re, Complex.mul_im]
  simp only [Int.cast_one]
  rw [harg, Complex.exp_add, ← Complex.ofReal_exp,
    exp_neg_pi_mul_thetaGaugeHeight]
  norm_num

/-- The normalized first harmonic fixes both height and phase of an
already selected unit-speed unary line. -/
theorem height_phase_of_unitHorizontal_first_mean
    {z : ℝ → LinkedJacobiState ℂ}
    (x y : ℝ) (hy : 0 < y)
    (hunary : ∀ t, (z t).unary = canonicalUnaryTheta (horizontalLine x y 1 hy t))
    (η : ℂ) (hη : ‖η‖ = 1)
    (hfirst : Tendsto (HGAS.Analysis.cesaroMeanAt
      (fun t ↦ (z t).unary.Y * (η * standardUnaryFirstCharacter t)))
      atTop (𝓝 (1 / 128 : ℂ))) :
    y = thetaGaugeHeight ∧ η * Complex.exp ((Real.pi * x : ℝ) * Complex.I) = 1 := by
  have htimes : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have htheta := cesaroMeanAt_theta₃_first_horizontalLine_tendsto x y hy htimes
  have hscaled : Tendsto (fun n : ℕ ↦ HGAS.Analysis.cesaroMeanAt
      (fun t ↦ (z t).unary.Y * (η * standardUnaryFirstCharacter t)) (n + 1 : ℝ))
      atTop (𝓝 (η * (2 * theta3HorizontalCoefficient x y hy 1))) := by
    simpa only [hunary, canonicalUnaryTheta_Y, cesaroMeanAt_const_mul,
      mul_assoc, mul_left_comm, mul_comm] using htheta.const_mul η
  have hcoefficient := tendsto_nhds_unique hscaled (hfirst.comp htimes)
  have hheight := thetaGaugeHeight_of_unitPhase_firstCoefficient x y hy η hη hcoefficient
  refine ⟨hheight, ?_⟩
  subst y
  rw [theta3HorizontalCoefficient_one_at_gaugeHeight] at hcoefficient
  linear_combination (128 : ℂ) * hcoefficient

/-- The canonical unary conclusion from full forward ordinary-time data.
The phase equation is literal; the theorem makes no claim yet about the
remaining Jacobi coordinates or about an unnormalized physical clock. -/
theorem exists_canonicalUnary_of_recurrent_selector_limits
    {κZ : ℂ} {z : ℝ → LinkedJacobiState ℂ}
    (hz : IsScaledLinkedJacobiTrajectory κZ modularIndependentVariableClock z)
    {t₀ : ℝ}
    (hrec : ForwardRecurrentAt (fun t ↦ LinkedJacobiPolynomialCode.point (z t)) t₀)
    (hresidual : ∀ t (r : LinkedJacobiResidualIndex), linkedJacobiResidual r (z t) = 0)
    (χ : ℝ → ℂ)
    (hY : Tendsto (HGAS.Analysis.cesaroMeanAt (unaryMeanObservable z)) atTop (𝓝 0))
    (hp4 : Tendsto (HGAS.Analysis.cesaroMeanAt (rootP4MeanObservable z)) atTop (𝓝 0))
    (hp2 : Tendsto (HGAS.Analysis.cesaroMeanAt (rootP2MeanObservable z χ)) atTop (𝓝 0))
    (η : ℂ) (hη : ‖η‖ = 1)
    (hfirst : Tendsto (HGAS.Analysis.cesaroMeanAt
      (fun t ↦ (z t).unary.Y * (η * standardUnaryFirstCharacter t)))
      atTop (𝓝 (1 / 128 : ℂ)))
    {μ : ℝ} (hμ : 1 ≤ μ) (B : ℝ)
    (hgrowth : ∀ᶠ H : ℝ in atTop,
      H⁻¹ * (∫ t in (0 : ℝ)..H, ‖LinkedJacobiPolynomialCode.point (z t)‖ ^ μ) ≤ B) :
    ∃ x : ℝ,
      (∀ t, (z t).unary = canonicalUnaryTheta
        (horizontalLine x thetaGaugeHeight 1 thetaGaugeHeight_pos t)) ∧
      (∀ t, (z t).jacobi.p4 = theta₄
        (horizontalLine x thetaGaugeHeight 1 thetaGaugeHeight_pos t) ^ 2) ∧
      η * Complex.exp ((Real.pi * x : ℝ) * Complex.I) = 1 := by
  obtain ⟨x, y, hy, hunary, hp4eq⟩ :=
    exists_unitHorizontalCanonical_of_recurrent_selector_limits
      hz hrec hresidual χ hY hp4 hp2 hμ B hgrowth
  obtain ⟨hheight, hphase⟩ := height_phase_of_unitHorizontal_first_mean
    x y hy hunary η hη hfirst
  subst y
  exact ⟨x, hunary, hp4eq, hphase⟩

/-- Only the `Y`, `p₄`, and first-harmonic means are needed for the linked
unary selector. The nonzero first-harmonic limit itself excludes the
degenerate divisors, so no `p₂` moment or auxiliary character is assumed. -/
theorem exists_canonicalUnary_of_forward_means
    {κZ : ℂ} {z : ℝ → LinkedJacobiState ℂ}
    (hz : IsScaledLinkedJacobiTrajectory κZ modularIndependentVariableClock z)
    {t₀ : ℝ}
    (hrec : ForwardRecurrentAt (fun t ↦ LinkedJacobiPolynomialCode.point (z t)) t₀)
    (hresidual : ∀ t (r : LinkedJacobiResidualIndex), linkedJacobiResidual r (z t) = 0)
    (hY : Tendsto (HGAS.Analysis.cesaroMeanAt (unaryMeanObservable z)) atTop (𝓝 0))
    (hp4 : Tendsto (HGAS.Analysis.cesaroMeanAt (rootP4MeanObservable z)) atTop (𝓝 0))
    (η : ℂ) (hη : ‖η‖ = 1)
    (hfirst : Tendsto (HGAS.Analysis.cesaroMeanAt
      (fun t ↦ (z t).unary.Y * (η * standardUnaryFirstCharacter t)))
      atTop (𝓝 (1 / 128 : ℂ)))
    {μ : ℝ} (hμ : 1 ≤ μ) (B : ℝ)
    (hgrowth : ∀ᶠ H : ℝ in atTop,
      H⁻¹ * (∫ t in (0 : ℝ)..H, ‖LinkedJacobiPolynomialCode.point (z t)‖ ^ μ) ≤ B) :
    ∃ x : ℝ,
      (∀ t, (z t).unary = canonicalUnaryTheta
        (horizontalLine x thetaGaugeHeight 1 thetaGaugeHeight_pos t)) ∧
      (∀ t, (z t).jacobi.p4 = theta₄
        (horizontalLine x thetaGaugeHeight 1 thetaGaugeHeight_pos t) ^ 2) ∧
      η * Complex.exp ((Real.pi * x : ℝ) * Complex.I) = 1 := by
  have hrecUnary := forwardRecurrentUnaryModularAt_of_linkedPolynomialPoint hrec
  obtain ⟨hA, hC, hB⟩ := unary_generic_of_recurrent_nonzero_harmonic_mean
    hz.unary modularIndependentVariableClock_ne_zero hrecUnary
    (hresidual t₀ .unaryJacobi) η (neg_ne_zero.mpr Real.pi_ne_zero)
    (by norm_num : (1 / 128 : ℂ) ≠ 0) hfirst
  have htimes : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hCgrowth : ∀ᶠ n : ℕ in atTop,
      (n + 1 : ℝ)⁻¹ * (∫ t in (0 : ℝ)..(n + 1 : ℝ), ‖(z t).unary.C‖ ^ μ) ≤ B := by
    filter_upwards [htimes.eventually hgrowth] with n hn
    exact (unaryC_rpow_average_le_linkedPoint_rpow_average hz
      (zero_le_one.trans hμ) (by positivity : (0 : ℝ) < (n + 1 : ℝ))).trans hn
  obtain ⟨T, _, hlambda, hdiff, ⟨c⟩⟩ := exists_closedFrame_of_recurrent_unary_growth
    hz.unary hA hC hB hrecUnary hμ B hCgrowth
  have hYraw := HGAS.Analysis.tendsto_cesaroMeanAt_of_sub_const_tendsto_zero
    hz.unary.continuous_Y 1 htimes (hY.comp htimes)
  have hp4raw := HGAS.Analysis.tendsto_cesaroMeanAt_of_sub_const_tendsto_zero
    hz.jacobi.continuous_p4 1 htimes (hp4.comp htimes)
  obtain ⟨x, y, hy, hunary, hp4eq⟩ := exists_unitHorizontalCanonical_of_closedFrame_means
    hz c (hz.unary.B_ne_zero hB) hlambda hdiff hresidual htimes hYraw hp4raw
  obtain ⟨hheight, hphase⟩ := height_phase_of_unitHorizontal_first_mean
    x y hy hunary η hη hfirst
  subst y
  exact ⟨x, hunary, hp4eq, hphase⟩

end Stability.Selection
