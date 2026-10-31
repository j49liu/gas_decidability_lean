import Stability.Selection.LinearThetaCuspExclusion
import HGAS.Modular.RecurrentLiftExactFrameDifferentiable
import HGAS.Modular.HorizontalUnaryClosedChart
import HGAS.Modular.RecurrentUnaryMomentGenericity
import HGAS.Modular.LinkedJacobiTrajectoryPolynomialCrosswalk

/-!
# Closed frames from ordinary-time trajectory bounds

A complete recurrent unary trajectory on the generic locus admits a
differentiable canonical-lambda lift. A forward moment bound of any real
order at least one excludes its nonperiodic frame branch, giving a closed
horocycle chart. For a linked trajectory, the residuals and three forward
selector means establish genericity, and the full-state norm controls the
unary coordinate used in the cusp estimate.

This is the closed-orbit step of Proposition `prop:modselect` in Section 8
of the manuscript. The clock is already normalized; no invariant measure
or backward recurrence is assumed. Cusp, height, and phase selection are
separate steps.
-/

noncomputable section

namespace Stability.Selection

open HGAS HGAS.Modular Filter MeasureTheory Topology

/-- A recurrent generic normalized unary trajectory with bounded forward
moments has a differentiable lambda lift in a closed horocycle chart.
The lift and the frame are conclusions, not additional hypotheses. -/
theorem exists_closedFrame_of_recurrent_unary_growth
    {z : ℝ → UnaryModularState ℂ}
    (hz : IsScaledUnaryModularTrajectory modularIndependentVariableClock z)
    {t₀ : ℝ}
    (hA : (z t₀).A ≠ 0) (hC : (z t₀).C ≠ 0)
    (hB : UnaryModularState.B (z t₀) ≠ 0)
    (hrec : ForwardRecurrentUnaryModularAt z t₀)
    {μ : ℝ} (hμ : 1 ≤ μ) (B : ℝ)
    (hgrowth : ∀ᶠ n : ℕ in atTop,
      (n + 1 : ℝ)⁻¹ * (∫ t in (0 : ℝ)..(n + 1 : ℝ), ‖(z t).C‖ ^ μ) ≤ B) :
    ∃ T : ℝ → UpperHalfPlane,
      Continuous T ∧
      (∀ t, UnaryModularState.lambdaCoordinate (z t) = canonicalLambda (T t)) ∧
      (∀ t, ∃ v : ℂ, HasDerivAt (fun u : ℝ ↦ (T u : ℂ)) v t) ∧
      Nonempty (ClosedUnaryHorocycleChart z T) := by
  obtain ⟨T, hT, hlambda, hdiff, hgeometry⟩ :=
    recurrentGenericUnaryTrajectory_exists_differentiable_horizontal_or_exactFrame
      hz hA hC hB hrec
  refine ⟨T, hT, hlambda, hdiff, ?_⟩
  rcases hgeometry with ⟨x, y, s, hy, hline⟩ | ⟨g, s, hs, hframe⟩
  · exact exists_closedUnaryHorocycleChart_of_horizontalLine
      hz (hz.B_ne_zero hB) hlambda x y s hy hline
  · exact exists_closedUnaryHorocycleChart z T g s hs hframe
      (periodic_of_bounded_unaryC_rpow_average
        hz (hz.B_ne_zero hB) hlambda g hs hframe hμ B hgrowth)

/-- Each unary coordinate is bounded by the norm of the literal linked
polynomial state. This is the coordinate used by the linear cusp bound. -/
theorem unaryC_norm_le_linkedPoint_norm (z : LinkedJacobiState ℂ) :
    ‖z.unary.C‖ ≤ ‖LinkedJacobiPolynomialCode.point z‖ := by
  simpa [LinkedJacobiPolynomialCode.point, UnaryPolynomialCode.modularPoint] using
    norm_le_pi_norm (LinkedJacobiPolynomialCode.point z)
      (LinkedJacobiPolynomialCode.unaryEmbedding UnaryPolynomialCode.CIndex)

/-- A full linked-state moment controls the corresponding unary moment
on each positive ordinary-time interval. -/
theorem unaryC_rpow_average_le_linkedPoint_rpow_average
    {κZ κPhi : ℂ} {z : ℝ → LinkedJacobiState ℂ}
    (hz : IsScaledLinkedJacobiTrajectory κZ κPhi z)
    {μ : ℝ} (hμ : 0 ≤ μ) {T : ℝ} (hT : 0 < T) :
    T⁻¹ * (∫ t in (0 : ℝ)..T, ‖(z t).unary.C‖ ^ μ) ≤
      T⁻¹ * (∫ t in (0 : ℝ)..T, ‖LinkedJacobiPolynomialCode.point (z t)‖ ^ μ) := by
  have hpoint : Continuous (fun t ↦ LinkedJacobiPolynomialCode.point (z t)) :=
    continuous_pi (fun i ↦ continuous_iff_continuousAt.mpr
      (fun t ↦ (hz.point_hasDerivAt i t).continuousAt))
  have hC := (Real.continuous_rpow_const hμ).comp hz.unary.continuous_C.norm
  have hfull := (Real.continuous_rpow_const hμ).comp hpoint.norm
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hT.le)
  apply intervalIntegral.integral_mono_on hT.le
    (hC.intervalIntegrable _ _) (hfull.intervalIntegrable _ _)
  intro t _
  exact Real.rpow_le_rpow (norm_nonneg _) (unaryC_norm_le_linkedPoint_norm (z t)) hμ

/-- The raw complete linked trajectory version of the closed-frame step.

The means and growth bound are full forward real-horizon statements.
The character in the root mean is unrestricted here: only its nonzero
target excludes the `A = 0` divisor. Later frequency selection uses its
specific phase-clock form. The Jacobi clock is arbitrary.
-/
theorem exists_closedFrame_of_recurrent_linked_selector_limits
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
    (hgrowth : ∀ᶠ T : ℝ in atTop,
      T⁻¹ * (∫ t in (0 : ℝ)..T, ‖LinkedJacobiPolynomialCode.point (z t)‖ ^ μ) ≤ B) :
    (z t₀).unary.A ≠ 0 ∧ (z t₀).unary.C ≠ 0 ∧
      UnaryModularState.B (z t₀).unary ≠ 0 ∧
      ∃ T : ℝ → UpperHalfPlane,
        Continuous T ∧
        (∀ t, UnaryModularState.lambdaCoordinate (z t).unary = canonicalLambda (T t)) ∧
        (∀ t, ∃ v : ℂ, HasDerivAt (fun u : ℝ ↦ (T u : ℂ)) v t) ∧
        Nonempty (ClosedUnaryHorocycleChart (fun t ↦ (z t).unary) T) := by
  have htimes : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hrecUnary := forwardRecurrentUnaryModularAt_of_linkedPolynomialPoint hrec
  obtain ⟨hA, hC, hB, _⟩ := recurrentUnary_generic_of_selectorMomentLimits
    hz.unary hrecUnary hresidual htimes χ (hY.comp htimes) (hp4.comp htimes) (hp2.comp htimes)
  refine ⟨hA, hC, hB, exists_closedFrame_of_recurrent_unary_growth
    hz.unary hA hC hB hrecUnary hμ B ?_⟩
  filter_upwards [htimes.eventually hgrowth] with n hn
  exact (unaryC_rpow_average_le_linkedPoint_rpow_average hz
    (zero_le_one.trans hμ) (by positivity : (0 : ℝ) < (n + 1 : ℝ))).trans hn

end Stability.Selection
