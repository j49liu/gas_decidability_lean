import Stability.Selection.OrdinaryTimeUnarySelection
import Stability.Selection.LinkedClockConjugation
import Stability.Selection.CanonicalThetaReflection

/-!
# Unary selection in a nonzero physical clock

Positive frequencies are normalized by a positive constant time change.
For negative frequencies, coordinatewise conjugation first changes the
modular clock's sign. All means and recurrence remain forward in time.
Conjugation sends the elliptic clock to its conjugate, leaving a real
elliptic clock unchanged; the subsequent rescaling multiplies both clocks.

The output is the canonical unary trajectory at the original signed
physical speed. This does not classify the remaining Jacobi coordinates.
-/

noncomputable section

namespace Stability.Selection

open HGAS HGAS.Modular Filter MeasureTheory Topology

/-- Full forward Cesàro limits are unchanged by a positive rescaling. -/
theorem tendsto_cesaroMeanAt_positive_rescale
    (f : ℝ → ℂ) {a : ℝ} (ha : 0 < a) {L : ℂ}
    (hmean : Tendsto (HGAS.Analysis.cesaroMeanAt f) atTop (𝓝 L)) :
    Tendsto (HGAS.Analysis.cesaroMeanAt (fun t ↦ f (a * t))) atTop (𝓝 L) := by
  have hscaled := hmean.comp (tendsto_id.const_mul_atTop ha)
  have hid (T : ℝ) : HGAS.Analysis.cesaroMeanAt (fun t ↦ f (a * t)) T =
      HGAS.Analysis.cesaroMeanAt f (a * T) := by
    have h := HGAS.Analysis.cesaroMeanAt_comp_mul_div f (T := a * T) ha.ne'
    simpa only [mul_div_cancel_left₀ _ ha.ne'] using h
  change Tendsto (fun T : ℝ ↦ HGAS.Analysis.cesaroMeanAt (fun t ↦ f (a * t)) T)
    atTop (𝓝 L)
  simpa only [Function.comp_def, hid, id_eq] using hscaled

/-- The real-valued average transforms at the actual real horizon. -/
theorem realAverage_positive_rescale (f : ℝ → ℝ) {a : ℝ} (ha : 0 < a) (T : ℝ) :
    T⁻¹ * (∫ t in (0 : ℝ)..T, f (a * t)) =
      (a * T)⁻¹ * (∫ t in (0 : ℝ)..(a * T), f t) := by
  rw [intervalIntegral.integral_comp_mul_left f ha.ne']
  simp only [mul_zero, smul_eq_mul, mul_inv_rev]
  ring

/-- A positive physical frequency gives the canonical unary conclusion
after a positive rescaling of both linked clocks. -/
theorem exists_canonicalUnary_of_positive_physical_clock
    {κZ : ℂ} {Ω : ℝ} (hΩ : 0 < Ω) {z : ℝ → LinkedJacobiState ℂ}
    (hz : IsScaledLinkedJacobiTrajectory κZ (Complex.I * (Ω : ℂ)) z)
    (hrec : ForwardRecurrentAt (fun t ↦ LinkedJacobiPolynomialCode.point (z t)) 0)
    (hresidual : ∀ t (r : LinkedJacobiResidualIndex), linkedJacobiResidual r (z t) = 0)
    (hY : Tendsto (HGAS.Analysis.cesaroMeanAt (unaryMeanObservable z)) atTop (𝓝 0))
    (hp4 : Tendsto (HGAS.Analysis.cesaroMeanAt (rootP4MeanObservable z)) atTop (𝓝 0))
    (η : ℂ) (hη : ‖η‖ = 1)
    (hfirst : Tendsto (HGAS.Analysis.cesaroMeanAt
      (fun t ↦ (z t).unary.Y * (η * HGAS.Analysis.realFrequencyExponential (-Ω) t)))
      atTop (𝓝 (1 / 128 : ℂ)))
    {μ : ℝ} (hμ : 1 ≤ μ) (B : ℝ)
    (hgrowth : ∀ᶠ H : ℝ in atTop,
      H⁻¹ * (∫ t in (0 : ℝ)..H, ‖LinkedJacobiPolynomialCode.point (z t)‖ ^ μ) ≤ B) :
    ∃ x : ℝ,
      (∀ t, (z t).unary = canonicalUnaryTheta
        (horizontalLine x thetaGaugeHeight (Ω / Real.pi) thetaGaugeHeight_pos t)) ∧
      (∀ t, (z t).jacobi.p4 = theta₄
        (horizontalLine x thetaGaugeHeight (Ω / Real.pi) thetaGaugeHeight_pos t) ^ 2) ∧
      η * Complex.exp ((Real.pi * x : ℝ) * Complex.I) = 1 := by
  let a : ℝ := Real.pi / Ω
  have ha : 0 < a := div_pos Real.pi_pos hΩ
  have hscale : a * Ω = Real.pi := div_mul_cancel₀ _ hΩ.ne'
  let za : ℝ → LinkedJacobiState ℂ := fun t ↦ z (a * t)
  have hclock : (a : ℂ) * (Complex.I * (Ω : ℂ)) = modularIndependentVariableClock := by
    unfold modularIndependentVariableClock
    calc
      _ = ((a * Ω : ℝ) : ℂ) * Complex.I := by push_cast; ring
      _ = _ := by rw [hscale]
  have hza : IsScaledLinkedJacobiTrajectory ((a : ℂ) * κZ)
      modularIndependentVariableClock za := by
    simpa only [hclock, za] using hz.rescale a
  have hYscaled := tendsto_cesaroMeanAt_positive_rescale (unaryMeanObservable z) ha hY
  have hp4scaled := tendsto_cesaroMeanAt_positive_rescale (rootP4MeanObservable z) ha hp4
  have hchar (t : ℝ) : HGAS.Analysis.realFrequencyExponential (-Ω) (a * t) =
      standardUnaryFirstCharacter t := by
    unfold HGAS.Analysis.realFrequencyExponential standardUnaryFirstCharacter
    congr 1
    have hscaleC := congrArg (fun u : ℝ ↦ (u : ℂ)) hscale
    push_cast at hscaleC ⊢
    linear_combination -Complex.I * (t : ℂ) * hscaleC
  have hfirstscaled : Tendsto (HGAS.Analysis.cesaroMeanAt
      (fun t ↦ (za t).unary.Y * (η * standardUnaryFirstCharacter t)))
      atTop (𝓝 (1 / 128 : ℂ)) := by
    simpa only [za, hchar] using tendsto_cesaroMeanAt_positive_rescale
      (fun t ↦ (z t).unary.Y * (η * HGAS.Analysis.realFrequencyExponential (-Ω) t)) ha hfirst
  have hgrowthscaled : ∀ᶠ H : ℝ in atTop,
      H⁻¹ * (∫ t in (0 : ℝ)..H, ‖LinkedJacobiPolynomialCode.point (za t)‖ ^ μ) ≤ B := by
    filter_upwards [(tendsto_id.const_mul_atTop ha).eventually hgrowth] with H hH
    simpa only [za, realAverage_positive_rescale
      (fun t ↦ ‖LinkedJacobiPolynomialCode.point (z t)‖ ^ μ) ha H] using hH
  obtain ⟨x, hunary, hp4eq, hphase⟩ := exists_canonicalUnary_of_forward_means
    hza (hrec.rescale_zero ha) (fun t r ↦ hresidual (a * t) r)
    hYscaled hp4scaled η hη hfirstscaled hμ B hgrowthscaled
  have hline (t : ℝ) : horizontalLine x thetaGaugeHeight 1 thetaGaugeHeight_pos (t / a) =
      horizontalLine x thetaGaugeHeight (Ω / Real.pi) thetaGaugeHeight_pos t := by
    apply UpperHalfPlane.ext
    apply Complex.ext
    · simp only [horizontalLine]
      dsimp [a]
      field_simp
    · rfl
  refine ⟨x, ?_, ?_, hphase⟩
  · intro t
    have h := hunary (t / a)
    simpa only [za, mul_div_cancel₀ _ ha.ne', hline] using h
  · intro t
    have h := hp4eq (t / a)
    simpa only [za, mul_div_cancel₀ _ ha.ne', hline] using h

/-- The unary selector in every nonzero physical modular clock. Negative
frequencies use conjugation, never backward recurrence or backward means.
The elliptic clock is arbitrary and is conjugated, not negated. -/
theorem exists_canonicalUnary_of_nonzero_physical_clock
    {κZ : ℂ} {Ω : ℝ} (hΩ : Ω ≠ 0) {z : ℝ → LinkedJacobiState ℂ}
    (hz : IsScaledLinkedJacobiTrajectory κZ (Complex.I * (Ω : ℂ)) z)
    (hrec : ForwardRecurrentAt (fun t ↦ LinkedJacobiPolynomialCode.point (z t)) 0)
    (hresidual : ∀ t (r : LinkedJacobiResidualIndex), linkedJacobiResidual r (z t) = 0)
    (hY : Tendsto (HGAS.Analysis.cesaroMeanAt (unaryMeanObservable z)) atTop (𝓝 0))
    (hp4 : Tendsto (HGAS.Analysis.cesaroMeanAt (rootP4MeanObservable z)) atTop (𝓝 0))
    (η : ℂ) (hη : ‖η‖ = 1)
    (hfirst : Tendsto (HGAS.Analysis.cesaroMeanAt
      (fun t ↦ (z t).unary.Y * (η * HGAS.Analysis.realFrequencyExponential (-Ω) t)))
      atTop (𝓝 (1 / 128 : ℂ)))
    {μ : ℝ} (hμ : 1 ≤ μ) (B : ℝ)
    (hgrowth : ∀ᶠ H : ℝ in atTop,
      H⁻¹ * (∫ t in (0 : ℝ)..H, ‖LinkedJacobiPolynomialCode.point (z t)‖ ^ μ) ≤ B) :
    ∃ x : ℝ,
      (∀ t, (z t).unary = canonicalUnaryTheta
        (horizontalLine x thetaGaugeHeight (Ω / Real.pi) thetaGaugeHeight_pos t)) ∧
      (∀ t, (z t).jacobi.p4 = theta₄
        (horizontalLine x thetaGaugeHeight (Ω / Real.pi) thetaGaugeHeight_pos t) ^ 2) ∧
      η * Complex.exp ((Real.pi * x : ℝ) * Complex.I) = 1 := by
  rcases lt_or_gt_of_ne hΩ with hnegative | hpositive
  · let zbar : ℝ → LinkedJacobiState ℂ := fun t ↦ conjugateLinked (z t)
    have hzbar : IsScaledLinkedJacobiTrajectory (star κZ)
        (Complex.I * ((-Ω : ℝ) : ℂ)) zbar := by
      simpa [zbar] using conjugateLinked_isScaledTrajectory hz
    have hresbar : ∀ t (r : LinkedJacobiResidualIndex), linkedJacobiResidual r (zbar t) = 0 := by
      intro t r
      simp only [zbar, linkedJacobiResidual_conjugateLinked, hresidual, star_zero]
    have hYbar : Tendsto (HGAS.Analysis.cesaroMeanAt (unaryMeanObservable zbar)) atTop (𝓝 0) := by
      simpa [unaryMeanObservable, zbar, conjugateLinked, conjugateUnary] using
        tendsto_cesaroMeanAt_star hY
    have hp4bar : Tendsto (HGAS.Analysis.cesaroMeanAt (rootP4MeanObservable zbar)) atTop (𝓝 0) := by
      simpa [rootP4MeanObservable, zbar, conjugateLinked, conjugateJacobi] using
        tendsto_cesaroMeanAt_star hp4
    have hfirstbar : Tendsto (HGAS.Analysis.cesaroMeanAt
        (fun t ↦ (zbar t).unary.Y * (star η * HGAS.Analysis.realFrequencyExponential (-(-Ω)) t)))
        atTop (𝓝 (1 / 128 : ℂ)) := by
      simpa [zbar, conjugateLinked, conjugateUnary, HGAS.Analysis.realFrequencyExponential,
        ← Complex.exp_conj] using tendsto_cesaroMeanAt_star hfirst
    have hgrowthbar : ∀ᶠ H : ℝ in atTop,
        H⁻¹ * (∫ t in (0 : ℝ)..H, ‖LinkedJacobiPolynomialCode.point (zbar t)‖ ^ μ) ≤ B := by
      simpa only [zbar, norm_linkedPoint_conjugateLinked] using hgrowth
    obtain ⟨x, hunary, hp4eq, hphase⟩ := exists_canonicalUnary_of_positive_physical_clock
      (neg_pos.mpr hnegative) hzbar (conjugateLinked_forwardRecurrentAt hrec) hresbar hYbar hp4bar
      (star η) (by simpa using hη) hfirstbar hμ B hgrowthbar
    refine ⟨-x, ?_, ?_, ?_⟩
    · intro t
      have h := eq_canonicalUnaryTheta_reflect_of_conjugate_eq (hunary t)
      simpa only [reflectUpperHalfPlane_horizontalLine, neg_div, neg_neg] using h
    · intro t
      have h := congrArg star (hp4eq t)
      simpa only [zbar, conjugateLinked, conjugateJacobi, star_star, star_pow,
        ← theta₄_reflect, reflectUpperHalfPlane_horizontalLine, neg_div, neg_neg] using h
    · have h := congrArg star hphase
      simpa [← Complex.exp_conj] using h
  · exact exists_canonicalUnary_of_positive_physical_clock hpositive hz hrec hresidual
      hY hp4 η hη hfirst hμ B hgrowth

end Stability.Selection
