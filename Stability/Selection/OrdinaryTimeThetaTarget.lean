import Stability.Selection.OrdinaryTimeJacobiMoments
import HGAS.Arithmetic.CanonicalDetectorThetaQuadraticGeometric

/-!
# The detector theta target with its initial phases

The six ordinary-time selector means identify the literal theta factor
along the detector torus translation. The target coefficients and the two
neighbouring coefficient identities are derived from the initial phase.
This is the theta-output part of Section 8, Theorem `thm:selector`.
-/

noncomputable section

namespace Stability.Selection

open HGAS HGAS.Modular HGAS.Clocks Filter MeasureTheory Topology
open HGAS.CanonicalDetectorThetaQuadraticGeometric

/-- Centered full real-horizon means give the corresponding raw means. -/
theorem tendsto_forwardMean_of_centered
    {f : ℝ → ℂ} (hf : Continuous f) (c : ℂ)
    (h : Tendsto (HGAS.Analysis.cesaroMeanAt (fun t ↦ f t - c))
      atTop (𝓝 0)) :
    Tendsto (HGAS.Analysis.cesaroMeanAt f) atTop (𝓝 c) := by
  have hsum : Tendsto (fun H ↦
      HGAS.Analysis.cesaroMeanAt (fun t ↦ f t - c) H + c) atTop (𝓝 c) := by
    simpa only [zero_add] using h.add_const c
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
  unfold HGAS.Analysis.cesaroMeanAt
  rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _)
    (continuous_const.intervalIntegrable _ _), intervalIntegral.integral_const]
  simp only [sub_zero, Complex.real_smul]
  have hcancel : (H : ℂ)⁻¹ * H = 1 :=
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hH.ne')
  linear_combination -c * hcancel

/-- The six forward means select the intended theta factor, including its
actual initial torus phase. Frequencies are angular frequencies read from
the private and linear torus characters; no target coefficient family is
an input. The root-half mean is not needed by this conclusion. -/
theorem gaugedLinkedJacobi_eq_thetaSum_of_forward_means
    {eqs vars : ℕ} (I : DQLSystem eqs vars) (j : Fin vars)
    (frequency : DetectorPhase eqs vars → ℝ)
    (phase₀ : UnitAddTorus (DetectorPhase eqs vars))
    (hΩ : privateAngularFrequency j frequency ≠ 0)
    (hρ : Irrational (linearAngularFrequency I j frequency /
      privateAngularFrequency j frequency))
    {z : ℝ → LinkedJacobiState ℂ}
    (hz : IsScaledLinkedJacobiTrajectory
      (((privateAngularFrequency j frequency + linearAngularFrequency I j frequency) / 2 : ℝ) : ℂ)
      (Complex.I * (privateAngularFrequency j frequency : ℂ)) z)
    (hrec : ForwardRecurrentAt (fun t ↦ LinkedJacobiPolynomialCode.point (z t)) 0)
    (hresidual : ∀ t (r : LinkedJacobiResidualIndex), linkedJacobiResidual r (z t) = 0)
    (hY : Tendsto (HGAS.Analysis.cesaroMeanAt (unaryMeanObservable z)) atTop (𝓝 0))
    (hp4 : Tendsto (HGAS.Analysis.cesaroMeanAt (rootP4MeanObservable z)) atTop (𝓝 0))
    (η : ℂ) (hη : ‖η‖ = 1)
    (hfirst : Tendsto (HGAS.Analysis.cesaroMeanAt (fun t ↦
      (z t).unary.Y * (η * HGAS.Analysis.realFrequencyExponential
        (-privateAngularFrequency j frequency) t) - 1 / 128)) atTop (𝓝 0))
    {μ : ℝ} (hμ : 1 ≤ μ) (B : ℝ)
    (hgrowth : ∀ᶠ H : ℝ in atTop,
      H⁻¹ * (∫ t in (0 : ℝ)..H, ‖LinkedJacobiPolynomialCode.point (z t)‖ ^ μ) ≤ B)
    (g : ℝ → ℂ)
    (hg : ∀ t, HasDerivAt g
      ((((privateAngularFrequency j frequency + 2 * linearAngularFrequency I j frequency) /
        4 : ℝ) : ℂ) * Complex.I * g t) t)
    (hmean : Tendsto (HGAS.Analysis.cesaroMeanAt
      (fun t ↦ g t * (z t).jacobi.T1 - 1)) atTop (𝓝 0))
    (hplus : Tendsto (HGAS.Analysis.cesaroMeanAt (fun t ↦
      (jacobiPlusTorusTwist I j phase₀ * HGAS.Analysis.realFrequencyExponential
        (-(privateAngularFrequency j frequency + linearAngularFrequency I j frequency)) t) *
        (g t * (z t).jacobi.T1) - 1 / 256)) atTop (𝓝 0))
    (hminus : Tendsto (HGAS.Analysis.cesaroMeanAt (fun t ↦
      (jacobiMinusTorusTwist I j phase₀ * HGAS.Analysis.realFrequencyExponential
        (-(privateAngularFrequency j frequency - linearAngularFrequency I j frequency)) t) *
        (g t * (z t).jacobi.T1) - 1 / 256)) atTop (𝓝 0)) :
    ∀ t, g t * (z t).jacobi.T1 = ∑' n : ℤ,
      DetectorFactorizedFourier.thetaTerm (1 / 256 : ℝ) I j n
        (RadicalClock.torusTranslationFlow frequency t phase₀) := by
  have hgcont : Continuous g := continuous_iff_continuousAt.mpr
    (fun t ↦ (hg t).continuousAt)
  have hT1 : Continuous (fun t ↦ (z t).jacobi.T1) := hz.jacobi.continuous_T1
  have hfreq (ω : ℝ) : Continuous (HGAS.Analysis.realFrequencyExponential ω) := by
    unfold HGAS.Analysis.realFrequencyExponential
    fun_prop
  have hfirstRaw := tendsto_forwardMean_of_centered
    (hz.unary.continuous_Y.mul (continuous_const.mul (hfreq _))) (1 / 128) hfirst
  have hmeanRaw := tendsto_forwardMean_of_centered (hgcont.mul hT1) 1 hmean
  have hplusRaw := tendsto_forwardMean_of_centered
    ((continuous_const.mul (hfreq _)).mul (hgcont.mul hT1)) (1 / 256) hplus
  have hminusRaw := tendsto_forwardMean_of_centered
    ((continuous_const.mul (hfreq _)).mul (hgcont.mul hT1)) (1 / 256) hminus
  have htrace := gaugedLinkedJacobi_eq_target_of_forward_means hΩ hρ hz hrec hresidual
    hY hp4 η hη hfirstRaw hμ B hgrowth g hg
    (fixedPhaseThetaCoefficient (1 / 256 : ℝ) I j phase₀)
    (canonicalFixedPhaseThetaCoefficient_isQuadraticGeometric I j phase₀)
    (jacobiPlusTorusTwist I j phase₀) (jacobiMinusTorusTwist I j phase₀)
    (jacobiPlusTorusTwist_ne_zero I j phase₀) (jacobiMinusTorusTwist_ne_zero I j phase₀)
    hmeanRaw
    (by simpa only [jacobiPlusTorusTwist_mul_canonicalThetaCoefficient_one,
      Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using hplusRaw)
    (by simpa only [jacobiMinusTorusTwist_mul_canonicalThetaCoefficient_neg_one,
      Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using hminusRaw)
  intro t
  exact (htrace t).trans
    (quadraticMomentSeries_fixedPhaseThetaCoefficient_eq_thetaSum
      (1 / 256 : ℝ) I j frequency phase₀ hΩ t)

end Stability.Selection
