import Stability.Selection.OrdinaryTimeBlochClassification
import HGAS.Modular.AffineBlochQuadraticGeometric

/-!
# Three forward means select the gauged Jacobi trace

The gauge ODE determines its exponential branch. On a recurrent affine
Bloch trajectory, the resulting actual output has an absolutely summable
quadratic Fourier series. At an irrational clock ratio, its mean and two
first-character means determine the full target trace.
-/

noncomputable section

namespace Stability.Selection

open HGAS HGAS.Modular Filter MeasureTheory Topology

/-- Every solution of a constant imaginary-clock equation is its initial
value times the corresponding unit-modulus exponential. -/
theorem eq_initial_mul_frequency_of_hasDerivAt
    (g : ℝ → ℂ) (ω : ℝ)
    (hg : ∀ t, HasDerivAt g (((ω : ℂ) * Complex.I) * g t) t) :
    ∀ t, g t = g 0 * HGAS.Analysis.realFrequencyExponential ω t := by
  let f : ℝ → ℂ := fun t ↦ g 0 * HGAS.Analysis.realFrequencyExponential ω t
  have hf : ∀ t, HasDerivAt f (((ω : ℂ) * Complex.I) * f t) t := by
    intro t
    have hlinear : HasDerivAt (fun u : ℝ ↦ ((ω : ℂ) * Complex.I) * (u : ℂ))
        ((ω : ℂ) * Complex.I) t := by
      simpa only [mul_one] using
        ((hasDerivAt_id (t : ℂ)).const_mul ((ω : ℂ) * Complex.I)).comp_ofReal
    convert hlinear.cexp.const_mul (g 0) using 1
    dsimp [f, HGAS.Analysis.realFrequencyExponential]
    ring
  have hzero := complex_eq_zero_of_hasDerivAt_eq_mul
    (fun _ ↦ (ω : ℂ) * Complex.I) (fun t ↦ g t - f t) continuous_const
    (fun t ↦ by convert (hg t).sub (hf t) using 1; ring)
    (t₀ := 0) (by simp [f, HGAS.Analysis.realFrequencyExponential])
  intro t
  exact sub_eq_zero.mp (congrFun hzero t)

/-- The actual gauge trajectory agrees with one branch of the Bloch
fourth-root gauge. No initial-value normalization is imposed. -/
theorem exists_fourthRootGauge_eq_of_gauge_ODE
    (p : AffineBlochParameters) (g : ℝ → ℂ)
    (hg : ∀ t, HasDerivAt g
      (((p.fourthRootGaugeFrequency : ℝ) : ℂ) * Complex.I * g t) t) :
    ∃ d : ℂ, ∀ t, g t = p.fourthRootGauge d t := by
  let d := g 0 / Complex.exp
    ((Real.pi : ℂ) * Complex.I * (p.centeredW 0 + p.tauComplex 0 / 4))
  have hzero : p.fourthRootGauge d 0 = g 0 := by
    unfold AffineBlochParameters.fourthRootGauge d
    exact div_mul_cancel₀ _ (Complex.exp_ne_zero _)
  refine ⟨d, ?_⟩
  intro t
  rw [p.fourthRootGauge_eq_zero_mul_frequency, hzero]
  exact eq_initial_mul_frequency_of_hasDerivAt g p.fourthRootGaugeFrequency hg t

/-- Three full forward means of the actual gauged Jacobi output determine
its target trace. The two character multipliers are arbitrary nonzero
initial phases; the target coefficients may have arbitrary initial phases.
-/
theorem gaugedJacobi_eq_target_of_three_forward_means
    (p : AffineBlochParameters) {z : ℝ → JacobiState ℂ}
    (heq : z = p.jacobiBlochPath) (ha : p.a0.im = 0) (hkappa : p.kappa ≠ 0)
    (hρ : Irrational p.quadraticClockRatio)
    (g : ℝ → ℂ)
    (hg : ∀ t, HasDerivAt g
      (((p.fourthRootGaugeFrequency : ℝ) : ℂ) * Complex.I * g t) t)
    (target : ℤ → ℂ) (htarget : IsQuadraticGeometric target)
    (cPlus cMinus : ℂ) (hcPlus : cPlus ≠ 0) (hcMinus : cMinus ≠ 0)
    (hmean : Tendsto (HGAS.Analysis.cesaroMeanAt (fun t ↦ g t * (z t).T1))
      atTop (𝓝 1))
    (hplus : Tendsto (HGAS.Analysis.cesaroMeanAt (fun t ↦
      (cPlus * HGAS.Analysis.realFrequencyExponential
        (-p.quadraticOmega * (1 + p.quadraticClockRatio)) t) * (g t * (z t).T1)))
      atTop (𝓝 (cPlus * target 1)))
    (hminus : Tendsto (HGAS.Analysis.cesaroMeanAt (fun t ↦
      (cMinus * HGAS.Analysis.realFrequencyExponential
        (-p.quadraticOmega * (1 - p.quadraticClockRatio)) t) * (g t * (z t).T1)))
      atTop (𝓝 (cMinus * target (-1)))) :
    ∀ t, g t * (z t).T1 =
      quadraticMomentSeries target p.quadraticOmega p.quadraticClockRatio 0 0 t := by
  obtain ⟨d, hgd⟩ := exists_fourthRootGauge_eq_of_gauge_ODE p g hg
  have houtput (t : ℝ) : g t * (z t).T1 = quadraticMomentSeries
      (p.gaugedBlochCoefficient d) p.quadraticOmega p.quadraticClockRatio p.a0.re 0 t := by
    rw [hgd t, heq]
    exact p.fourthRootGauge_mul_jacobiBlochPath_T1_eq_quadraticMomentSeries d ha hkappa t
  have hplusPoint (t : ℝ) :
      (cPlus * HGAS.Analysis.realFrequencyExponential
        (-p.quadraticOmega * (1 + p.quadraticClockRatio)) t) * (g t * (z t).T1) =
      quadraticMomentSeries (fun n ↦ cPlus * p.gaugedBlochCoefficient d n)
        p.quadraticOmega p.quadraticClockRatio p.a0.re 1 t := by
    rw [houtput, mul_assoc, quadraticMomentSeries_plus_character,
      const_mul_quadraticMomentSeries]
  have hminusPoint (t : ℝ) :
      (cMinus * HGAS.Analysis.realFrequencyExponential
        (-p.quadraticOmega * (1 - p.quadraticClockRatio)) t) * (g t * (z t).T1) =
      quadraticMomentSeries (fun n ↦ cMinus * p.gaugedBlochCoefficient d n)
        p.quadraticOmega p.quadraticClockRatio p.a0.re (-1) t := by
    rw [houtput, mul_assoc, quadraticMomentSeries_minus_character,
      const_mul_quadraticMomentSeries]
  have htimes : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hrigidity := quadraticTrace_eq_target_of_three_moments
    (p.gaugedBlochCoefficient d) target p.quadraticOmega p.quadraticClockRatio p.a0.re
    (p.quadraticOmega_ne_zero hkappa) hρ (p.summable_norm_gaugedBlochCoefficient d)
    (p.gaugedBlochCoefficient_translate_isScaledQuadraticGeometric d)
    (p.gaugedBlochCoefficient_reflectTranslate_isScaledQuadraticGeometric d)
    htarget cPlus cMinus hcPlus hcMinus htimes
    (by simpa only [houtput] using hmean.comp htimes)
    (by simpa only [hplusPoint] using hplus.comp htimes)
    (by simpa only [hminusPoint] using hminus.comp htimes)
  intro t
  exact (houtput t).trans (hrigidity t)

/-- The linked trajectory selector, expressed entirely in physical time.

The elliptic clock is `(Ω + N)/2`, the modular clock is `iΩ`, and the
gauge clock is `i(Ω + 2N)/4`. All six means are full forward real-horizon
limits. The target is any normalized nondegenerate quadratic-geometric
coefficient family, including theta coefficients with initial phases.
No Bloch representation, selected measure, or reverse recurrence is an
input to this theorem.
-/
theorem gaugedLinkedJacobi_eq_target_of_forward_means
    {Ω N : ℝ} (hΩ : Ω ≠ 0) (hρ : Irrational (N / Ω))
    {z : ℝ → LinkedJacobiState ℂ}
    (hz : IsScaledLinkedJacobiTrajectory (((Ω + N) / 2 : ℝ) : ℂ)
      (Complex.I * (Ω : ℂ)) z)
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
      H⁻¹ * (∫ t in (0 : ℝ)..H, ‖LinkedJacobiPolynomialCode.point (z t)‖ ^ μ) ≤ B)
    (g : ℝ → ℂ)
    (hg : ∀ t, HasDerivAt g
      ((((Ω + 2 * N) / 4 : ℝ) : ℂ) * Complex.I * g t) t)
    (target : ℤ → ℂ) (htarget : IsQuadraticGeometric target)
    (cPlus cMinus : ℂ) (hcPlus : cPlus ≠ 0) (hcMinus : cMinus ≠ 0)
    (hmean : Tendsto (HGAS.Analysis.cesaroMeanAt (fun t ↦ g t * (z t).jacobi.T1))
      atTop (𝓝 1))
    (hplus : Tendsto (HGAS.Analysis.cesaroMeanAt (fun t ↦
      (cPlus * HGAS.Analysis.realFrequencyExponential (-(Ω + N)) t) *
        (g t * (z t).jacobi.T1))) atTop (𝓝 (cPlus * target 1)))
    (hminus : Tendsto (HGAS.Analysis.cesaroMeanAt (fun t ↦
      (cMinus * HGAS.Analysis.realFrequencyExponential (-(Ω - N)) t) *
        (g t * (z t).jacobi.T1))) atTop (𝓝 (cMinus * target (-1)))) :
    ∀ t, g t * (z t).jacobi.T1 = quadraticMomentSeries target Ω (N / Ω) 0 0 t := by
  obtain ⟨p, hnu, hkappa, _, _, ha, _, heq⟩ :=
    exists_realAffineBloch_of_forward_means hΩ hz hrec hresidual hY hp4
      η hη hfirst hμ B hgrowth
  have hkappaNe : p.kappa ≠ 0 := by rw [hkappa]; exact div_ne_zero hΩ Real.pi_ne_zero
  have hOmega : p.quadraticOmega = Ω := by
    rw [AffineBlochParameters.quadraticOmega, hkappa]
    field_simp
  have hN : p.quadraticLinearFrequency = N := by
    rw [AffineBlochParameters.quadraticLinearFrequency, hnu, hOmega]
    field_simp
    ring
  have hRatio : p.quadraticClockRatio = N / Ω := by
    rw [AffineBlochParameters.quadraticClockRatio, hN, hOmega]
  have hGauge : p.fourthRootGaugeFrequency = (Ω + 2 * N) / 4 := by
    rw [AffineBlochParameters.fourthRootGaugeFrequency, hnu, hkappa]
    field_simp
    ring
  have hPlus : -p.quadraticOmega * (1 + p.quadraticClockRatio) = -(Ω + N) := by
    rw [hOmega, hRatio]
    field_simp
  have hMinus : -p.quadraticOmega * (1 - p.quadraticClockRatio) = -(Ω - N) := by
    rw [hOmega, hRatio]
    field_simp
  have htrace := gaugedJacobi_eq_target_of_three_forward_means p heq ha hkappaNe
    (by simpa only [hRatio] using hρ) g (by simpa only [hGauge] using hg)
    target htarget cPlus cMinus hcPlus hcMinus hmean
    (by simpa only [hPlus] using hplus) (by simpa only [hMinus] using hminus)
  simpa only [hOmega, hRatio] using htrace

end Stability.Selection
