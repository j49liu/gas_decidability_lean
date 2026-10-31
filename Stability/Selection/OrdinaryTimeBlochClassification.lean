import Stability.Selection.OrdinaryTimePhysicalClock
import HGAS.Modular.JacobiBlochSelectedContinuationNonzero
import HGAS.Modular.JacobiBlochRecurrentReality

/-!
# Real Bloch parameters from ordinary-time linked trajectories

The unary selector fixes the modular coefficients. The linked residuals
then fix their square roots up to the sign absorbed by translation of the
modulus by two. Pointwise theta saturation and reciprocal-chart
continuation give one global affine Bloch formula. Forward recurrence
forces its Bloch parameter to be real.

This is a trajectory classification. Selecting the gauged output by its
three Fourier means is a separate step.
-/

noncomputable section

namespace Stability.Selection

open HGAS HGAS.Modular Filter MeasureTheory Topology

/-- Canonical unary data and the linked residuals give a canonical root
seed, possibly after translation by two. The height is unchanged. -/
theorem exists_sameHeight_canonicalRootSeed
    (z : LinkedJacobiState ℂ) (τ : UpperHalfPlane)
    (hunary : z.unary = canonicalUnaryTheta τ)
    (hp4 : z.jacobi.p4 = theta₄ τ ^ 2)
    (hresidual : ∀ r : LinkedJacobiResidualIndex, linkedJacobiResidual r z = 0) :
    ∃ τ' : UpperHalfPlane, τ'.im = τ.im ∧
      z.jacobi.p2 = (canonicalUnaryRoots τ').p2 ∧
      z.jacobi.p3 = (canonicalUnaryRoots τ').p3 ∧
      z.jacobi.p4 = (canonicalUnaryRoots τ').p4 ∧
      z.jacobi.H = (canonicalUnaryRoots τ').H := by
  have hp3 : z.jacobi.p3 = (canonicalUnaryRoots τ).p3 := by
    have h := hresidual .signedRootLinkThree
    change z.jacobi.p3 - z.unary.Y ^ 2 = 0 at h
    rw [sub_eq_zero.mp h, hunary]
    rfl
  have hH : z.jacobi.H = (canonicalUnaryRoots τ).H := by
    have h := hresidual .eisensteinLink
    change 12 * z.jacobi.H - z.unary.E = 0 at h
    rw [hunary] at h
    change 12 * z.jacobi.H - EisensteinSeries.E2 τ = 0 at h
    change z.jacobi.H = EisensteinSeries.E2 τ / 12
    linear_combination (1 / 12 : ℂ) * h
  have hp2sq : z.jacobi.p2 ^ 2 = (canonicalUnaryRoots τ).p2 ^ 2 := by
    have h := hresidual .coefficientLinkTwo
    change z.jacobi.p2 ^ 2 - z.unary.A = 0 at h
    rw [hunary] at h
    rw [sub_eq_zero.mp h]
    simp only [canonicalUnaryTheta_A, canonicalUnaryRoots_p2, H₂]
    ring
  rcases eq_or_eq_neg_of_sq_eq_sq z.jacobi.p2 (canonicalUnaryRoots τ).p2 hp2sq with hp2 | hp2
  · exact ⟨τ, rfl, hp2, hp3, hp4, hH⟩
  · let τ' : UpperHalfPlane := (2 : ℝ) +ᵥ τ
    have htranslate := canonicalUnaryRoots_vadd_two τ
    refine ⟨τ', ?_, hp2.trans htranslate.1.symm,
      hp3.trans htranslate.2.1.symm, hp4.trans htranslate.2.2.1.symm,
      hH.trans htranslate.2.2.2.symm⟩
    simp [τ']

/-- Recurrence of the linked state projects to the ten Jacobi coordinates
along the same forward return-time sequence. -/
theorem forwardRecurrentJacobiPoint_of_linkedPoint
    {z : ℝ → LinkedJacobiState ℂ} {t₀ : ℝ}
    (hrec : ForwardRecurrentAt (fun t ↦ LinkedJacobiPolynomialCode.point (z t)) t₀) :
    ForwardRecurrentAt (fun t ↦ JacobiPolynomialCode.point (z t).jacobi) t₀ := by
  have hprojection : Continuous (fun q : Fin LinkedJacobiPolynomialCode.dimension → ℂ ↦
      fun j : Fin JacobiPolynomialCode.dimension ↦
        q (LinkedJacobiPolynomialCode.jacobiEmbedding j)) :=
    continuous_pi (fun _ ↦ continuous_apply _)
  simpa only [LinkedJacobiPolynomialCode.point,
    LinkedJacobiPolynomialCode.jacobiEmbedding,
    ComplexPolynomialBlockCode.point_rightEmbedding] using hrec.map hprojection

/-- Full forward linked selector data produce a single globally regular
affine Bloch path with real Bloch parameter. The elliptic clock is real,
and its value is retained exactly in the parameter `nu`. -/
theorem exists_realAffineBloch_of_forward_means
    {kZ Ω : ℝ} (hΩ : Ω ≠ 0) {z : ℝ → LinkedJacobiState ℂ}
    (hz : IsScaledLinkedJacobiTrajectory (kZ : ℂ) (Complex.I * (Ω : ℂ)) z)
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
    ∃ p : AffineBlochParameters,
      p.nu = kZ / Real.pi ∧ p.kappa = Ω / Real.pi ∧
      p.gamma = thetaGaugeHeight ∧ p.c0 ≠ 0 ∧ p.a0.im = 0 ∧
      (∀ t, jacobiTheta1 (p.xi t) (p.tau t : ℂ) ≠ 0) ∧
      (fun t ↦ (z t).jacobi) = p.jacobiBlochPath := by
  obtain ⟨x, hunary, hp4eq, _⟩ := exists_canonicalUnary_of_nonzero_physical_clock
    hΩ hz hrec hresidual hY hp4 η hη hfirst hμ B hgrowth
  let τ₀ := horizontalLine x thetaGaugeHeight (Ω / Real.pi) thetaGaugeHeight_pos 0
  obtain ⟨τ, hheight, hp2seed, hp3seed, hp4seed, hHseed⟩ :=
    exists_sameHeight_canonicalRootSeed (z 0) τ₀ (hunary 0) (hp4eq 0) (hresidual 0)
  have hclockZ : (Real.pi : ℂ) * ((kZ / Real.pi : ℝ) : ℂ) = (kZ : ℂ) := by
    push_cast
    field_simp
  have hclockPhi : (Real.pi : ℂ) * Complex.I * ((Ω / Real.pi : ℝ) : ℂ) =
      Complex.I * (Ω : ℂ) := by
    push_cast
    field_simp
  have hJacobi : IsScaledJacobiTrajectory ((Real.pi : ℂ) * ((kZ / Real.pi : ℝ) : ℂ))
      ((Real.pi : ℂ) * Complex.I * ((Ω / Real.pi : ℝ) : ℂ)) (fun t ↦ (z t).jacobi) := by
    simpa only [hclockZ, hclockPhi] using hz.jacobi
  have hreciprocal : ∀ t, (z t).jacobi.U * (z t).jacobi.T1 = 1 := by
    intro t
    have h := hresidual t .reciprocalChart
    exact sub_eq_zero.mp h
  obtain ⟨p, hnu, hkappa, htau, _, hc0, hregular, heq⟩ :=
    exists_affineBlochParameters_with_c0_ne_zero_eq_of_canonical_residual_at
      τ 0 (kZ / Real.pi) (Ω / Real.pi) 0 hJacobi hp2seed hp3seed hp4seed hHseed
      (hresidual 0 .thetaQuadricOne) (hresidual 0 .thetaQuadricTwo) hreciprocal
  have hgamma : p.gamma = thetaGaugeHeight := by
    have h := congrArg UpperHalfPlane.im htau
    rw [p.tau_im, hheight] at h
    exact h
  have ha0 := p.a0_im_eq_zero_of_forwardRecurrent_point
    (forwardRecurrentJacobiPoint_of_linkedPoint hrec) heq
    (by rw [hkappa]; exact div_ne_zero hΩ Real.pi_ne_zero) hc0
  exact ⟨p, hnu, hkappa, hgamma, hc0, ha0, hregular, heq⟩

end Stability.Selection
