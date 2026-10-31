import Stability.Selection.OrdinaryTimeDetectorTheta

/-!
# Scalar polynomial tests and complex forward means

The real and imaginary polynomial coordinates of the detector tests
recover the complex selector means at the same ordinary-time horizons.
No subsequence or change of averaging measure is involved.
-/

noncomputable section

namespace Stability.Selection

open HGAS HGAS.Clocks.ControllerPhaseProductCharacterCode Filter MeasureTheory Topology

/-- The realification used by the polynomial compiler is continuous. -/
theorem continuous_evalPair_comp {n : ℕ} (code : ComplexPairCode n)
    {x : ℝ → Fin n → ℝ} (hx : Continuous x) :
    Continuous (fun t ↦ evalPair code (x t)) := by
  have hc (p : PolynomialCode n) : Continuous (fun t ↦
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) (x t) (PolynomialCode.decode p)) := by
    simpa only [MvPolynomial.eval_map] using
      (MvPolynomial.continuous_eval
        (MvPolynomial.map (algebraMap ℚ ℝ) (PolynomialCode.decode p))).comp hx
  exact Complex.equivRealProdCLM.symm.continuous.comp ((hc code.1).prodMk (hc code.2))

/-- The complex average is the realification of its two scalar averages. -/
theorem forwardMean_eq_components {f : ℝ → ℂ} (hf : Continuous f) (H : ℝ) :
    HGAS.Analysis.cesaroMeanAt f H =
      ((H⁻¹ * ∫ t in (0 : ℝ)..H, (f t).re : ℝ) : ℂ) +
        ((H⁻¹ * ∫ t in (0 : ℝ)..H, (f t).im : ℝ) : ℂ) * Complex.I := by
  have hint : IntervalIntegrable f volume 0 H := hf.intervalIntegrable 0 H
  have hre : (∫ t in (0 : ℝ)..H, (f t).re) = (∫ t in (0 : ℝ)..H, f t).re :=
    intervalIntegral.intervalIntegral_re hint
  have him : (∫ t in (0 : ℝ)..H, (f t).im) = (∫ t in (0 : ℝ)..H, f t).im :=
    intervalIntegral.intervalIntegral_im hint
  rw [hre, him]
  unfold HGAS.Analysis.cesaroMeanAt
  push_cast
  symm
  calc
    _ = (H : ℂ)⁻¹ *
        (((∫ t in (0 : ℝ)..H, f t).re : ℂ) +
          ((∫ t in (0 : ℝ)..H, f t).im : ℂ) * Complex.I) := by ring
    _ = _ := by rw [Complex.re_add_im]

theorem tendsto_forwardMean_zero_of_components {f : ℝ → ℂ} (hf : Continuous f)
    (hre : Tendsto (fun H : ℝ ↦ H⁻¹ * ∫ t in (0 : ℝ)..H, (f t).re) atTop (𝓝 0))
    (him : Tendsto (fun H : ℝ ↦ H⁻¹ * ∫ t in (0 : ℝ)..H, (f t).im) atTop (𝓝 0)) :
    Tendsto (HGAS.Analysis.cesaroMeanAt f) atTop (𝓝 0) := by
  have h := ((Complex.continuous_ofReal.tendsto 0).comp hre).add
    (((Complex.continuous_ofReal.tendsto 0).comp him).mul_const Complex.I)
  simpa only [Function.comp_apply, ← forwardMean_eq_components hf,
    Complex.ofReal_zero, zero_mul, zero_add] using h

/-- All literal scalar moment-code means imply each literal complex
local moment-code mean, with the same full real horizons. -/
theorem detector_complexMeans_of_scalarMeans
    {eqs vars : ℕ} (I : DQLSystem eqs vars)
    {x : ℝ → Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ}
    (hx : Continuous x)
    (hmeans : ∀ k : Fin (FixedDetectorMomentCode.scalarMomentCount vars),
      Tendsto (fun H : ℝ ↦ H⁻¹ * ∫ t in (0 : ℝ)..H,
        MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) (x t)
          (PolynomialCode.decode (FixedDetectorMomentCode.scalarMomentCode I k))) atTop (𝓝 0))
    (j : Fin vars) (r : Fin FixedDetectorMomentCode.localMomentCount) :
    Tendsto (HGAS.Analysis.cesaroMeanAt (fun t ↦
      evalPair (FixedDetectorMomentCode.localMomentCode I j r) (x t))) atTop (𝓝 0) := by
  apply tendsto_forwardMean_zero_of_components
    (continuous_evalPair_comp (FixedDetectorMomentCode.localMomentCode I j r) hx)
  · simpa [FixedDetectorMomentCode.scalarMomentCode, FixedDetectorMomentCode.momentCode,
      evalPair] using hmeans (finProdFinEquiv (finProdFinEquiv (j, r), (0 : Fin 2)))
  · simpa [FixedDetectorMomentCode.scalarMomentCode, FixedDetectorMomentCode.momentCode,
      evalPair] using hmeans (finProdFinEquiv (finProdFinEquiv (j, r), (1 : Fin 2)))

end Stability.Selection
