import Stability.Selection.OrdinaryTimeDetectorClocks

/-!
# Theta output of the concrete polynomial source

The complete flattened source ODE, forward recurrence, zero normalized
validity, its literal polynomial moment means, and bounded Euclidean
growth determine each theta output. All clocks, gauges, initial phases,
and column trajectories below are read from that same raw source curve.
This proves the theta-output conclusion in Section 8, Theorem `thm:selector`;
the detector product and its arithmetic average are separate conclusions.
-/

noncomputable section

namespace Stability.Selection

open HGAS HGAS.Modular HGAS.Clocks Filter MeasureTheory Topology
open HGAS.FixedDetectorReverseTrajectoryCrosswalk
open HGAS.Clocks.ControllerPhaseProductCharacterCode
open HGAS.CanonicalDetectorThetaQuadraticGeometric
open HGAS.NormalizedCorrectedFixedDetectorNormalizationConsequences

variable {eqs vars : ℕ}

/-- Literal polynomial source hypotheses select the intended theta
factor at the actual fourth-power phase. The remaining arithmetic input
is irrationality of the actual linear/private controller-frequency ratio.
All seven moment-code means are permitted; row three is not used. -/
theorem detector_thetaOutput_eq_thetaSum
    (parameters : Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → RationalCode)
    (hp : ∀ i, (1 : ℝ) < (parameters i).decode) (I : DQLSystem eqs vars)
    {x : ℝ → Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ}
    (hx : IsIntegralCurve x (fun _ y ↦ PolynomialFieldCode.realize
      (FixedDetectorPolynomialCode.fieldCode parameters I) y))
    (hrec : ForwardRecurrentAt x 0)
    (hvalid : ∀ t, NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue I
      (recoveredState x t) = 0) (j : Fin vars)
    (hρ : Irrational
      (CanonicalFixedDetectorTrajectory.numberFrequency
          parameters I (detectorInitialController x) j /
        CanonicalFixedDetectorTrajectory.omegaFrequency
          parameters (detectorInitialController x) j))
    {μ : ℝ} (hμ : 1 ≤ μ) (B : ℝ)
    (hgrowth : ∀ᶠ H : ℝ in atTop,
      H⁻¹ * (∫ t in (0 : ℝ)..H, (Real.sqrt (HGAS.normSq (x t))) ^ μ) ≤ B)
    (hmeans : ∀ r : Fin FixedDetectorMomentCode.localMomentCount,
      Tendsto (HGAS.Analysis.cesaroMeanAt (fun t ↦
        evalPair (FixedDetectorMomentCode.localMomentCode I j r) (x t))) atTop (𝓝 0)) :
    ∀ t, (recoveredState x t).base.base.gauge j *
        ((recoveredState x t).base.base.source.linked j).jacobi.T1 =
      ∑' n : ℤ, DetectorFactorizedFourier.thetaTerm (1 / 256 : ℝ) I j n
        (detectorPhase I x hvalid t) := by
  let frequency := controllerDetectorTurnsFrequency parameters (detectorInitialController x)
  let phase₀ := detectorPhase I x hvalid 0
  let z := detectorLinkedColumn x j
  let η := characterValue (FixedDetectorMomentCode.unaryFirstHarmonicExponent j)
    (recoveredState x 0).base.base.source.controllers
  have hη : ‖η‖ = 1 := norm_characterValue_eq_one _ _
    (onPhaseCircles_of_validityEnergyValue_eq_zero I _ (hvalid 0))
  have hω := privateAngularFrequency_controllerDetectorTurnsFrequency
    parameters (detectorInitialController x) j
  have hN := linearAngularFrequency_controllerDetectorTurnsFrequency
    parameters (detectorInitialController x) I j
  have hm (r : Fin FixedDetectorMomentCode.localMomentCount) :
      Tendsto (HGAS.Analysis.cesaroMeanAt (fun t ↦
        FixedDetectorMomentCode.localMomentValue I j (recoveredState x t) r)) atTop (𝓝 0) := by
    have hsemantic (t : ℝ) :
        evalPair (FixedDetectorMomentCode.localMomentCode I j r) (x t) =
          FixedDetectorMomentCode.localMomentValue I j (recoveredState x t) r := by
      simpa only [point_recoveredState] using
        FixedDetectorMomentCode.evalPair_localMomentCode I j r (recoveredState x t)
    simpa only [hsemantic] using hmeans r
  have hfirstChar (t : ℝ) : η * HGAS.Analysis.realFrequencyExponential
      (-privateAngularFrequency j frequency) t =
      characterValue (FixedDetectorMomentCode.unaryFirstHarmonicExponent j)
        (recoveredState x t).base.base.source.controllers := by
    rw [detector_character_eq_initial_mul_exponential parameters hp I hx hrec hvalid,
      FixedDetectorSelectorCharacterFrequency.characterFrequency_unaryFirstHarmonicExponent]
    rw [show privateAngularFrequency j frequency = _ from hω]
  have hplusChar (t : ℝ) : jacobiPlusTorusTwist I j phase₀ *
      HGAS.Analysis.realFrequencyExponential
        (-(privateAngularFrequency j frequency + linearAngularFrequency I j frequency)) t =
      characterValue (FixedDetectorMomentCode.jacobiPlusExponent I j)
        (recoveredState x t).base.base.source.controllers := by
    rw [detector_character_eq_initial_mul_exponential parameters hp I hx hrec hvalid,
      FixedDetectorMomentCode.characterFrequency_jacobiPlusExponent]
    dsimp only [jacobiPlusTorusTwist, phase₀, frequency]
    rw [mFourier_detectorPhase, ← jacobiPlusExponent_eq_flattenCharacter, hω, hN]
  have hminusChar (t : ℝ) : jacobiMinusTorusTwist I j phase₀ *
      HGAS.Analysis.realFrequencyExponential
        (-(privateAngularFrequency j frequency - linearAngularFrequency I j frequency)) t =
      characterValue (FixedDetectorMomentCode.jacobiMinusExponent I j)
        (recoveredState x t).base.base.source.controllers := by
    rw [detector_character_eq_initial_mul_exponential parameters hp I hx hrec hvalid,
      FixedDetectorMomentCode.characterFrequency_jacobiMinusExponent]
    dsimp only [jacobiMinusTorusTwist, phase₀, frequency]
    rw [mFourier_detectorPhase, ← jacobiMinusExponent_eq_flattenCharacter, hω, hN]
    congr 2
    ring
  have htrace := gaugedLinkedJacobi_eq_thetaSum_of_forward_means I j frequency phase₀
    (by simpa only [frequency, hω] using detector_omega_ne_zero parameters hp I hx hrec hvalid j)
    (by simpa only [frequency, hω, hN] using hρ)
    (z := z)
    (by simpa only [frequency, hω, hN] using
      detectorLinkedColumn_isScaledTrajectory parameters hp I hx hrec hvalid j)
    (detectorLinkedColumn_forwardRecurrentAt hrec j)
    (detectorLinkedColumn_residual_zero I hvalid j)
    (by simpa [unaryMeanObservable, z, detectorLinkedColumn,
      FixedDetectorMomentCode.localMomentValue] using hm 0)
    (by simpa [rootP4MeanObservable, z, detectorLinkedColumn,
      FixedDetectorMomentCode.localMomentValue] using hm 2)
    η hη
    (by simpa [hfirstChar, z, detectorLinkedColumn,
      FixedDetectorMomentCode.localMomentValue] using hm 1)
    hμ ((2 : ℝ) ^ μ * B)
    (detectorLinkedColumn_growth hx.continuous j (zero_le_one.trans hμ) B hgrowth)
    (fun t ↦ (recoveredState x t).base.base.gauge j)
    (by simpa only [frequency, hω, hN] using
      detector_gauge_hasDerivAt parameters hp I hx hrec hvalid j)
    (by simpa [z, detectorLinkedColumn,
      FixedDetectorMomentCode.localMomentValue] using hm 4)
    (by
      simp_rw [hplusChar]
      simpa [z, detectorLinkedColumn, FixedDetectorMomentCode.localMomentValue, mul_comm]
        using hm 5)
    (by
      simp_rw [hminusChar]
      simpa [z, detectorLinkedColumn, FixedDetectorMomentCode.localMomentValue, mul_comm]
        using hm 6)
  intro t
  rw [detectorPhase_eq_translation parameters hp I hx hrec hvalid t]
  exact htrace t

end Stability.Selection
