import Stability.Selection.OrdinaryTimeDetectorGraphFlow
import Stability.Selection.OrdinaryTimeDetectorGain
import Stability.Selection.OrdinaryTimeFourierZeroMode

/-!
# Arithmetic vanishing of the literal detector's constant mode

The no-instance Fourier identity gives a bounded primitive along the
zero-phase orbit. Its zero forward mean identifies the actual Haar
coefficient of each scalar polynomial test. The resulting graph primitive
differentiates to the uncentered detector drift at every torus point.
-/

noncomputable section

namespace Stability.Selection

open HGAS HGAS.Analysis HGAS.Clocks Filter Topology MeasureTheory
open CanonicalFixedDetectorFundamentalPhase ObservedTimeChangedControllerPhaseHaar
open NormalizedCorrectedCanonicalDriftFourierFamily

variable {eqs vars : ℕ}

/-- Arithmetic no-instance data imply zero mean on the literal graph's
zero-phase orbit, without assuming any selector mean. -/
theorem detectorGraph_zeroOrbit_driftMean_zero
    (I : DQLSystem eqs vars) (hnot : ¬ I.Solvable)
    (p : Fin (vars + eqs) → ℕ) (hp : ∀ i, (p i).Prime)
    (hinjective : Function.Injective p) (q : Fin (driftCount vars)) :
    Tendsto (fun H : ℝ ↦ H⁻¹ * ∫ t in (0 : ℝ)..H,
      NormalizedCorrectedFixedDetectorDriftCode.driftValue I
        (intendedSourceStateGraph I
          (fun i ↦ ExplicitPositiveControllerEquilibrium.state (p i : ℝ))
          (RadicalClock.torusTranslationFlow
            (ScaledRadicalClock.scaledSignedPrimeSqrtFrequency
              (1 / (2 * Real.pi)) p (fun _ ↦ 1)) t 0)) q) atTop (𝓝 0) := by
  let ω := ScaledRadicalClock.scaledSignedPrimeSqrtFrequency
    (1 / (2 * Real.pi)) p (fun _ ↦ 1)
  let c := coefficient I hnot q
  let e := exponent I hnot q
  have hω : RadicalIndependence.HasNoNontrivialIntegerCharacter ω :=
    ScaledRadicalClock.scaledSignedPrimeSqrtFrequency_hasNoCharacter
      _ (by positivity) p hp hinjective (fun _ ↦ 1) (fun _ ↦ Or.inl rfl)
  have hprimitive : Summable fun i ↦ ‖cohomologicalPrimitiveCoefficient c e ω i‖ :=
    summable_norm_cohomologicalPrimitiveCoefficient_of_radical
      _ (by positivity) p hp hinjective (fun _ ↦ 1) (fun _ ↦ Or.inl rfl) c e
      (coefficient_weighted_summable I hnot p _ q)
  have hf : Continuous (fun t : ℝ ↦
      (torusFourierSeries c e (RadicalClock.torusTranslationFlow ω t 0)).re) :=
    Complex.continuous_re.comp
      ((continuous_torusFourierSeries c e (coefficient_summable I hnot q)).comp
        ((RadicalClock.torusTranslationFlow ω).continuous continuous_id continuous_const))
  have hmean := forwardMean_zero_of_bounded_primitive hf
    (torusCohomologicalPrimitive_re_hasDerivAt_of_zeroMode c e ω hω
      (zeroMode I hnot q) (coefficient_summable I hnot q) hprimitive 0)
    (∑' i, ‖cohomologicalPrimitiveCoefficient c e ω i‖)
    (fun t ↦ (Complex.abs_re_le_norm _).trans
      (norm_torusCohomologicalPrimitive_le c e ω hprimitive _))
  convert hmean using 1
  funext H
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  have h := intendedSourceGraph_zeroOrbit_drift_eq_fourier (primeClockCodes p) I
    (fun i ↦ ExplicitPositiveControllerEquilibrium.state (p i : ℝ))
    (fun i ↦ ExplicitPositiveControllerEquilibrium.state_radiusSq _) hnot t
  rw [positivePrimeController_turnsFrequency p hp] at h
  exact congrFun h q

/-- The constant coefficient is the actual Haar coefficient of the
literal real scalar test, not a coefficient of an alternate expansion. -/
theorem detectorGraph_drift_fourierCoeff_zero
    (I : DQLSystem eqs vars) (hnot : ¬ I.Solvable)
    (p : Fin (vars + eqs) → ℕ) (hp : ∀ i, (p i).Prime)
    (hinjective : Function.Injective p) (q : Fin (driftCount vars)) :
    UnitAddTorus.mFourierCoeff (fun x ↦
      (NormalizedCorrectedFixedDetectorDriftCode.driftValue I
        (intendedSourceStateGraph I
          (fun i ↦ ExplicitPositiveControllerEquilibrium.state (p i : ℝ)) x) q : ℂ)) 0 = 0 := by
  let controller := fun i ↦ ExplicitPositiveControllerEquilibrium.state (p i : ℝ)
  let f := sourcePolynomialFunction I controller (detectorDriftPolynomials I q)
  have hweighted := (sourcePolynomialFunction_weightedFourier_bound I controller
    (fun i ↦ explicitController_coordinates_le_one (p i : ℝ))
    (show 1 ≤ 1 + 1 / (sourceRadiusIndex I : ℝ) from le_add_of_nonneg_right (by positivity))
    (sourceRadiusIndex_bounds I).1 (sourceRadiusIndex_bounds I).2
    (detectorDriftPolynomials I q) (detectorDriftDegree I)
    (detectorDriftPolynomials_degree_le I q)).1
  have hre : (UnitAddTorus.mFourierCoeff (fun x ↦ (f x : ℂ)) 0).re = 0 := by
    apply fourierZeroMode_re_eq_zero_of_forwardMean p hp hinjective (fun _ ↦ 1)
      (fun _ ↦ Or.inl rfl) (sourceRadiusIndex I) (sourceRadiusIndex_pos I) f
      (continuous_sourcePolynomialFunction I controller (detectorDriftPolynomials I q))
      hweighted 0
    simpa only [f, controller, sourcePolynomialFunction_detectorDrift] using
      detectorGraph_zeroOrbit_driftMean_zero I hnot p hp hinjective q
  have him : (UnitAddTorus.mFourierCoeff (fun x ↦ (f x : ℂ)) 0).im = 0 := by
    apply Complex.conj_eq_iff_im.mp
    simpa only [neg_zero] using (fourierCoeff_real_neg f 0).symm
  have hz : UnitAddTorus.mFourierCoeff (fun x ↦ (f x : ℂ)) 0 = 0 :=
    Complex.ext hre him
  simpa only [f, controller, sourcePolynomialFunction_detectorDrift] using hz

/-- The actual bounded primitive solves the uncentered physical-time
drift equation for every initial phase of a no-instance. -/
theorem detectorSourcePrimitive_hasDerivAt_of_not_solvable
    (I : DQLSystem eqs vars) (hnot : ¬ I.Solvable)
    (p : Fin (vars + eqs) → ℕ) (hp : ∀ i, (p i).Prime)
    (hinjective : Function.Injective p)
    (x : UnitAddTorus (Fin (vars + eqs))) (t : ℝ) (q : Fin (driftCount vars)) :
    let ω := ScaledRadicalClock.scaledSignedPrimeSqrtFrequency
      (1 / (2 * Real.pi)) p (fun _ ↦ 1)
    HasDerivAt (fun s ↦ detectorSourcePrimitive I p (RadicalClock.torusTranslationFlow ω s x) q)
      (NormalizedCorrectedFixedDetectorDriftCode.driftValue I
        (intendedSourceStateGraph I
          (fun i ↦ ExplicitPositiveControllerEquilibrium.state (p i : ℝ))
          (RadicalClock.torusTranslationFlow ω t x)) q) t := by
  have h := (detectorSourcePrimitive_resources I p hp hinjective
    (sourceRadiusIndex I) (sourceRadiusIndex_pos I)
    (sourceRadiusIndex_bounds I).1 (sourceRadiusIndex_bounds I).2).2.2 x t q
  simpa only [detectorGraph_drift_fourierCoeff_zero I hnot p hp hinjective q,
    Complex.zero_re, sub_zero] using h

end Stability.Selection
