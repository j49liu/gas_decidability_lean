import Stability.Selection.OrdinaryTimeIntendedAverages
import HGAS.Clocks.ExplicitPositiveControllerEquilibrium

/-!
# Recurrent prime-source trajectories passing all tests

An unsolvable DQL instance has an actual complete, bounded, valid,
forward-recurrent trajectory of the prime-clock source field whose every
scalar test has zero full ordinary-time average. The controller states,
return sequence, and test means are conclusions, not additional inputs.

This is the existence direction of Section 8, Corollary `cor:yes`, realized
on the closure of the explicit canonical orbit.
-/

noncomputable section

namespace Stability.Selection

open HGAS HGAS.Analysis HGAS.Clocks Filter Topology MeasureTheory
open HGAS.NormalizedCorrectedCanonicalOrbitClosureChart
open HGAS.Clocks.ObservedTimeChangedControllerPhaseHaar

/-- A uniform Euclidean bound controls every nonnegative real growth
moment, at each positive real horizon. -/
theorem forwardGrowth_le_of_normSq_le
    {n : ℕ} {x : ℝ → Fin n → ℝ} (hx : Continuous x)
    {C : ℝ} (hbound : ∀ t, normSq (x t) ≤ C) {μ : ℝ} (hμ : 0 ≤ μ)
    {H : ℝ} (hH : 0 < H) :
    H⁻¹ * (∫ t in (0 : ℝ)..H, (Real.sqrt (normSq (x t))) ^ μ) ≤
      (Real.sqrt C) ^ μ := by
  have hnormSq : Continuous (fun t ↦ normSq (x t)) := by
    unfold normSq dot
    fun_prop
  have hc := (Real.continuous_rpow_const hμ).comp hnormSq.sqrt
  have hint : (∫ t in (0 : ℝ)..H, (Real.sqrt (normSq (x t))) ^ μ) ≤
      H * (Real.sqrt C) ^ μ := by
    have h := intervalIntegral.integral_mono_on (μ := volume) hH.le
      (hc.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _) (fun t _ ↦
        Real.rpow_le_rpow (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt (hbound t)) hμ)
    simpa using h
  calc
    _ ≤ H⁻¹ * (H * (Real.sqrt C) ^ μ) :=
      mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hH.le)
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hH.ne', one_mul]

variable {eqs vars : ℕ}

/-- Concrete prime controllers and the canonical orbit closure furnish a
complete source trajectory passing every actual normalized scalar test.
The statement permits zero linear columns because it uses their correctly
centered compiled tests. -/
theorem exists_prime_source_trajectory_of_not_solvable
    (p : Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (I : DQLSystem eqs vars) (hnot : ¬ I.Solvable) :
    ∃ x : ℝ → Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ,
      IsIntegralCurve x (fun _ y ↦ PolynomialFieldCode.realize
        (FixedDetectorPolynomialCode.fieldCode (primeClockCodes p) I) y) ∧
      ForwardRecurrentAt x 0 ∧
      (∀ t, NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue I
        (FixedDetectorReverseTrajectoryCrosswalk.recoveredState x t) = 0) ∧
      (∀ t, normSq (x t) ≤
        CanonicalFixedDetectorRawOrbitBound.canonicalRawNormSqBound eqs vars) ∧
      ∀ q : Fin (NormalizedCorrectedFixedDetectorDriftCode.driftCount vars),
        Tendsto (fun H : ℝ ↦ H⁻¹ * ∫ t in (0 : ℝ)..H,
          MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) (x t)
            (PolynomialCode.decode (NormalizedCorrectedFixedDetectorDriftCode.driftCode I q)))
          atTop (𝓝 0) := by
  let controller : Fin (vars + eqs) → Controller.ControllerState ℝ :=
    fun i ↦ ExplicitPositiveControllerEquilibrium.state (p i : ℝ)
  have hunit : ∀ i, Controller.controllerRadiusSq (controller i) = 1 :=
    fun i ↦ ExplicitPositiveControllerEquilibrium.state_radiusSq _
  have heq : ∀ i, Controller.IsControllerEquilibrium (p i : ℝ) (controller i) := by
    intro i
    exact ExplicitPositiveControllerEquilibrium.state_isControllerEquilibrium _
      (by exact_mod_cast (hp i).one_lt)
  have hlock : ∀ i, Controller.IsControllerEquilibrium
      (RationalCode.decode (primeClockCodes p i) : ℝ) (controller i) := by
    simpa only [decode_primeClockCodes] using heq
  obtain ⟨sign, hsign, hfreq⟩ :=
    RadicalClock.exists_signs_for_primeControllerEquilibria p controller hunit heq
  obtain ⟨b, hb⟩ := exists_intended_recurrent_physicalCurve
    (primeClockCodes p) I controller hunit hlock
  refine ⟨physicalCurve (primeClockCodes p) I controller hunit hlock b,
    physicalCurve_isIntegralCurve (primeClockCodes p) I controller hunit hlock b, hb,
    intended_physicalCurve_valid (primeClockCodes p) I controller hunit hlock b,
    intended_physicalCurve_normSq_le (primeClockCodes p) I controller hunit hlock b, ?_⟩
  intro q
  exact intended_physicalCurve_driftMean_zero (primeClockCodes p) I controller hunit hlock
    hnot (1 / (2 * Real.pi)) (by positivity) p hp hinj sign hsign
    (CanonicalFixedDetectorFundamentalPhase.turnsFrequency_primeClockCodes_eq_scaledRadical
      p controller sign hfreq) b q

end Stability.Selection
