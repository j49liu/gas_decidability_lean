import Stability.Selection.OrdinaryTimeIntendedOrbit
import Stability.Selection.OrdinaryTimeBoundedPrimitive

/-!
# Ordinary-time test averages on the intended orbit closure

For an unsolvable arithmetic instance, every scalar source test is a
centered Fourier series. Prime-radical estimates give a bounded primitive.
Its compact-time derivative contains exactly the clock speed; inversion
of the positive clock gives zero means at all ordinary real horizons.

This is the averaging step in Section 8, Corollary `cor:yes`.
-/

noncomputable section

namespace Stability.Selection

open HGAS HGAS.Analysis HGAS.Clocks Filter Topology MeasureTheory
open HGAS.NormalizedCorrectedCanonicalOrbitClosureChart
open HGAS.NormalizedCorrectedCanonicalOrbitClosurePhase
open HGAS.Analysis.NormalizedCorrectedCanonicalDriftFourierFamily

variable {eqs vars : ℕ}

/-- Every actual normalized drift coordinate has zero full-horizon mean
on every physical-time orbit in the intended closure of a no-instance.
No recurrence or selector-mean hypothesis is needed for this assertion. -/
theorem intended_physicalCurve_driftMean_zero
    (parameters : Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (controller : Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
      Controller.ControllerState ℝ)
    (hcontroller : ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (hlock : ∀ i, Controller.IsControllerEquilibrium
      (RationalCode.decode (parameters i) : ℝ) (controller i))
    (hnot : ¬ I.Solvable)
    (scale : ℝ) (hscale : scale ≠ 0)
    (p : Fin (vars + eqs) → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p)
    (sign : Fin (vars + eqs) → ℤ) (hsign : ∀ i, sign i = 1 ∨ sign i = -1)
    (hfrequency : CanonicalFixedDetectorFundamentalPhase.turnsFrequency parameters controller =
      ScaledRadicalClock.scaledSignedPrimeSqrtFrequency scale p sign)
    (b : (component parameters I controller).Space) (q : Fin (driftCount vars)) :
    Tendsto (fun H : ℝ ↦ H⁻¹ * ∫ t in (0 : ℝ)..H,
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (physicalCurve parameters I controller hcontroller hlock b t)
        (PolynomialCode.decode (NormalizedCorrectedFixedDetectorDriftCode.driftCode I q)))
      atTop (𝓝 0) := by
  let ω := CanonicalFixedDetectorFundamentalPhase.turnsFrequency parameters controller
  let c := coefficient I hnot q
  let e := exponent I hnot q
  let path : ℝ → UnitAddTorus (Fin (vars + eqs)) := fun s ↦
    phase parameters I controller hcontroller hlock
      ((component parameters I controller).flow s b)
  let w : ℝ → ℝ := fun s ↦ speed parameters I controller hcontroller hlock
    ((component parameters I controller).flow s b)
  let f : ℝ → ℝ := fun s ↦ NormalizedCorrectedFixedDetectorDriftCode.driftValue I
    (rawState parameters I controller hcontroller hlock
      ((component parameters I controller).flow s b)) q
  let F : ℝ → ℝ := fun s ↦ (torusCohomologicalPrimitive c e ω (path s)).re
  have hω : RadicalIndependence.HasNoNontrivialIntegerCharacter ω := by
    dsimp [ω]
    rw [hfrequency]
    exact ScaledRadicalClock.scaledSignedPrimeSqrtFrequency_hasNoCharacter
      scale hscale p hp hinj sign hsign
  have hprimitive : Summable fun i ↦ ‖cohomologicalPrimitiveCoefficient c e ω i‖ := by
    dsimp [ω]
    rw [hfrequency]
    exact summable_norm_cohomologicalPrimitiveCoefficient_of_radical
      scale hscale p hp hinj sign hsign c e
      (coefficient_weighted_summable I hnot p _ q)
  have hf : Continuous f :=
    (continuous_apply q).comp
      ((NormalizedCorrectedCanonicalOrbitClosureModel.continuous_rawDriftValue
        parameters I controller hcontroller hlock).comp
          ((component parameters I controller).flow.continuous continuous_id continuous_const))
  have hfseries (t : ℝ) : f t = (torusFourierSeries c e (path t)).re := by
    exact congrFun (congrFun
      (NormalizedCorrectedCanonicalOrbitClosureModel.rawDriftValue_eq_fourier
        parameters I controller hcontroller hlock hnot)
      ((component parameters I controller).flow t b)) q
  have hF (t : ℝ) : HasDerivAt F (w t * f t) t := by
    rw [hfseries]
    exact torusCohomologicalPrimitive_re_comp_hasDerivAt_timeChanged_of_zeroMode
      c e ω path w 1 zero_le_one
      (fun s ↦ by
        rw [abs_of_pos (speed_pos parameters I controller hcontroller hlock _)]
        exact speed_le_one parameters I controller hcontroller hlock _)
      (mFourier_phase_flow_hasDerivAt parameters I controller hcontroller hlock b)
      hω (zeroMode I hnot q) (coefficient_summable I hnot q) hprimitive t
  have hbound (t : ℝ) : |F t| ≤
      ∑' i, ‖cohomologicalPrimitiveCoefficient c e ω i‖ :=
    (Complex.abs_re_le_norm _).trans
      (norm_torusCohomologicalPrimitive_le c e ω hprimitive (path t))
  have hmean := forwardMean_zero_of_timeChanged_bounded_primitive
    (physicalClock parameters I controller hcontroller hlock b) hf hF _ hbound
  convert hmean using 1
  funext H
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  simpa only [f, rawState, physicalCurve, FixedDetectorPolynomialCode.point_state] using
    (NormalizedCorrectedFixedDetectorDriftCode.eval_driftCode I q
      (FixedDetectorPolynomialCode.state
        (physicalCurve parameters I controller hcontroller hlock b t)))

end Stability.Selection
