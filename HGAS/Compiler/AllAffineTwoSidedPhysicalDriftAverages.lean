import HGAS.Compiler.AllAffineCompactSourceTwoSidedClock
import HGAS.Compiler.AllAffineCompactSourceDrift
import HGAS.Dynamics.PositiveMeanTimeReparametrization
import Mathlib.Tactic

/-!
# Transporting compact drift averages to physical time

The compact drift identity is

```
                g_i(t) = κ a_K(z(t)) h_i(z(t)).
```

If the compact-time average of `g_i` vanishes and the speed average tends
to `c > 0`, division by `κ` followed by the exact clock substitution shows
that the ordinary-time average of `h_i` vanishes along the clock horizons.
This file formalizes that calculation independently of the detector.
-/

namespace HGAS

open _root_.MvPolynomial
open Filter Function Set Topology
open scoped BoundedContinuousFunction

noncomputable section

namespace CompactAccumulatorPipelineCode

namespace AllAffineTwoSidedPhysicalDriftAverages

open AllAffineCompactSourceChart
open AllAffineCompactSourceClock
open AllAffineCompactSourceTwoSidedClock
open AllAffineCompactSourceDrift

variable {n m : ℕ}

variable
  (K : ℕ) (κ : RationalCode)
  (h : Fin m → PolynomialCode n)
  (hh :
    ∀ i,
      MixedCentralPolynomialCode.TermsAffineBlockDegreeLE
        (layout n) (2 * K) (h i))
  (ϕ : Flow ℝ (SourceSpace n m))
  (hinv :
    IsInvariant ϕ (sourceFiniteInteriorSet (m := m) (layout n)))
  (v : FiniteSourceSpace n m)

/-- One uncompactified drift coordinate evaluated along the recovered
affine curve. -/
def affineDriftAlong (i : Fin m) (t : ℝ) : ℝ :=
  eval₂Hom (algebraMap ℚ ℝ)
    (affineCurve ϕ hinv v t)
    (PolynomialCode.decode (h i))

theorem continuous_affineDriftAlong
    (i : Fin m) :
    Continuous (affineDriftAlong h ϕ hinv v i) := by
  have hpoly :=
    MvPolynomial.continuous_eval
      (MvPolynomial.map (algebraMap ℚ ℝ)
        (PolynomialCode.decode (h i)))
  have hcomp :=
    hpoly.comp (continuous_affineCurve ϕ hinv v)
  simpa only [MvPolynomial.eval_map,
    affineDriftAlong] using hcomp

include hh in
/-- On every horizon, the compact drift orbit integral is
`κ` times the speed-weighted affine drift integral. -/
theorem orbitIntegral_finiteDrift_eq
    (i : Fin m) (T : ℝ) :
    Dynamics.orbitIntegral (ϕ.restrict hinv)
        (finiteDriftCoordinateBCF K κ h i) T v =
      (RationalCode.decode κ : ℝ) *
        ∫ t in (0 : ℝ)..T,
          affineDriftAlong h ϕ hinv v i t *
            twoSidedClockWeight K
              (affineCurve ϕ hinv v) t := by
  unfold Dynamics.orbitIntegral
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  change
    finiteDriftCoordinateBCF K κ h i
        ((ϕ.restrict hinv) t v) =
      (RationalCode.decode κ : ℝ) *
        (affineDriftAlong h ϕ hinv v i t *
          twoSidedClockWeight K
            (affineCurve ϕ hinv v) t)
  rw [finiteDriftCoordinateBCF_eq K κ h hh]
  simp only [affineCurve, affineDriftAlong,
    twoSidedClockWeight]
  ring

include hh in
/-- A zero compact-time drift mean gives a zero speed-weighted affine
drift mean, provided the rational accumulator scale is nonzero. -/
theorem weightedDriftAverage_tendsto_zero
    (i : Fin m)
    (hκ : (RationalCode.decode κ : ℝ) ≠ 0)
    (hgeneric :
      Tendsto
        (fun q : ℕ ↦
          Dynamics.integerOrbitAverageObservable
            (ϕ.restrict hinv)
            (finiteDriftCoordinateBCF K κ h i)
            (q + 1) v)
        atTop (𝓝 0)) :
    Tendsto
      (fun q : ℕ ↦
        (positiveIntegerHorizon q)⁻¹ *
          ∫ t in (0 : ℝ)..positiveIntegerHorizon q,
            affineDriftAlong h ϕ hinv v i t *
              twoSidedClockWeight K
                (affineCurve ϕ hinv v) t)
      atTop (𝓝 0) := by
  have hscaled :=
    hgeneric.const_mul
      ((RationalCode.decode κ : ℝ)⁻¹)
  have hscaled' :
      Tendsto
        (fun q : ℕ ↦
          (RationalCode.decode κ : ℝ)⁻¹ *
            Dynamics.integerOrbitAverageObservable
              (ϕ.restrict hinv)
              (finiteDriftCoordinateBCF K κ h i)
              (q + 1) v)
        atTop (𝓝 0) := by
    simpa only [mul_zero] using hscaled
  apply hscaled'.congr'
  exact Eventually.of_forall fun q ↦ by
    change
      (RationalCode.decode κ : ℝ)⁻¹ *
          Dynamics.integerOrbitAverageObservable
            (ϕ.restrict hinv)
            (finiteDriftCoordinateBCF K κ h i)
            (q + 1) v =
        (positiveIntegerHorizon q)⁻¹ *
          ∫ t in (0 : ℝ)..positiveIntegerHorizon q,
            affineDriftAlong h ϕ hinv v i t *
              twoSidedClockWeight K
                (affineCurve ϕ hinv v) t
    rw [Dynamics.integerOrbitAverageObservable_apply]
    simp only [positiveIntegerHorizon, Nat.cast_add,
      Nat.cast_one]
    rw [orbitIntegral_finiteDrift_eq
      K κ h hh ϕ hinv v i]
    field_simp

include hh in
/-- Final clock-substitution statement: zero compact drift mean becomes a
zero ordinary-time drift mean along the unbounded physical clock
horizons. -/
theorem physicalDriftAverage_tendsto_zero
    (i : Fin m)
    (hκ : (RationalCode.decode κ : ℝ) ≠ 0)
    {c : ℝ} (hc : c ≠ 0)
    (hspeed :
      Tendsto
        (fun q : ℕ ↦
          Dynamics.integerOrbitAverageObservable
            (ϕ.restrict hinv) (affineSpeedBCF K)
            (q + 1) v)
        atTop (𝓝 c))
    (hgeneric :
      Tendsto
        (fun q : ℕ ↦
          Dynamics.integerOrbitAverageObservable
            (ϕ.restrict hinv)
            (finiteDriftCoordinateBCF K κ h i)
            (q + 1) v)
        atTop (𝓝 0))
    (hclock :
      PositiveIntegralClock
        (twoSidedClockWeight K
          (affineCurve ϕ hinv v))) :
    Tendsto
      (fun q : ℕ ↦
        (integralClock
          (twoSidedClockWeight K
            (affineCurve ϕ hinv v))
          (positiveIntegerHorizon q))⁻¹ *
          ∫ τ in (0 : ℝ)..
              integralClock
                (twoSidedClockWeight K
                  (affineCurve ϕ hinv v))
                (positiveIntegerHorizon q),
            eval₂Hom (algebraMap ℚ ℝ)
              (AllAffineCompactSourceTwoSidedClock.physicalCurve
                K ϕ hinv v hclock τ)
              (PolynomialCode.decode (h i)))
      atTop (𝓝 0) := by
  let w : ℝ → ℝ :=
    twoSidedClockWeight K
      (affineCurve ϕ hinv v)
  let a : ℝ → ℝ :=
    affineDriftAlong h ϕ hinv v i
  have hspeed' :
      Tendsto
        (fun q : ℕ ↦
          (positiveIntegerHorizon q)⁻¹ *
            integralClock w (positiveIntegerHorizon q))
        atTop (𝓝 c) := by
    have heq :
        (fun q : ℕ ↦
          Dynamics.integerOrbitAverageObservable
            (ϕ.restrict hinv) (affineSpeedBCF K)
            (q + 1) v) =
          fun q : ℕ ↦
            (positiveIntegerHorizon q)⁻¹ *
              integralClock w (positiveIntegerHorizon q) := by
      funext q
      rw [Dynamics.integerOrbitAverageObservable_apply]
      simp only [positiveIntegerHorizon, Nat.cast_add,
        Nat.cast_one]
      symm
      exact congrArg
        (fun r : ℝ ↦ ((q : ℝ) + 1)⁻¹ * r)
        (integralClock_twoSidedWeight_eq_orbitIntegral
          K ϕ hinv v (positiveIntegerHorizon q))
    rw [← heq]
    exact hspeed
  have hweighted :
      Tendsto
        (fun q : ℕ ↦
          (positiveIntegerHorizon q)⁻¹ *
            ∫ t in (0 : ℝ)..positiveIntegerHorizon q,
              a t * w t)
        atTop (𝓝 0) := by
    exact weightedDriftAverage_tendsto_zero
      K κ h hh ϕ hinv v i hκ hgeneric
  have hratio :=
    inverseClockAverage_tendsto_ratio
      hclock (continuous_affineDriftAlong h ϕ hinv v i)
      hc hspeed' hweighted
  simpa only [w, a, affineDriftAlong,
    AllAffineCompactSourceTwoSidedClock.physicalCurve,
    zero_div] using hratio

end AllAffineTwoSidedPhysicalDriftAverages

end CompactAccumulatorPipelineCode

end

end HGAS
