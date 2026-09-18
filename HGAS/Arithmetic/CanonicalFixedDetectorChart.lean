import HGAS.Arithmetic.CanonicalFixedDetectorGraph
import HGAS.Modular.CanonicalThetaGaugeHeight
import HGAS.Modular.JacobiThetaVectorNonvanishing
import Mathlib.Tactic

/-!
# An explicit global theta chart for the canonical detector orbit

The canonical linked-Jacobi compiler stores the reciprocal of `θ₁`, so
its explicit analytic trajectory must remain in the chart `θ₁ ≠ 0`.
This file discharges that condition from transparent initial data.

Choose an upper-half-plane point `τ₀` with imaginary part at least `4/5`
and a real elliptic offset `z₀`.  Initialize the stored odd theta
coordinate at the opposite half-period

```text
                    ξ₀ = z₀ + (1 + τ₀)/2.
```

The detector velocities then preserve the decomposition

```text
             ξ(t) = z(t) + (1 + τ(t))/2,
             z(t) = z₀ + N t/(2π).
```

Thus `z(t)` stays real and `Im τ(t)=Im τ₀`.  The quantitative central-strip
estimate proves `θ₃(z(t)|τ(t)) ≠ 0`; the exact half-period identity

```text
 θ₃(z|τ) = exp(π i (z + τ/4)) θ₁(z + (1+τ)/2 | τ)
```

then proves `θ₁(ξ(t)|τ(t)) ≠ 0` for all real time.  The final two theorems
feed this fact directly into the exact polynomial integral-curve and
validity-energy statements.
-/

namespace HGAS.CanonicalFixedDetectorChart

open HGAS
open Modular
open Complex
open Clocks

noncomputable section

variable {eqs vars : ℕ}

/-- The real-direction path left after subtracting the moving
half-period from the detector's elliptic parameter. -/
def centeredEllipticPath
    (z₀ : ℂ) (N : ℝ) (t : ℝ) : ℂ :=
  z₀ + Complex.ofReal ((N / (2 * Real.pi)) * t)

/-- Initial elliptic parameter at the opposite half-period. -/
def halfPeriodInitialElliptic
    (z₀ : ℂ) (τ₀ : UpperHalfPlane) : ℂ :=
  z₀ + (1 + (τ₀ : ℂ)) / 2

/-- The affine detector paths preserve the half-period decomposition
exactly. -/
theorem ellipticPath_halfPeriod_decomposition
    (z₀ : ℂ) (τ₀ : UpperHalfPlane)
    (ω N t : ℝ) :
    CanonicalFixedDetectorTrajectory.ellipticPath
        (halfPeriodInitialElliptic z₀ τ₀) ω N t =
      centeredEllipticPath z₀ N t +
        (1 +
          (CanonicalFixedDetectorTrajectory.modularPath
            τ₀ ω t : ℂ)) / 2 := by
  unfold halfPeriodInitialElliptic centeredEllipticPath
  unfold CanonicalFixedDetectorTrajectory.ellipticPath
    CanonicalFixedDetectorTrajectory.modularPath
  push_cast
  ring

@[simp]
theorem centeredEllipticPath_im
    (z₀ : ℂ) (N t : ℝ) :
    (centeredEllipticPath z₀ N t).im = z₀.im := by
  change
    (z₀ + Complex.ofReal ((N / (2 * Real.pi)) * t)).im =
      z₀.im
  rw [Complex.add_im, Complex.ofReal_im, add_zero]

@[simp]
theorem modularPath_im
    (τ₀ : UpperHalfPlane) (ω t : ℝ) :
    (CanonicalFixedDetectorTrajectory.modularPath
      τ₀ ω t : ℂ).im = τ₀.im := by
  simp [CanonicalFixedDetectorTrajectory.modularPath]

/-- The canonical odd theta coordinate never leaves its reciprocal chart
when initialized at a real opposite-half-period and at sufficient cusp
height. -/
theorem jacobiTheta1_ellipticPath_ne_zero
    (z₀ : ℂ) (τ₀ : UpperHalfPlane)
    (ω N t : ℝ)
    (hz₀ : z₀.im = 0)
    (hτ₀ : 4 / 5 ≤ τ₀.im) :
    jacobiTheta1
        (CanonicalFixedDetectorTrajectory.ellipticPath
          (halfPeriodInitialElliptic z₀ τ₀) ω N t)
        (CanonicalFixedDetectorTrajectory.modularPath
          τ₀ ω t : ℂ) ≠
      0 := by
  let z := centeredEllipticPath z₀ N t
  let τ :=
    CanonicalFixedDetectorTrajectory.modularPath τ₀ ω t
  have hτ : 4 / 5 ≤ (τ : ℂ).im := by
    rw [show (τ : ℂ).im = τ₀.im by
      exact modularPath_im τ₀ ω t]
    exact hτ₀
  have hz : |z.im| ≤ (τ : ℂ).im / 4 := by
    rw [show z.im = z₀.im by
      exact centeredEllipticPath_im z₀ N t]
    rw [hz₀, abs_zero]
    positivity
  have htheta3 : jacobiTheta3 z (τ : ℂ) ≠ 0 := by
    exact
      jacobiTheta₂_ne_zero_of_im_large_of_im_centered
        hτ hz
  intro htheta1
  have hhalf :=
    jacobiTheta3_eq_halfPeriod_jacobiTheta1 z (τ : ℂ)
  have hpath :
      CanonicalFixedDetectorTrajectory.ellipticPath
          (halfPeriodInitialElliptic z₀ τ₀) ω N t =
        z + (1 + (τ : ℂ)) / 2 := by
    exact ellipticPath_halfPeriod_decomposition z₀ τ₀ ω N t
  rw [← hpath, htheta1, mul_zero] at hhalf
  exact htheta3 hhalf

/-- Family form of the global chart theorem, with the frequencies filled
by the exact DQL detector readouts. -/
theorem detectorChart_nonvanishing
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (z₀ : Fin vars → ℂ)
    (τ₀ : Fin vars → UpperHalfPlane)
    (hz₀ : ∀ j, (z₀ j).im = 0)
    (hτ₀ : ∀ j, 4 / 5 ≤ (τ₀ j).im) :
    ∀ j t,
      jacobiTheta1
        (CanonicalFixedDetectorTrajectory.ellipticPath
          (halfPeriodInitialElliptic (z₀ j) (τ₀ j))
          (CanonicalFixedDetectorTrajectory.omegaFrequency
            parameters controller j)
          (CanonicalFixedDetectorTrajectory.numberFrequency
            parameters I controller j) t)
        (CanonicalFixedDetectorTrajectory.modularPath
          (τ₀ j)
          (CanonicalFixedDetectorTrajectory.omegaFrequency
            parameters controller j) t : ℂ) ≠
      0 := by
  intro j t
  exact jacobiTheta1_ellipticPath_ne_zero
    (z₀ j) (τ₀ j)
    (CanonicalFixedDetectorTrajectory.omegaFrequency
      parameters controller j)
    (CanonicalFixedDetectorTrajectory.numberFrequency
      parameters I controller j)
    t (hz₀ j) (hτ₀ j)

/-- Fully canonical specialization: zero centered elliptic offsets and
the exact rational-gauge height `log(256)/π`. -/
theorem canonicalDetectorChart_nonvanishing
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ) :
    ∀ j t,
      jacobiTheta1
        (CanonicalFixedDetectorTrajectory.ellipticPath
          (halfPeriodInitialElliptic 0 thetaGaugeBasePoint)
          (CanonicalFixedDetectorTrajectory.omegaFrequency
            parameters controller j)
          (CanonicalFixedDetectorTrajectory.numberFrequency
            parameters I controller j) t)
        (CanonicalFixedDetectorTrajectory.modularPath
          thetaGaugeBasePoint
          (CanonicalFixedDetectorTrajectory.omegaFrequency
            parameters controller j) t : ℂ) ≠
      0 := by
  exact
    detectorChart_nonvanishing
      parameters I controller
      (fun _ ↦ 0)
      (fun _ ↦ thetaGaugeBasePoint)
      (by intro j; simp)
      (by
        intro j
        exact thetaGaugeBasePoint_im_ge_four_fifths)

/-- Explicit chart-safe canonical detector orbit for every locked
controller family. -/
theorem fixedDetectorPath_point_isIntegralCurve
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Circle)
    (z₀ : Fin vars → ℂ)
    (τ₀ : Fin vars → UpperHalfPlane)
    (rhs₀ : Circle)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i))
    (hz₀ : ∀ j, (z₀ j).im = 0)
    (hτ₀ : ∀ j, 4 / 5 ≤ (τ₀ j).im) :
    IsIntegralCurve
      (fun t =>
        FixedDetectorPolynomialCode.point
          (CanonicalFixedDetectorTrajectory.fixedDetectorPath
            parameters I controller phase₀
            (fun j ↦ halfPeriodInitialElliptic (z₀ j) (τ₀ j))
            τ₀ rhs₀ t))
      (fun _ x =>
        PolynomialFieldCode.realize
          (FixedDetectorPolynomialCode.fieldCode parameters I) x) := by
  exact
    CanonicalFixedDetectorTrajectory.fixedDetectorPath_point_isIntegralCurve
      parameters I controller phase₀
      (fun j ↦ halfPeriodInitialElliptic (z₀ j) (τ₀ j))
      τ₀ rhs₀ hlock
      (detectorChart_nonvanishing
        parameters I controller z₀ τ₀ hz₀ hτ₀)

/-- The same explicit chart-safe orbit lies pointwise on every algebraic
validity graph, hence has zero aggregate validity drift. -/
theorem fixedDetectorPath_validityEnergyValue_eq_zero
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Circle)
    (z₀ : Fin vars → ℂ)
    (τ₀ : Fin vars → UpperHalfPlane)
    (rhs₀ : Circle)
    (hz₀ : ∀ j, (z₀ j).im = 0)
    (hτ₀ : ∀ j, 4 / 5 ≤ (τ₀ j).im)
    (t : ℝ) :
    FixedDetectorDriftCode.validityEnergyValue I
        (CanonicalFixedDetectorTrajectory.fixedDetectorPath
          parameters I controller phase₀
          (fun j ↦ halfPeriodInitialElliptic (z₀ j) (τ₀ j))
          τ₀ rhs₀ t) =
      0 := by
  exact
    CanonicalFixedDetectorGraph.fixedDetectorPath_validityEnergyValue_eq_zero
      parameters I controller phase₀
      (fun j ↦ halfPeriodInitialElliptic (z₀ j) (τ₀ j))
      τ₀ rhs₀
      (detectorChart_nonvanishing
        parameters I controller z₀ τ₀ hz₀ hτ₀)
      t

/-- The completely canonical chart-safe orbit, using zero centered
offsets and the exact theta-gauge height, is an integral curve. -/
theorem canonicalFixedDetectorPath_point_isIntegralCurve
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Circle)
    (rhs₀ : Circle)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i)) :
    IsIntegralCurve
      (fun t =>
        FixedDetectorPolynomialCode.point
          (CanonicalFixedDetectorTrajectory.fixedDetectorPath
            parameters I controller phase₀
            (fun _ ↦
              halfPeriodInitialElliptic 0 thetaGaugeBasePoint)
            (fun _ ↦ thetaGaugeBasePoint) rhs₀ t))
      (fun _ x =>
        PolynomialFieldCode.realize
          (FixedDetectorPolynomialCode.fieldCode parameters I) x) := by
  exact
    fixedDetectorPath_point_isIntegralCurve
      parameters I controller phase₀
      (fun _ ↦ 0)
      (fun _ ↦ thetaGaugeBasePoint)
      rhs₀ hlock
      (by intro j; simp)
      (by
        intro j
        exact thetaGaugeBasePoint_im_ge_four_fifths)

/-- The completely canonical chart-safe orbit has zero validity energy
at every time. -/
theorem canonicalFixedDetectorPath_validityEnergyValue_eq_zero
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Circle)
    (rhs₀ : Circle)
    (t : ℝ) :
    FixedDetectorDriftCode.validityEnergyValue I
        (CanonicalFixedDetectorTrajectory.fixedDetectorPath
          parameters I controller phase₀
          (fun _ ↦
            halfPeriodInitialElliptic 0 thetaGaugeBasePoint)
          (fun _ ↦ thetaGaugeBasePoint) rhs₀ t) =
      0 := by
  exact
    fixedDetectorPath_validityEnergyValue_eq_zero
      parameters I controller phase₀
      (fun _ ↦ 0)
      (fun _ ↦ thetaGaugeBasePoint)
      rhs₀
      (by intro j; simp)
      (by
        intro j
        exact thetaGaugeBasePoint_im_ge_four_fifths)
      t

end

end HGAS.CanonicalFixedDetectorChart
