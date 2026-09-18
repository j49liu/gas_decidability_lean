import HGAS.Arithmetic.CanonicalFixedDetectorChart
import HGAS.Clocks.LockedControllerPhaseCharacterFormula
import Mathlib.Tactic

/-!
# Exact alignment of the polynomial theta gauge

The preceding trajectory modules show that the compiled gauge and the
analytic half-period multiplier satisfy the correct differential
equations.  For the detector crosswalk we need the stronger literal
identity.  We obtain it by choosing:

* every fundamental phase initially equal to `1`;
* centered elliptic offset `z₀ = 0`; and
* modular height `log(256)/π`.

The unflattened fourth-root character then rotates with frequency

```text
                         (Ω + 2N)/4,
```

while the half-period multiplier has exactly the same phase and the
amplitude `1/4`.  Consequently the compiled polynomial output `G*T₁`
is exactly Jacobi's zero-free `θ₃`, pointwise along the orbit.
-/

namespace HGAS.CanonicalFixedDetectorAlignment

open HGAS
open Modular
open Clocks
open Complex
open Clocks.ControllerPhaseProductCharacterCode

noncomputable section

variable {eqs vars : ℕ}

/-- The unflattened fourth-root character has one quarter of the
flattened `Q*V²` frequency. -/
theorem gaugeRootFrequency_eq
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (j : Fin vars) :
    CanonicalFixedDetectorTrajectory.gaugeRootFrequency
        parameters I controller j =
      (CanonicalFixedDetectorTrajectory.omegaFrequency
          parameters controller j +
        2 *
          CanonicalFixedDetectorTrajectory.numberFrequency
            parameters I controller j) / 4 := by
  unfold CanonicalFixedDetectorTrajectory.gaugeRootFrequency
    Clocks.LockedControllerPhaseTrajectory.characterFrequency
    Clocks.LockedControllerPhaseTrajectory.angularVelocity
    CanonicalFixedDetectorTrajectory.gaugeRootExponent
    CanonicalFixedDetectorTrajectory.omegaFrequency
    CanonicalFixedDetectorTrajectory.numberFrequency
    DetectorJacobiGaugeData.gaugeCharacter
    DetectorCharacterCode.omegaWeights
    DetectorCharacterCode.numberWeights
    ControllerPhaseProductCharacterCode.exponentWeightCode
  simp only [RationalCode.decode_encode, Rat.cast_intCast,
    DetectorCharacterCode.flattenCharacter]
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring

/-- Closed formula for the canonical gauge when all initial fundamental
phases are one. -/
theorem gaugePath_onePhase
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ) (j : Fin vars) :
    CanonicalFixedDetectorTrajectory.gaugePath
        parameters I controller
        Clocks.LockedControllerPhaseTrajectory.onePhase t j =
      ((1 / 4 : ℝ) : ℂ) *
        Complex.exp
          (((((CanonicalFixedDetectorTrajectory.omegaFrequency
                    parameters controller j +
                2 *
                  CanonicalFixedDetectorTrajectory.numberFrequency
                    parameters I controller j) / 4) *
              t : ℝ) : ℂ) *
            Complex.I) := by
  unfold CanonicalFixedDetectorTrajectory.gaugePath
    CanonicalFixedDetectorTrajectory.clockPath
  rw [
    Clocks.LockedControllerPhaseTrajectory.characterValue_onePhase]
  have hfreq :
      Clocks.LockedControllerPhaseTrajectory.characterFrequency
          parameters controller
          (CanonicalFixedDetectorTrajectory.gaugeRootExponent I j) =
        (CanonicalFixedDetectorTrajectory.omegaFrequency
              parameters controller j +
          2 *
            CanonicalFixedDetectorTrajectory.numberFrequency
              parameters I controller j) / 4 := by
    simpa only [
      CanonicalFixedDetectorTrajectory.gaugeRootFrequency] using
      gaugeRootFrequency_eq parameters I controller j
  rw [hfreq]

/-- At the canonical height, the analytic half-period factor is exactly
the compiled fourth-root gauge exponential. -/
theorem halfPeriodGaugeFactor_eq
    (ω N t : ℝ) :
    Complex.exp
        (Real.pi * Complex.I *
          (CanonicalFixedDetectorChart.centeredEllipticPath 0 N t +
            (CanonicalFixedDetectorTrajectory.modularPath
              thetaGaugeBasePoint ω t : ℂ) / 4)) =
      ((1 / 4 : ℝ) : ℂ) *
        Complex.exp
          (((((ω + 2 * N) / 4) * t : ℝ) : ℂ) *
            Complex.I) := by
  rw [show
      (Real.pi : ℂ) * Complex.I *
          (CanonicalFixedDetectorChart.centeredEllipticPath 0 N t +
            (CanonicalFixedDetectorTrajectory.modularPath
              thetaGaugeBasePoint ω t : ℂ) / 4) =
        (((-Real.pi * thetaGaugeHeight / 4 : ℝ) : ℂ)) +
          (((((ω + 2 * N) / 4) * t : ℝ) : ℂ) *
            Complex.I) by
    unfold CanonicalFixedDetectorChart.centeredEllipticPath
      CanonicalFixedDetectorTrajectory.modularPath
      thetaGaugeBasePoint
    push_cast
    field_simp [Real.pi_ne_zero]
    ring_nf
    rw [Complex.I_sq]
    ring]
  rw [Complex.exp_add]
  rw [← Complex.ofReal_exp]
  rw [exp_neg_pi_mul_thetaGaugeHeight_div_four]

/-- The canonical gauge is literally the multiplier in the theta
half-period identity. -/
theorem gaugePath_onePhase_eq_halfPeriodFactor
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ) (j : Fin vars) :
    CanonicalFixedDetectorTrajectory.gaugePath
        parameters I controller
        Clocks.LockedControllerPhaseTrajectory.onePhase t j =
      Complex.exp
        (Real.pi * Complex.I *
          (CanonicalFixedDetectorChart.centeredEllipticPath 0
              (CanonicalFixedDetectorTrajectory.numberFrequency
                parameters I controller j) t +
            (CanonicalFixedDetectorTrajectory.modularPath
              thetaGaugeBasePoint
              (CanonicalFixedDetectorTrajectory.omegaFrequency
                parameters controller j) t : ℂ) / 4)) := by
  rw [halfPeriodGaugeFactor_eq]
  exact gaugePath_onePhase parameters I controller t j

/-- **Exact analytic/polynomial output crosswalk.**

On the fully aligned canonical detector orbit, the literal state
coordinate `G_j*T₁,j` is Jacobi's `θ₃` at the centered elliptic and
modular paths. -/
theorem canonical_thetaOutput_eq_jacobiTheta3
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (rhs₀ : Circle)
    (t : ℝ) (j : Fin vars) :
    let state :=
      CanonicalFixedDetectorTrajectory.fixedDetectorPath
        parameters I controller
        Clocks.LockedControllerPhaseTrajectory.onePhase
        (fun _ ↦
          CanonicalFixedDetectorChart.halfPeriodInitialElliptic
            0 thetaGaugeBasePoint)
        (fun _ ↦ thetaGaugeBasePoint) rhs₀ t
    state.base.base.gauge j *
        (state.base.base.source.linked j).jacobi.T1 =
      jacobiTheta3
        (CanonicalFixedDetectorChart.centeredEllipticPath 0
          (CanonicalFixedDetectorTrajectory.numberFrequency
            parameters I controller j) t)
        (CanonicalFixedDetectorTrajectory.modularPath
          thetaGaugeBasePoint
          (CanonicalFixedDetectorTrajectory.omegaFrequency
            parameters controller j) t : ℂ) := by
  dsimp only [CanonicalFixedDetectorTrajectory.fixedDetectorPath,
    CanonicalFixedDetectorTrajectory.poissonSourcePath,
    CanonicalFixedDetectorTrajectory.gaugeSourcePath,
    CanonicalFixedDetectorTrajectory.linkedSourcePath,
    canonicalControllerLinkedJacobiFamilyPath,
    canonicalLinkedJacobiThetaFamilyMovingPath,
    canonicalLinkedJacobiThetaMovingPath,
    canonicalJacobiThetaMovingPath,
    canonicalJacobiThetaState_T1]
  let ω :=
    CanonicalFixedDetectorTrajectory.omegaFrequency
      parameters controller j
  let N :=
    CanonicalFixedDetectorTrajectory.numberFrequency
      parameters I controller j
  let z :=
    CanonicalFixedDetectorChart.centeredEllipticPath 0 N t
  let τ :=
    CanonicalFixedDetectorTrajectory.modularPath
      thetaGaugeBasePoint ω t
  have hdecomp :
      CanonicalFixedDetectorTrajectory.ellipticPath
          (CanonicalFixedDetectorChart.halfPeriodInitialElliptic
            0 thetaGaugeBasePoint)
          ω N t =
        z + (1 + (τ : ℂ)) / 2 := by
    exact
      CanonicalFixedDetectorChart.ellipticPath_halfPeriod_decomposition
        0 thetaGaugeBasePoint ω N t
  rw [hdecomp]
  rw [gaugePath_onePhase_eq_halfPeriodFactor
    parameters I controller t j]
  exact
    (jacobiTheta3_eq_halfPeriod_jacobiTheta1
      z (τ : ℂ)).symm

end

end HGAS.CanonicalFixedDetectorAlignment
