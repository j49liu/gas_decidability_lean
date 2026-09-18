import HGAS.Arithmetic.FixedDetectorDriftCode
import HGAS.Arithmetic.FixedDetectorJacobiMomentSeries
import HGAS.Arithmetic.FixedDetectorTrajectoryCrosswalk
import HGAS.Modular.LinkedJacobiTrajectoryPolynomialReverseCrosswalk
import Mathlib.Tactic

/-!
# Reverse trajectory crosswalk for the fixed detector

The forward detector crosswalk starts with trajectories for the nested
semantic blocks and produces a trajectory of the final flattened
polynomial field.  Compactification arguments naturally give the
opposite kind of object: an ordinary-time curve in the final Euclidean
coordinate space.

For an arbitrary curve

```text
x : ℝ → Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ
```

this file sets

```text
z(t) = FixedDetectorPolynomialCode.state (x(t)).
```

If `x` solves the literal fixed-detector polynomial ODE, the inverse
`point_state` identity and the ambient realization theorems recover:

* the Poisson-source integral curve;
* the gauge-source integral curve;
* the common controller--linked-Jacobi integral curve;
* the common product-controller integral curve;
* every complex gauge equation;
* every complex reciprocal equation; and
* both real equations of the final right-hand-side oscillator.

No validity, circle, equilibrium, or nonvanishing assumption is required
for this reverse ODE statement.  Such hypotheses enter only in the later
identification with locked Fourier clocks and affine Bloch solutions.
-/

namespace HGAS

open Modular
open Clocks.ControllerPhaseProductCharacterCode

noncomputable section

namespace FixedDetectorReverseTrajectoryCrosswalk

variable {eqs vars : ℕ}

/-- Reassemble the nested semantic state from an arbitrary ordinary-time
Euclidean curve. -/
def recoveredState
    (x :
      ℝ →
        Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (t : ℝ) :
    FixedDetectorPolynomialCode.State eqs vars :=
  FixedDetectorPolynomialCode.state (x t)

@[simp]
theorem point_recoveredState
    (x :
      ℝ →
        Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (t : ℝ) :
    FixedDetectorPolynomialCode.point (recoveredState x t) =
      x t :=
  FixedDetectorPolynomialCode.point_state _

/-- The complete collection of nested trajectory equations recovered
from a flattened fixed-detector trajectory. -/
structure IsStructuredTrajectory
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (x :
      ℝ →
        Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ) :
    Prop where
  full :
    IsIntegralCurve
      (fun t =>
        FixedDetectorPolynomialCode.point (recoveredState x t))
      (fun _ y =>
        PolynomialFieldCode.realize
          (FixedDetectorPolynomialCode.fieldCode parameters I) y)
  poissonSource :
    IsIntegralCurve
      (fun t =>
        DetectorPoissonReciprocalCode.point
          (recoveredState x t).base)
      (fun _ y =>
        PolynomialFieldCode.realize
          (DetectorPoissonReciprocalCode.fieldCode parameters I) y)
  gaugeSource :
    IsIntegralCurve
      (fun t =>
        ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.point
          (recoveredState x t).base.base)
      (fun _ y =>
        PolynomialFieldCode.realize
          (DetectorJacobiGaugeData.fieldCode parameters I) y)
  linkedSource :
    IsIntegralCurve
      (fun t =>
        ControllerProductLinkedJacobiFamilyPolynomialCode.point
          (recoveredState x t).base.base.source)
      (fun _ y =>
        PolynomialFieldCode.realize
          (ControllerProductLinkedJacobiFamilyPolynomialCode.fieldCode
            parameters
            (DetectorCharacterCode.omegaWeights (eqs := eqs))
            (DetectorCharacterCode.numberWeights I)) y)
  controllers :
    IsIntegralCurve
      (fun t =>
        ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint
          (recoveredState x t).base.base.source)
      (fun _ y =>
        PolynomialFieldCode.realize
          (Clocks.ControllerPhaseProductPolynomialCode.fieldCode
            parameters) y)
  gauge :
    ∀ j t,
      HasDerivAt
        (fun s => (recoveredState x s).base.base.gauge j)
        ((ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.vectorField
          parameters
          (DetectorCharacterCode.omegaWeights (eqs := eqs))
          (DetectorCharacterCode.numberWeights I)
          (DetectorJacobiGaugeData.gaugeExponents I)
          (recoveredState x t).base.base).gauge j) t
  reciprocal :
    ∀ k t,
      HasDerivAt
        (fun s => (recoveredState x s).base.reciprocal k)
        ((DetectorPoissonReciprocalCode.vectorField
          parameters I (recoveredState x t).base).reciprocal k) t
  rhs :
    Clocks.RHSOscillatorPolynomialCode.IsOscillatorTrajectory
      (FixedDetectorPolynomialCode.rhsWeightCode I)
      (FixedDetectorPolynomialCode.equationFrequencyCode parameters)
      (fun t =>
        DetectorPoissonReciprocalCode.point
          (recoveredState x t).base)
      (fun t => (recoveredState x t).rhs)

/-- **Reverse layerwise trajectory theorem.**

Every ordinary-time solution of the literal flattened fixed-detector
field canonically determines a structured solution of every compiler
layer. -/
theorem isStructuredTrajectory_of_isIntegralCurve
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (x :
      ℝ →
        Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (hx :
      IsIntegralCurve
        x
        (fun _ y =>
          PolynomialFieldCode.realize
            (FixedDetectorPolynomialCode.fieldCode parameters I) y)) :
    IsStructuredTrajectory parameters I x := by
  let z : ℝ → FixedDetectorPolynomialCode.State eqs vars :=
    recoveredState x
  have hfull :
      IsIntegralCurve
        (fun t => FixedDetectorPolynomialCode.point (z t))
        (fun _ y =>
          PolynomialFieldCode.realize
            (FixedDetectorPolynomialCode.fieldCode parameters I) y) := by
    simpa only [z, point_recoveredState] using hx
  have hcombined :
      IsIntegralCurve
        (fun t =>
          Clocks.RHSOscillatorPolynomialCode.combinedPoint
            (DetectorPoissonReciprocalCode.point (z t).base)
            (z t).rhs)
        (fun _ y =>
          PolynomialFieldCode.realize
            (Clocks.RHSOscillatorPolynomialCode.fieldCode
              (DetectorPoissonReciprocalCode.fieldCode parameters I)
              (FixedDetectorPolynomialCode.rhsWeightCode I)
              (FixedDetectorPolynomialCode.equationFrequencyCode
                parameters)) y) := by
    simpa only [FixedDetectorPolynomialCode.point,
      FixedDetectorPolynomialCode.fieldCode] using hfull
  have hpoisson :
      IsIntegralCurve
        (fun t =>
          DetectorPoissonReciprocalCode.point (z t).base)
        (fun _ y =>
          PolynomialFieldCode.realize
            (DetectorPoissonReciprocalCode.fieldCode parameters I) y) :=
    Clocks.RHSOscillatorPolynomialCode.base_isIntegralCurve_of_combinedPoint
      (DetectorPoissonReciprocalCode.fieldCode parameters I)
      (FixedDetectorPolynomialCode.rhsWeightCode I)
      (FixedDetectorPolynomialCode.equationFrequencyCode parameters)
      (fun t =>
        DetectorPoissonReciprocalCode.point (z t).base)
      (fun t => (z t).rhs)
      hcombined
  have hrhs :
      Clocks.RHSOscillatorPolynomialCode.IsOscillatorTrajectory
        (FixedDetectorPolynomialCode.rhsWeightCode I)
        (FixedDetectorPolynomialCode.equationFrequencyCode parameters)
        (fun t =>
          DetectorPoissonReciprocalCode.point (z t).base)
        (fun t => (z t).rhs) :=
    Clocks.RHSOscillatorPolynomialCode.isOscillatorTrajectory_of_combinedPoint
      (DetectorPoissonReciprocalCode.fieldCode parameters I)
      (FixedDetectorPolynomialCode.rhsWeightCode I)
      (FixedDetectorPolynomialCode.equationFrequencyCode parameters)
      (fun t =>
        DetectorPoissonReciprocalCode.point (z t).base)
      (fun t => (z t).rhs)
      hcombined
  have hrawReciprocal :
      IsIntegralCurve
        (fun t =>
          ComplexReciprocalFamilyPolynomialCode.point
            (DetectorPoissonReciprocalCode.rawState (z t).base))
        (fun _ y =>
          PolynomialFieldCode.realize
            (ComplexReciprocalFamilyPolynomialCode.fieldCode
              (DetectorJacobiGaugeData.fieldCode parameters I)
              (DetectorPoissonReciprocalCode.etaCode (vars := vars))
              (DetectorPoissonReciprocalCode.derivativeBaseCode
                parameters I)) y) := by
    simpa only [DetectorPoissonReciprocalCode.point,
      DetectorPoissonReciprocalCode.fieldCode] using hpoisson
  have hreciprocalSplit :=
    (ComplexReciprocalFamilyPolynomialCode.point_isIntegralCurve_iff
      (DetectorJacobiGaugeData.fieldCode parameters I)
      (DetectorPoissonReciprocalCode.etaCode (vars := vars))
      (DetectorPoissonReciprocalCode.derivativeBaseCode parameters I)
      (fun t =>
        DetectorPoissonReciprocalCode.rawState (z t).base)).mp
      hrawReciprocal
  have hgaugeSource :
      IsIntegralCurve
        (fun t =>
          ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.point
            (z t).base.base)
        (fun _ y =>
          PolynomialFieldCode.realize
            (DetectorJacobiGaugeData.fieldCode parameters I) y) := by
    simpa only [DetectorPoissonReciprocalCode.rawState] using
      hreciprocalSplit.1
  have hreciprocal :
      ∀ k t,
        HasDerivAt
          (fun s => (z s).base.reciprocal k)
          ((DetectorPoissonReciprocalCode.vectorField
            parameters I (z t).base).reciprocal k) t := by
    intro k t
    have hk := hreciprocalSplit.2 k t
    have heta :
        (((RationalCode.decode
          (DetectorPoissonReciprocalCode.etaCode
            (vars := vars) k) : ℝ) : ℂ)) =
          (((1 / 2 : ℝ) : ℂ)) := by
      norm_num [DetectorPoissonReciprocalCode.etaCode]
    simpa only [DetectorPoissonReciprocalCode.rawState,
      DetectorPoissonReciprocalCode.vectorField,
      heta,
      ComplexReciprocalFamilyPolynomialCode.evalObservable,
      ComplexReciprocalPolynomialCode.evalObservable,
      evalPair] using hk
  have hrawGauge :
      IsIntegralCurve
        (fun t =>
          ComplexGaugeFamilyPolynomialCode.point
            (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.rawState
              (z t).base.base))
        (fun _ y =>
          PolynomialFieldCode.realize
            (ComplexGaugeFamilyPolynomialCode.fieldCode
              (ControllerProductLinkedJacobiFamilyPolynomialCode.fieldCode
                parameters
                (DetectorCharacterCode.omegaWeights (eqs := eqs))
                (DetectorCharacterCode.numberWeights I))
              (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.gaugeFrequencyBaseCode
                parameters
                (DetectorJacobiGaugeData.gaugeExponents I))) y) := by
    simpa only [
      ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.point,
      DetectorJacobiGaugeData.fieldCode,
      ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.fieldCode]
      using hgaugeSource
  have hgaugeSplit :=
    (ComplexGaugeFamilyPolynomialCode.point_isIntegralCurve_iff
      (ControllerProductLinkedJacobiFamilyPolynomialCode.fieldCode
        parameters
        (DetectorCharacterCode.omegaWeights (eqs := eqs))
        (DetectorCharacterCode.numberWeights I))
      (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.gaugeFrequencyBaseCode
        parameters
        (DetectorJacobiGaugeData.gaugeExponents I))
      (fun t =>
        ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.rawState
          (z t).base.base)).mp
      hrawGauge
  have hlinkedSource :
      IsIntegralCurve
        (fun t =>
          ControllerProductLinkedJacobiFamilyPolynomialCode.point
            (z t).base.base.source)
        (fun _ y =>
          PolynomialFieldCode.realize
            (ControllerProductLinkedJacobiFamilyPolynomialCode.fieldCode
              parameters
              (DetectorCharacterCode.omegaWeights (eqs := eqs))
              (DetectorCharacterCode.numberWeights I)) y) := by
    simpa only [
      ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.rawState]
      using hgaugeSplit.1
  have hgauge :
      ∀ j t,
        HasDerivAt
          (fun s => (z s).base.base.gauge j)
          ((ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.vectorField
            parameters
            (DetectorCharacterCode.omegaWeights (eqs := eqs))
            (DetectorCharacterCode.numberWeights I)
            (DetectorJacobiGaugeData.gaugeExponents I)
            (z t).base.base).gauge j) t := by
    intro j t
    have hj := hgaugeSplit.2 j t
    simpa only [
      ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.rawState,
      ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.vectorField,
      ComplexGaugeFamilyPolynomialCode.gaugeVelocity,
      ComplexGaugeFamilyPolynomialCode.evalRealObservable,
      ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.eval₂Hom_gaugeFrequencyBaseCode]
      using hj
  have hcontrollers :=
    ControllerProductLinkedJacobiFamilyPolynomialCode.controllers_isIntegralCurve_of_point
      parameters
      (DetectorCharacterCode.omegaWeights (eqs := eqs))
      (DetectorCharacterCode.numberWeights I)
      (fun t => (z t).base.base.source)
      hlinkedSource
  exact {
    full := by simpa only [z] using hfull
    poissonSource := by simpa only [z] using hpoisson
    gaugeSource := by simpa only [z] using hgaugeSource
    linkedSource := by simpa only [z] using hlinkedSource
    controllers := by simpa only [z] using hcontrollers
    gauge := by simpa only [z] using hgauge
    reciprocal := by simpa only [z] using hreciprocal
    rhs := by simpa only [z] using hrhs
  }

/-! ## Dynamic and constant-clock linked blocks -/

/-- Every linked block of the recovered state satisfies all fourteen
complex equations with the instantaneous controller readouts. -/
theorem linkedPoint_hasDerivAt
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (x :
      ℝ →
        Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (h : IsStructuredTrajectory parameters I x)
    (j : Fin vars)
    (i : Fin LinkedJacobiPolynomialCode.dimension)
    (t : ℝ) :
    HasDerivAt
      (fun s =>
        LinkedJacobiPolynomialCode.point
          ((recoveredState x s).base.base.source.linked j) i)
      (LinkedJacobiPolynomialCode.point
        ((ControllerProductLinkedJacobiFamilyPolynomialCode.vectorField
          (fun k =>
            (RationalCode.decode (parameters k) : ℝ))
          (fun a k =>
            (RationalCode.decode
              (DetectorCharacterCode.omegaWeights
                (eqs := eqs) a k) : ℝ))
          (fun a k =>
            (RationalCode.decode
              (DetectorCharacterCode.numberWeights I a k) : ℝ))
          (recoveredState x t).base.base.source).linked j) i) t :=
  ControllerProductLinkedJacobiFamilyPolynomialCode.linkedPoint_hasDerivAt_of_point
    parameters
    (DetectorCharacterCode.omegaWeights (eqs := eqs))
    (DetectorCharacterCode.numberWeights I)
    (fun s => (recoveredState x s).base.base.source)
    h.linkedSource j i t

/-- If the two controller readouts of a selected block are constant, its
ordinary-time curve is a standard scaled linked-Jacobi trajectory. -/
theorem linked_isScaledTrajectory
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (x :
      ℝ →
        Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (h : IsStructuredTrajectory parameters I x)
    (j : Fin vars)
    (κZ κPhi : ℂ)
    (hkappaZ :
      ∀ t,
        ControllerProductLinkedJacobiFamilyPolynomialCode.kappaZ
            (fun a i =>
              (RationalCode.decode
                (DetectorCharacterCode.omegaWeights
                  (eqs := eqs) a i) : ℝ))
            (fun a i =>
              (RationalCode.decode
                (DetectorCharacterCode.numberWeights I a i) : ℝ))
            (fun i =>
              (RationalCode.decode (parameters i) : ℝ))
            (recoveredState x t).base.base.source j =
          κZ)
    (hkappaPhi :
      ∀ t,
        ControllerProductLinkedJacobiFamilyPolynomialCode.kappaPhi
            (fun a i =>
              (RationalCode.decode
                (DetectorCharacterCode.omegaWeights
                  (eqs := eqs) a i) : ℝ))
            (fun i =>
              (RationalCode.decode (parameters i) : ℝ))
            (recoveredState x t).base.base.source j =
          κPhi) :
    IsScaledLinkedJacobiTrajectory
      κZ κPhi
      (fun t =>
        (recoveredState x t).base.base.source.linked j) :=
  ControllerProductLinkedJacobiFamilyPolynomialCode.isScaledLinkedJacobiTrajectory_of_point
    parameters
    (DetectorCharacterCode.omegaWeights (eqs := eqs))
    (DetectorCharacterCode.numberWeights I)
    (fun t => (recoveredState x t).base.base.source)
    h.linkedSource j κZ κPhi hkappaZ hkappaPhi

/-! ## The explicit validity hypothesis -/

/-- Pointwise zero aggregate validity is exactly the conjunction of all
three graph-residual families.  It is intentionally a separate
hypothesis from the reverse ODE theorem. -/
theorem validityEnergy_eq_zero_iff
    (I : DQLSystem eqs vars)
    (x :
      ℝ →
        Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (t : ℝ) :
    FixedDetectorDriftCode.validityEnergyValue I
        (recoveredState x t) = 0 ↔
      (∀ a (r : LinkedJacobiResidualIndex),
          linkedJacobiResidual r
            ((recoveredState x t).base.base.source.linked a) = 0) ∧
        (∀ k,
          MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
            (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.point
              (recoveredState x t).base.base)
            (PolynomialCode.decode
              (DetectorJacobiGaugeData.residualCode
                FixedDetectorValidityEnergyCode.thetaGaugeScale I k)) =
              0) ∧
        ∀ k,
          MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
            (DetectorPoissonReciprocalCode.point
              (recoveredState x t).base)
            (PolynomialCode.decode
              (DetectorPoissonReciprocalCode.residualCode I k)) = 0 :=
  FixedDetectorDriftCode.validityEnergyValue_eq_zero_iff
    I (recoveredState x t)

end FixedDetectorReverseTrajectoryCrosswalk

end

end HGAS
