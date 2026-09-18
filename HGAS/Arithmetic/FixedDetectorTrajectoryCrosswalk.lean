import HGAS.Compiler.PolynomialExtensionTrajectoryCrosswalk
import HGAS.Modular.LinkedJacobiTrajectoryPolynomialCrosswalk
import HGAS.Arithmetic.FixedDetectorPolynomialCode
import Mathlib.Tactic

/-!
# Trajectory crosswalk for the complete fixed detector

The fixed detector is built in four nested polynomial layers:

1. a common controller product coupled to linked unary--Jacobi blocks;
2. one fourth-root gauge for each Jacobi block;
3. two Poisson reciprocals for each arithmetic variable; and
4. the right-hand-side phase oscillator.

Each compiler already has an exact pointwise realization theorem.  This
file proves the complementary dynamical statement: coordinatewise
solutions of the scalar equations assemble into an integral curve of the
literal final polynomial field.  The argument is layerwise, matching both
the written construction and the nesting of the structured Lean states.
-/

namespace HGAS

open Modular

noncomputable section

/-! ## Gauge-completed linked families -/

namespace Modular.ControllerProductLinkedJacobiGaugeFamilyPolynomialCode

variable {q b : ℕ}

/-- Lift an integral curve of the controller--linked source through all
fourth-root gauge equations. -/
theorem point_isIntegralCurve
    (parameters : Fin q → RationalCode)
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode)
    (gaugeExponents : Fin b → Fin q → ℤ)
    (z :
      ℝ →
        ControllerProductLinkedJacobiGaugeFamilyState q b)
    (hsource :
      IsIntegralCurve
        (fun t =>
          ControllerProductLinkedJacobiFamilyPolynomialCode.point
            (z t).source)
        (fun _ x =>
          PolynomialFieldCode.realize
            (ControllerProductLinkedJacobiFamilyPolynomialCode.fieldCode
              parameters omegaWeights numberWeights) x))
    (hgauge :
      ∀ a t,
        HasDerivAt
          (fun s => (z s).gauge a)
          ((vectorField parameters omegaWeights numberWeights
            gaugeExponents (z t)).gauge a) t) :
    IsIntegralCurve
      (fun t => point (z t))
      (fun _ x =>
        PolynomialFieldCode.realize
          (fieldCode parameters omegaWeights numberWeights
            gaugeExponents) x) := by
  have h :=
    ComplexGaugeFamilyPolynomialCode.point_isIntegralCurve
      (ControllerProductLinkedJacobiFamilyPolynomialCode.fieldCode
        parameters omegaWeights numberWeights)
      (gaugeFrequencyBaseCode parameters gaugeExponents)
      (fun t => rawState (z t))
      hsource
  apply h
  intro a t
  simpa only [rawState, vectorField,
    ComplexGaugeFamilyPolynomialCode.gaugeVelocity,
    ComplexGaugeFamilyPolynomialCode.evalRealObservable,
    eval₂Hom_gaugeFrequencyBaseCode] using
    hgauge a t

end Modular.ControllerProductLinkedJacobiGaugeFamilyPolynomialCode

/-! ## Detector Poisson reciprocals -/

namespace DetectorPoissonReciprocalCode

variable {eqs vars : ℕ}

/-- Lift a gauge-completed detector source trajectory through every
positive and negative Poisson reciprocal equation. -/
theorem point_isIntegralCurve
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (z : ℝ → State eqs vars)
    (hbase :
      IsIntegralCurve
        (fun t =>
          ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.point
            (z t).base)
        (fun _ x =>
          PolynomialFieldCode.realize
            (DetectorJacobiGaugeData.fieldCode parameters I) x))
    (hreciprocal :
      ∀ k t,
        HasDerivAt
          (fun s => (z s).reciprocal k)
          ((vectorField parameters I (z t)).reciprocal k) t) :
    IsIntegralCurve
      (fun t => point (z t))
      (fun _ x =>
        PolynomialFieldCode.realize
          (fieldCode parameters I) x) := by
  have h :=
    ComplexReciprocalFamilyPolynomialCode.point_isIntegralCurve
      (DetectorJacobiGaugeData.fieldCode parameters I)
      (etaCode (vars := vars))
      (derivativeBaseCode parameters I)
      (fun t => rawState (z t))
      hbase
  apply h
  intro k t
  have heval :
      ComplexReciprocalFamilyPolynomialCode.evalObservable
          (derivativeBaseCode parameters I k)
          (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.point
            (z t).base) =
        Clocks.ControllerPhaseProductCharacterCode.evalPair
          (derivativeBaseCode parameters I k)
          (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.point
            (z t).base) :=
    rfl
  have heta :
      (((RationalCode.decode
          (etaCode (vars := vars) k) : ℝ) : ℂ)) =
        (((1 / 2 : ℝ) : ℂ)) := by
    norm_num [etaCode]
  simpa only [rawState, vectorField,
    heval, heta,
    evalPair_derivativeBaseCode] using
    hreciprocal k t

end DetectorPoissonReciprocalCode

/-! ## Right-hand-side oscillator -/

namespace FixedDetectorPolynomialCode

variable {eqs vars : ℕ}

/-- Lift a complete Poisson-source trajectory through the final
right-hand-side oscillator. -/
theorem point_isIntegralCurve
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (z : ℝ → State eqs vars)
    (hbase :
      IsIntegralCurve
        (fun t =>
          DetectorPoissonReciprocalCode.point (z t).base)
        (fun _ x =>
          PolynomialFieldCode.realize
            (DetectorPoissonReciprocalCode.fieldCode
              parameters I) x))
    (hrhs :
      Clocks.RHSOscillatorPolynomialCode.IsOscillatorTrajectory
        (rhsWeightCode I)
        (equationFrequencyCode parameters)
        (fun t =>
          DetectorPoissonReciprocalCode.point (z t).base)
        (fun t => (z t).rhs)) :
    IsIntegralCurve
      (fun t => point (z t))
      (fun _ x =>
        PolynomialFieldCode.realize
          (fieldCode parameters I) x) := by
  simpa only [point, fieldCode] using
    Clocks.RHSOscillatorPolynomialCode.combinedPoint_isIntegralCurve
      (DetectorPoissonReciprocalCode.fieldCode parameters I)
      (rhsWeightCode I)
      (equationFrequencyCode parameters)
      (fun t =>
        DetectorPoissonReciprocalCode.point (z t).base)
      (fun t => (z t).rhs)
      hbase hrhs

/-! ## The whole nested state -/

/-- **Full layerwise trajectory theorem for the fixed detector.**

It is enough to verify exactly four interfaces:

* the innermost controller--linked path follows its compiler;
* every fourth-root gauge follows its complex scalar equation;
* every Poisson reciprocal follows its complex Riccati equation; and
* the final RHS phase follows its two real oscillator equations.

The conclusion concerns the literal flattened polynomial code, not merely
the structured semantic vector field. -/
theorem point_isIntegralCurve_of_layerwise
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (z : ℝ → State eqs vars)
    (hsource :
      IsIntegralCurve
        (fun t =>
          ControllerProductLinkedJacobiFamilyPolynomialCode.point
            (z t).base.base.source)
        (fun _ x =>
          PolynomialFieldCode.realize
            (ControllerProductLinkedJacobiFamilyPolynomialCode.fieldCode
              parameters
              (DetectorCharacterCode.omegaWeights (eqs := eqs))
              (DetectorCharacterCode.numberWeights I)) x))
    (hgauge :
      ∀ j t,
        HasDerivAt
          (fun s => (z s).base.base.gauge j)
          ((ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.vectorField
            parameters
            (DetectorCharacterCode.omegaWeights (eqs := eqs))
            (DetectorCharacterCode.numberWeights I)
            (DetectorJacobiGaugeData.gaugeExponents I)
            (z t).base.base).gauge j) t)
    (hreciprocal :
      ∀ k t,
        HasDerivAt
          (fun s => (z s).base.reciprocal k)
          ((DetectorPoissonReciprocalCode.vectorField
            parameters I (z t).base).reciprocal k) t)
    (hrhs :
      Clocks.RHSOscillatorPolynomialCode.IsOscillatorTrajectory
        (rhsWeightCode I)
        (equationFrequencyCode parameters)
        (fun t =>
          DetectorPoissonReciprocalCode.point (z t).base)
        (fun t => (z t).rhs)) :
    IsIntegralCurve
      (fun t => point (z t))
      (fun _ x =>
        PolynomialFieldCode.realize
          (fieldCode parameters I) x) := by
  have hgaugeLayer :
      IsIntegralCurve
        (fun t =>
          ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.point
            (z t).base.base)
        (fun _ x =>
          PolynomialFieldCode.realize
            (DetectorJacobiGaugeData.fieldCode parameters I) x) := by
    exact
      ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.point_isIntegralCurve
        parameters
        (DetectorCharacterCode.omegaWeights (eqs := eqs))
        (DetectorCharacterCode.numberWeights I)
        (DetectorJacobiGaugeData.gaugeExponents I)
        (fun t => (z t).base.base)
        hsource hgauge
  have hreciprocalLayer :
      IsIntegralCurve
        (fun t =>
          DetectorPoissonReciprocalCode.point (z t).base)
        (fun _ x =>
          PolynomialFieldCode.realize
            (DetectorPoissonReciprocalCode.fieldCode
              parameters I) x) := by
    exact
      DetectorPoissonReciprocalCode.point_isIntegralCurve
        parameters I (fun t => (z t).base)
        hgaugeLayer hreciprocal
  exact
    point_isIntegralCurve
      parameters I z hreciprocalLayer hrhs

end FixedDetectorPolynomialCode

end

end HGAS
