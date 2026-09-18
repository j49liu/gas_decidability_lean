import HGAS.Arithmetic.FixedDetectorCompactSourceTrajectory
import HGAS.Arithmetic.FixedDetectorReverseTrajectoryCrosswalk
import HGAS.Compiler.PolynomialExtensionPointwiseReverseCrosswalk
import HGAS.Modular.LinkedJacobiPointwiseTrajectoryReverseCrosswalk
import Mathlib.Tactic

/-!
# Reverse crosswalk for forward fixed-detector trajectories

The physical trajectory produced by compact-source time change is an
`IsForwardTrajectory`.  Its values at negative ordinary times are a
constant extension used only to make the clock a total function; they do
not solve the physical polynomial ODE, nor are they required to.

This file gives the exact forward-time reverse interface.  At every
strictly positive time, the one-sided derivative supplied on `Set.Ici 0`
is an ordinary derivative.  Projecting that derivative through the
compiler recovers, at that time:

* the Poisson-source equation;
* the gauge-source equation;
* the common linked-Jacobi/controller equation;
* the product-controller equation;
* every complex gauge equation;
* every complex reciprocal equation; and
* both coordinates of the final right-hand-side oscillator.

The original `IsForwardTrajectory` is retained in the bundled result, so
the right derivative at time zero remains available as a
`HasDerivWithinAt` statement.  No equation at negative time is asserted.
-/

namespace HGAS

open Set
open Modular
open Clocks.ControllerPhaseProductCharacterCode

noncomputable section

namespace FixedDetectorForwardTrajectoryReverseCrosswalk

variable {eqs vars : ℕ}

open FixedDetectorReverseTrajectoryCrosswalk

/-- All semantic compiler equations recovered at one fixed time. -/
structure IsStructuredAt
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (x :
      ℝ →
        Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (t : ℝ) : Prop where
  full :
    HasDerivAt
      (fun s =>
        FixedDetectorPolynomialCode.point (recoveredState x s))
      (PolynomialFieldCode.realize
        (FixedDetectorPolynomialCode.fieldCode parameters I)
        (FixedDetectorPolynomialCode.point (recoveredState x t))) t
  poissonSource :
    HasDerivAt
      (fun s =>
        DetectorPoissonReciprocalCode.point
          (recoveredState x s).base)
      (PolynomialFieldCode.realize
        (DetectorPoissonReciprocalCode.fieldCode parameters I)
        (DetectorPoissonReciprocalCode.point
          (recoveredState x t).base)) t
  gaugeSource :
    HasDerivAt
      (fun s =>
        ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.point
          (recoveredState x s).base.base)
      (PolynomialFieldCode.realize
        (DetectorJacobiGaugeData.fieldCode parameters I)
        (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.point
          (recoveredState x t).base.base)) t
  linkedSource :
    HasDerivAt
      (fun s =>
        ControllerProductLinkedJacobiFamilyPolynomialCode.point
          (recoveredState x s).base.base.source)
      (PolynomialFieldCode.realize
        (ControllerProductLinkedJacobiFamilyPolynomialCode.fieldCode
          parameters
          (DetectorCharacterCode.omegaWeights (eqs := eqs))
          (DetectorCharacterCode.numberWeights I))
        (ControllerProductLinkedJacobiFamilyPolynomialCode.point
          (recoveredState x t).base.base.source)) t
  controllers :
    HasDerivAt
      (fun s =>
        ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint
          (recoveredState x s).base.base.source)
      (PolynomialFieldCode.realize
        (Clocks.ControllerPhaseProductPolynomialCode.fieldCode parameters)
        (ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint
          (recoveredState x t).base.base.source)) t
  gauge :
    ∀ j,
      HasDerivAt
        (fun s => (recoveredState x s).base.base.gauge j)
        ((ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.vectorField
          parameters
          (DetectorCharacterCode.omegaWeights (eqs := eqs))
          (DetectorCharacterCode.numberWeights I)
          (DetectorJacobiGaugeData.gaugeExponents I)
          (recoveredState x t).base.base).gauge j) t
  reciprocal :
    ∀ k,
      HasDerivAt
        (fun s => (recoveredState x s).base.reciprocal k)
        ((DetectorPoissonReciprocalCode.vectorField
          parameters I (recoveredState x t).base).reciprocal k) t
  rhsC :
    HasDerivAt
      (fun s => (recoveredState x s).rhs.c)
      ((Clocks.RHSOscillatorPolynomialCode.oscillatorField
        (FixedDetectorPolynomialCode.rhsWeightCode I)
        (FixedDetectorPolynomialCode.equationFrequencyCode parameters)
        (DetectorPoissonReciprocalCode.point
          (recoveredState x t).base)
        (recoveredState x t).rhs).c) t
  rhsD :
    HasDerivAt
      (fun s => (recoveredState x s).rhs.d)
      ((Clocks.RHSOscillatorPolynomialCode.oscillatorField
        (FixedDetectorPolynomialCode.rhsWeightCode I)
        (FixedDetectorPolynomialCode.equationFrequencyCode parameters)
        (DetectorPoissonReciprocalCode.point
          (recoveredState x t).base)
        (recoveredState x t).rhs).d) t

/-- One derivative of the flattened fixed-detector field recovers every
nested semantic derivative at the same time. -/
theorem isStructuredAt_of_hasDerivAt
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (x :
      ℝ →
        Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (t : ℝ)
    (hx :
      HasDerivAt
        x
        (PolynomialFieldCode.realize
          (FixedDetectorPolynomialCode.fieldCode parameters I)
          (x t)) t) :
    IsStructuredAt parameters I x t := by
  let z : ℝ → FixedDetectorPolynomialCode.State eqs vars :=
    recoveredState x
  have hfull :
      HasDerivAt
        (fun s => FixedDetectorPolynomialCode.point (z s))
        (PolynomialFieldCode.realize
          (FixedDetectorPolynomialCode.fieldCode parameters I)
          (FixedDetectorPolynomialCode.point (z t))) t := by
    simpa only [z, point_recoveredState] using hx
  have hcombined :
      HasDerivAt
        (fun s =>
          Clocks.RHSOscillatorPolynomialCode.combinedPoint
            (DetectorPoissonReciprocalCode.point (z s).base)
            (z s).rhs)
        (PolynomialFieldCode.realize
          (Clocks.RHSOscillatorPolynomialCode.fieldCode
            (DetectorPoissonReciprocalCode.fieldCode parameters I)
            (FixedDetectorPolynomialCode.rhsWeightCode I)
            (FixedDetectorPolynomialCode.equationFrequencyCode
              parameters))
          (Clocks.RHSOscillatorPolynomialCode.combinedPoint
            (DetectorPoissonReciprocalCode.point (z t).base)
            (z t).rhs)) t := by
    simpa only [FixedDetectorPolynomialCode.point,
      FixedDetectorPolynomialCode.fieldCode] using hfull
  have hpoisson :=
    Clocks.RHSOscillatorPolynomialCode.base_hasDerivAt_of_combinedPointAt
      (DetectorPoissonReciprocalCode.fieldCode parameters I)
      (FixedDetectorPolynomialCode.rhsWeightCode I)
      (FixedDetectorPolynomialCode.equationFrequencyCode parameters)
      (fun s => DetectorPoissonReciprocalCode.point (z s).base)
      (fun s => (z s).rhs) t hcombined
  have hrhsC :=
    Clocks.RHSOscillatorPolynomialCode.c_hasDerivAt_of_combinedPointAt
      (DetectorPoissonReciprocalCode.fieldCode parameters I)
      (FixedDetectorPolynomialCode.rhsWeightCode I)
      (FixedDetectorPolynomialCode.equationFrequencyCode parameters)
      (fun s => DetectorPoissonReciprocalCode.point (z s).base)
      (fun s => (z s).rhs) t hcombined
  have hrhsD :=
    Clocks.RHSOscillatorPolynomialCode.d_hasDerivAt_of_combinedPointAt
      (DetectorPoissonReciprocalCode.fieldCode parameters I)
      (FixedDetectorPolynomialCode.rhsWeightCode I)
      (FixedDetectorPolynomialCode.equationFrequencyCode parameters)
      (fun s => DetectorPoissonReciprocalCode.point (z s).base)
      (fun s => (z s).rhs) t hcombined
  have hrawReciprocal :
      HasDerivAt
        (fun s =>
          ComplexReciprocalFamilyPolynomialCode.point
            (DetectorPoissonReciprocalCode.rawState (z s).base))
        (PolynomialFieldCode.realize
          (ComplexReciprocalFamilyPolynomialCode.fieldCode
            (DetectorJacobiGaugeData.fieldCode parameters I)
            (DetectorPoissonReciprocalCode.etaCode (vars := vars))
            (DetectorPoissonReciprocalCode.derivativeBaseCode
              parameters I))
          (ComplexReciprocalFamilyPolynomialCode.point
            (DetectorPoissonReciprocalCode.rawState (z t).base))) t := by
    simpa only [DetectorPoissonReciprocalCode.point,
      DetectorPoissonReciprocalCode.fieldCode] using hpoisson
  have hgaugeSource :=
    ComplexReciprocalFamilyPolynomialCode.base_hasDerivAt_of_pointAt
      (DetectorJacobiGaugeData.fieldCode parameters I)
      (DetectorPoissonReciprocalCode.etaCode (vars := vars))
      (DetectorPoissonReciprocalCode.derivativeBaseCode parameters I)
      (fun s => DetectorPoissonReciprocalCode.rawState (z s).base)
      t hrawReciprocal
  have hreciprocal :
      ∀ k,
        HasDerivAt
          (fun s => (z s).base.reciprocal k)
          ((DetectorPoissonReciprocalCode.vectorField
            parameters I (z t).base).reciprocal k) t := by
    intro k
    have hk :=
      ComplexReciprocalFamilyPolynomialCode.reciprocal_hasDerivAt_of_pointAt
        (DetectorJacobiGaugeData.fieldCode parameters I)
        (DetectorPoissonReciprocalCode.etaCode (vars := vars))
        (DetectorPoissonReciprocalCode.derivativeBaseCode parameters I)
        (fun s => DetectorPoissonReciprocalCode.rawState (z s).base)
        t hrawReciprocal k
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
      HasDerivAt
        (fun s =>
          ComplexGaugeFamilyPolynomialCode.point
            (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.rawState
              (z s).base.base))
        (PolynomialFieldCode.realize
          (ComplexGaugeFamilyPolynomialCode.fieldCode
            (ControllerProductLinkedJacobiFamilyPolynomialCode.fieldCode
              parameters
              (DetectorCharacterCode.omegaWeights (eqs := eqs))
              (DetectorCharacterCode.numberWeights I))
            (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.gaugeFrequencyBaseCode
              parameters
              (DetectorJacobiGaugeData.gaugeExponents I)))
          (ComplexGaugeFamilyPolynomialCode.point
            (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.rawState
              (z t).base.base))) t := by
    simpa only [
      ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.point,
      DetectorJacobiGaugeData.fieldCode,
      ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.fieldCode]
      using hgaugeSource
  have hlinkedSource :=
    ComplexGaugeFamilyPolynomialCode.base_hasDerivAt_of_pointAt
      (ControllerProductLinkedJacobiFamilyPolynomialCode.fieldCode
        parameters
        (DetectorCharacterCode.omegaWeights (eqs := eqs))
        (DetectorCharacterCode.numberWeights I))
      (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.gaugeFrequencyBaseCode
        parameters
        (DetectorJacobiGaugeData.gaugeExponents I))
      (fun s =>
        ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.rawState
          (z s).base.base)
      t hrawGauge
  have hgauge :
      ∀ j,
        HasDerivAt
          (fun s => (z s).base.base.gauge j)
          ((ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.vectorField
            parameters
            (DetectorCharacterCode.omegaWeights (eqs := eqs))
            (DetectorCharacterCode.numberWeights I)
            (DetectorJacobiGaugeData.gaugeExponents I)
            (z t).base.base).gauge j) t := by
    intro j
    have hj :=
      ComplexGaugeFamilyPolynomialCode.gauge_hasDerivAt_of_pointAt
        (ControllerProductLinkedJacobiFamilyPolynomialCode.fieldCode
          parameters
          (DetectorCharacterCode.omegaWeights (eqs := eqs))
          (DetectorCharacterCode.numberWeights I))
        (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.gaugeFrequencyBaseCode
          parameters
          (DetectorJacobiGaugeData.gaugeExponents I))
        (fun s =>
          ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.rawState
            (z s).base.base)
        t hrawGauge j
    simpa only [
      ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.rawState,
      ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.vectorField,
      ComplexGaugeFamilyPolynomialCode.gaugeVelocity,
      ComplexGaugeFamilyPolynomialCode.evalRealObservable,
      ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.eval₂Hom_gaugeFrequencyBaseCode]
      using hj
  have hcontrollers :=
    ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint_hasDerivAt_of_pointAt
      parameters
      (DetectorCharacterCode.omegaWeights (eqs := eqs))
      (DetectorCharacterCode.numberWeights I)
      (fun s => (z s).base.base.source)
      t hlinkedSource
  exact {
    full := by simpa only [z] using hfull
    poissonSource := by simpa only [z] using hpoisson
    gaugeSource := by simpa only [z] using hgaugeSource
    linkedSource := by simpa only [z] using hlinkedSource
    controllers := by simpa only [z] using hcontrollers
    gauge := by simpa only [z] using hgauge
    reciprocal := by simpa only [z] using hreciprocal
    rhsC := by simpa only [z] using hrhsC
    rhsD := by simpa only [z] using hrhsD
  }

/-- Forward-time structured semantics.  The first field retains the
one-sided derivative at zero; the second supplies every semantic
equation as an ordinary derivative at each positive time. -/
structure IsForwardStructuredTrajectory
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (x :
      ℝ →
        Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (x₀ :
      Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ) :
    Prop where
  full :
    IsForwardTrajectory
      (PolynomialFieldCode.realize
        (FixedDetectorPolynomialCode.fieldCode parameters I))
      x x₀
  positive :
    ∀ t, 0 < t → IsStructuredAt parameters I x t

/-- Every forward solution of the literal flattened detector field has
the complete nested semantic equations for all positive times. -/
theorem isForwardStructuredTrajectory_of_isForwardTrajectory
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (x :
      ℝ →
        Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (x₀ :
      Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (hx :
      IsForwardTrajectory
        (PolynomialFieldCode.realize
          (FixedDetectorPolynomialCode.fieldCode parameters I))
        x x₀) :
    IsForwardStructuredTrajectory parameters I x x₀ where
  full := hx
  positive := by
    intro t ht
    exact
      isStructuredAt_of_hasDerivAt parameters I x t
        ((hx.2 t ht.le).hasDerivAt (Ici_mem_nhds ht))

/-- The compact-source physical path therefore has the full reverse
compiler semantics at every positive ordinary time, without any
negative-time ODE claim. -/
theorem compactSourcePhysicalPoint_isForwardStructuredTrajectory
    (u : FixedDetectorCompactSourceCode.CompilerInput eqs vars)
    (v :
      FixedDetectorCompactSourceTrajectory.FiniteSourceSpace eqs vars)
    (hclock :
      PositiveIntegralClock
        (stateClockWeight
          (CompactAccumulatorPipelineCode.AllAffineCompactSourceChart.affineSpeed
            (FixedDetectorCompactSourceCode.sourceDegreeBound
              (FixedDetectorCompactSourceCode.system u)))
          (FixedDetectorCompactSourceTrajectory.affineCurve u v))) :
    IsForwardStructuredTrajectory
      (FixedDetectorCompactSourceCode.parameters u)
      (FixedDetectorCompactSourceCode.system u)
      (FixedDetectorCompactSourceTrajectory.physicalPoint u v hclock)
      (CompactAccumulatorPipelineCode.AllAffineCompactSourceChart.affinePoint
        v) :=
  isForwardStructuredTrajectory_of_isForwardTrajectory
    (FixedDetectorCompactSourceCode.parameters u)
    (FixedDetectorCompactSourceCode.system u)
    (FixedDetectorCompactSourceTrajectory.physicalPoint u v hclock)
    (CompactAccumulatorPipelineCode.AllAffineCompactSourceChart.affinePoint
      v)
    (FixedDetectorCompactSourceTrajectory.physicalPoint_isForwardTrajectory
      u v hclock)

/-! ## Selected linked block at positive time -/

/-- The selected linked block satisfies all fourteen complex dynamic
equations at every positive time. -/
theorem linkedPoint_hasDerivAt_positive
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (x :
      ℝ →
        Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (x₀ :
      Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (h : IsForwardStructuredTrajectory parameters I x x₀)
    (j : Fin vars)
    (i : Fin LinkedJacobiPolynomialCode.dimension)
    (t : ℝ)
    (ht : 0 < t) :
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
  ControllerProductLinkedJacobiFamilyPolynomialCode.linkedPoint_hasDerivAt_of_pointAt
    parameters
    (DetectorCharacterCode.omegaWeights (eqs := eqs))
    (DetectorCharacterCode.numberWeights I)
    (fun s => (recoveredState x s).base.base.source)
    t (h.positive t ht).linkedSource j i

/-- With constant controller readouts, the preceding equations are the
standard scaled linked-Jacobi equations at every positive time. -/
theorem linkedPoint_hasScaledDerivAt_positive
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (x :
      ℝ →
        Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (x₀ :
      Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (h : IsForwardStructuredTrajectory parameters I x x₀)
    (j : Fin vars)
    (κZ κPhi : ℂ)
    (hkappaZ :
      ∀ t, 0 < t →
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
      ∀ t, 0 < t →
        ControllerProductLinkedJacobiFamilyPolynomialCode.kappaPhi
            (fun a i =>
              (RationalCode.decode
                (DetectorCharacterCode.omegaWeights
                  (eqs := eqs) a i) : ℝ))
            (fun i =>
              (RationalCode.decode (parameters i) : ℝ))
            (recoveredState x t).base.base.source j =
          κPhi) :
    ∀ t, 0 < t →
      ∀ i : Fin LinkedJacobiPolynomialCode.dimension,
        HasDerivAt
          (fun s =>
            LinkedJacobiPolynomialCode.point
              ((recoveredState x s).base.base.source.linked j) i)
          (LinkedJacobiPolynomialCode.point
            (LinkedJacobiState.combinedVectorField
              κZ κPhi
              ((recoveredState x t).base.base.source.linked j)) i) t := by
  intro t ht i
  have hi := linkedPoint_hasDerivAt_positive
    parameters I x x₀ h j i t ht
  simpa only [
    ControllerProductLinkedJacobiFamilyPolynomialCode.vectorField,
    hkappaZ t ht, hkappaPhi t ht] using hi

end FixedDetectorForwardTrajectoryReverseCrosswalk

end

end HGAS
