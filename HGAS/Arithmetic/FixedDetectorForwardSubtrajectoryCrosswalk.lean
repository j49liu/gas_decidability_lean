import HGAS.Arithmetic.FixedDetectorForwardTrajectoryReverseCrosswalk
import HGAS.Compiler.PolynomialExtensionWithinReverseCrosswalk
import HGAS.Modular.LinkedJacobiWithinTrajectoryReverseCrosswalk
import Mathlib.Tactic

/-!
# Forward subtrajectories of the fixed detector

The positive-time reverse crosswalk gives ordinary derivatives for
`t > 0`.  For forward uniqueness one also needs the one-sided derivative
at `t = 0`.  This module projects the original
`IsIntegralCurveOn … (Set.Ici 0)` through the relevant compiler layers
without discarding that boundary derivative.
-/

namespace HGAS

open Set
open Modular
open Clocks.ControllerPhaseProductCharacterCode

noncomputable section

namespace FixedDetectorForwardSubtrajectoryCrosswalk

open FixedDetectorReverseTrajectoryCrosswalk

variable {eqs vars : ℕ}

/-- The controller-linked source, controller projection, and gauges at
one time, with derivatives restricted to a common time set. -/
structure IsStructuredWithinAt
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (x :
      ℝ →
        Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (s : Set ℝ) (t : ℝ) : Prop where
  linkedSource :
    HasDerivWithinAt
      (fun u =>
        ControllerProductLinkedJacobiFamilyPolynomialCode.point
          (recoveredState x u).base.base.source)
      (PolynomialFieldCode.realize
        (ControllerProductLinkedJacobiFamilyPolynomialCode.fieldCode
          parameters
          (DetectorCharacterCode.omegaWeights (eqs := eqs))
          (DetectorCharacterCode.numberWeights I))
        (ControllerProductLinkedJacobiFamilyPolynomialCode.point
          (recoveredState x t).base.base.source)) s t
  controllers :
    HasDerivWithinAt
      (fun u =>
        ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint
          (recoveredState x u).base.base.source)
      (PolynomialFieldCode.realize
        (Clocks.ControllerPhaseProductPolynomialCode.fieldCode parameters)
        (ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint
          (recoveredState x t).base.base.source)) s t
  gauge :
    ∀ j,
      HasDerivWithinAt
        (fun u => (recoveredState x u).base.base.gauge j)
        ((ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.vectorField
          parameters
          (DetectorCharacterCode.omegaWeights (eqs := eqs))
          (DetectorCharacterCode.numberWeights I)
          (DetectorJacobiGaugeData.gaugeExponents I)
          (recoveredState x t).base.base).gauge j) s t

/-- One within-derivative of the final flattened point projects to the
controller-linked source, controller block, and every gauge coordinate. -/
theorem isStructuredWithinAt_of_hasDerivWithinAt
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (x :
      ℝ →
        Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (s : Set ℝ) (t : ℝ)
    (hx :
      HasDerivWithinAt
        x
        (PolynomialFieldCode.realize
          (FixedDetectorPolynomialCode.fieldCode parameters I)
          (x t)) s t) :
    IsStructuredWithinAt parameters I x s t := by
  let z : ℝ → FixedDetectorPolynomialCode.State eqs vars :=
    recoveredState x
  have hfull :
      HasDerivWithinAt
        (fun u => FixedDetectorPolynomialCode.point (z u))
        (PolynomialFieldCode.realize
          (FixedDetectorPolynomialCode.fieldCode parameters I)
          (FixedDetectorPolynomialCode.point (z t))) s t := by
    simpa only [z, point_recoveredState] using hx
  have hcombined :
      HasDerivWithinAt
        (fun u =>
          Clocks.RHSOscillatorPolynomialCode.combinedPoint
            (DetectorPoissonReciprocalCode.point (z u).base)
            (z u).rhs)
        (PolynomialFieldCode.realize
          (Clocks.RHSOscillatorPolynomialCode.fieldCode
            (DetectorPoissonReciprocalCode.fieldCode parameters I)
            (FixedDetectorPolynomialCode.rhsWeightCode I)
            (FixedDetectorPolynomialCode.equationFrequencyCode
              parameters))
          (Clocks.RHSOscillatorPolynomialCode.combinedPoint
            (DetectorPoissonReciprocalCode.point (z t).base)
            (z t).rhs)) s t := by
    simpa only [FixedDetectorPolynomialCode.point,
      FixedDetectorPolynomialCode.fieldCode] using hfull
  have hpoisson :=
    Clocks.RHSOscillatorPolynomialCode.base_hasDerivWithinAt_of_combinedPoint
      (DetectorPoissonReciprocalCode.fieldCode parameters I)
      (FixedDetectorPolynomialCode.rhsWeightCode I)
      (FixedDetectorPolynomialCode.equationFrequencyCode parameters)
      (fun u => DetectorPoissonReciprocalCode.point (z u).base)
      (fun u => (z u).rhs) s t hcombined
  have hrawReciprocal :
      HasDerivWithinAt
        (fun u =>
          ComplexReciprocalFamilyPolynomialCode.point
            (DetectorPoissonReciprocalCode.rawState (z u).base))
        (PolynomialFieldCode.realize
          (ComplexReciprocalFamilyPolynomialCode.fieldCode
            (DetectorJacobiGaugeData.fieldCode parameters I)
            (DetectorPoissonReciprocalCode.etaCode (vars := vars))
            (DetectorPoissonReciprocalCode.derivativeBaseCode
              parameters I))
          (ComplexReciprocalFamilyPolynomialCode.point
            (DetectorPoissonReciprocalCode.rawState (z t).base))) s t := by
    simpa only [DetectorPoissonReciprocalCode.point,
      DetectorPoissonReciprocalCode.fieldCode] using hpoisson
  have hgaugeSource :=
    ComplexReciprocalFamilyPolynomialCode.base_hasDerivWithinAt_of_point
      (DetectorJacobiGaugeData.fieldCode parameters I)
      (DetectorPoissonReciprocalCode.etaCode (vars := vars))
      (DetectorPoissonReciprocalCode.derivativeBaseCode parameters I)
      (fun u => DetectorPoissonReciprocalCode.rawState (z u).base)
      s t hrawReciprocal
  have hrawGauge :
      HasDerivWithinAt
        (fun u =>
          ComplexGaugeFamilyPolynomialCode.point
            (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.rawState
              (z u).base.base))
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
              (z t).base.base))) s t := by
    simpa only [
      ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.point,
      DetectorJacobiGaugeData.fieldCode,
      ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.fieldCode]
      using hgaugeSource
  have hlinkedSource :=
    ComplexGaugeFamilyPolynomialCode.base_hasDerivWithinAt_of_point
      (ControllerProductLinkedJacobiFamilyPolynomialCode.fieldCode
        parameters
        (DetectorCharacterCode.omegaWeights (eqs := eqs))
        (DetectorCharacterCode.numberWeights I))
      (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.gaugeFrequencyBaseCode
        parameters
        (DetectorJacobiGaugeData.gaugeExponents I))
      (fun u =>
        ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.rawState
          (z u).base.base)
      s t hrawGauge
  have hcontrollers :=
    ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint_hasDerivWithinAt_of_point
      parameters
      (DetectorCharacterCode.omegaWeights (eqs := eqs))
      (DetectorCharacterCode.numberWeights I)
      (fun u => (z u).base.base.source)
      s t hlinkedSource
  have hgauge :
      ∀ j,
        HasDerivWithinAt
          (fun u => (z u).base.base.gauge j)
          ((ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.vectorField
            parameters
            (DetectorCharacterCode.omegaWeights (eqs := eqs))
            (DetectorCharacterCode.numberWeights I)
            (DetectorJacobiGaugeData.gaugeExponents I)
            (z t).base.base).gauge j) s t := by
    intro j
    have hj :=
      ComplexGaugeFamilyPolynomialCode.gauge_hasDerivWithinAt_of_point
        (ControllerProductLinkedJacobiFamilyPolynomialCode.fieldCode
          parameters
          (DetectorCharacterCode.omegaWeights (eqs := eqs))
          (DetectorCharacterCode.numberWeights I))
        (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.gaugeFrequencyBaseCode
          parameters
          (DetectorJacobiGaugeData.gaugeExponents I))
        (fun u =>
          ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.rawState
            (z u).base.base)
        s t hrawGauge j
    simpa only [
      ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.rawState,
      ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.vectorField,
      ComplexGaugeFamilyPolynomialCode.gaugeVelocity,
      ComplexGaugeFamilyPolynomialCode.evalRealObservable,
      ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.eval₂Hom_gaugeFrequencyBaseCode]
      using hj
  exact {
    linkedSource := by simpa only [z] using hlinkedSource
    controllers := by simpa only [z] using hcontrollers
    gauge := by simpa only [z] using hgauge
  }

/-- Every nonnegative time of a forward structured detector trajectory
has the one-sided nested equations on `Ici 0`. -/
theorem structuredWithinAt_Ici
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (x :
      ℝ →
        Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (x₀ :
      Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (h :
      FixedDetectorForwardTrajectoryReverseCrosswalk.IsForwardStructuredTrajectory
        parameters I x x₀)
    (t : ℝ) (ht : 0 ≤ t) :
    IsStructuredWithinAt parameters I x (Ici 0) t :=
  isStructuredWithinAt_of_hasDerivWithinAt
    parameters I x (Ici 0) t (h.full.2 t ht)

/-- The selected complex linked block satisfies all ten Jacobi coordinate
equations as within-derivatives on the forward ray. -/
theorem linkedPoint_hasDerivWithinAt_Ici
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (x :
      ℝ →
        Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (x₀ :
      Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (h :
      FixedDetectorForwardTrajectoryReverseCrosswalk.IsForwardStructuredTrajectory
        parameters I x x₀)
    (j : Fin vars)
    (i : Fin LinkedJacobiPolynomialCode.dimension)
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt
      (fun u =>
        LinkedJacobiPolynomialCode.point
          ((recoveredState x u).base.base.source.linked j) i)
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
          (recoveredState x t).base.base.source).linked j) i)
      (Ici 0) t :=
  ControllerProductLinkedJacobiFamilyPolynomialCode.linkedPoint_hasDerivWithinAt_of_point
    parameters
    (DetectorCharacterCode.omegaWeights (eqs := eqs))
    (DetectorCharacterCode.numberWeights I)
    (fun u => (recoveredState x u).base.base.source)
    (Ici 0) t (structuredWithinAt_Ici
      parameters I x x₀ h t ht).linkedSource j i

end FixedDetectorForwardSubtrajectoryCrosswalk

end

end HGAS
