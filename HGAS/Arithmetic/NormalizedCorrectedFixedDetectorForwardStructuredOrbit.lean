import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorValidityOrbit
import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorNormalizationConsequences
import HGAS.Arithmetic.FixedDetectorForwardTrajectoryReverseCrosswalk
import Mathlib.Tactic

/-!
# Forward semantic structure of the normalized corrected selected orbit

The normalized corrected compact source changes only the accumulator drift.  Its
ordinary-time source equation is still the literal fixed-detector
polynomial vector field.  Consequently the physical orbit selected from
a zero conditional drift measure inherits the full reverse-compiler
semantics at every strictly positive time.

This short module is the reusable junction between the measure-theoretic
selection argument and the Jacobi/Bloch analysis.  It deliberately makes
no assertion that the constant extension at negative physical time
solves the detector ODE.
-/

namespace HGAS.NormalizedCorrectedFixedDetectorForwardStructuredOrbit

open HGAS
open CompactAccumulatorPipelineCode.AllAffineCompactSourceChart

noncomputable section

variable {eqs vars : ℕ}
variable
  {u : NormalizedCorrectedFixedDetectorCompactSourceCode.CompilerInput eqs vars}

namespace SelectedValidityOrbit

open NormalizedCorrectedFixedDetectorValidityOrbit
open FixedDetectorForwardTrajectoryReverseCrosswalk

variable (O : NormalizedCorrectedFixedDetectorValidityOrbit.SelectedValidityOrbit u)

/-- The selected physical orbit satisfies every nested detector equation
at each strictly positive ordinary time. -/
theorem physicalPoint_isForwardStructuredTrajectory :
    IsForwardStructuredTrajectory
      (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
      (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
      O.physicalPoint
      (affinePoint O.point) := by
  apply isForwardStructuredTrajectory_of_isForwardTrajectory
  simpa only [NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode] using
    O.physicalPoint_isForwardTrajectory

/-- The reassembled state used by the reverse compiler is definitionally
the selected physical detector state. -/
theorem recoveredState_physicalPoint (t : ℝ) :
    FixedDetectorReverseTrajectoryCrosswalk.recoveredState
        O.physicalPoint t =
      O.physicalState t :=
  rfl

/-- Pointwise vanishing of the repaired validity coordinate, expressed on
the reassembled detector state used by all semantic crosswalks. -/
theorem normalizedValidityEnergy_zero_physicalTime
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale u).decode :
          ℝ))
    (t : ℝ) :
    NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
        (FixedDetectorReverseTrajectoryCrosswalk.recoveredState
          O.physicalPoint t) = 0 := by
  simpa only [recoveredState_physicalPoint] using
    O.validityEnergy_zero_physicalTime hscale t

/-- The repaired equation still implies every graph residual imposed by
the old validity energy. -/
theorem oldValidityEnergy_zero_physicalTime
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale u).decode :
          ℝ))
    (t : ℝ) :
    FixedDetectorDriftCode.validityEnergyValue
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
        (FixedDetectorReverseTrajectoryCrosswalk.recoveredState
          O.physicalPoint t) = 0 := by
  let I := NormalizedCorrectedFixedDetectorCompactSourceCode.system u
  let z :=
    FixedDetectorReverseTrajectoryCrosswalk.recoveredState
      O.physicalPoint t
  have hnormalized :
      NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue
          I z = 0 := by
    simpa only [I, z] using
      normalizedValidityEnergy_zero_physicalTime O hscale t
  have hgraphs :=
    (NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue_eq_zero_iff
      I z).1 hnormalized
  exact
    (FixedDetectorReverseTrajectoryCrosswalk.validityEnergy_eq_zero_iff
      I O.physicalPoint t).2 hgraphs.1

/-- Hence every linked-Jacobi, theta-gauge, and reciprocal graph residual
vanishes along the selected physical orbit. -/
theorem validityResiduals_zero_physicalTime
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale u).decode :
          ℝ))
    (t : ℝ) :
    (∀ a (r : Modular.LinkedJacobiResidualIndex),
        Modular.linkedJacobiResidual r
          ((FixedDetectorReverseTrajectoryCrosswalk.recoveredState
              O.physicalPoint t).base.base.source.linked a) = 0) ∧
      (∀ k,
        MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
          (Modular.ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.point
            (FixedDetectorReverseTrajectoryCrosswalk.recoveredState
              O.physicalPoint t).base.base)
          (PolynomialCode.decode
            (DetectorJacobiGaugeData.residualCode
              FixedDetectorValidityEnergyCode.thetaGaugeScale
              (NormalizedCorrectedFixedDetectorCompactSourceCode.system u) k)) =
            0) ∧
      ∀ k,
        MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
          (DetectorPoissonReciprocalCode.point
            (FixedDetectorReverseTrajectoryCrosswalk.recoveredState
              O.physicalPoint t).base)
          (PolynomialCode.decode
            (DetectorPoissonReciprocalCode.residualCode
              (NormalizedCorrectedFixedDetectorCompactSourceCode.system u) k)) =
            0 := by
  exact
      (FixedDetectorReverseTrajectoryCrosswalk.validityEnergy_eq_zero_iff
      (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
      O.physicalPoint t).mp
      (oldValidityEnergy_zero_physicalTime O hscale t)

/-- Every physical-time clock block lies on both of its intended unit
circles. -/
theorem clockRadii_one_physicalTime
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale u).decode :
          ℝ))
    (t : ℝ) :
    (∀ i,
      Clocks.Controller.controllerRadiusSq
        ((FixedDetectorReverseTrajectoryCrosswalk.recoveredState
          O.physicalPoint t).base.base.source.controllers i).controller =
          1) ∧
    (∀ i,
      Clocks.Controller.phaseRadiusSq
        ((FixedDetectorReverseTrajectoryCrosswalk.recoveredState
          O.physicalPoint t).base.base.source.controllers i).phase =
          1) := by
  have hzero :=
    normalizedValidityEnergy_zero_physicalTime O hscale t
  have h :=
    (NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue_eq_zero_iff
      (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
      (FixedDetectorReverseTrajectoryCrosswalk.recoveredState
        O.physicalPoint t)).1 hzero
  exact ⟨h.2.1, h.2.2.1⟩

/-- The final right-hand-side oscillator has unit radius at every physical
time, so the zero-oscillator branch is excluded pointwise. -/
theorem rhsRadius_one_physicalTime
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale u).decode :
          ℝ))
    (t : ℝ) :
    Clocks.Controller.phaseRadiusSq
      (FixedDetectorReverseTrajectoryCrosswalk.recoveredState
        O.physicalPoint t).rhs = 1 := by
  have hzero :=
    normalizedValidityEnergy_zero_physicalTime O hscale t
  exact
    ((NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue_eq_zero_iff
      (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
      (FixedDetectorReverseTrajectoryCrosswalk.recoveredState
        O.physicalPoint t)).1 hzero).2.2.2

end SelectedValidityOrbit

end

end HGAS.NormalizedCorrectedFixedDetectorForwardStructuredOrbit
