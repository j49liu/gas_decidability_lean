import HGAS.Arithmetic.CorrectedFixedDetectorValidityOrbit
import HGAS.Arithmetic.FixedDetectorForwardTrajectoryReverseCrosswalk
import Mathlib.Tactic

/-!
# Forward semantic structure of the corrected selected orbit

The corrected compact source changes only the accumulator drift.  Its
ordinary-time source equation is still the literal fixed-detector
polynomial vector field.  Consequently the physical orbit selected from
a zero conditional drift measure inherits the full reverse-compiler
semantics at every strictly positive time.

This short module is the reusable junction between the measure-theoretic
selection argument and the Jacobi/Bloch analysis.  It deliberately makes
no assertion that the constant extension at negative physical time
solves the detector ODE.
-/

namespace HGAS.CorrectedFixedDetectorForwardStructuredOrbit

open HGAS
open CompactAccumulatorPipelineCode.AllAffineCompactSourceChart

noncomputable section

variable {eqs vars : ℕ}
variable
  {u : CorrectedFixedDetectorCompactSourceCode.CompilerInput eqs vars}

namespace SelectedValidityOrbit

open CorrectedFixedDetectorValidityOrbit
open FixedDetectorForwardTrajectoryReverseCrosswalk

variable (O : CorrectedFixedDetectorValidityOrbit.SelectedValidityOrbit u)

/-- The selected physical orbit satisfies every nested detector equation
at each strictly positive ordinary time. -/
theorem physicalPoint_isForwardStructuredTrajectory :
    IsForwardStructuredTrajectory
      (CorrectedFixedDetectorCompactSourceCode.parameters u)
      (CorrectedFixedDetectorCompactSourceCode.system u)
      O.physicalPoint
      (affinePoint O.point) := by
  apply isForwardStructuredTrajectory_of_isForwardTrajectory
  simpa only [CorrectedFixedDetectorCompactSourceCode.sourceFieldCode] using
    O.physicalPoint_isForwardTrajectory

/-- The reassembled state used by the reverse compiler is definitionally
the selected physical detector state. -/
theorem recoveredState_physicalPoint (t : ℝ) :
    FixedDetectorReverseTrajectoryCrosswalk.recoveredState
        O.physicalPoint t =
      O.physicalState t :=
  rfl

/-- Pointwise vanishing of the corrected validity coordinate is the old
fixed-detector validity equation, since the correction changes only the
centering of selector moments. -/
theorem oldValidityEnergy_zero_physicalTime
    (hscale :
      0 <
        ((CorrectedFixedDetectorCompactSourceCode.accumulatorScale u).decode :
          ℝ))
    (t : ℝ) :
    FixedDetectorDriftCode.validityEnergyValue
        (CorrectedFixedDetectorCompactSourceCode.system u)
        (FixedDetectorReverseTrajectoryCrosswalk.recoveredState
          O.physicalPoint t) = 0 := by
  simpa only [recoveredState_physicalPoint] using
    O.validityEnergy_zero_physicalTime hscale t

/-- Hence every linked-Jacobi, theta-gauge, and reciprocal graph residual
vanishes along the selected physical orbit. -/
theorem validityResiduals_zero_physicalTime
    (hscale :
      0 <
        ((CorrectedFixedDetectorCompactSourceCode.accumulatorScale u).decode :
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
              (CorrectedFixedDetectorCompactSourceCode.system u) k)) =
            0) ∧
      ∀ k,
        MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
          (DetectorPoissonReciprocalCode.point
            (FixedDetectorReverseTrajectoryCrosswalk.recoveredState
              O.physicalPoint t).base)
          (PolynomialCode.decode
            (DetectorPoissonReciprocalCode.residualCode
              (CorrectedFixedDetectorCompactSourceCode.system u) k)) =
            0 := by
  exact
      (FixedDetectorReverseTrajectoryCrosswalk.validityEnergy_eq_zero_iff
      (CorrectedFixedDetectorCompactSourceCode.system u)
      O.physicalPoint t).mp
      (oldValidityEnergy_zero_physicalTime O hscale t)

end SelectedValidityOrbit

end

end HGAS.CorrectedFixedDetectorForwardStructuredOrbit
