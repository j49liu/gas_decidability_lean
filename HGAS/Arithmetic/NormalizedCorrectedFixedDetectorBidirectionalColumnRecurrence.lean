import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorBidirectionalValidityOrbit
import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorColumnRecurrence
import HGAS.Compiler.AllAffineCompactSourceReverseRecurrence
import Mathlib.Tactic

/-!
# Reverse recurrence of a normalized detector column

The bidirectional compact selector supplies recurrence for the reversed
compact flow.  The reversed-clock theorem transports it to the curve
`physicalPoint (-t)`.  Continuous coordinate projection then gives
recurrence of every reversed linked column and of its unary subsystem.
-/

namespace HGAS.NormalizedCorrectedFixedDetectorBidirectionalColumnRecurrence

open HGAS
open HGAS.Modular
open CompactAccumulatorPipelineCode
open CompactAccumulatorPipelineCode.AllAffineCompactSourceReverseRecurrence
open NormalizedCorrectedFixedDetectorTwoSidedValidityOrbit
open NormalizedCorrectedFixedDetectorBidirectionalValidityOrbit
open NormalizedCorrectedFixedDetectorColumnTrajectory
open NormalizedCorrectedFixedDetectorColumnRecurrence
open NormalizedCorrectedFixedDetectorTwoSidedValidityOrbit.SelectedTwoSidedValidityOrbit
open NormalizedCorrectedFixedDetectorColumnTrajectory.SelectedTwoSidedValidityOrbit
open NormalizedCorrectedFixedDetectorColumnRecurrence.SelectedTwoSidedValidityOrbit

noncomputable section

variable {eqs vars : ℕ}
variable
  {u :
    NormalizedCorrectedFixedDetectorCompactSourceCode.CompilerInput
      eqs vars}

namespace SelectedBidirectionalValidityOrbit

variable (O : SelectedBidirectionalValidityOrbit u)

/-- Reverse compact recurrence becomes recurrence of the complete
physical point after physical time is reversed. -/
theorem physicalPoint_reverse_forwardRecurrentAt :
    ForwardRecurrentAt
      (fun τ ↦
        O.toSelectedTwoSidedValidityOrbit.physicalPoint (-τ)) 0 := by
  simpa only [
    SelectedTwoSidedValidityOrbit.physicalPoint_eq_physicalCurve] using
    (physicalCurve_reverse_forwardRecurrentAt
      (NormalizedCorrectedFixedDetectorTwoSidedValidityOrbit.speedExponent
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
      (NormalizedCorrectedFixedDetectorTwoSidedValidityOrbit.compactFlow u)
      (NormalizedCorrectedFixedDetectorTwoSidedValidityOrbit.finiteInvariant u)
      O.point O.clock O.recurrent_reverse)

/-- The reversed linked polynomial point inherits the common return
sequence of the reversed physical detector point. -/
theorem linkedColumn_reverse_forwardRecurrentAt
    (j : Fin vars) :
    ForwardRecurrentAt
      (fun t ↦
        LinkedJacobiPolynomialCode.point
          (linkedColumn O.toSelectedTwoSidedValidityOrbit j (-t))) 0 := by
  simpa only [linkedPointProjection, linkedColumn,
    FixedDetectorReverseTrajectoryCrosswalk.recoveredState] using
    (physicalPoint_reverse_forwardRecurrentAt O).map
      (continuous_linkedPointProjection
        (eqs := eqs) (vars := vars) j)

/-- The unary subsystem of a reversed detector column is recurrent at
time zero. -/
noncomputable def unaryColumn_reverse_forwardRecurrentAt
    (j : Fin vars) :
    ForwardRecurrentUnaryModularAt
      (fun t ↦
        (linkedColumn O.toSelectedTwoSidedValidityOrbit j (-t)).unary) 0 :=
  forwardRecurrentUnaryModularAt_of_linkedPolynomialPoint
    (linkedColumn_reverse_forwardRecurrentAt O j)

end SelectedBidirectionalValidityOrbit

end

end HGAS.NormalizedCorrectedFixedDetectorBidirectionalColumnRecurrence
