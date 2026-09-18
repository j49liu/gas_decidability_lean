import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorTwoSidedCompleteStructure
import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorTwoSidedControllerLocking
import HGAS.Clocks.CompleteRecurrentNormalizedControllerProduct
import Mathlib.Tactic

/-!
# All-time controller locking on the selected detector orbit

Forward recurrence first forces the controller at time zero onto the
polynomial equilibrium set.  Because the physical detector orbit is a
complete solution, uniqueness then shows that every controller coordinate
is constant on the whole real line.

The statement retains the actual signed equilibrium coordinate.  Later
frequency lemmas use it to expose, rather than hide, the sign of the
modular clock.
-/

namespace HGAS.NormalizedCorrectedFixedDetectorTwoSidedCompleteControllerLocking

open HGAS
open HGAS.Clocks
open HGAS.Modular
open NormalizedCorrectedFixedDetectorTwoSidedValidityOrbit
open NormalizedCorrectedFixedDetectorTwoSidedControllerLocking
open NormalizedCorrectedFixedDetectorTwoSidedCompleteStructure
open NormalizedCorrectedFixedDetectorTwoSidedControllerLocking.SelectedTwoSidedValidityOrbit
open NormalizedCorrectedFixedDetectorTwoSidedCompleteStructure.SelectedTwoSidedValidityOrbit

noncomputable section

variable {eqs vars : ℕ}
variable
  {u :
    NormalizedCorrectedFixedDetectorCompactSourceCode.CompilerInput
      eqs vars}

namespace SelectedTwoSidedValidityOrbit

variable (O : SelectedTwoSidedValidityOrbit u)

/-- The raw clock projection is a complete integral curve of the standalone
clock product. -/
theorem clockPoint_isIntegralCurve :
    IsIntegralCurve
      (clockPoint O)
      (fun _ y ↦
        PolynomialFieldCode.realize
          (ControllerPhaseProductPolynomialCode.fieldCode
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
              u)) y) := by
  exact (physicalPoint_isStructuredTrajectory O).controllers

/-- Every controller pair on the selected complete physical orbit equals
its value at time zero. -/
theorem controller_state_eq_zero
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (hp :
      ∀ i,
        (1 : ℝ) <
          (RationalCode.decode
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
              u i) : ℝ))
    (t : ℝ)
    (i : Fin (FixedDetectorPolynomialCode.clockCount eqs vars)) :
    ((FixedDetectorReverseTrajectoryCrosswalk.recoveredState
        O.physicalPoint t).base.base.source.controllers i).controller =
      ((FixedDetectorReverseTrajectoryCrosswalk.recoveredState
        O.physicalPoint 0).base.base.source.controllers i).controller := by
  let x := clockPoint O
  have h :=
    CompleteRecurrentNormalizedControllerProduct.controller_state_eq_zero
      (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
      hp x
      (clockPoint_onClockCircles O hscale)
      (clockPoint_isIntegralCurve O)
      (clockPoint_forwardRecurrentAt O)
      t i
  simpa only [x, clockPoint,
    ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint,
    ControllerPhaseProductPolynomialCode.state_point] using h

end SelectedTwoSidedValidityOrbit

end

end HGAS.NormalizedCorrectedFixedDetectorTwoSidedCompleteControllerLocking
