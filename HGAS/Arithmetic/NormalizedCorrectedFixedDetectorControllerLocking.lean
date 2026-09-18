import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorForwardStructuredOrbit
import HGAS.Arithmetic.FixedDetectorForwardSubtrajectoryCrosswalk
import HGAS.Clocks.RecurrentNormalizedControllerProduct
import Mathlib.Tactic

/-!
# Controller locking on the normalized selected detector orbit

The repaired validity coordinate forces every controller and driven phase
pair onto its unit circle.  The selected physical detector orbit is also
forward recurrent and solves the literal detector ODE.  This file combines
those facts with `RecurrentNormalizedControllerProduct` to derive the
controller-lock equations needed by the canonical clock and selector
arguments.

No invariant-measure factor map from the full affine ambient space to a
circle is assumed.  The proof is pointwise:

1. project the recurrent physical detector trajectory to its raw clock
   coordinates;
2. use zero repaired validity to put that whole curve on the compact
   clock-product sphere;
3. use polynomial ODE uniqueness to identify it with the canonical sphere
   flow for positive time; and
4. apply the recurrence obstruction for the hyperbolic controller flow.
-/

noncomputable section

namespace HGAS.NormalizedCorrectedFixedDetectorControllerLocking

open HGAS
open HGAS.Clocks
open HGAS.Modular
open CompactAccumulatorPipelineCode.AllAffineCompactSourceChart
open NormalizedCorrectedFixedDetectorValidityOrbit
open NormalizedCorrectedFixedDetectorForwardStructuredOrbit
open FixedDetectorReverseTrajectoryCrosswalk
open FixedDetectorForwardSubtrajectoryCrosswalk
open HGAS.NormalizedCorrectedFixedDetectorValidityOrbit.SelectedValidityOrbit
open HGAS.NormalizedCorrectedFixedDetectorForwardStructuredOrbit.SelectedValidityOrbit
open HGAS.NormalizedCorrectedFixedDetectorNormalizationConsequences

variable {eqs vars : ℕ}
variable
  {u :
    NormalizedCorrectedFixedDetectorCompactSourceCode.CompilerInput
      eqs vars}

namespace SelectedValidityOrbit

variable
  (O :
    NormalizedCorrectedFixedDetectorValidityOrbit.SelectedValidityOrbit u)

/-- The raw `4q` clock coordinates extracted from the selected physical
detector orbit. -/
def clockPoint (t : ℝ) :
    Fin
      (ControllerPhaseProductPolynomialCode.dimension
        (FixedDetectorPolynomialCode.clockCount eqs vars)) → ℝ :=
  ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint
    (recoveredState O.physicalPoint t).base.base.source

/-- Coordinate embedding of the raw clock block through the linked,
gauge, reciprocal, and final-RHS compiler layers. -/
def clockEmbedding :
    Fin
        (ControllerPhaseProductPolynomialCode.dimension
          (FixedDetectorPolynomialCode.clockCount eqs vars)) ↪
      Fin (FixedDetectorPolynomialCode.dimension eqs vars) :=
  (((ControllerProductLinkedJacobiFamilyPolynomialCode.controllersEmbedding).trans
      ComplexGaugeFamilyPolynomialCode.baseEmbedding).trans
    ComplexReciprocalFamilyPolynomialCode.baseEmbedding).trans
  PolynomialBlockCode.leftEmbedding

/-- Reassembling a full detector point and then reading its clock block is
literally restriction along `clockEmbedding`. -/
theorem clockProjection_eq_comp_clockEmbedding
    (x : Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ) :
    ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint
        (FixedDetectorPolynomialCode.state x).base.base.source =
      x ∘ (clockEmbedding (eqs := eqs) (vars := vars)) := by
  funext k
  simp [clockEmbedding,
    ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint,
    FixedDetectorPolynomialCode.state,
    DetectorPoissonReciprocalCode.state,
    ComplexReciprocalFamilyPolynomialCode.state,
    ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.state,
    ComplexGaugeFamilyPolynomialCode.baseEmbedding,
    ComplexGaugeFamilyPolynomialCode.state,
    ControllerProductLinkedJacobiFamilyPolynomialCode.state]

/-- The clock-coordinate projection from the complete affine detector
space is continuous. -/
theorem continuous_clockProjection :
    Continuous
      (fun x :
          Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ ↦
        ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint
          (FixedDetectorPolynomialCode.state x).base.base.source) := by
  simp_rw [clockProjection_eq_comp_clockEmbedding]
  apply continuous_pi
  intro k
  exact continuous_apply _

/-- Recurrence of the complete selected source descends to its clock
coordinates. -/
theorem clockPoint_forwardRecurrentAt :
    ForwardRecurrentAt (clockPoint O) 0 := by
  simpa only [clockPoint, recoveredState] using
    (physicalPoint_forwardRecurrentAt O).map
      (continuous_clockProjection (eqs := eqs) (vars := vars))

/-- The projected clock curve solves the standalone finite-product clock
field on the nonnegative ray. -/
theorem clockPoint_isForwardTrajectory :
    IsForwardTrajectory
      (PolynomialFieldCode.realize
        (ControllerPhaseProductPolynomialCode.fieldCode
          (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
            u)))
      (clockPoint O) (clockPoint O 0) := by
  have hstructured :=
    physicalPoint_isForwardStructuredTrajectory O
  refine ⟨rfl, ?_⟩
  intro t ht
  exact
    (structuredWithinAt_Ici
      (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
      (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
      O.physicalPoint (affinePoint O.point)
      hstructured t ht).controllers

/-- Zero repaired validity places the projected clock curve on the exact
product of controller and phase unit circles at every physical time. -/
theorem clockPoint_onClockCircles
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (t : ℝ) :
    ControllerPhaseProductSphereFlow.OnClockCircles
      (clockPoint O t) := by
  have hzero :=
    validityEnergy_zero_physicalTime O hscale t
  simpa only [clockPoint, physicalState, recoveredState] using
    onClockCircles_of_validityEnergyValue_eq_zero
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
        (physicalState O t) hzero

/-- **Selected-orbit controller locking.**  If every compiled controller
parameter is greater than one, each controller at physical time zero is
a polynomial equilibrium. -/
theorem controller_equilibrium_at_zero
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
    (i : Fin (FixedDetectorPolynomialCode.clockCount eqs vars)) :
    Controller.IsControllerEquilibrium
      (RationalCode.decode
        (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
          u i) : ℝ)
      ((recoveredState O.physicalPoint 0).base.base.source.controllers i).controller := by
  simpa only [clockPoint,
    ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint,
    ControllerPhaseProductPolynomialCode.state_point] using
    RecurrentNormalizedControllerProduct.controller_equilibrium_at_zero
      (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
      hp (clockPoint O)
      (clockPoint_onClockCircles O hscale)
      (clockPoint_isForwardTrajectory O)
      (clockPoint_forwardRecurrentAt O) i

end SelectedValidityOrbit

end HGAS.NormalizedCorrectedFixedDetectorControllerLocking
