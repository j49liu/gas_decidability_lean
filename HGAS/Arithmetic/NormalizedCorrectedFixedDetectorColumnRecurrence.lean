import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorColumnTrajectory
import Mathlib.Tactic

/-!
# Recurrence and residuals of a selected detector column

The full physical detector point returns along one common sequence.  A
linked column is obtained from that point by a finite coordinate
projection followed by pairing real and imaginary coordinates.  The
projection is continuous, so the same return sequence recurs in all
fourteen complex coordinates of the linked state and hence in its unary
subsystem.
-/

namespace HGAS.NormalizedCorrectedFixedDetectorColumnRecurrence

open HGAS
open HGAS.Modular
open NormalizedCorrectedFixedDetectorTwoSidedValidityOrbit
open NormalizedCorrectedFixedDetectorTwoSidedStructuredOrbit
open NormalizedCorrectedFixedDetectorColumnTrajectory
open NormalizedCorrectedFixedDetectorTwoSidedStructuredOrbit.SelectedTwoSidedValidityOrbit
open NormalizedCorrectedFixedDetectorColumnTrajectory.SelectedTwoSidedValidityOrbit

noncomputable section

variable {eqs vars : ℕ}
variable
  {u :
    NormalizedCorrectedFixedDetectorCompactSourceCode.CompilerInput
      eqs vars}

namespace SelectedTwoSidedValidityOrbit

variable (O : SelectedTwoSidedValidityOrbit u)

/-- Continuous projection from a flattened detector point to the fourteen
complex coordinates of column `j`. -/
def linkedPointProjection
    (j : Fin vars)
    (x :
      Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ) :
    Fin LinkedJacobiPolynomialCode.dimension → ℂ :=
  LinkedJacobiPolynomialCode.point
    ((FixedDetectorPolynomialCode.state x).base.base.source.linked j)

/-- Coordinate embedding of one realified linked block through every
outer compiler layer. -/
def linkedRealEmbedding
    (j : Fin vars) :
    Fin
        (LinkedJacobiPolynomialCode.dimension +
          LinkedJacobiPolynomialCode.dimension) ↪
      Fin (FixedDetectorPolynomialCode.dimension eqs vars) :=
  (((((ControllerProductLinkedJacobiFamilyPolynomialCode.linkedBlockEmbedding
      j).trans
      ControllerProductLinkedJacobiFamilyPolynomialCode.linkedFamilyEmbedding).trans
      ComplexGaugeFamilyPolynomialCode.baseEmbedding).trans
      ComplexReciprocalFamilyPolynomialCode.baseEmbedding).trans
      PolynomialBlockCode.leftEmbedding)

/-- Reading a linked block after reassembly is exactly restriction to its
embedded real coordinates followed by complexification. -/
theorem linkedPointProjection_eq
    (j : Fin vars)
    (x :
      Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ) :
    linkedPointProjection j x =
      ComplexCoordinates.complexifyPoint
        (x ∘ linkedRealEmbedding j) := by
  unfold linkedPointProjection
    FixedDetectorPolynomialCode.state
    DetectorPoissonReciprocalCode.state
    ComplexReciprocalFamilyPolynomialCode.state
    ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.state
    ComplexGaugeFamilyPolynomialCode.state
    ControllerProductLinkedJacobiFamilyPolynomialCode.state
  rw [LinkedJacobiPolynomialCode.point_state]
  congr 1

theorem continuous_linkedPointProjection
    (j : Fin vars) :
    Continuous
      (linkedPointProjection (eqs := eqs) (vars := vars) j) := by
  have heq :
      linkedPointProjection (eqs := eqs) (vars := vars) j =
        fun x ↦
          ComplexCoordinates.complexifyPoint
            (x ∘ linkedRealEmbedding j) := by
    funext x
    exact linkedPointProjection_eq j x
  rw [heq]
  apply continuous_pi
  intro k
  unfold ComplexCoordinates.complexifyPoint
  let r :=
    linkedRealEmbedding (eqs := eqs) (vars := vars) j
      (ComplexCoordinates.realIndex k)
  let s :=
    linkedRealEmbedding (eqs := eqs) (vars := vars) j
      (ComplexCoordinates.imagIndex k)
  have h :
      Continuous
        (fun x :
            Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ ↦
          (x r : ℂ) + (x s : ℂ) * Complex.I) :=
    (Complex.continuous_ofReal.comp (continuous_apply r)).add
      ((Complex.continuous_ofReal.comp (continuous_apply s)).mul
        continuous_const)
  apply h.congr
  intro x
  apply Complex.ext <;> simp [r, s]

/-- The linked polynomial point inherits the full detector return
sequence. -/
theorem linkedColumn_forwardRecurrentAt
    (j : Fin vars) :
    ForwardRecurrentAt
      (fun t ↦
        LinkedJacobiPolynomialCode.point
          (linkedColumn O j t)) 0 := by
  simpa only [linkedPointProjection, linkedColumn,
    FixedDetectorReverseTrajectoryCrosswalk.recoveredState] using
    (O.physicalPoint_forwardRecurrentAt).map
      (continuous_linkedPointProjection
        (eqs := eqs) (vars := vars) j)

/-- The unary modular component inherits coordinatewise recurrence along
that same return sequence. -/
noncomputable def unaryColumn_forwardRecurrentAt
    (j : Fin vars) :
    ForwardRecurrentUnaryModularAt
      (fun t ↦ (linkedColumn O j t).unary) 0 :=
  forwardRecurrentUnaryModularAt_of_linkedPolynomialPoint
    (linkedColumn_forwardRecurrentAt O j)

/-- Every linked residual of the selected column vanishes at every
physical time. -/
theorem linkedColumn_residual_zero
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (j : Fin vars)
    (t : ℝ)
    (r : LinkedJacobiResidualIndex) :
    linkedJacobiResidual r (linkedColumn O j t) = 0 := by
  exact
    (validityResiduals_zero_physicalTime O hscale t).1 j r

end SelectedTwoSidedValidityOrbit

end

end HGAS.NormalizedCorrectedFixedDetectorColumnRecurrence
