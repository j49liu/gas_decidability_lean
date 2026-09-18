import HGAS.Compiler.PolynomialExtensionTrajectoryReverseCrosswalk
import HGAS.Modular.LinkedJacobiTrajectoryPolynomialCrosswalk
import Mathlib.Tactic

/-!
# Recovering linked Jacobi trajectories from the family compiler

The forward crosswalk in
`LinkedJacobiTrajectoryPolynomialCrosswalk` starts from structured
controller and linked-Jacobi equations and proves the flattened polynomial
ODE.  Here we prove the converse.

The first results are completely ambient: a solution of the compiled
family field projects to the controller field and to the real and
imaginary equations of every linked block.  If the two controller
readouts of a block are constant, those component equations bundle into
the usual `IsScaledLinkedJacobiTrajectory` interface.
-/

namespace HGAS.Modular

open HGAS

noncomputable section

/-! ## Reassembling one linked block -/

/-- Realified coordinate equations determine all fourteen complex
coordinate equations of a linked Jacobi state. -/
theorem linkedPoint_hasDerivAt_of_realifyPoint
    {z : ℝ → LinkedJacobiState ℂ}
    {v : ℝ → LinkedJacobiState ℂ}
    (h :
      ∀ j t,
        HasDerivAt
          (fun s =>
            ComplexCoordinates.realifyPoint
              (LinkedJacobiPolynomialCode.point (z s)) j)
          (ComplexCoordinates.realifyPoint
            (LinkedJacobiPolynomialCode.point (v t)) j) t)
    (i : Fin LinkedJacobiPolynomialCode.dimension)
    (t : ℝ) :
    HasDerivAt
      (fun s => LinkedJacobiPolynomialCode.point (z s) i)
      (LinkedJacobiPolynomialCode.point (v t) i) t := by
  apply HGAS.HasDerivAt.complex_of_re_im
  · simpa only [
      ComplexCoordinates.realifyPoint_realIndex] using
      h (ComplexCoordinates.realIndex i) t
  · simpa only [
      ComplexCoordinates.realifyPoint_imagIndex] using
      h (ComplexCoordinates.imagIndex i) t

/-- The fourteen complex component equations bundle into the standard
linked unary--Jacobi trajectory structure. -/
theorem isScaledLinkedJacobiTrajectory_of_linkedPoint
    (κZ κPhi : ℂ)
    (z : ℝ → LinkedJacobiState ℂ)
    (h :
      ∀ i t,
        HasDerivAt
          (fun s =>
            LinkedJacobiPolynomialCode.point (z s) i)
          (LinkedJacobiPolynomialCode.point
            (LinkedJacobiState.combinedVectorField
              κZ κPhi (z t)) i) t) :
    IsScaledLinkedJacobiTrajectory κZ κPhi z where
  unary := {
    A := by
      intro t
      simpa [LinkedJacobiPolynomialCode.point,
        LinkedJacobiPolynomialCode.unaryEmbedding,
        UnaryPolynomialCode.modularPoint,
        LinkedJacobiState.combinedVectorField] using
        h (LinkedJacobiPolynomialCode.unaryEmbedding
          (0 : Fin LinkedJacobiPolynomialCode.unaryDimension)) t
    C := by
      intro t
      simpa [LinkedJacobiPolynomialCode.point,
        LinkedJacobiPolynomialCode.unaryEmbedding,
        UnaryPolynomialCode.modularPoint,
        LinkedJacobiState.combinedVectorField] using
        h (LinkedJacobiPolynomialCode.unaryEmbedding
          (1 : Fin LinkedJacobiPolynomialCode.unaryDimension)) t
    E := by
      intro t
      simpa [LinkedJacobiPolynomialCode.point,
        LinkedJacobiPolynomialCode.unaryEmbedding,
        UnaryPolynomialCode.modularPoint,
        LinkedJacobiState.combinedVectorField] using
        h (LinkedJacobiPolynomialCode.unaryEmbedding
          (2 : Fin LinkedJacobiPolynomialCode.unaryDimension)) t
    Y := by
      intro t
      simpa [LinkedJacobiPolynomialCode.point,
        LinkedJacobiPolynomialCode.unaryEmbedding,
        UnaryPolynomialCode.modularPoint,
        LinkedJacobiState.combinedVectorField] using
        h (LinkedJacobiPolynomialCode.unaryEmbedding
          (3 : Fin LinkedJacobiPolynomialCode.unaryDimension)) t
  }
  jacobi := {
    p2 := by
      intro t
      simpa [LinkedJacobiPolynomialCode.point,
        LinkedJacobiPolynomialCode.jacobiEmbedding,
        JacobiPolynomialCode.point,
        LinkedJacobiState.combinedVectorField] using
        h (LinkedJacobiPolynomialCode.jacobiEmbedding
          (0 : Fin LinkedJacobiPolynomialCode.jacobiDimension)) t
    p3 := by
      intro t
      simpa [LinkedJacobiPolynomialCode.point,
        LinkedJacobiPolynomialCode.jacobiEmbedding,
        JacobiPolynomialCode.point,
        LinkedJacobiState.combinedVectorField] using
        h (LinkedJacobiPolynomialCode.jacobiEmbedding
          (1 : Fin LinkedJacobiPolynomialCode.jacobiDimension)) t
    p4 := by
      intro t
      simpa [LinkedJacobiPolynomialCode.point,
        LinkedJacobiPolynomialCode.jacobiEmbedding,
        JacobiPolynomialCode.point,
        LinkedJacobiState.combinedVectorField] using
        h (LinkedJacobiPolynomialCode.jacobiEmbedding
          (2 : Fin LinkedJacobiPolynomialCode.jacobiDimension)) t
    H := by
      intro t
      simpa [LinkedJacobiPolynomialCode.point,
        LinkedJacobiPolynomialCode.jacobiEmbedding,
        JacobiPolynomialCode.point,
        LinkedJacobiState.combinedVectorField] using
        h (LinkedJacobiPolynomialCode.jacobiEmbedding
          (3 : Fin LinkedJacobiPolynomialCode.jacobiDimension)) t
    T1 := by
      intro t
      simpa [LinkedJacobiPolynomialCode.point,
        LinkedJacobiPolynomialCode.jacobiEmbedding,
        JacobiPolynomialCode.point,
        LinkedJacobiState.combinedVectorField] using
        h (LinkedJacobiPolynomialCode.jacobiEmbedding
          (4 : Fin LinkedJacobiPolynomialCode.jacobiDimension)) t
    T2 := by
      intro t
      simpa [LinkedJacobiPolynomialCode.point,
        LinkedJacobiPolynomialCode.jacobiEmbedding,
        JacobiPolynomialCode.point,
        LinkedJacobiState.combinedVectorField] using
        h (LinkedJacobiPolynomialCode.jacobiEmbedding
          (5 : Fin LinkedJacobiPolynomialCode.jacobiDimension)) t
    T3 := by
      intro t
      simpa [LinkedJacobiPolynomialCode.point,
        LinkedJacobiPolynomialCode.jacobiEmbedding,
        JacobiPolynomialCode.point,
        LinkedJacobiState.combinedVectorField] using
        h (LinkedJacobiPolynomialCode.jacobiEmbedding
          (6 : Fin LinkedJacobiPolynomialCode.jacobiDimension)) t
    T4 := by
      intro t
      simpa [LinkedJacobiPolynomialCode.point,
        LinkedJacobiPolynomialCode.jacobiEmbedding,
        JacobiPolynomialCode.point,
        LinkedJacobiState.combinedVectorField] using
        h (LinkedJacobiPolynomialCode.jacobiEmbedding
          (7 : Fin LinkedJacobiPolynomialCode.jacobiDimension)) t
    Delta := by
      intro t
      simpa [LinkedJacobiPolynomialCode.point,
        LinkedJacobiPolynomialCode.jacobiEmbedding,
        JacobiPolynomialCode.point,
        LinkedJacobiState.combinedVectorField] using
        h (LinkedJacobiPolynomialCode.jacobiEmbedding
          (8 : Fin LinkedJacobiPolynomialCode.jacobiDimension)) t
    U := by
      intro t
      simpa [LinkedJacobiPolynomialCode.point,
        LinkedJacobiPolynomialCode.jacobiEmbedding,
        JacobiPolynomialCode.point,
        LinkedJacobiState.combinedVectorField] using
        h (LinkedJacobiPolynomialCode.jacobiEmbedding
          (9 : Fin LinkedJacobiPolynomialCode.jacobiDimension)) t
  }

/-! ## The common-controller family -/

namespace ControllerProductLinkedJacobiFamilyPolynomialCode

variable {q b : ℕ}

/-- A compiled common-controller family trajectory projects to the
literal product controller field. -/
theorem controllers_isIntegralCurve_of_point
    (parameters : Fin q → RationalCode)
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode)
    (z : ℝ → ControllerProductLinkedJacobiFamilyState q b)
    (h :
      IsIntegralCurve
        (fun t => point (z t))
        (fun _ x =>
          PolynomialFieldCode.realize
            (fieldCode parameters omegaWeights numberWeights) x)) :
    IsIntegralCurve
      (fun t => controllersPoint (z t))
      (fun _ x =>
        PolynomialFieldCode.realize
          (HGAS.Clocks.ControllerPhaseProductPolynomialCode.fieldCode
            parameters) x) := by
  intro t
  rw [hasDerivAt_pi]
  intro i
  have ht := h t
  rw [hasDerivAt_pi] at ht
  have hi := ht (controllersEmbedding (b := b) i)
  change
    HasDerivAt
      (fun s => point (z s) (controllersEmbedding i))
      (PolynomialFieldCode.realize
        (fieldCode parameters omegaWeights numberWeights)
        (point (z t)) (controllersEmbedding i)) t at hi
  rw [realize_fieldCode] at hi
  change
    HasDerivAt
      (fun s =>
        HGAS.Clocks.ControllerPhaseProductPolynomialCode.point
          (z s).controllers i)
      (PolynomialFieldCode.realize
        (HGAS.Clocks.ControllerPhaseProductPolynomialCode.fieldCode
          parameters)
        (HGAS.Clocks.ControllerPhaseProductPolynomialCode.point
          (z t).controllers) i) t
  rw [congrFun
    (HGAS.Clocks.ControllerPhaseProductPolynomialCode.realize_fieldCode
      parameters (z t).controllers) i]
  simpa [point, controllersEmbedding,
    PolynomialBlockCode.point_leftEmbedding,
    vectorField, controllersPoint] using hi

/-- Every real coordinate in every linked block satisfies the semantic
dynamic-clock equation read from the common controller state. -/
theorem linkedRealifyPoint_hasDerivAt_of_point
    (parameters : Fin q → RationalCode)
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode)
    (z : ℝ → ControllerProductLinkedJacobiFamilyState q b)
    (h :
      IsIntegralCurve
        (fun t => point (z t))
        (fun _ x =>
          PolynomialFieldCode.realize
            (fieldCode parameters omegaWeights numberWeights) x))
    (a : Fin b)
    (j : Fin localLinkedRealDimension)
    (t : ℝ) :
    HasDerivAt
      (fun s =>
        ComplexCoordinates.realifyPoint
          (LinkedJacobiPolynomialCode.point
            ((z s).linked a)) j)
      (ComplexCoordinates.realifyPoint
        (LinkedJacobiPolynomialCode.point
          ((vectorField
            (fun i =>
              (RationalCode.decode (parameters i) : ℝ))
            (fun d i =>
              (RationalCode.decode
                (omegaWeights d i) : ℝ))
            (fun d i =>
              (RationalCode.decode
                (numberWeights d i) : ℝ))
            (z t)).linked a)) j) t := by
  have ht := h t
  rw [hasDerivAt_pi] at ht
  let k : Fin (dimension q b) :=
    linkedFamilyEmbedding (q := q)
      (linkedBlockEmbedding a j)
  have hj := ht k
  change
    HasDerivAt
      (fun s => point (z s) k)
      (PolynomialFieldCode.realize
        (fieldCode parameters omegaWeights numberWeights)
        (point (z t)) k) t at hj
  rw [realize_fieldCode] at hj
  simpa only [k, point, linkedFamilyEmbedding,
    PolynomialBlockCode.point_rightEmbedding,
    linkedFamilyPoint_linkedBlockEmbedding] using hj

/-- The real block equations reassemble to the fourteen complex linked
equations with the instantaneous controller readouts. -/
theorem linkedPoint_hasDerivAt_of_point
    (parameters : Fin q → RationalCode)
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode)
    (z : ℝ → ControllerProductLinkedJacobiFamilyState q b)
    (h :
      IsIntegralCurve
        (fun t => point (z t))
        (fun _ x =>
          PolynomialFieldCode.realize
            (fieldCode parameters omegaWeights numberWeights) x))
    (a : Fin b)
    (i : Fin LinkedJacobiPolynomialCode.dimension)
    (t : ℝ) :
    HasDerivAt
      (fun s =>
        LinkedJacobiPolynomialCode.point
          ((z s).linked a) i)
      (LinkedJacobiPolynomialCode.point
        ((vectorField
          (fun k =>
            (RationalCode.decode (parameters k) : ℝ))
          (fun d k =>
            (RationalCode.decode
              (omegaWeights d k) : ℝ))
          (fun d k =>
            (RationalCode.decode
              (numberWeights d k) : ℝ))
          (z t)).linked a) i) t := by
  exact
    linkedPoint_hasDerivAt_of_realifyPoint
      (z := fun s => (z s).linked a)
      (v := fun s =>
        (vectorField
          (fun k =>
            (RationalCode.decode (parameters k) : ℝ))
          (fun d k =>
            (RationalCode.decode
              (omegaWeights d k) : ℝ))
          (fun d k =>
            (RationalCode.decode
              (numberWeights d k) : ℝ))
          (z s)).linked a)
      (fun j s =>
        linkedRealifyPoint_hasDerivAt_of_point
          parameters omegaWeights numberWeights z h a j s)
      i t

/-- If a block's two controller readouts are constant, the projected
block is a standard scaled linked-Jacobi trajectory with those constants. -/
theorem isScaledLinkedJacobiTrajectory_of_point
    (parameters : Fin q → RationalCode)
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode)
    (z : ℝ → ControllerProductLinkedJacobiFamilyState q b)
    (h :
      IsIntegralCurve
        (fun t => point (z t))
        (fun _ x =>
          PolynomialFieldCode.realize
            (fieldCode parameters omegaWeights numberWeights) x))
    (a : Fin b)
    (κZ κPhi : ℂ)
    (hkappaZ :
      ∀ t,
        kappaZ
            (fun d i =>
              (RationalCode.decode
                (omegaWeights d i) : ℝ))
            (fun d i =>
              (RationalCode.decode
                (numberWeights d i) : ℝ))
            (fun i =>
              (RationalCode.decode
                (parameters i) : ℝ))
            (z t) a =
          κZ)
    (hkappaPhi :
      ∀ t,
        kappaPhi
            (fun d i =>
              (RationalCode.decode
                (omegaWeights d i) : ℝ))
            (fun i =>
              (RationalCode.decode
                (parameters i) : ℝ))
            (z t) a =
          κPhi) :
    IsScaledLinkedJacobiTrajectory
      κZ κPhi (fun t => (z t).linked a) := by
  apply
    isScaledLinkedJacobiTrajectory_of_linkedPoint
      κZ κPhi
  intro i t
  have hi :=
    linkedPoint_hasDerivAt_of_point
      parameters omegaWeights numberWeights z h a i t
  simpa only [vectorField, hkappaZ t, hkappaPhi t] using hi

end ControllerProductLinkedJacobiFamilyPolynomialCode

end

end HGAS.Modular
