import HGAS.Compiler.PolynomialExtensionWithinReverseCrosswalk
import HGAS.Modular.LinkedJacobiPointwiseTrajectoryReverseCrosswalk
import Mathlib.Tactic

/-!
# One-sided reverse crosswalk for a linked-Jacobi family

The results here retain `HasDerivWithinAt` on a prescribed time set.
They are used at the boundary `t = 0` of a physical forward trajectory.
-/

namespace HGAS.Modular

open HGAS

noncomputable section

theorem linkedPoint_hasDerivWithinAt_of_realifyPoint
    {z : ℝ → LinkedJacobiState ℂ}
    {v : LinkedJacobiState ℂ}
    {s : Set ℝ} {t : ℝ}
    (h :
      ∀ j,
        HasDerivWithinAt
          (fun u =>
            ComplexCoordinates.realifyPoint
              (LinkedJacobiPolynomialCode.point (z u)) j)
          (ComplexCoordinates.realifyPoint
            (LinkedJacobiPolynomialCode.point v) j) s t)
    (i : Fin LinkedJacobiPolynomialCode.dimension) :
    HasDerivWithinAt
      (fun u => LinkedJacobiPolynomialCode.point (z u) i)
      (LinkedJacobiPolynomialCode.point v i) s t := by
  apply HGAS.HasDerivWithinAt.complex_of_re_im
  · simpa only [
      ComplexCoordinates.realifyPoint_realIndex] using
      h (ComplexCoordinates.realIndex i)
  · simpa only [
      ComplexCoordinates.realifyPoint_imagIndex] using
      h (ComplexCoordinates.imagIndex i)

namespace ControllerProductLinkedJacobiFamilyPolynomialCode

variable {q b : ℕ}

theorem controllersPoint_hasDerivWithinAt_of_point
    (parameters : Fin q → RationalCode)
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode)
    (z : ℝ → ControllerProductLinkedJacobiFamilyState q b)
    (s : Set ℝ) (t : ℝ)
    (h :
      HasDerivWithinAt
        (fun u => point (z u))
        (PolynomialFieldCode.realize
          (fieldCode parameters omegaWeights numberWeights)
          (point (z t))) s t) :
    HasDerivWithinAt
      (fun u => controllersPoint (z u))
      (PolynomialFieldCode.realize
        (HGAS.Clocks.ControllerPhaseProductPolynomialCode.fieldCode
          parameters)
        (controllersPoint (z t))) s t := by
  rw [hasDerivWithinAt_pi]
  intro i
  rw [hasDerivWithinAt_pi] at h
  have hi := h (controllersEmbedding (b := b) i)
  change
    HasDerivWithinAt
      (fun u => point (z u) (controllersEmbedding i))
      (PolynomialFieldCode.realize
        (fieldCode parameters omegaWeights numberWeights)
        (point (z t)) (controllersEmbedding i)) s t at hi
  rw [realize_fieldCode] at hi
  change
    HasDerivWithinAt
      (fun u =>
        HGAS.Clocks.ControllerPhaseProductPolynomialCode.point
          (z u).controllers i)
      (PolynomialFieldCode.realize
        (HGAS.Clocks.ControllerPhaseProductPolynomialCode.fieldCode
          parameters)
        (HGAS.Clocks.ControllerPhaseProductPolynomialCode.point
          (z t).controllers) i) s t
  rw [congrFun
    (HGAS.Clocks.ControllerPhaseProductPolynomialCode.realize_fieldCode
      parameters (z t).controllers) i]
  simpa [point, controllersEmbedding,
    PolynomialBlockCode.point_leftEmbedding,
    vectorField, controllersPoint] using hi

theorem linkedRealifyPoint_hasDerivWithinAt_of_point
    (parameters : Fin q → RationalCode)
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode)
    (z : ℝ → ControllerProductLinkedJacobiFamilyState q b)
    (s : Set ℝ) (t : ℝ)
    (h :
      HasDerivWithinAt
        (fun u => point (z u))
        (PolynomialFieldCode.realize
          (fieldCode parameters omegaWeights numberWeights)
          (point (z t))) s t)
    (a : Fin b)
    (j : Fin localLinkedRealDimension) :
    HasDerivWithinAt
      (fun u =>
        ComplexCoordinates.realifyPoint
          (LinkedJacobiPolynomialCode.point
            ((z u).linked a)) j)
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
            (z t)).linked a)) j) s t := by
  rw [hasDerivWithinAt_pi] at h
  let k : Fin (dimension q b) :=
    linkedFamilyEmbedding (q := q)
      (linkedBlockEmbedding a j)
  have hj := h k
  change
    HasDerivWithinAt
      (fun u => point (z u) k)
      (PolynomialFieldCode.realize
        (fieldCode parameters omegaWeights numberWeights)
        (point (z t)) k) s t at hj
  rw [realize_fieldCode] at hj
  simpa only [k, point, linkedFamilyEmbedding,
    PolynomialBlockCode.point_rightEmbedding,
    linkedFamilyPoint_linkedBlockEmbedding] using hj

theorem linkedPoint_hasDerivWithinAt_of_point
    (parameters : Fin q → RationalCode)
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode)
    (z : ℝ → ControllerProductLinkedJacobiFamilyState q b)
    (s : Set ℝ) (t : ℝ)
    (h :
      HasDerivWithinAt
        (fun u => point (z u))
        (PolynomialFieldCode.realize
          (fieldCode parameters omegaWeights numberWeights)
          (point (z t))) s t)
    (a : Fin b)
    (i : Fin LinkedJacobiPolynomialCode.dimension) :
    HasDerivWithinAt
      (fun u =>
        LinkedJacobiPolynomialCode.point
          ((z u).linked a) i)
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
          (z t)).linked a) i) s t := by
  exact
    linkedPoint_hasDerivWithinAt_of_realifyPoint
      (z := fun u => (z u).linked a)
      (v :=
        (vectorField
          (fun k =>
            (RationalCode.decode (parameters k) : ℝ))
          (fun d k =>
            (RationalCode.decode
              (omegaWeights d k) : ℝ))
          (fun d k =>
            (RationalCode.decode
              (numberWeights d k) : ℝ))
          (z t)).linked a)
      (s := s) (t := t)
      (fun j =>
        linkedRealifyPoint_hasDerivWithinAt_of_point
          parameters omegaWeights numberWeights z s t h a j)
      i

end ControllerProductLinkedJacobiFamilyPolynomialCode

end

end HGAS.Modular
