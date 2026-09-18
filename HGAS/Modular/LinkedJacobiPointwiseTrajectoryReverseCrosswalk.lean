import HGAS.Compiler.PolynomialExtensionPointwiseReverseCrosswalk
import HGAS.Modular.LinkedJacobiTrajectoryPolynomialReverseCrosswalk
import Mathlib.Tactic

/-!
# Pointwise reverse crosswalk for the linked-Jacobi family

This is the local-time counterpart of
`LinkedJacobiTrajectoryPolynomialReverseCrosswalk`.  It needs only one
derivative of the compiled common-controller point at one time.  The
result projects that derivative to the controller block and reassembles
the realified linked coordinates into complex linked-Jacobi equations.

The pointwise formulation is what a forward trajectory supplies at each
strictly positive time.
-/

namespace HGAS.Modular

open HGAS

noncomputable section

/-- At one fixed time, real and imaginary coordinate derivatives
reassemble into a complex linked-state coordinate derivative. -/
theorem linkedPoint_hasDerivAt_of_realifyPointAt
    {z : ℝ → LinkedJacobiState ℂ}
    {v : LinkedJacobiState ℂ}
    {t : ℝ}
    (h :
      ∀ j,
        HasDerivAt
          (fun s =>
            ComplexCoordinates.realifyPoint
              (LinkedJacobiPolynomialCode.point (z s)) j)
          (ComplexCoordinates.realifyPoint
            (LinkedJacobiPolynomialCode.point v) j) t)
    (i : Fin LinkedJacobiPolynomialCode.dimension) :
    HasDerivAt
      (fun s => LinkedJacobiPolynomialCode.point (z s) i)
      (LinkedJacobiPolynomialCode.point v i) t := by
  apply HGAS.HasDerivAt.complex_of_re_im
  · simpa only [
      ComplexCoordinates.realifyPoint_realIndex] using
      h (ComplexCoordinates.realIndex i)
  · simpa only [
      ComplexCoordinates.realifyPoint_imagIndex] using
      h (ComplexCoordinates.imagIndex i)

namespace ControllerProductLinkedJacobiFamilyPolynomialCode

variable {q b : ℕ}

/-- At a fixed time, projection of the compiled family derivative gives
the derivative of the common controller point. -/
theorem controllersPoint_hasDerivAt_of_pointAt
    (parameters : Fin q → RationalCode)
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode)
    (z : ℝ → ControllerProductLinkedJacobiFamilyState q b)
    (t : ℝ)
    (h :
      HasDerivAt
        (fun s => point (z s))
        (PolynomialFieldCode.realize
          (fieldCode parameters omegaWeights numberWeights)
          (point (z t))) t) :
    HasDerivAt
      (fun s => controllersPoint (z s))
      (PolynomialFieldCode.realize
        (HGAS.Clocks.ControllerPhaseProductPolynomialCode.fieldCode
          parameters)
        (controllersPoint (z t))) t := by
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi] at h
  have hi := h (controllersEmbedding (b := b) i)
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

/-- At one fixed time, every real coordinate in a selected linked block
satisfies its dynamic-clock equation. -/
theorem linkedRealifyPoint_hasDerivAt_of_pointAt
    (parameters : Fin q → RationalCode)
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode)
    (z : ℝ → ControllerProductLinkedJacobiFamilyState q b)
    (t : ℝ)
    (h :
      HasDerivAt
        (fun s => point (z s))
        (PolynomialFieldCode.realize
          (fieldCode parameters omegaWeights numberWeights)
          (point (z t))) t)
    (a : Fin b)
    (j : Fin localLinkedRealDimension) :
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
  rw [hasDerivAt_pi] at h
  let k : Fin (dimension q b) :=
    linkedFamilyEmbedding (q := q)
      (linkedBlockEmbedding a j)
  have hj := h k
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

/-- At one fixed time, the real block equations reassemble to all
fourteen complex linked-Jacobi equations. -/
theorem linkedPoint_hasDerivAt_of_pointAt
    (parameters : Fin q → RationalCode)
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode)
    (z : ℝ → ControllerProductLinkedJacobiFamilyState q b)
    (t : ℝ)
    (h :
      HasDerivAt
        (fun s => point (z s))
        (PolynomialFieldCode.realize
          (fieldCode parameters omegaWeights numberWeights)
          (point (z t))) t)
    (a : Fin b)
    (i : Fin LinkedJacobiPolynomialCode.dimension) :
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
    linkedPoint_hasDerivAt_of_realifyPointAt
      (z := fun s => (z s).linked a)
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
      (t := t)
      (fun j =>
        linkedRealifyPoint_hasDerivAt_of_pointAt
          parameters omegaWeights numberWeights z t h a j)
      i

end ControllerProductLinkedJacobiFamilyPolynomialCode

end

end HGAS.Modular
