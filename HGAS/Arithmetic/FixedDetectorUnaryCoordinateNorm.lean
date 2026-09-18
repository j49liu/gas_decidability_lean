import HGAS.Arithmetic.FixedDetectorPolynomialCode
import HGAS.Analysis.FiniteCoordinateNormSq
import HGAS.Compiler.AllAffineCompactSourceChart
import Mathlib.Tactic

/-!
# Unary-coordinate bounds inside the fixed detector

The fixed detector is assembled from several canonical Euclidean block
encodings: controller coordinates, a family of realified linked Jacobi
states, gauges, reciprocals, and the final right-hand-side oscillator.
This module records the norm estimate needed by the compactification
argument without exposing raw ambient indices.

For every linked unary block, its complex `C` coordinate contributes
exactly two real squares to the complete detector norm.  Therefore

```text
  ‖Cⱼ‖² ≤ ‖point(z)‖².
```

The second theorem is independent of the detector layout.  It says that
any nonnegative scalar whose square is bounded by an affine squared norm
has every even power bounded by the reciprocal compactification speed:

```text
  a² ≤ ‖x‖²  ⇒  a^(2K) ≤ ((1 + ‖x‖²)⁻ᴷ)⁻¹.
```

Both statements are reusable by other coordinate-based observables.
-/

namespace HGAS

open Analysis.FiniteCoordinateNormSq
open Modular

noncomputable section

/-- The squared norm of any linked unary `C` coordinate is bounded by
the squared norm of the complete fixed-detector point. -/
theorem fixedDetector_unaryC_norm_sq_le
    {eqs vars : ℕ}
    (z : FixedDetectorPolynomialCode.State eqs vars)
    (j : Fin vars) :
    ‖(z.base.base.source.linked j).unary.C‖ ^ 2 ≤
      normSq (FixedDetectorPolynomialCode.point z) := by
  let linked := z.base.base.source.linked j
  have hC :
      ‖linked.unary.C‖ ^ 2 ≤
        normSq
          (ComplexCoordinates.realifyPoint
            (LinkedJacobiPolynomialCode.point linked)) := by
    rw [normSq_realifyPoint]
    have hterm :
        ‖linked.unary.C‖ ^ 2 =
          ‖LinkedJacobiPolynomialCode.point linked
              (LinkedJacobiPolynomialCode.unaryEmbedding
                UnaryPolynomialCode.CIndex)‖ ^ 2 := by
      simp [LinkedJacobiPolynomialCode.point,
        LinkedJacobiPolynomialCode.unaryEmbedding,
        UnaryPolynomialCode.modularPoint,
        UnaryPolynomialCode.CIndex]
    rw [hterm]
    exact Finset.single_le_sum
      (fun i _ ↦ pow_nonneg
        (norm_nonneg
          (LinkedJacobiPolynomialCode.point linked i)) 2)
      (Finset.mem_univ _)
  have hblock :
      normSq
          (ComplexCoordinates.realifyPoint
            (LinkedJacobiPolynomialCode.point linked)) ≤
        normSq
          (ControllerProductLinkedJacobiFamilyPolynomialCode.linkedFamilyPoint
            z.base.base.source) := by
    rw [ControllerProductLinkedJacobiFamilyPolynomialCode.linkedFamilyPoint,
      normSq_flattenPoint]
    exact Finset.single_le_sum
      (fun a _ ↦ normSq_nonneg
        (ComplexCoordinates.realifyPoint
          (LinkedJacobiPolynomialCode.point
            (z.base.base.source.linked a))))
      (Finset.mem_univ j)
  have hsource :
      normSq
          (ControllerProductLinkedJacobiFamilyPolynomialCode.linkedFamilyPoint
            z.base.base.source) ≤
        normSq
          (ControllerProductLinkedJacobiFamilyPolynomialCode.point
            z.base.base.source) := by
    rw [ControllerProductLinkedJacobiFamilyPolynomialCode.point,
      normSq_blockPoint]
    exact le_add_of_nonneg_left
      (normSq_nonneg
        (ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint
          z.base.base.source))
  have hgauge :
      normSq
          (ControllerProductLinkedJacobiFamilyPolynomialCode.point
            z.base.base.source) ≤
        normSq
          (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.point
            z.base.base) := by
    rw [ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.point,
      ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.rawState,
      ComplexGaugeFamilyPolynomialCode.point,
      ComplexReciprocalFamilyPolynomialCode.point,
      normSq_blockPoint]
    exact le_add_of_nonneg_right
      (normSq_nonneg
        (ComplexReciprocalFamilyPolynomialCode.reciprocalPoint
          z.base.base.gauge))
  have hreciprocal :
      normSq
          (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.point
            z.base.base) ≤
        normSq
          (DetectorPoissonReciprocalCode.point z.base) := by
    rw [DetectorPoissonReciprocalCode.point,
      DetectorPoissonReciprocalCode.rawState,
      ComplexReciprocalFamilyPolynomialCode.point,
      normSq_blockPoint]
    exact le_add_of_nonneg_right
      (normSq_nonneg
        (ComplexReciprocalFamilyPolynomialCode.reciprocalPoint
          z.base.reciprocal))
  have hfull :
      normSq (DetectorPoissonReciprocalCode.point z.base) ≤
        normSq (FixedDetectorPolynomialCode.point z) := by
    rw [FixedDetectorPolynomialCode.point,
      Clocks.RHSOscillatorPolynomialCode.combinedPoint,
      normSq_blockPoint]
    exact le_add_of_nonneg_right
      (normSq_nonneg ![z.rhs.c, z.rhs.d])
  exact hC.trans (hblock.trans (hsource.trans
    (hgauge.trans (hreciprocal.trans hfull))))

/-- A square bound implies domination of all matching even powers by
reciprocal affine compactification speed. -/
theorem evenPower_le_inverse_affineSpeed
    {n K : ℕ} {a : ℝ} {x : Fin n → ℝ}
    (ha : 0 ≤ a)
    (hax : a ^ 2 ≤ normSq x) :
    a ^ (2 * K) ≤
      (CompactAccumulatorPipelineCode.AllAffineCompactSourceChart.affineSpeed
        K x)⁻¹ := by
  have hbase :
      a ^ 2 ≤ 1 + normSq x := by
    linarith
  have hpow :
      (a ^ 2) ^ K ≤ (1 + normSq x) ^ K :=
    pow_le_pow_left₀ (pow_nonneg ha 2) hbase K
  rw [← pow_mul] at hpow
  rw [CompactAccumulatorPipelineCode.AllAffineCompactSourceChart.affineSpeed]
  rw [inv_pow, inv_inv]
  exact hpow

end

end HGAS
