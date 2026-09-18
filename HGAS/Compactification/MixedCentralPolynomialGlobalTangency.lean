import HGAS.Compactification.MixedCentralPolynomialField
import HGAS.Wrapper.UnitSphereWrapperChart
import Mathlib.Tactic

/-!
# Global tangency of the mixed central compiler

The chart-semantics theorem for mixed central compactification is naturally
stated at points

```
                 x_j = w_b z_j
```

in the affine blocks.  At an equator `w_b = 0`, however, an arbitrary point
of the compactifying sphere need not have that form.  Tangency must therefore
be checked directly on the emitted polynomial, without division by `w_b`.

This file supplies that global check.  At an arbitrary ambient point
`chartPoint x w`, let `p̃_j` be the value of the denominator-cleared source
polynomial `homogenize P_j`.  Literal evaluation of the emitted field is the
semantic mixed central field with common scalar `1` and velocity `p̃`.
Consequently:

* every new affine sphere is tangent by the central-projective identity;
* an old compact sphere is tangent whenever its cleared source velocity is
  tangent there.

The final theorems translate the result into the product-sphere vocabulary
used by the homogeneous wrapper.
-/

namespace HGAS

open _root_.MvPolynomial

noncomputable section

namespace MixedCentralPolynomialCode

variable {n k l : ℕ}

/-- Values of all denominator-cleared source coordinates at an arbitrary
mixed ambient point. -/
def clearedSourceVelocity
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (P : PolynomialFieldCode n)
    (y : Fin (n + k) → R) :
    Fin n → R :=
  fun j ↦
    eval₂Hom (algebraMap ℚ R) y
      (PolynomialCode.decode (homogenize layout M (P j)))

/-- Every mixed ambient point is uniquely recovered from its old and chart
coordinates. -/
theorem chartPoint_decompose
    {R : Type*}
    (y : Fin (n + k) → R) :
    chartPoint
        (fun j ↦ y (xIndex (k := k) j))
        (fun b ↦ y (wIndex (n := n) b)) =
      y := by
  funext q
  obtain ⟨j | b, rfl⟩ := finSumFinEquiv.surjective q
  · simp [xIndex, chartPoint,
      MultiCentralPolynomialCode.xIndex,
      MultiCentralPolynomialCode.chartPoint]
  · simp [wIndex, chartPoint,
      MultiCentralPolynomialCode.wIndex,
      MultiCentralPolynomialCode.chartPoint]

/-- Literal evaluation of the mixed compiler at an arbitrary point.  No
chart denominator is introduced, so this theorem remains valid on every
equator and corner. -/
theorem eval₂Hom_fieldCode_chartPoint
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (P : PolynomialFieldCode n)
    (x : Fin n → R) (w : Fin k → R) :
    (fun q ↦
      eval₂Hom (algebraMap ℚ R) (chartPoint x w)
        (PolynomialCode.decode (fieldCode layout M P q))) =
      mixedAmbientField layout 1 w x
        (clearedSourceVelocity layout M P (chartPoint x w)) := by
  funext q
  cases hq : finSumFinEquiv.symm q with
  | inl j =>
      have hq' : q = xIndex (k := k) j := by
        rw [xIndex, MultiCentralPolynomialCode.xIndex, ← hq]
        simp
      rw [hq']
      simp only [fieldCode, mixedAmbientField,
        finSumFinEquiv_symm_xIndex]
      change
        eval₂Hom (algebraMap ℚ R) (chartPoint x w)
            (PolynomialCode.decode (xFieldCode layout M P j)) =
          mixedXField layout 1 w x
            (clearedSourceVelocity layout M P (chartPoint x w)) j
      cases hj : layout j with
      | inl b =>
          simp only [xFieldCode, hj,
            PolynomialCode.decode_mul_code,
            PolynomialCode.decode_sub_code,
            PolynomialCode.decode_varCode, map_mul, map_sub,
            eval₂Hom_X', chartPoint_wIndex, chartPoint_xIndex,
            mixedXField, clearedSourceVelocity]
          rw [eval₂Hom_affineBlockDotCode]
          unfold affineBlockDot
          simp only [chartPoint_xIndex, clearedSourceVelocity]
          ring
      | inr c =>
          simp [xFieldCode, hj, mixedXField,
            clearedSourceVelocity]
  | inr b =>
      have hq' : q = wIndex (n := n) b := by
        rw [wIndex, MultiCentralPolynomialCode.wIndex, ← hq]
        simp
      rw [hq']
      simp only [fieldCode, mixedAmbientField,
        finSumFinEquiv_symm_wIndex]
      change
        eval₂Hom (algebraMap ℚ R) (chartPoint x w)
            (PolynomialCode.decode (wFieldCode layout M P b)) =
          mixedWField layout 1 w x
            (clearedSourceVelocity layout M P (chartPoint x w)) b
      simp only [wFieldCode,
        PolynomialCode.decode_neg_code,
        PolynomialCode.decode_mul_code,
        PolynomialCode.decode_pow_code,
        PolynomialCode.decode_varCode, map_neg, map_mul, map_pow,
        eval₂Hom_X', chartPoint_wIndex,
        mixedWField]
      rw [eval₂Hom_affineBlockDotCode]
      unfold affineBlockDot
      simp only [chartPoint_xIndex, clearedSourceVelocity]
      ring

/-- Global target-block tangency of the emitted mixed field.  The affine
target spheres need only satisfy their sphere equations; compact target
blocks require the corresponding cleared source dot products to vanish. -/
theorem fieldCode_target_tangent_chartPoint
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (P : PolynomialFieldCode n)
    (x : Fin n → R) (w : Fin k → R)
    (haffine :
      ∀ b, affineBlockNormSq layout x b + w b ^ 2 = 1)
    (hcompact :
      ∀ c, compactBlockDot layout x
        (clearedSourceVelocity layout M P (chartPoint x w)) c = 0) :
    ∀ d,
      targetBlockDot layout (chartPoint x w)
        (fun q ↦
          eval₂Hom (algebraMap ℚ R) (chartPoint x w)
            (PolynomialCode.decode (fieldCode layout M P q))) d = 0 := by
  rw [eval₂Hom_fieldCode_chartPoint]
  exact
    mixedAmbientField_target_tangent
      layout 1 w x
        (clearedSourceVelocity layout M P (chartPoint x w))
        haffine hcompact

/-- The wrapper's block-dot definition is literally the mixed compiler's
target-block dot product. -/
theorem sourceBlockDot_targetBlock
    (layout : Fin n → Fin k ⊕ Fin l)
    (y v : Fin (n + k) → ℝ) (d : Fin (k + l)) :
    UnitSpherePolynomialWrapper.sourceBlockDot
        (targetBlock layout) y v d =
      targetBlockDot layout y v d :=
  rfl

/-- The two block-norm conventions agree. -/
theorem sourceBlockNormSq_targetBlock
    (layout : Fin n → Fin k ⊕ Fin l)
    (y : Fin (n + k) → ℝ) (d : Fin (k + l)) :
    UnitSpherePolynomialWrapper.sourceBlockNormSq
        (targetBlock layout) y d =
      targetBlockNormSq layout y d := by
  unfold UnitSpherePolynomialWrapper.sourceBlockNormSq
    targetBlockNormSq targetBlockDot
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : targetBlock layout q = d
  · simp [hq, pow_two]
  · simp [hq]

/-- A wrapper product-sphere point supplies exactly the affine and compact
sphere equations needed by the global tangency theorem. -/
theorem onSourceProductSpheres_targetBlock_iff
    (layout : Fin n → Fin k ⊕ Fin l)
    (x : Fin n → ℝ) (w : Fin k → ℝ) :
    UnitSpherePolynomialWrapper.OnSourceProductSpheres
        (targetBlock layout) (chartPoint x w) ↔
      (∀ b, affineBlockNormSq layout x b + w b ^ 2 = 1) ∧
      (∀ c, compactBlockNormSq layout x c = 1) := by
  constructor
  · intro h
    constructor
    · intro b
      have hb :=
        h (finSumFinEquiv (Sum.inl b : Fin k ⊕ Fin l))
      rw [sourceBlockNormSq_targetBlock,
        targetBlockNormSq_affine] at hb
      exact hb
    · intro c
      have hc :=
        h (finSumFinEquiv (Sum.inr c : Fin k ⊕ Fin l))
      rw [sourceBlockNormSq_targetBlock,
        targetBlockNormSq_compact] at hc
      exact hc
  · rintro ⟨haffine, hcompact⟩ d
    rw [sourceBlockNormSq_targetBlock]
    obtain ⟨b | c, rfl⟩ := finSumFinEquiv.surjective d
    · exact targetBlockNormSq_affine layout x w b |>.trans
        (haffine b)
    · exact targetBlockNormSq_compact layout x w c |>.trans
        (hcompact c)

/-- Wrapper-facing global tangency theorem. -/
theorem fieldCode_sourceTangentAt_chartPoint
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (P : PolynomialFieldCode n)
    (x : Fin n → ℝ) (w : Fin k → ℝ)
    (hspheres :
      UnitSpherePolynomialWrapper.OnSourceProductSpheres
        (targetBlock layout) (chartPoint x w))
    (hcompact :
      ∀ c, compactBlockDot layout x
        (clearedSourceVelocity layout M P (chartPoint x w)) c = 0) :
    UnitSpherePolynomialWrapper.SourceTangentAt
        (targetBlock layout) (chartPoint x w)
        (PolynomialFieldCode.realize (fieldCode layout M P)
          (chartPoint x w)) := by
  have haffine :=
    (onSourceProductSpheres_targetBlock_iff layout x w).mp
      hspheres |>.1
  intro d
  rw [sourceBlockDot_targetBlock]
  exact
    fieldCode_target_tangent_chartPoint
      layout M P x w haffine hcompact d

end MixedCentralPolynomialCode

end

end HGAS
