import HGAS.Modular.CanonicalLambdaCovering
import HGAS.Modular.ThetaTransformations

/-!
# Explicit deck-generator identities for canonical lambda

The global modular-lambda covering theorem has two elementary transformation
identities at its entrance:

```
  Λ(τ + 1) = Λ(τ) / (Λ(τ) - 1),
  Λ(-1 / τ) = 1 - Λ(τ).
```

It follows that translation by two and its `S`-conjugate preserve lambda.
This file proves those statements directly from the already formalized
theta transformation laws.  These are the expected generators of the
projective level-two deck group.  The separate global tasks of constructing
the quotient, separating fibers, and proving surjectivity are not assumed
here.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I
open Complex Real ModularGroup ModularForm SlashAction
open scoped MatrixGroups ModularForm

noncomputable section

/-- The point `-1/z` of the upper half-plane, written in the same form as
Mathlib's slash-action formula for the generator `S`. -/
def modularSPoint (z : ℍ) : ℍ :=
  UpperHalfPlane.mk (-z)⁻¹ z.im_inv_neg_coe_pos

/-- Lambda's transformation under translation by one. -/
theorem canonicalLambda_vadd_one (z : ℍ) :
    canonicalLambda ((1 : ℝ) +ᵥ z) =
      canonicalLambda z / (canonicalLambda z - 1) := by
  have h₂ :
      H₂ ((1 : ℝ) +ᵥ z) = -H₂ z := by
    simpa only [modularSlashT_apply, Pi.neg_apply] using
      congrFun H₂_T_action z
  have h₃ :
      H₃ ((1 : ℝ) +ᵥ z) = H₄ z := by
    simpa only [modularSlashT_apply] using
      congrFun H₃_T_action z
  rw [canonicalLambda, h₂, h₃, canonicalLambda]
  have hJacobi : H₂ z + H₄ z = H₃ z := by
    simpa only [Pi.add_apply] using
      congrFun jacobi_quartic_identity z
  have hdiff : H₂ z - H₃ z ≠ 0 := by
    rw [show H₂ z - H₃ z = -H₄ z by
      linear_combination hJacobi]
    exact neg_ne_zero.mpr (H₄_ne_zero z)
  field_simp [H₃_ne_zero z, H₄_ne_zero z, hdiff]
  linear_combination -H₂ z * hJacobi

/-- Translation by two preserves canonical lambda. -/
theorem canonicalLambda_vadd_two (z : ℍ) :
    canonicalLambda ((2 : ℝ) +ᵥ z) =
      canonicalLambda z := by
  have hfirst :=
    canonicalLambda_vadd_one z
  have hsecond :=
    canonicalLambda_vadd_one ((1 : ℝ) +ᵥ z)
  have hvadd :
      (1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ z) =
        (2 : ℝ) +ᵥ z := by
    rw [← add_vadd]
    norm_num
  rw [hvadd] at hsecond
  rw [hfirst] at hsecond
  have hneOne := canonicalLambda_ne_one z
  calc
    canonicalLambda ((2 : ℝ) +ᵥ z)
        = (canonicalLambda z /
            (canonicalLambda z - 1)) /
          (canonicalLambda z /
              (canonicalLambda z - 1) - 1) := hsecond
    _ = canonicalLambda z := by
      field_simp [sub_ne_zero.mpr hneOne]
      ring

/-- Lambda's transformation under inversion. -/
theorem canonicalLambda_modularSPoint (z : ℍ) :
    canonicalLambda (modularSPoint z) =
      1 - canonicalLambda z := by
  have h₂ :
      H₂ (modularSPoint z) * z ^ (-2 : ℤ) =
        -H₄ z := by
    simpa only [modularSlashS_apply, Pi.neg_apply,
      modularSPoint] using
        congrFun H₂_S_action z
  have h₃ :
      H₃ (modularSPoint z) * z ^ (-2 : ℤ) =
        -H₃ z := by
    simpa only [modularSlashS_apply, Pi.neg_apply,
      modularSPoint] using
        congrFun H₃_S_action z
  have hz : (z : ℂ) ≠ 0 := by
    intro hzero
    have himzero :
        (z : ℂ).im = 0 := by rw [hzero]; rfl
    exact z.im_pos.ne' himzero
  have hfactor : (z : ℂ) ^ (-2 : ℤ) ≠ 0 :=
    zpow_ne_zero _ hz
  have h₂' :
      H₂ (modularSPoint z) =
        -H₄ z / z ^ (-2 : ℤ) :=
    (eq_div_iff hfactor).mpr h₂
  have h₃' :
      H₃ (modularSPoint z) =
        -H₃ z / z ^ (-2 : ℤ) :=
    (eq_div_iff hfactor).mpr h₃
  have hJacobi : H₂ z + H₄ z = H₃ z := by
    simpa only [Pi.add_apply] using
      congrFun jacobi_quartic_identity z
  rw [canonicalLambda, h₂', h₃',
    canonicalLambda]
  field_simp [H₃_ne_zero z, hfactor]
  linear_combination hJacobi

/-- The `S`-conjugate of translation by two preserves lambda.  This is the
second standard projective generator of the level-two deck group. -/
theorem canonicalLambda_modularSPoint_vadd_two_modularSPoint
    (z : ℍ) :
    canonicalLambda
        (modularSPoint
          ((2 : ℝ) +ᵥ modularSPoint z)) =
      canonicalLambda z := by
  rw [canonicalLambda_modularSPoint,
    canonicalLambda_vadd_two,
    canonicalLambda_modularSPoint]
  ring

end

end HGAS.Modular
