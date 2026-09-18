import HGAS.Modular.SL2ZFrameFundamentalDomain
import HGAS.Modular.UpperHalfPlaneCurve

/-!
# Derivative of an integral modular action along a real curve

For `γ ∈ SL(2,ℤ)` and a differentiable curve `T : ℝ → ℍ`, the ordinary
Möbius derivative gives

```text
       d/dt (γ · T(t)) = T'(t) / (c T(t) + d)².
```

The denominator is exactly `UpperHalfPlane.denom` used by Mathlib's slash
action.  Keeping that literal denominator makes the later cancellation
with weight-two theta automorphy transparent.
-/

namespace HGAS.Modular

open Complex
open UpperHalfPlane hiding I
open Matrix ModularForm
open scoped MatrixGroups ModularForm

noncomputable section

/-- Chain rule for an integral modular transformation along a real
upper-half-plane curve. -/
theorem hasDerivAt_integral_smul_upperHalfPlaneCurve
    (γ : IntegralModularGroup)
    (T : ℝ → UpperHalfPlane) (t : ℝ) {v : ℂ}
    (hT :
      HasDerivAt (fun s : ℝ ↦ (T s : ℂ)) v t) :
    HasDerivAt
      (fun s : ℝ ↦ ((γ • T s : UpperHalfPlane) : ℂ))
      (v / UpperHalfPlane.denom
        (Matrix.SpecialLinearGroup.mapGL ℝ γ) (T t) ^ 2) t := by
  let g : GL (Fin 2) ℝ :=
    Matrix.SpecialLinearGroup.mapGL ℝ γ
  have hdet : g.val.det = 1 := by
    change ((g.det : ℝˣ) : ℝ) = 1
    rw [show g = Matrix.SpecialLinearGroup.mapGL ℝ γ by rfl,
      Matrix.SpecialLinearGroup.det_mapGL]
    rfl
  have hg : 0 < g.val.det := by
    rw [hdet]
    norm_num
  have houter :
      HasDerivAt
        (fun z : ℂ ↦
          ((g • UpperHalfPlane.ofComplex z : UpperHalfPlane) : ℂ))
        (g.val.det / UpperHalfPlane.denom g (T t) ^ 2)
        (T t : ℂ) := by
    exact
      (UpperHalfPlane.hasStrictDerivAt_smul hg (T t)).hasDerivAt
  have hcomp := houter.scomp t hT
  convert hcomp using 1
  · funext s
    change
      ((γ • T s : UpperHalfPlane) : ℂ) =
        ((g • UpperHalfPlane.ofComplex (T s : ℂ) :
          UpperHalfPlane) : ℂ)
    simp only [UpperHalfPlane.ofComplex_apply]
    rfl
  · rw [hdet]
    simp [g, smul_eq_mul, div_eq_mul_inv]

/-- If the transformed curve is an affine horizontal line, its displayed
real speed is the Möbius-transformed derivative. -/
theorem transformedVelocity_eq_horizontalSpeed
    (γ : IntegralModularGroup)
    (T : ℝ → UpperHalfPlane)
    (x y s : ℝ) (hy : 0 < y)
    (hline : ∀ u, γ • T u = horizontalLine x y s hy u)
    (t : ℝ) {v : ℂ}
    (hT :
      HasDerivAt (fun u : ℝ ↦ (T u : ℂ)) v t) :
    v / UpperHalfPlane.denom
          (Matrix.SpecialLinearGroup.mapGL ℝ γ) (T t) ^ 2 =
      (s : ℂ) := by
  have hleft :=
    hasDerivAt_integral_smul_upperHalfPlaneCurve γ T t hT
  have hright :
      HasDerivAt
        (fun u : ℝ ↦
          (horizontalLine x y s hy u : ℂ))
        (s : ℂ) t := by
    convert
      (complexHorizontalAffine_hasDerivAt x y s (t : ℂ)).comp_ofReal
        using 1
    funext u
    exact (complexHorizontalAffine_ofReal x y s u hy).symm
  exact HasDerivAt.unique
    (hleft.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun u ↦ by
        change
          (horizontalLine x y s hy u : ℂ) =
            ((γ • T u : UpperHalfPlane) : ℂ)
        exact congrArg
          (fun w : UpperHalfPlane ↦ (w : ℂ))
          (hline u).symm))
    hright

end

end HGAS.Modular
