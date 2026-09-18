import HGAS.Modular.GammaTwoThetaQuarticAutomorphy
import HGAS.Modular.IntegralModularActionDerivative

/-!
# Cancellation of modular velocity with weight-two theta automorphy

Let `T(t)` be a differentiable upper-half-plane curve and let
`γ ∈ SL(2,ℤ)`.  If

```text
                    γ · T(t) = x + s t + i y,
```

then the Möbius derivative is

```text
                    s = T'(t)/(cT(t)+d)².
```

The weight-two slash identity for the theta quartics contains the inverse
factor `(cT+d)⁻²`.  Multiplying a theta quartic by `T'(t)` therefore
cancels the automorphy factor exactly, leaving the constant horizontal
speed `s` and the finite signed permutation determined modulo two.

This small lemma is the normalization mechanism behind the closed-orbit
moment selector.  It avoids choosing any square root of an automorphy
factor.
-/

namespace HGAS.Modular

open Complex
open UpperHalfPlane hiding I
open Matrix ModularForm
open scoped MatrixGroups ModularForm

noncomputable section

/-- Pointwise value form of signed theta-quartic automorphy. -/
theorem thetaEvenQuartic_smul_value
    (γ : IntegralModularGroup)
    (i : Fin 3) (τ : UpperHalfPlane) :
    thetaEvenQuartic i (γ • τ) /
          UpperHalfPlane.denom
            (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ ^ 2 =
      (thetaQuarticSign (reduceModTwo γ) i : ℂ) *
        thetaEvenQuartic
          (thetaSquareIndex (reduceModTwo γ) i) τ := by
  have hfun := thetaEvenQuartic_smul γ i
  have hvalue := congrFun hfun τ
  rw [ModularForm.SL_slash_apply] at hvalue
  simpa only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv,
    zpow_neg, Int.reduceNeg, inv_pow] using hvalue

/-- The transformed derivative and the theta weight cancel exactly. -/
theorem velocity_mul_thetaQuartic_index_eq
    (γ : IntegralModularGroup)
    (T : ℝ → UpperHalfPlane)
    (x y s : ℝ) (hy : 0 < y)
    (hline : ∀ u, γ • T u = horizontalLine x y s hy u)
    (t : ℝ) {v : ℂ}
    (hT :
      HasDerivAt (fun u : ℝ ↦ (T u : ℂ)) v t)
    (i : Fin 3) :
    v *
        thetaEvenQuartic
          (thetaSquareIndex (reduceModTwo γ) i) (T t) =
      (thetaQuarticSign (reduceModTwo γ) i : ℂ) *
        (s : ℂ) *
          thetaEvenQuartic i (γ • T t) := by
  let D : ℂ :=
    UpperHalfPlane.denom
      (Matrix.SpecialLinearGroup.mapGL ℝ γ) (T t)
  let ε : ℂ :=
    (thetaQuarticSign (reduceModTwo γ) i : ℂ)
  have hD : D ≠ 0 := by
    exact UpperHalfPlane.denom_ne_zero _ _
  have hvelocity :
      v / D ^ 2 = (s : ℂ) := by
    simpa only [D] using
      transformedVelocity_eq_horizontalSpeed
        γ T x y s hy hline t hT
  have hslash :
      thetaEvenQuartic i (γ • T t) / D ^ 2 =
        ε *
          thetaEvenQuartic
            (thetaSquareIndex (reduceModTwo γ) i) (T t) := by
    simpa only [D, ε] using
      thetaEvenQuartic_smul_value γ i (T t)
  have hε : ε ^ 2 = 1 := by
    dsimp only [ε]
    exact_mod_cast thetaQuarticSign_sq (reduceModTwo γ) i
  field_simp [hD] at hvelocity hslash
  rw [hvelocity, hslash]
  change
    D ^ 2 * (s : ℂ) *
        thetaEvenQuartic
          (thetaSquareIndex (reduceModTwo γ) i) (T t) =
      ε * (s : ℂ) *
        (D ^ 2 * ε *
          thetaEvenQuartic
            (thetaSquareIndex (reduceModTwo γ) i) (T t))
  calc
    D ^ 2 * (s : ℂ) *
          thetaEvenQuartic
            (thetaSquareIndex (reduceModTwo γ) i) (T t) =
        ε ^ 2 *
          (D ^ 2 * (s : ℂ) *
            thetaEvenQuartic
              (thetaSquareIndex (reduceModTwo γ) i) (T t)) := by
          rw [hε, one_mul]
    _ = _ := by ring

end

end HGAS.Modular
