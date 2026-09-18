import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Complex.Basic

/-!
# A real chain rule for a holomorphic function of two variables

The theta trajectory depends holomorphically on an elliptic variable and
a modular variable, while the dynamical trajectory is parametrized by
real time.  This small module isolates the resulting mixed-scalar chain
rule.

If the two complex partial derivatives of `F` are `A` and `B`, and real
paths `x,y` have complex-valued velocities `x',y'`, then

```
       d/dt F(x(t),y(t)) = x' * A + y' * B.
```

The proof first applies the Fréchet chain rule after restriction of
scalars from `ℂ` to `ℝ`, and then uses complex linearity to split the
direction `(x',y')`.
-/

namespace HGAS.Modular

open Complex

noncomputable section

/-- Real-time chain rule for a holomorphic function of two complex
variables, expressed solely in terms of its two ordinary partial
derivatives. -/
theorem HasDerivAt.comp_twoComplex
    {F : ℂ × ℂ → ℂ} {x y A B : ℂ}
    (hF : DifferentiableAt ℂ F (x, y))
    (hxPartial :
      HasDerivAt (fun z : ℂ => F (z, y)) A x)
    (hyPartial :
      HasDerivAt (fun z : ℂ => F (x, z)) B y)
    {ξ η : ℝ → ℂ} {t : ℝ} {ξ' η' : ℂ}
    (hξ : HasDerivAt ξ ξ' t)
    (hη : HasDerivAt η η' t)
    (hξt : ξ t = x)
    (hηt : η t = y) :
    HasDerivAt
      (fun s : ℝ => F (ξ s, η s))
      (ξ' * A + η' * B) t := by
  let L : (ℂ × ℂ) →L[ℂ] ℂ :=
    fderiv ℂ F (x, y)
  have hLF :
      HasFDerivAt F L (x, y) := by
    simpa only [L] using hF.hasFDerivAt
  have hfirstCurve :
      HasDerivAt
        (fun z : ℂ => (z, y))
        ((1, 0) : ℂ × ℂ) x :=
    (hasDerivAt_id x).prodMk
      (hasDerivAt_const x y)
  have hsecondCurve :
      HasDerivAt
        (fun z : ℂ => (x, z))
        ((0, 1) : ℂ × ℂ) y :=
    (hasDerivAt_const y x).prodMk
      (hasDerivAt_id y)
  have hLA :
      L ((1, 0) : ℂ × ℂ) = A :=
    (hLF.comp_hasDerivAt x hfirstCurve).unique
      hxPartial
  have hLB :
      L ((0, 1) : ℂ × ℂ) = B :=
    (hLF.comp_hasDerivAt y hsecondCurve).unique
      hyPartial
  have hinner :
      HasDerivAt
        (fun s : ℝ => (ξ s, η s))
        (ξ', η') t :=
    hξ.prodMk hη
  have hLFactual :
      HasFDerivAt F L (ξ t, η t) := by
    simpa only [hξt, hηt] using hLF
  have hcomp :=
    (hLFactual.restrictScalars ℝ).comp_hasDerivAt
      t hinner
  convert hcomp using 1
  change
    ξ' * A + η' * B =
      L (ξ', η')
  have hv :
      ((ξ', η') : ℂ × ℂ) =
        ξ' • ((1, 0) : ℂ × ℂ) +
          η' • ((0, 1) : ℂ × ℂ) := by
    ext <;> simp
  rw [hv, map_add, map_smul, map_smul, hLA, hLB]
  simp only [smul_eq_mul]

end

end HGAS.Modular
