import HGAS.Modular.JacobiThetaPrimeHeatEquation

/-!
# Differentiated heat equation for the classical theta characteristics

Mathlib's basic series is `θ₃`.  Our `θ₂` is obtained from it by the
standard half-characteristic transformation

```
  θ₂(z|τ) =
    exp(π i (τ/4+z)) · θ₃(z+τ/2|τ).
```

This file checks, by the chain rule, that the differentiated heat
equation is preserved by that transformation and then transfers it to
`θ₁(z|τ) = -θ₂(z+1/2|τ)`.
-/

namespace HGAS.Modular

open Complex Real
open UpperHalfPlane hiding I

noncomputable section

/-- Third elliptic derivative of classical `θ₂`. -/
def jacobiTheta2Third
    (z : ℂ) (τ : ℍ) : ℂ :=
  deriv (fun w =>
    jacobiTheta2Second w τ) z

/-- Third elliptic derivative of classical `θ₁`. -/
def jacobiTheta1Third
    (z : ℂ) (τ : ℍ) : ℂ :=
  deriv (fun w =>
    jacobiTheta1Second w τ) z

theorem hasDerivAt_jacobiTheta2Second
    (z : ℂ) (τ : ℍ) :
    HasDerivAt
      (fun w => jacobiTheta2Second w τ)
      (jacobiTheta2Third z τ) z :=
  (differentiable_jacobiTheta2Second τ z).hasDerivAt

theorem hasDerivAt_jacobiTheta1Second
    (z : ℂ) (τ : ℍ) :
    HasDerivAt
      (fun w => jacobiTheta1Second w τ)
      (jacobiTheta1Third z τ) z :=
  (differentiable_jacobiTheta1Second τ z).hasDerivAt

/-- The elliptic direction of the joint derivative of the basic prime
series is its second derivative. -/
theorem jacobiTheta₂PrimeFDeriv_fst_eq
    (z : ℂ) {τ : ℂ} (hτ : 0 < im τ) :
    (jacobiTheta₂PrimeFDeriv z τ) (1, 0) =
      jacobiTheta₂Second z τ := by
  have hcurve :
      HasDerivAt
        (fun w : ℂ => (w, τ))
        (1, 0) z :=
    (hasDerivAt_id z).prodMk
      (hasDerivAt_const z τ)
  have hjoint :=
    (hasFDerivAt_jacobiTheta₂Prime_joint
      z τ hτ).comp_hasDerivAt z hcurve
  exact hjoint.unique
    (hasDerivAt_jacobiTheta₂Prime_fst z hτ)

/-- Decomposition of the diagonal `(1/2,1)` direction for the joint
prime derivative. -/
theorem jacobiTheta₂PrimeFDeriv_half_one_eq
    (z : ℂ) {τ : ℂ} (hτ : 0 < im τ) :
    (jacobiTheta₂PrimeFDeriv z τ) (1 / 2, 1) =
      1 / 2 * jacobiTheta₂Second z τ +
        (jacobiTheta₂PrimeFDeriv z τ) (0, 1) := by
  have hv :
      ((1 / 2, 1) : ℂ × ℂ) =
        (1 / 2 : ℂ) •
          ((1, 0) : ℂ × ℂ) +
            ((0, 1) : ℂ × ℂ) := by
    ext <;> norm_num
  rw [hv, map_add, map_smul,
    jacobiTheta₂PrimeFDeriv_fst_eq z hτ]
  simp only [smul_eq_mul]

/-- Explicit third derivative after the half-characteristic
transformation. -/
theorem jacobiTheta2Third_eq_base
    (z : ℂ) (τ : ℍ) :
    jacobiTheta2Third z τ =
      cexp (π * I * ((τ : ℂ) / 4 + z)) *
        ((π * I) ^ 3 *
            jacobiTheta₂
              (z + (τ : ℂ) / 2) (τ : ℂ) +
          3 * (π * I) ^ 2 *
            jacobiTheta₂'
              (z + (τ : ℂ) / 2) (τ : ℂ) +
          3 * π * I *
            jacobiTheta₂Second
              (z + (τ : ℂ) / 2) (τ : ℂ) +
          jacobiTheta₂Third
              (z + (τ : ℂ) / 2) (τ : ℂ)) := by
  let a : ℂ := π * I
  let x : ℂ := z + (τ : ℂ) / 2
  have hE :
      HasDerivAt
        (fun w : ℂ =>
          cexp (a * ((τ : ℂ) / 4 + w)))
        (cexp (a * ((τ : ℂ) / 4 + z)) * a) z := by
    have hlinear :
        HasDerivAt
          (fun w : ℂ =>
            a * ((τ : ℂ) / 4 + w))
          a z := by
      convert
        ((hasDerivAt_id z).const_add
          ((τ : ℂ) / 4)).const_mul a using 1
      ring
    exact hlinear.cexp
  have htheta :
      HasDerivAt
        (fun w : ℂ =>
          jacobiTheta₂
            (w + (τ : ℂ) / 2) (τ : ℂ))
        (jacobiTheta₂' x (τ : ℂ)) z := by
    simpa only [x, Function.comp_apply,
      id_eq, mul_one] using
      (hasDerivAt_jacobiTheta₂_fst
        x τ.im_pos).comp z
          ((hasDerivAt_id z).add_const
            ((τ : ℂ) / 2))
  have hprime :
      HasDerivAt
        (fun w : ℂ =>
          jacobiTheta₂'
            (w + (τ : ℂ) / 2) (τ : ℂ))
        (jacobiTheta₂Second x (τ : ℂ)) z := by
    simpa only [x, Function.comp_apply,
      id_eq, mul_one] using
      (hasDerivAt_jacobiTheta₂Prime_fst
        x τ.im_pos).comp z
          ((hasDerivAt_id z).add_const
            ((τ : ℂ) / 2))
  have hsecond :
      HasDerivAt
        (fun w : ℂ =>
          jacobiTheta₂Second
            (w + (τ : ℂ) / 2) (τ : ℂ))
        (jacobiTheta₂Third x (τ : ℂ)) z := by
    simpa only [x, Function.comp_apply,
      id_eq, mul_one] using
      (hasDerivAt_jacobiTheta₂Second_fst
        x τ.im_pos).comp z
          ((hasDerivAt_id z).add_const
            ((τ : ℂ) / 2))
  have hinner :=
    ((htheta.const_mul (a ^ 2)).add
      (hprime.const_mul (2 * a))).add hsecond
  have hproduct := hE.mul hinner
  have hfunction :
      (fun w : ℂ =>
        jacobiTheta2Second w τ) =
      (fun w : ℂ =>
        cexp (a * ((τ : ℂ) / 4 + w)) *
          (a ^ 2 *
              jacobiTheta₂
                (w + (τ : ℂ) / 2) (τ : ℂ) +
            2 * a *
              jacobiTheta₂'
                (w + (τ : ℂ) / 2) (τ : ℂ) +
            jacobiTheta₂Second
              (w + (τ : ℂ) / 2) (τ : ℂ))) := by
    funext w
    convert jacobiTheta2Second_eq_base w τ using 1
    simp only [a]
    ring
  have hcanonical :=
    hasDerivAt_jacobiTheta2Second z τ
  rw [hfunction] at hcanonical
  have heq :=
    hcanonical.unique hproduct
  simp only [Pi.add_apply] at heq
  rw [heq]
  simp only [a, x]
  ring

/-- The differentiated heat equation for classical `θ₂`. -/
theorem jacobiTheta2Prime_heat_equation
    (z : ℂ) (τ : ℍ) :
    jacobiTheta2Third z τ =
      4 * π * I *
        deriv
          (fun u : ℂ =>
            jacobiTheta2Prime z u)
          (τ : ℂ) := by
  let a : ℂ := π * I
  let x : ℂ := z + (τ : ℂ) / 2
  have hE :
      HasDerivAt
        (fun u : ℂ =>
          cexp (a * (u / 4 + z)))
        (cexp (a * ((τ : ℂ) / 4 + z)) *
          (a / 4)) (τ : ℂ) := by
    have hlinear :
        HasDerivAt
          (fun u : ℂ =>
            a * (u / 4 + z))
          (a / 4) (τ : ℂ) := by
      convert
        ((hasDerivAt_id (τ : ℂ)).div_const 4
          |>.add_const z).const_mul a using 1
      ring
    exact hlinear.cexp
  have hcurve :
      HasDerivAt
        (fun u : ℂ =>
          (z + u / 2, u))
        (1 / 2, 1) (τ : ℂ) := by
    exact
      (((hasDerivAt_id (τ : ℂ)).div_const 2)
        |>.const_add z).prodMk
          (hasDerivAt_id (τ : ℂ))
  have htheta :=
    (hasFDerivAt_jacobiTheta₂
      x τ.im_pos).comp_hasDerivAt
        (f := fun u : ℂ =>
          (z + u / 2, u))
        (τ : ℂ) hcurve
  have hprime :=
    (hasFDerivAt_jacobiTheta₂Prime_joint
      x (τ : ℂ) τ.im_pos).comp_hasDerivAt
        (f := fun u : ℂ =>
          (z + u / 2, u))
        (τ : ℂ) hcurve
  have hinner :=
    (htheta.const_mul a).add hprime
  have hproduct := hE.mul hinner
  have hderiv :
      deriv
          (fun u : ℂ =>
            jacobiTheta2Prime z u)
          (τ : ℂ) =
        cexp (a * ((τ : ℂ) / 4 + z)) *
              (a / 4) *
            (a * jacobiTheta₂ x (τ : ℂ) +
              jacobiTheta₂' x (τ : ℂ)) +
          cexp (a * ((τ : ℂ) / 4 + z)) *
            (a *
                (jacobiTheta₂_fderiv
                  x (τ : ℂ)) (1 / 2, 1) +
              (jacobiTheta₂PrimeFDeriv
                x (τ : ℂ)) (1 / 2, 1)) := by
    exact hproduct.deriv
  rw [jacobiTheta2Third_eq_base, hderiv,
    jacobiTheta₂_fderiv_half_one_eq
      x τ.im_pos,
    jacobiTheta₂PrimeFDeriv_half_one_eq
      x τ.im_pos,
    jacobiTheta₂_heat_equation
      x τ.im_pos,
    jacobiTheta₂Prime_heat_equation
      x τ.im_pos]
  simp only [a, x]
  ring

/-- Half-period transfer of the third derivatives. -/
theorem jacobiTheta2Third_add_half
    (z : ℂ) (τ : ℍ) :
    jacobiTheta2Third (z + 1 / 2) τ =
      -jacobiTheta1Third z τ := by
  have hleft :=
    (hasDerivAt_jacobiTheta2Second
      (z + 1 / 2) τ).comp z
        ((hasDerivAt_id z).add_const (1 / 2))
  have hfunction :
      (fun w : ℂ =>
        jacobiTheta2Second (w + 1 / 2) τ) =
      (fun w : ℂ =>
        -jacobiTheta1Second w τ) := by
    funext w
    exact jacobiTheta2Second_add_half w τ
  have hleft' :
      HasDerivAt
        (fun w : ℂ =>
          jacobiTheta2Second (w + 1 / 2) τ)
        (jacobiTheta2Third
          (z + 1 / 2) τ) z := by
    simpa only [Function.comp_apply,
      id_eq, mul_one] using hleft
  rw [hfunction] at hleft'
  exact hleft'.unique
    (hasDerivAt_jacobiTheta1Second z τ).neg

/-- The differentiated heat equation for classical `θ₁`. -/
theorem jacobiTheta1Prime_heat_equation
    (z : ℂ) (τ : ℍ) :
    jacobiTheta1Third z τ =
      4 * π * I *
        deriv
          (fun u : ℂ =>
            jacobiTheta1Prime z u)
          (τ : ℂ) := by
  have htheta2 :=
    differentiableAt_jacobiTheta2Prime_joint
      (z + 1 / 2) (τ : ℂ) τ.im_pos
  have htheta2snd :
      DifferentiableAt ℂ
        (fun u : ℂ =>
          jacobiTheta2Prime (z + 1 / 2) u)
        (τ : ℂ) := by
    have hcurve :
        DifferentiableAt ℂ
          (fun u : ℂ =>
            (z + 1 / 2, u)) (τ : ℂ) := by
      fun_prop
    simpa only [Function.comp_apply] using
      htheta2.comp (τ : ℂ) hcurve
  have hderiv :
      deriv
          (fun u : ℂ =>
            jacobiTheta1Prime z u)
          (τ : ℂ) =
        -deriv
          (fun u : ℂ =>
            jacobiTheta2Prime (z + 1 / 2) u)
          (τ : ℂ) := by
    have hneg :
        (fun u : ℂ =>
          jacobiTheta1Prime z u) =
        (fun u : ℂ =>
          -jacobiTheta2Prime
            (z + 1 / 2) u) := by
      rfl
    rw [hneg]
    exact (htheta2snd.hasDerivAt.neg).deriv
  rw [hderiv]
  have hthird :
      jacobiTheta1Third z τ =
        -jacobiTheta2Third
          (z + 1 / 2) τ := by
    simpa using
      (congrArg Neg.neg
        (jacobiTheta2Third_add_half z τ)).symm
  rw [hthird,
    jacobiTheta2Prime_heat_equation
      (z + 1 / 2) τ]
  ring

end

end HGAS.Modular
