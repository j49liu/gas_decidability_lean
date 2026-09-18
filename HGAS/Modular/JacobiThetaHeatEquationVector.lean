import HGAS.Modular.JacobiThetaDeltaIdentity
import HGAS.Modular.JacobiThetaPrimeJointDifferentiability

/-!
# The heat equation for the four Jacobi characteristics

The series calculation in `JacobiThetaDeltaIdentity` proves the heat
equation for Mathlib's basic two-variable theta series and for our
classical `θ₂`.  Here we transfer it to all four characteristics and
package their second elliptic derivatives as a vector.

The normalization is

```
                   ∂w² θ = 4 π i ∂τ θ.
```

These are identities of derivatives, not formal rewrite rules: every
derivative appearing below is accompanied by an actual `HasDerivAt`
theorem.
-/

namespace HGAS.Modular

open Complex Real
open UpperHalfPlane hiding I

noncomputable section

/-- Second elliptic derivatives of the four theta coordinates. -/
def jacobiThetaVectorSecond
    (z : ℂ) (τ : ℍ) : Fin 4 → ℂ :=
  ![jacobiTheta1Second z τ,
    jacobiTheta2Second z τ,
    jacobiTheta₂Second z (τ : ℂ),
    jacobiTheta₂Second (z + 1 / 2) (τ : ℂ)]

/-- The base theta heat equation, expressed using an ordinary derivative
in the modular variable. -/
theorem jacobiTheta₂_heat_equation_deriv_snd
    (z : ℂ) (τ : ℍ) :
    jacobiTheta₂Second z (τ : ℂ) =
      4 * π * I *
        deriv (fun u : ℂ => jacobiTheta₂ z u) (τ : ℂ) := by
  have hcurve :
      HasDerivAt
        (fun u : ℂ => (z, u)) (0, 1) (τ : ℂ) :=
    (hasDerivAt_const (τ : ℂ) z).prodMk
      (hasDerivAt_id (τ : ℂ))
  have hjoint :=
    (hasFDerivAt_jacobiTheta₂ z τ.im_pos)
      |>.comp_hasDerivAt (τ : ℂ) hcurve
  have hderiv :
      deriv (fun u : ℂ => jacobiTheta₂ z u) (τ : ℂ) =
        (jacobiTheta₂_fderiv z (τ : ℂ)) (0, 1) := by
    exact hjoint.deriv
  rw [hderiv]
  exact jacobiTheta₂_heat_equation z τ.im_pos

theorem jacobiTheta3_heat_equation
    (z : ℂ) (τ : ℍ) :
    jacobiTheta₂Second z (τ : ℂ) =
      4 * π * I *
        deriv (fun u : ℂ => jacobiTheta3 z u) (τ : ℂ) := by
  simpa only [jacobiTheta3] using
    jacobiTheta₂_heat_equation_deriv_snd z τ

theorem jacobiTheta4_heat_equation
    (z : ℂ) (τ : ℍ) :
    jacobiTheta₂Second (z + 1 / 2) (τ : ℂ) =
      4 * π * I *
        deriv (fun u : ℂ => jacobiTheta4 z u) (τ : ℂ) := by
  simpa only [jacobiTheta4] using
    jacobiTheta₂_heat_equation_deriv_snd
      (z + 1 / 2) τ

theorem jacobiTheta1_heat_equation
    (z : ℂ) (τ : ℍ) :
    jacobiTheta1Second z τ =
      4 * π * I *
        deriv (fun u : ℂ => jacobiTheta1 z u) (τ : ℂ) := by
  have htheta2 :=
    hasDerivAt_jacobiTheta2_snd (z + 1 / 2) τ
  have hneg :
      HasDerivAt
        (fun u : ℂ => jacobiTheta1 z u)
        (-deriv
          (fun u : ℂ => jacobiTheta2 (z + 1 / 2) u)
          (τ : ℂ))
        (τ : ℂ) := by
    convert htheta2.neg using 1
    rw [htheta2.deriv]
  have hderiv :
      deriv (fun u : ℂ => jacobiTheta1 z u) (τ : ℂ) =
        -deriv
          (fun u : ℂ => jacobiTheta2 (z + 1 / 2) u)
          (τ : ℂ) :=
    hneg.deriv
  rw [hderiv]
  calc
    jacobiTheta1Second z τ =
        -jacobiTheta2Second (z + 1 / 2) τ :=
      by
        simpa using
          (congrArg Neg.neg
            (jacobiTheta2Second_add_half z τ)).symm
    _ =
        -(4 * π * I *
          deriv
            (fun u : ℂ =>
              jacobiTheta2 (z + 1 / 2) u)
            (τ : ℂ)) := by
      rw [jacobiTheta2_heat_equation]
    _ =
        4 * π * I *
          -deriv
            (fun u : ℂ =>
              jacobiTheta2 (z + 1 / 2) u)
            (τ : ℂ) := by ring

/-- The second vector really is the elliptic derivative of the first
derivative vector. -/
theorem hasDerivAt_jacobiThetaVectorPrime_component
    (j : Fin 4) (z : ℂ) (τ : ℍ) :
    HasDerivAt
      (fun w : ℂ =>
        jacobiThetaVectorPrime w (τ : ℂ) j)
      (jacobiThetaVectorSecond z τ j) z := by
  fin_cases j
  · simpa only [jacobiThetaVectorPrime,
      jacobiThetaVectorSecond, Matrix.cons_val_zero] using
      hasDerivAt_jacobiTheta1Prime z τ
  · simpa only [jacobiThetaVectorPrime,
      jacobiThetaVectorSecond, Matrix.cons_val_one,
      Matrix.cons_val_zero] using
      hasDerivAt_jacobiTheta2Prime z τ
  · simpa only [jacobiThetaVectorPrime,
      jacobiThetaVectorSecond, Matrix.cons_val_one,
      Matrix.cons_val_zero] using
      hasDerivAt_jacobiTheta₂Prime_fst z τ.im_pos
  · have h :=
      (hasDerivAt_jacobiTheta₂Prime_fst
        (z + 1 / 2) τ.im_pos).comp z
          ((hasDerivAt_id z).add_const (1 / 2))
    simpa only [jacobiThetaVectorPrime,
      jacobiThetaVectorSecond, Matrix.cons_val_one,
      Matrix.cons_val_zero, jacobiTheta4Prime,
      Function.comp_apply, id_eq, mul_one] using h

/-- Componentwise heat equation for the four-theta vector. -/
theorem jacobiThetaVector_heat_equation
    (j : Fin 4) (z : ℂ) (τ : ℍ) :
    jacobiThetaVectorSecond z τ j =
      4 * π * I *
        deriv
          (fun u : ℂ =>
            jacobiThetaVector z u j)
          (τ : ℂ) := by
  fin_cases j
  · simpa only [jacobiThetaVectorSecond,
      jacobiThetaVector, Matrix.cons_val_zero] using
      jacobiTheta1_heat_equation z τ
  · simpa only [jacobiThetaVectorSecond,
      jacobiThetaVector, Matrix.cons_val_one,
      Matrix.cons_val_zero] using
      jacobiTheta2_heat_equation z τ
  · simpa only [jacobiThetaVectorSecond,
      jacobiThetaVector, Matrix.cons_val_one,
      Matrix.cons_val_zero] using
      jacobiTheta3_heat_equation z τ
  · simpa only [jacobiThetaVectorSecond,
      jacobiThetaVector, Matrix.cons_val_one,
      Matrix.cons_val_zero] using
      jacobiTheta4_heat_equation z τ

end

end HGAS.Modular
