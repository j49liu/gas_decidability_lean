import HGAS.Modular.JacobiThetaClassicalPrimeHeatEquation
import HGAS.Modular.JacobiThetaModularTrajectory

/-!
# The derivative coordinate of the canonical modular theta trajectory

The modular equation for `Delta = θ₁'/π` is one derivative deeper than
the equations for the four theta coordinates.  Its proof has three
conceptually separate steps.

1.  The elliptic Jacobi system identifies
    `θ₁'' = π² · Z.Delta`, where `Z` is the elliptic vector field.
2.  Differentiating once more and using the polynomial second-iterate
    identity gives

    ```
                  θ₁''' = -4 π³ · Phi.Delta.
    ```

3.  The differentiated heat equation
    `θ₁''' = 4 π i · ∂τ θ₁'` converts this into the desired modular
    equation

    ```
             ∂τ (θ₁'/π) = π i · Phi.Delta.
    ```

Keeping these three steps visible makes the proof reusable and mirrors
the paper calculation closely.
-/

namespace HGAS.Modular

open Complex Real Filter Topology
open UpperHalfPlane hiding I

noncomputable section

/-- The second elliptic derivative is `π²` times the `Delta` component
of the elliptic Jacobi field. -/
theorem jacobiTheta1Second_eq_pi_sq_ellipticDelta
    (z : ℂ) (τ : ℍ)
    (h1 : jacobiTheta1 z (τ : ℂ) ≠ 0) :
    jacobiTheta1Second z τ =
      π ^ 2 *
        (JacobiState.ellipticVectorField
          (canonicalJacobiThetaState z τ)).Delta := by
  let s : ℂ → JacobiState ℂ :=
    fun w => canonicalJacobiThetaState w τ
  have helliptic :
      IsScaledJacobiEllipticTrajectoryAt π s z :=
    canonicalJacobiThetaState_elliptic_unconditional
      z τ h1
  have hcanonical :=
    (hasDerivAt_jacobiTheta1Prime z τ).div_const π
  have heq := helliptic.Delta.unique hcanonical
  have hpi :
      (π : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [s] at heq
  field_simp [hpi] at heq
  exact heq.symm

/-- The third elliptic derivative is the `Delta` coordinate of the
modular Jacobi field with the heat-equation scale `-4π³`. -/
theorem jacobiTheta1Third_eq_modularVectorField
    (z : ℂ) (τ : ℍ)
    (h1 : jacobiTheta1 z (τ : ℂ) ≠ 0) :
    jacobiTheta1Third z τ =
      -4 * π ^ 3 *
        (JacobiState.modularVectorField
          (canonicalJacobiThetaState z τ)).Delta := by
  let s : ℂ → JacobiState ℂ :=
    fun w => canonicalJacobiThetaState w τ
  have hpoint :
      IsScaledJacobiEllipticTrajectoryAt π s z :=
    canonicalJacobiThetaState_elliptic_unconditional
      z τ h1
  have hfield :=
    hpoint.elliptic_Delta_hasDerivAt.const_mul
      (π ^ 2 : ℂ)
  have htheta1diff :=
    (hasDerivAt_jacobiTheta1 z (τ : ℂ)
      τ.im_pos).differentiableAt
  have hlocal :
      (fun w : ℂ =>
        jacobiTheta1Second w τ) =ᶠ[nhds z]
      (fun w : ℂ =>
        π ^ 2 *
          (JacobiState.ellipticVectorField
            (s w)).Delta) := by
    filter_upwards
      [htheta1diff.continuousAt.eventually_ne h1]
        with w hw
    exact jacobiTheta1Second_eq_pi_sq_ellipticDelta
      w τ hw
  have hthirdRaw :=
    (hasDerivAt_jacobiTheta1Second z τ).unique
      (hfield.congr_of_eventuallyEq hlocal)
  calc
    jacobiTheta1Third z τ =
        π ^ 2 *
          (π *
            JacobiState.ellipticSecondDelta (s z)) := hthirdRaw
    _ =
        π ^ 2 *
          (π *
            (-4 *
              (JacobiState.modularVectorField
                (s z)).Delta)) := by
      rw [JacobiState.ellipticSecondDelta_eq_modular]
      simp only [s, canonicalJacobiThetaState_U,
        canonicalJacobiThetaState_T1]
      exact inv_mul_cancel₀ h1
    _ =
        -4 * π ^ 3 *
          (JacobiState.modularVectorField
            (canonicalJacobiThetaState z τ)).Delta := by
      simp only [s]
      ring

/-- Ordinary modular derivative of `θ₁'`, obtained by cancelling the
nonzero heat-equation coefficient. -/
theorem canonicalJacobiThetaState_prime_modular_hasDerivAt
    (z : ℂ) (τ : ℍ)
    (h1 : jacobiTheta1 z (τ : ℂ) ≠ 0) :
    HasDerivAt
      (fun u : ℂ => jacobiTheta1Prime z u)
      (π ^ 2 * I *
        (JacobiState.modularVectorField
          (canonicalJacobiThetaState z τ)).Delta)
      (τ : ℂ) := by
  let f : ℂ → ℂ :=
    fun u => jacobiTheta1Prime z u
  let P : ℂ :=
    (JacobiState.modularVectorField
      (canonicalJacobiThetaState z τ)).Delta
  have hdiff :
      DifferentiableAt ℂ f (τ : ℂ) := by
    have hcurve :
        DifferentiableAt ℂ
          (fun u : ℂ => (z, u)) (τ : ℂ) := by
      fun_prop
    simpa only [f, Function.comp_apply] using
      (differentiableAt_jacobiTheta1Prime_joint
        z (τ : ℂ) τ.im_pos).comp
          (τ : ℂ) hcurve
  have hcoefficient :
      (4 * π * I : ℂ) ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      I_ne_zero
  have hderiv :
      deriv f (τ : ℂ) =
        π ^ 2 * I * P := by
    apply mul_left_cancel₀ hcoefficient
    calc
      4 * π * I * deriv f (τ : ℂ) =
          jacobiTheta1Third z τ := by
        symm
        simpa only [f] using
          jacobiTheta1Prime_heat_equation z τ
      _ = -4 * π ^ 3 * P := by
        simpa only [P] using
          jacobiTheta1Third_eq_modularVectorField
            z τ h1
      _ = 4 * π * I * (π ^ 2 * I * P) := by
        calc
          -4 * π ^ 3 * P =
              4 * π ^ 3 * (-1) * P := by ring
          _ = 4 * π ^ 3 * (I * I) * P := by
            rw [I_mul_I]
          _ = 4 * π * I * (π ^ 2 * I * P) := by
            ring
  rw [← hderiv]
  exact hdiff.hasDerivAt

/-- The canonical `Delta = θ₁'/π` coordinate has the required
paper-scaled modular derivative before totalizing the upper half-plane
path. -/
theorem canonicalJacobiThetaState_Delta_modular_hasDerivAt
    (z : ℂ) (τ : ℍ)
    (h1 : jacobiTheta1 z (τ : ℂ) ≠ 0) :
    HasDerivAt
      (fun u : ℂ =>
        jacobiTheta1Prime z u / π)
      (π * I *
        (JacobiState.modularVectorField
          (canonicalJacobiThetaState z τ)).Delta)
      (τ : ℂ) := by
  have hraw :=
    (canonicalJacobiThetaState_prime_modular_hasDerivAt
      z τ h1).div_const π
  convert hraw using 1
  field_simp [Real.pi_ne_zero]

/-- The full canonical state satisfies every coordinate of the modular
Jacobi vector field on the reciprocal chart. -/
theorem canonicalJacobiThetaState_modular_unconditional
    (z : ℂ) (τ : ℍ)
    (h1 : jacobiTheta1 z (τ : ℂ) ≠ 0) :
    IsScaledJacobiModularTrajectoryAt
      (π * I) (canonicalJacobiThetaModularPath z) (τ : ℂ) := by
  have hbase :=
    canonicalJacobiThetaState_modular_exceptDelta
      z τ h1
  have hraw :=
    canonicalJacobiThetaState_Delta_modular_hasDerivAt
      z τ h1
  have hupp :
      ∀ᶠ u : ℂ in nhds (τ : ℂ),
        u ∈ upperHalfPlaneSet :=
    isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos
  have hlocal :
      (fun u : ℂ =>
        (canonicalJacobiThetaModularPath z u).Delta) =ᶠ[nhds (τ : ℂ)]
      (fun u : ℂ =>
        jacobiTheta1Prime z u / π) := by
    filter_upwards [hupp] with u hu
    simp only [canonicalJacobiThetaModularPath,
      canonicalJacobiThetaState_Delta,
      ofComplex_apply_of_im_pos hu]
  have hDelta :=
    hraw.congr_of_eventuallyEq hlocal
  exact
    {
      toIsScaledJacobiModularTrajectoryAtExceptDelta := hbase
      Delta := by
        simpa only [
          canonicalJacobiThetaModularPath_at_upperHalfPlane]
          using hDelta
    }

end

end HGAS.Modular
