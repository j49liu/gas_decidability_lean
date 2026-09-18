import HGAS.Modular.JacobiSecondOrderTrajectory
import HGAS.Modular.JacobiThetaHeatEquationVector

/-!
# From the elliptic system to the canonical modular theta equations

This module joins two independent ingredients:

* the analytic heat equation for the four theta characteristics; and
* the algebraic identity saying that the modular Jacobi field is minus
  one quarter of the second elliptic field.

It follows that, on the reciprocal chart, the second elliptic derivative
of each canonical theta coordinate is exactly `-4π²` times the
corresponding modular-vector-field coordinate.  Together with the heat
equation this gives the correct modular derivative.
-/

namespace HGAS.Modular

open Complex Real Filter Topology
open UpperHalfPlane hiding I

noncomputable section

private theorem canonicalJacobiThetaState_reciprocal
    (z : ℂ) (τ : ℍ)
    (h1 : jacobiTheta1 z (τ : ℂ) ≠ 0) :
    (canonicalJacobiThetaState z τ).U *
        (canonicalJacobiThetaState z τ).T1 = 1 := by
  simp only [canonicalJacobiThetaState_U,
    canonicalJacobiThetaState_T1]
  exact inv_mul_cancel₀ h1

theorem jacobiTheta1Second_eq_modularVectorField
    (z : ℂ) (τ : ℍ)
    (h1 : jacobiTheta1 z (τ : ℂ) ≠ 0) :
    jacobiTheta1Second z τ =
      -4 * π ^ 2 *
        (JacobiState.modularVectorField
          (canonicalJacobiThetaState z τ)).T1 := by
  let s : ℂ → JacobiState ℂ :=
    fun w => canonicalJacobiThetaState w τ
  have hpoint :
      IsScaledJacobiEllipticTrajectoryAt π s z :=
    canonicalJacobiThetaState_elliptic_unconditional
      z τ h1
  have hscaled :=
    HasDerivAt.const_mul (π : ℂ) hpoint.Delta
  have hlocal :
      (fun w : ℂ =>
        jacobiTheta1Prime w (τ : ℂ)) =ᶠ[nhds z]
      (fun w : ℂ =>
        π * (s w).Delta) := by
    filter_upwards [] with w
    simp only [s, canonicalJacobiThetaState_Delta]
    field_simp [Real.pi_ne_zero]
  have hprime :=
    hscaled.congr_of_eventuallyEq hlocal
  have hsecond :
      jacobiTheta1Second z τ =
        π *
          (π *
            (JacobiState.ellipticVectorField
              (s z)).Delta) :=
    (hasDerivAt_jacobiTheta1Prime z τ).unique hprime
  calc
    jacobiTheta1Second z τ =
        π ^ 2 *
          JacobiState.ellipticSecondT1 (s z) := by
      rw [hsecond]
      simp only [JacobiState.ellipticSecondT1,
        JacobiState.ellipticVectorField]
      ring
    _ =
        π ^ 2 *
          (-4 *
            (JacobiState.modularVectorField
              (s z)).T1) := by
      rw [JacobiState.ellipticSecondT1_eq_modular]
    _ =
        -4 * π ^ 2 *
          (JacobiState.modularVectorField
            (canonicalJacobiThetaState z τ)).T1 := by
      simp only [s]
      ring

theorem jacobiTheta2Second_eq_modularVectorField
    (z : ℂ) (τ : ℍ)
    (h1 : jacobiTheta1 z (τ : ℂ) ≠ 0) :
    jacobiTheta2Second z τ =
      -4 * π ^ 2 *
        (JacobiState.modularVectorField
          (canonicalJacobiThetaState z τ)).T2 := by
  let s : ℂ → JacobiState ℂ :=
    fun w => canonicalJacobiThetaState w τ
  have hpoint :
      IsScaledJacobiEllipticTrajectoryAt π s z :=
    canonicalJacobiThetaState_elliptic_unconditional
      z τ h1
  have hscaled :=
    HasDerivAt.const_mul (π : ℂ)
      hpoint.elliptic_T2_hasDerivAt
  have htheta1diff :=
    (hasDerivAt_jacobiTheta1 z (τ : ℂ)
      τ.im_pos).differentiableAt
  have hlocal :
      (fun w : ℂ =>
        jacobiTheta2Prime w (τ : ℂ)) =ᶠ[nhds z]
      (fun w : ℂ =>
        π *
          (JacobiState.ellipticVectorField
            (s w)).T2) := by
    filter_upwards
      [htheta1diff.continuousAt.eventually_ne h1]
        with w hw
    exact canonicalJacobiThetaState_T2_derivative_eq
      w τ hw
  have hprime :=
    hscaled.congr_of_eventuallyEq hlocal
  have hsecond :
      jacobiTheta2Second z τ =
        π *
          (π *
            JacobiState.ellipticSecondT2 (s z)) :=
    (hasDerivAt_jacobiTheta2Prime z τ).unique hprime
  calc
    jacobiTheta2Second z τ =
        π ^ 2 *
          JacobiState.ellipticSecondT2 (s z) := by
      rw [hsecond]
      ring
    _ =
        π ^ 2 *
          (-4 *
            (JacobiState.modularVectorField
              (s z)).T2) := by
      rw [JacobiState.ellipticSecondT2_eq_modular
        (s z)
        (canonicalJacobiThetaState_reciprocal
          z τ h1)]
    _ =
        -4 * π ^ 2 *
          (JacobiState.modularVectorField
            (canonicalJacobiThetaState z τ)).T2 := by
      simp only [s]
      ring

theorem jacobiTheta3Second_eq_modularVectorField
    (z : ℂ) (τ : ℍ)
    (h1 : jacobiTheta1 z (τ : ℂ) ≠ 0) :
    jacobiTheta₂Second z (τ : ℂ) =
      -4 * π ^ 2 *
        (JacobiState.modularVectorField
          (canonicalJacobiThetaState z τ)).T3 := by
  let s : ℂ → JacobiState ℂ :=
    fun w => canonicalJacobiThetaState w τ
  have hpoint :
      IsScaledJacobiEllipticTrajectoryAt π s z :=
    canonicalJacobiThetaState_elliptic_unconditional
      z τ h1
  have hscaled :=
    HasDerivAt.const_mul (π : ℂ)
      hpoint.elliptic_T3_hasDerivAt
  have htheta1diff :=
    (hasDerivAt_jacobiTheta1 z (τ : ℂ)
      τ.im_pos).differentiableAt
  have hlocal :
      (fun w : ℂ =>
        jacobiTheta3Prime w (τ : ℂ)) =ᶠ[nhds z]
      (fun w : ℂ =>
        π *
          (JacobiState.ellipticVectorField
            (s w)).T3) := by
    filter_upwards
      [htheta1diff.continuousAt.eventually_ne h1]
        with w hw
    exact canonicalJacobiThetaState_T3_derivative_eq
      w τ hw
  have hprime :=
    hscaled.congr_of_eventuallyEq hlocal
  have hsecond :
      jacobiTheta₂Second z (τ : ℂ) =
        π *
          (π *
            JacobiState.ellipticSecondT3 (s z)) := by
    have hbase :=
      hasDerivAt_jacobiTheta₂Prime_fst
        z τ.im_pos
    simpa only [jacobiTheta3Prime] using
      hbase.unique hprime
  calc
    jacobiTheta₂Second z (τ : ℂ) =
        π ^ 2 *
          JacobiState.ellipticSecondT3 (s z) := by
      rw [hsecond]
      ring
    _ =
        π ^ 2 *
          (-4 *
            (JacobiState.modularVectorField
              (s z)).T3) := by
      rw [JacobiState.ellipticSecondT3_eq_modular
        (s z)
        (canonicalJacobiThetaState_reciprocal
          z τ h1)]
    _ =
        -4 * π ^ 2 *
          (JacobiState.modularVectorField
            (canonicalJacobiThetaState z τ)).T3 := by
      simp only [s]
      ring

theorem jacobiTheta4Second_eq_modularVectorField
    (z : ℂ) (τ : ℍ)
    (h1 : jacobiTheta1 z (τ : ℂ) ≠ 0) :
    jacobiTheta₂Second (z + 1 / 2) (τ : ℂ) =
      -4 * π ^ 2 *
        (JacobiState.modularVectorField
          (canonicalJacobiThetaState z τ)).T4 := by
  let s : ℂ → JacobiState ℂ :=
    fun w => canonicalJacobiThetaState w τ
  have hpoint :
      IsScaledJacobiEllipticTrajectoryAt π s z :=
    canonicalJacobiThetaState_elliptic_unconditional
      z τ h1
  have hscaled :=
    HasDerivAt.const_mul (π : ℂ)
      hpoint.elliptic_T4_hasDerivAt
  have htheta1diff :=
    (hasDerivAt_jacobiTheta1 z (τ : ℂ)
      τ.im_pos).differentiableAt
  have hlocal :
      (fun w : ℂ =>
        jacobiTheta4Prime w (τ : ℂ)) =ᶠ[nhds z]
      (fun w : ℂ =>
        π *
          (JacobiState.ellipticVectorField
            (s w)).T4) := by
    filter_upwards
      [htheta1diff.continuousAt.eventually_ne h1]
        with w hw
    exact canonicalJacobiThetaState_T4_derivative_eq
      w τ hw
  have hprime :=
    hscaled.congr_of_eventuallyEq hlocal
  have hsecond :
      jacobiTheta₂Second (z + 1 / 2) (τ : ℂ) =
        π *
          (π *
            JacobiState.ellipticSecondT4 (s z)) := by
    have hbase :=
      (hasDerivAt_jacobiTheta₂Prime_fst
        (z + 1 / 2) τ.im_pos).comp z
          ((hasDerivAt_id z).add_const (1 / 2))
    simpa only [jacobiTheta4Prime,
      Function.comp_apply, id_eq, mul_one] using
      hbase.unique hprime
  calc
    jacobiTheta₂Second (z + 1 / 2) (τ : ℂ) =
        π ^ 2 *
          JacobiState.ellipticSecondT4 (s z) := by
      rw [hsecond]
      ring
    _ =
        π ^ 2 *
          (-4 *
            (JacobiState.modularVectorField
              (s z)).T4) := by
      rw [JacobiState.ellipticSecondT4_eq_modular
        (s z)
        (canonicalJacobiThetaState_reciprocal
          z τ h1)]
    _ =
        -4 * π ^ 2 *
          (JacobiState.modularVectorField
            (canonicalJacobiThetaState z τ)).T4 := by
      simp only [s]
      ring

/-- Unified second-order modular identity for the four theta
coordinates. -/
theorem jacobiThetaVectorSecond_eq_modularVectorField
    (j : Fin 4) (z : ℂ) (τ : ℍ)
    (h1 : jacobiTheta1 z (τ : ℂ) ≠ 0) :
    jacobiThetaVectorSecond z τ j =
      -4 * π ^ 2 *
        ![(JacobiState.modularVectorField
              (canonicalJacobiThetaState z τ)).T1,
          (JacobiState.modularVectorField
              (canonicalJacobiThetaState z τ)).T2,
          (JacobiState.modularVectorField
              (canonicalJacobiThetaState z τ)).T3,
          (JacobiState.modularVectorField
              (canonicalJacobiThetaState z τ)).T4] j := by
  fin_cases j
  · simpa only [jacobiThetaVectorSecond,
      Matrix.cons_val_zero] using
      jacobiTheta1Second_eq_modularVectorField z τ h1
  · simpa only [jacobiThetaVectorSecond,
      Matrix.cons_val_one, Matrix.cons_val_zero] using
      jacobiTheta2Second_eq_modularVectorField z τ h1
  · simpa only [jacobiThetaVectorSecond,
      Matrix.cons_val_one, Matrix.cons_val_zero] using
      jacobiTheta3Second_eq_modularVectorField z τ h1
  · simpa only [jacobiThetaVectorSecond,
      Matrix.cons_val_one, Matrix.cons_val_zero] using
      jacobiTheta4Second_eq_modularVectorField z τ h1

/-! ## First modular derivatives

The following small cancellation lemma records the normalization once:
combining `f₂ = 4πi f'` with `f₂ = -4π²P` gives `f' = πiP`.
-/

theorem hasDerivAt_of_jacobiHeat_and_second_eq_modular
    {f : ℂ → ℂ} {τ f₂ P : ℂ}
    (hdiff : DifferentiableAt ℂ f τ)
    (hheat :
      f₂ = 4 * π * I * deriv f τ)
    (hmodular :
      f₂ = -4 * π ^ 2 * P) :
    HasDerivAt f (π * I * P) τ := by
  have hcoefficient :
      (4 * π * I : ℂ) ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      I_ne_zero
  have hderiv :
      deriv f τ = π * I * P := by
    apply mul_left_cancel₀ hcoefficient
    calc
      4 * π * I * deriv f τ = f₂ := hheat.symm
      _ = -4 * π ^ 2 * P := hmodular
      _ = 4 * π * I * (π * I * P) := by
        ring_nf
        rw [I_sq]
        ring
  rw [← hderiv]
  exact hdiff.hasDerivAt

theorem canonicalJacobiThetaState_T1_modular_hasDerivAt
    (z : ℂ) (τ : ℍ)
    (h1 : jacobiTheta1 z (τ : ℂ) ≠ 0) :
    HasDerivAt
      (fun u : ℂ => jacobiTheta1 z u)
      (π * I *
        (JacobiState.modularVectorField
          (canonicalJacobiThetaState z τ)).T1)
      (τ : ℂ) := by
  have hdiff :
      DifferentiableAt ℂ
        (fun u : ℂ => jacobiTheta1 z u)
        (τ : ℂ) := by
    have hcurve :
        DifferentiableAt ℂ
          (fun u : ℂ => (z, u)) (τ : ℂ) := by
      fun_prop
    simpa only [Function.comp_apply] using
      (contDiffAt_one_jacobiTheta1_joint
        z (τ : ℂ) τ.im_pos).differentiableAt_one.comp
          (τ : ℂ) hcurve
  exact
    hasDerivAt_of_jacobiHeat_and_second_eq_modular
      hdiff
      (jacobiTheta1_heat_equation z τ)
      (jacobiTheta1Second_eq_modularVectorField
        z τ h1)

theorem canonicalJacobiThetaState_T2_modular_hasDerivAt
    (z : ℂ) (τ : ℍ)
    (h1 : jacobiTheta1 z (τ : ℂ) ≠ 0) :
    HasDerivAt
      (fun u : ℂ => jacobiTheta2 z u)
      (π * I *
        (JacobiState.modularVectorField
          (canonicalJacobiThetaState z τ)).T2)
      (τ : ℂ) := by
  exact
    hasDerivAt_of_jacobiHeat_and_second_eq_modular
      (hasDerivAt_jacobiTheta2_snd z τ).differentiableAt
      (jacobiTheta2_heat_equation z τ)
      (jacobiTheta2Second_eq_modularVectorField
        z τ h1)

theorem canonicalJacobiThetaState_T3_modular_hasDerivAt
    (z : ℂ) (τ : ℍ)
    (h1 : jacobiTheta1 z (τ : ℂ) ≠ 0) :
    HasDerivAt
      (fun u : ℂ => jacobiTheta3 z u)
      (π * I *
        (JacobiState.modularVectorField
          (canonicalJacobiThetaState z τ)).T3)
      (τ : ℂ) := by
  have hdiff :
      DifferentiableAt ℂ
        (fun u : ℂ => jacobiTheta3 z u)
        (τ : ℂ) := by
    simpa only [jacobiTheta3] using
      differentiableAt_jacobiTheta₂_snd
        z τ.im_pos
  exact
    hasDerivAt_of_jacobiHeat_and_second_eq_modular
      hdiff
      (jacobiTheta3_heat_equation z τ)
      (jacobiTheta3Second_eq_modularVectorField
        z τ h1)

theorem canonicalJacobiThetaState_T4_modular_hasDerivAt
    (z : ℂ) (τ : ℍ)
    (h1 : jacobiTheta1 z (τ : ℂ) ≠ 0) :
    HasDerivAt
      (fun u : ℂ => jacobiTheta4 z u)
      (π * I *
        (JacobiState.modularVectorField
          (canonicalJacobiThetaState z τ)).T4)
      (τ : ℂ) := by
  have hdiff :
      DifferentiableAt ℂ
        (fun u : ℂ => jacobiTheta4 z u)
        (τ : ℂ) := by
    simpa only [jacobiTheta4] using
      differentiableAt_jacobiTheta₂_snd
        (z + 1 / 2) τ.im_pos
  exact
    hasDerivAt_of_jacobiHeat_and_second_eq_modular
      hdiff
      (jacobiTheta4_heat_equation z τ)
      (jacobiTheta4Second_eq_modularVectorField
        z τ h1)

end

end HGAS.Modular
