import HGAS.Modular.ThetaE4Identity
import Mathlib.Tactic

/-!
# Differential identities for the even theta constants

This file proves the classical differential equations for

```
H₂ = θ₂⁴,  H₃ = θ₃⁴,  H₄ = θ₄⁴.
```

The argument is deliberately organized around two small auxiliary
modular forms.  We subtract the expected right-hand sides from the three
Serre derivatives and call the resulting errors `f₂`, `f₃`, and `f₄`.
Their transformations under the generators `S,T` assemble into invariant
forms of weights six and eight.  Those invariants vanish at the cusp, and
there are no nonzero level-one cusp forms below weight twelve.  A final
holomorphic zero-product argument forces all three errors to vanish.

The proof uses Mathlib's native `Derivative.serreDerivative`; in
particular the final statements are directly usable with Mathlib's
differential modular-form API.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I
open Complex Real Filter Topology
open ModularForm ModularGroup SlashAction EisensteinSeries
open scoped Manifold MatrixGroups ModularForm Real Topology

noncomputable section

local notation "D" =>
  Derivative.normalizedDerivOfComplex
local notation "∂[" k "]" =>
  Derivative.serreDerivative k

/-! ## 1. The three error functions -/

/-- Error in the proposed differential equation for `H₂`. -/
def f₂ : ℍ → ℂ :=
  ∂[(2 : ℂ)] H₂ -
    (1 / 6 : ℂ) •
      (H₂ * (H₂ + (2 : ℂ) • H₄))

/-- Error in the proposed differential equation for `H₃`. -/
def f₃ : ℍ → ℂ :=
  ∂[(2 : ℂ)] H₃ -
    (1 / 6 : ℂ) • (H₂ ^ 2 - H₄ ^ 2)

/-- Error in the proposed differential equation for `H₄`. -/
def f₄ : ℍ → ℂ :=
  ∂[(2 : ℂ)] H₄ +
    (1 / 6 : ℂ) •
      (H₄ * ((2 : ℂ) • H₂ + H₄))

theorem f₂_decompose :
    f₂ =
      ∂[(2 : ℂ)] H₂ +
        (-1 / 6 : ℂ) •
          (H₂ * (H₂ + (2 : ℂ) • H₄)) := by
  ext z
  simp [f₂, sub_eq_add_neg]
  ring

theorem f₄_decompose :
    f₄ =
      ∂[(2 : ℂ)] H₄ +
        (1 / 6 : ℂ) •
          (H₄ * ((2 : ℂ) • H₂ + H₄)) :=
  rfl

/-- Holomorphy of the first error function. -/
theorem f₂_mdifferentiable : MDiff f₂ := by
  intro z
  exact
    (Derivative.serreDerivative_mdifferentiable
      (2 : ℂ) H₂_mdifferentiable z).sub
        (((H₂_mdifferentiable z).mul
          ((H₂_mdifferentiable z).add
            ((H₄_mdifferentiable z).const_smul
              (2 : ℂ)))).const_smul
                (1 / 6 : ℂ))

/-- Holomorphy of the middle error function. -/
theorem f₃_mdifferentiable : MDiff f₃ := by
  intro z
  exact
    (Derivative.serreDerivative_mdifferentiable
      (2 : ℂ) H₃_mdifferentiable z).sub
        (((H₂_mdifferentiable z).pow 2
          |>.sub ((H₄_mdifferentiable z).pow 2))
            |>.const_smul (1 / 6 : ℂ))

/-- Holomorphy of the third error function. -/
theorem f₄_mdifferentiable : MDiff f₄ := by
  intro z
  exact
    (Derivative.serreDerivative_mdifferentiable
      (2 : ℂ) H₄_mdifferentiable z).add
        (((H₄_mdifferentiable z).mul
          (((H₂_mdifferentiable z).const_smul
            (2 : ℂ)).add
              (H₄_mdifferentiable z)))
                |>.const_smul (1 / 6 : ℂ))

/-! ## 2. Algebraic relation and generator transformations -/

/-- Jacobi's quartic identity makes the error functions satisfy
`f₂ + f₄ = f₃`. -/
theorem f₂_add_f₄_eq_f₃ :
    f₂ + f₄ = f₃ := by
  ext z
  simp only [Pi.add_apply, f₂, f₃, f₄]
  have hSerre :
      ∂[(2 : ℂ)] H₂ z +
          ∂[(2 : ℂ)] H₄ z =
        ∂[(2 : ℂ)] H₃ z := by
    have h :=
      congrFun
        (Derivative.serreDerivative_add
          (2 : ℂ) H₂ H₄
          H₂_mdifferentiable
          H₄_mdifferentiable) z
    simp only [Pi.add_apply] at h
    rw [jacobi_quartic_identity] at h
    exact h.symm
  calc
    ∂[(2 : ℂ)] H₂ z -
          1 / 6 *
            (H₂ z * (H₂ z + 2 * H₄ z)) +
        (∂[(2 : ℂ)] H₄ z +
          1 / 6 *
            (H₄ z * (2 * H₂ z + H₄ z))) =
        (∂[(2 : ℂ)] H₂ z +
          ∂[(2 : ℂ)] H₄ z) +
          (1 / 6 *
              (H₄ z * (2 * H₂ z + H₄ z)) -
            1 / 6 *
              (H₂ z * (H₂ z + 2 * H₄ z))) := by
            ring
    _ = ∂[(2 : ℂ)] H₃ z +
          (1 / 6 *
              (H₄ z * (2 * H₂ z + H₄ z)) -
            1 / 6 *
              (H₂ z * (H₂ z + 2 * H₄ z))) := by
            rw [hSerre]
    _ = ∂[(2 : ℂ)] H₃ z -
          1 / 6 *
            (H₂ z ^ 2 - H₄ z ^ 2) := by
            ring

/-- Under inversion, the first error becomes the negative third error. -/
theorem f₂_S_action :
    (f₂ ∣[(4 : ℤ)] S) = -f₄ := by
  have hSerre :
      (∂[(2 : ℂ)] H₂ ∣[(4 : ℤ)] S) =
        -∂[(2 : ℂ)] H₄ := by
    calc
      (∂[(2 : ℂ)] H₂ ∣[(4 : ℤ)] S) =
          ∂[(2 : ℂ)] (H₂ ∣[(2 : ℤ)] S) := by
            simpa using
              serreDerivative_slash_equivariant
                2 H₂ H₂_mdifferentiable S
      _ = ∂[(2 : ℂ)] (-H₄) := by
            rw [H₂_S_action]
      _ = -∂[(2 : ℂ)] H₄ := by
            simpa using
              Derivative.serreDerivative_smul
                (2 : ℂ) (-1 : ℂ) H₄
                H₄_mdifferentiable
  have hLinear :
      ((H₂ + (2 : ℂ) • H₄) ∣[(2 : ℤ)] S) =
        -(H₄ + (2 : ℂ) • H₂) := by
    rw [SlashAction.add_slash,
      ModularForm.SL_smul_slash,
      H₂_S_action, H₄_S_action]
    ext z
    simp only [Pi.add_apply, Pi.smul_apply,
      Pi.neg_apply, smul_eq_mul]
    ring
  have hProduct :
      ((H₂ * (H₂ + (2 : ℂ) • H₄))
          ∣[(4 : ℤ)] S) =
        H₄ * (H₄ + (2 : ℂ) • H₂) := by
    rw [show (4 : ℤ) = 2 + 2 by norm_num,
      ModularForm.mul_slash_SL2 2 2 S _ _,
      H₂_S_action, hLinear]
    ext z
    simp only [Pi.mul_apply, Pi.neg_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [f₂_decompose, SlashAction.add_slash,
    ModularForm.SL_smul_slash, hSerre, hProduct]
  unfold f₄
  ext z
  simp only [Pi.add_apply, Pi.smul_apply,
    Pi.neg_apply, Pi.mul_apply, smul_eq_mul]
  ring

/-- Translation changes the sign of the first error. -/
theorem f₂_T_action :
    (f₂ ∣[(4 : ℤ)] T) = -f₂ := by
  have hSerre :
      (∂[(2 : ℂ)] H₂ ∣[(4 : ℤ)] T) =
        -∂[(2 : ℂ)] H₂ := by
    calc
      (∂[(2 : ℂ)] H₂ ∣[(4 : ℤ)] T) =
          ∂[(2 : ℂ)] (H₂ ∣[(2 : ℤ)] T) := by
            simpa using
              serreDerivative_slash_equivariant
                2 H₂ H₂_mdifferentiable T
      _ = ∂[(2 : ℂ)] (-H₂) := by
            rw [H₂_T_action]
      _ = -∂[(2 : ℂ)] H₂ := by
            simpa using
              Derivative.serreDerivative_smul
                (2 : ℂ) (-1 : ℂ) H₂
                H₂_mdifferentiable
  have hLinear :
      ((H₂ + (2 : ℂ) • H₄) ∣[(2 : ℤ)] T) =
        H₂ + (2 : ℂ) • H₄ := by
    rw [SlashAction.add_slash,
      ModularForm.SL_smul_slash,
      H₂_T_action, H₄_T_action]
    ext z
    simp only [Pi.add_apply, Pi.smul_apply,
      Pi.neg_apply, smul_eq_mul]
    rw [show H₃ z = H₂ z + H₄ z by
      rw [← Pi.add_apply,
        (congrFun jacobi_quartic_identity z).symm]]
    ring
  have hProduct :
      ((H₂ * (H₂ + (2 : ℂ) • H₄))
          ∣[(4 : ℤ)] T) =
        -H₂ * (H₂ + (2 : ℂ) • H₄) := by
    rw [show (4 : ℤ) = 2 + 2 by norm_num,
      ModularForm.mul_slash_SL2 2 2 T _ _,
      H₂_T_action, hLinear]
  rw [f₂_decompose, SlashAction.add_slash,
    ModularForm.SL_smul_slash, hSerre, hProduct]
  ext z
  simp only [Pi.add_apply, Pi.smul_apply,
    Pi.neg_apply, Pi.mul_apply, smul_eq_mul]
  ring

/-- Under inversion, the third error becomes the negative first error. -/
theorem f₄_S_action :
    (f₄ ∣[(4 : ℤ)] S) = -f₂ := by
  have hSerre :
      (∂[(2 : ℂ)] H₄ ∣[(4 : ℤ)] S) =
        -∂[(2 : ℂ)] H₂ := by
    calc
      (∂[(2 : ℂ)] H₄ ∣[(4 : ℤ)] S) =
          ∂[(2 : ℂ)] (H₄ ∣[(2 : ℤ)] S) := by
            simpa using
              serreDerivative_slash_equivariant
                2 H₄ H₄_mdifferentiable S
      _ = ∂[(2 : ℂ)] (-H₂) := by
            rw [H₄_S_action]
      _ = -∂[(2 : ℂ)] H₂ := by
            simpa using
              Derivative.serreDerivative_smul
                (2 : ℂ) (-1 : ℂ) H₂
                H₂_mdifferentiable
  have hLinear :
      (((2 : ℂ) • H₂ + H₄) ∣[(2 : ℤ)] S) =
        -((2 : ℂ) • H₄ + H₂) := by
    rw [SlashAction.add_slash,
      ModularForm.SL_smul_slash,
      H₂_S_action, H₄_S_action]
    ext z
    simp only [Pi.add_apply, Pi.smul_apply,
      Pi.neg_apply, smul_eq_mul]
    ring
  have hProduct :
      ((H₄ * ((2 : ℂ) • H₂ + H₄))
          ∣[(4 : ℤ)] S) =
        H₂ * (H₂ + (2 : ℂ) • H₄) := by
    rw [show (4 : ℤ) = 2 + 2 by norm_num,
      ModularForm.mul_slash_SL2 2 2 S _ _,
      H₄_S_action, hLinear]
    ext z
    simp only [Pi.mul_apply, Pi.neg_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [f₄_decompose, SlashAction.add_slash,
    ModularForm.SL_smul_slash, hSerre, hProduct]
  unfold f₂
  ext z
  simp only [Pi.sub_apply, Pi.add_apply,
    Pi.smul_apply, Pi.neg_apply, Pi.mul_apply,
    smul_eq_mul]
  ring

/-- Translation sends the third error to the middle error. -/
theorem f₄_T_action :
    (f₄ ∣[(4 : ℤ)] T) = f₃ := by
  have hSerre :
      (∂[(2 : ℂ)] H₄ ∣[(4 : ℤ)] T) =
        ∂[(2 : ℂ)] H₃ := by
    calc
      (∂[(2 : ℂ)] H₄ ∣[(4 : ℤ)] T) =
          ∂[(2 : ℂ)] (H₄ ∣[(2 : ℤ)] T) := by
            simpa using
              serreDerivative_slash_equivariant
                2 H₄ H₄_mdifferentiable T
      _ = ∂[(2 : ℂ)] H₃ := by
            rw [H₄_T_action]
  have hLinear :
      (((2 : ℂ) • H₂ + H₄) ∣[(2 : ℤ)] T) =
        H₄ - H₂ := by
    rw [SlashAction.add_slash,
      ModularForm.SL_smul_slash,
      H₂_T_action, H₄_T_action]
    ext z
    simp only [Pi.add_apply, Pi.smul_apply,
      Pi.neg_apply, Pi.sub_apply, smul_eq_mul]
    rw [show H₃ z = H₂ z + H₄ z by
      rw [← Pi.add_apply,
        (congrFun jacobi_quartic_identity z).symm]]
    ring
  have hProduct :
      ((H₄ * ((2 : ℂ) • H₂ + H₄))
          ∣[(4 : ℤ)] T) =
        H₃ * (H₄ - H₂) := by
    rw [show (4 : ℤ) = 2 + 2 by norm_num,
      ModularForm.mul_slash_SL2 2 2 T _ _,
      H₄_T_action, hLinear]
  rw [f₄_decompose, SlashAction.add_slash,
    ModularForm.SL_smul_slash, hSerre, hProduct]
  unfold f₃
  ext z
  simp only [Pi.sub_apply, Pi.add_apply,
    Pi.smul_apply, Pi.mul_apply, Pi.pow_apply,
    smul_eq_mul]
  rw [show H₃ z = H₂ z + H₄ z by
    rw [← Pi.add_apply,
      (congrFun jacobi_quartic_identity z).symm]]
  ring

/-! ## 3. Two invariant combinations -/

/-- A weight-six combination of the errors.  The coefficients are chosen
so that the permutation of `H₂,H₃,H₄` cancels the permutation of the
errors. -/
def theta_g : ℍ → ℂ :=
  ((2 : ℂ) • H₂ + H₄) * f₂ +
    (H₂ + (2 : ℂ) • H₄) * f₄

/-- A symmetric quadratic combination of the errors, of weight eight. -/
def theta_h : ℍ → ℂ :=
  f₂ ^ 2 + f₂ * f₄ + f₄ ^ 2

/-- The weight-six combination is fixed by inversion. -/
theorem theta_g_S_action :
    (theta_g ∣[(6 : ℤ)] S) = theta_g := by
  have hFirstCoefficient :
      (((2 : ℂ) • H₂ + H₄) ∣[(2 : ℤ)] S) =
        -((2 : ℂ) • H₄ + H₂) := by
    simp only [SlashAction.add_slash,
      ModularForm.SL_smul_slash,
      H₂_S_action, H₄_S_action]
    ext z
    simp only [Pi.add_apply, Pi.smul_apply,
      Pi.neg_apply, smul_eq_mul]
    ring
  have hSecondCoefficient :
      ((H₂ + (2 : ℂ) • H₄) ∣[(2 : ℤ)] S) =
        -(H₄ + (2 : ℂ) • H₂) := by
    simp only [SlashAction.add_slash,
      ModularForm.SL_smul_slash,
      H₂_S_action, H₄_S_action]
    ext z
    simp only [Pi.add_apply, Pi.smul_apply,
      Pi.neg_apply, smul_eq_mul]
    ring
  have hFirstTerm :
      ((((2 : ℂ) • H₂ + H₄) * f₂)
          ∣[(6 : ℤ)] S) =
        ((2 : ℂ) • H₄ + H₂) * f₄ := by
    have h :=
      ModularForm.mul_slash_SL2
        2 4 S ((2 : ℂ) • H₂ + H₄) f₂
    simp only [hFirstCoefficient, f₂_S_action] at h
    rw [show (2 : ℤ) + 4 = 6 by norm_num] at h
    refine h.trans ?_
    ext z
    simp only [Pi.mul_apply, Pi.add_apply,
      Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    ring
  have hSecondTerm :
      (((H₂ + (2 : ℂ) • H₄) * f₄)
          ∣[(6 : ℤ)] S) =
        (H₄ + (2 : ℂ) • H₂) * f₂ := by
    have h :=
      ModularForm.mul_slash_SL2
        2 4 S (H₂ + (2 : ℂ) • H₄) f₄
    simp only [hSecondCoefficient, f₄_S_action] at h
    rw [show (2 : ℤ) + 4 = 6 by norm_num] at h
    refine h.trans ?_
    ext z
    simp only [Pi.mul_apply, Pi.add_apply,
      Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    ring
  simp only [theta_g, SlashAction.add_slash,
    hFirstTerm, hSecondTerm]
  ext z
  simp only [Pi.add_apply, Pi.mul_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

/-- The weight-six combination is fixed by translation. -/
theorem theta_g_T_action :
    (theta_g ∣[(6 : ℤ)] T) = theta_g := by
  have hFirstCoefficient :
      (((2 : ℂ) • H₂ + H₄) ∣[(2 : ℤ)] T) =
        -(2 : ℂ) • H₂ + H₃ := by
    simp only [SlashAction.add_slash,
      ModularForm.SL_smul_slash,
      H₂_T_action, H₄_T_action, smul_neg]
    ext z
    simp only [Pi.add_apply, Pi.smul_apply,
      Pi.neg_apply, smul_eq_mul]
    ring
  have hSecondCoefficient :
      ((H₂ + (2 : ℂ) • H₄) ∣[(2 : ℤ)] T) =
        -H₂ + (2 : ℂ) • H₃ := by
    simp only [SlashAction.add_slash,
      ModularForm.SL_smul_slash,
      H₂_T_action, H₄_T_action]
  have hFirstTerm :
      ((((2 : ℂ) • H₂ + H₄) * f₂)
          ∣[(6 : ℤ)] T) =
        (-(2 : ℂ) • H₂ + H₃) * (-f₂) := by
    have h :=
      ModularForm.mul_slash_SL2
        2 4 T ((2 : ℂ) • H₂ + H₄) f₂
    simp only [hFirstCoefficient, f₂_T_action] at h
    exact h
  have hSecondTerm :
      (((H₂ + (2 : ℂ) • H₄) * f₄)
          ∣[(6 : ℤ)] T) =
        (-H₂ + (2 : ℂ) • H₃) * f₃ := by
    have h :=
      ModularForm.mul_slash_SL2
        2 4 T (H₂ + (2 : ℂ) • H₄) f₄
    simp only [hSecondCoefficient, f₄_T_action] at h
    exact h
  simp only [theta_g, SlashAction.add_slash,
    hFirstTerm, hSecondTerm]
  ext z
  simp only [Pi.add_apply, Pi.mul_apply,
    Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  rw [(congrFun jacobi_quartic_identity z).symm,
    (congrFun f₂_add_f₄_eq_f₃ z).symm]
  simp only [Pi.add_apply]
  ring

/-- The weight-eight combination is fixed by inversion. -/
theorem theta_h_S_action :
    (theta_h ∣[(8 : ℤ)] S) = theta_h := by
  have hF₂Sq :
      ((f₂ ^ 2) ∣[(8 : ℤ)] S) = f₄ ^ 2 := by
    have h :=
      ModularForm.mul_slash_SL2 4 4 S f₂ f₂
    simp only [f₂_S_action] at h
    convert h using 1 <;> ext z <;>
      simp [pow_two]
  have hF₄Sq :
      ((f₄ ^ 2) ∣[(8 : ℤ)] S) = f₂ ^ 2 := by
    have h :=
      ModularForm.mul_slash_SL2 4 4 S f₄ f₄
    simp only [f₄_S_action] at h
    convert h using 1 <;> ext z <;>
      simp [pow_two]
  have hProduct :
      ((f₂ * f₄) ∣[(8 : ℤ)] S) =
        f₂ * f₄ := by
    have h :=
      ModularForm.mul_slash_SL2 4 4 S f₂ f₄
    simp only [f₂_S_action, f₄_S_action] at h
    simpa [show (4 : ℤ) + 4 = 8 by norm_num,
      mul_comm] using h
  simp only [theta_h, SlashAction.add_slash,
    hF₂Sq, hProduct, hF₄Sq]
  ext z
  simp only [Pi.add_apply, Pi.mul_apply,
    Pi.pow_apply]
  ring

/-- The weight-eight combination is fixed by translation. -/
theorem theta_h_T_action :
    (theta_h ∣[(8 : ℤ)] T) = theta_h := by
  have hF₂Sq :
      ((f₂ ^ 2) ∣[(8 : ℤ)] T) = f₂ ^ 2 := by
    have h :=
      ModularForm.mul_slash_SL2 4 4 T f₂ f₂
    simp only [f₂_T_action] at h
    convert h using 1 <;> ext z <;>
      simp [pow_two]
  have hF₄Sq :
      ((f₄ ^ 2) ∣[(8 : ℤ)] T) =
        (f₂ + f₄) ^ 2 := by
    have h :=
      ModularForm.mul_slash_SL2 4 4 T f₄ f₄
    simp only [f₄_T_action] at h
    convert h using 1
    · ext z
      simp [pow_two]
    · ext z
      simp only [Pi.pow_apply, Pi.mul_apply,
        pow_two]
      rw [(congrFun f₂_add_f₄_eq_f₃ z).symm,
        Pi.add_apply]
  have hProduct :
      ((f₂ * f₄) ∣[(8 : ℤ)] T) =
        (-f₂) * (f₂ + f₄) := by
    have h :=
      ModularForm.mul_slash_SL2 4 4 T f₂ f₄
    simp only [f₂_T_action, f₄_T_action] at h
    simpa [show (4 : ℤ) + 4 = 8 by norm_num,
      ← f₂_add_f₄_eq_f₃] using h
  simp only [theta_h, SlashAction.add_slash,
    hF₂Sq, hProduct, hF₄Sq]
  ext z
  simp only [Pi.add_apply, Pi.mul_apply,
    Pi.neg_apply, Pi.pow_apply]
  ring

/-- Holomorphy of the weight-six invariant. -/
theorem theta_g_mdifferentiable :
    MDiff theta_g := by
  intro z
  exact
    ((((H₂_mdifferentiable z).const_smul
      (2 : ℂ)).add (H₄_mdifferentiable z)).mul
        (f₂_mdifferentiable z)).add
      (((H₂_mdifferentiable z).add
        ((H₄_mdifferentiable z).const_smul
          (2 : ℂ))).mul
            (f₄_mdifferentiable z))

/-- Holomorphy of the weight-eight invariant. -/
theorem theta_h_mdifferentiable :
    MDiff theta_h := by
  intro z
  exact
    (((f₂_mdifferentiable z).pow 2).add
      ((f₂_mdifferentiable z).mul
        (f₄_mdifferentiable z))).add
          ((f₄_mdifferentiable z).pow 2)

/-! ## 4. Cusp limits and low-weight vanishing -/

/-- The first error tends to zero at the infinite cusp. -/
theorem f₂_tendsto_atImInfty :
    Tendsto f₂ atImInfty (𝓝 0) := by
  have hSerre :
      Tendsto (∂[(2 : ℂ)] H₂)
        atImInfty (𝓝 0) := by
    simpa using
      serreDerivative_tendsto_of_tendsto
        (2 : ℂ) H₂ 0 H₂_mdifferentiable
        (HGAS.Analysis.isBoundedAtImInfty_of_tendsto
          H₂_tendsto_atImInfty)
        H₂_tendsto_atImInfty
  have hTwoH₄ :
      Tendsto (fun z : ℍ ↦ (2 : ℂ) * H₄ z)
        atImInfty (𝓝 ((2 : ℂ) * 1)) :=
    tendsto_const_nhds.mul H₄_tendsto_atImInfty
  have hSum :
      Tendsto
        (fun z : ℍ ↦ H₂ z + 2 * H₄ z)
        atImInfty (𝓝 (0 + (2 : ℂ) * 1)) :=
    H₂_tendsto_atImInfty.add hTwoH₄
  have hProduct :
      Tendsto
        (fun z : ℍ ↦
          H₂ z * (H₂ z + 2 * H₄ z))
        atImInfty (𝓝 0) := by
    convert H₂_tendsto_atImInfty.mul hSum using 1
    ring
  have hScaled :
      Tendsto
        (fun z : ℍ ↦
          (1 / 6 : ℂ) *
            (H₂ z * (H₂ z + 2 * H₄ z)))
        atImInfty (𝓝 0) := by
    simpa using hProduct.const_mul (1 / 6 : ℂ)
  change
    Tendsto
      (fun z : ℍ ↦
        ∂[(2 : ℂ)] H₂ z -
          (1 / 6 : ℂ) *
            (H₂ z * (H₂ z + 2 * H₄ z)))
      atImInfty (𝓝 0)
  simpa using hSerre.sub hScaled

/-- The third error tends to zero at the infinite cusp.  Here the
constant term `-1/6` of the Serre derivative cancels the constant term
`+1/6` of the theta polynomial. -/
theorem f₄_tendsto_atImInfty :
    Tendsto f₄ atImInfty (𝓝 0) := by
  have hSerre :
      Tendsto (∂[(2 : ℂ)] H₄)
        atImInfty (𝓝 (-(1 / 6 : ℂ))) := by
    convert
      serreDerivative_tendsto_of_tendsto
        (2 : ℂ) H₄ 1 H₄_mdifferentiable
        (HGAS.Analysis.isBoundedAtImInfty_of_tendsto
          H₄_tendsto_atImInfty)
        H₄_tendsto_atImInfty using 1
    norm_num
  have hTwoH₂ :
      Tendsto (fun z : ℍ ↦ (2 : ℂ) * H₂ z)
        atImInfty (𝓝 ((2 : ℂ) * 0)) :=
    tendsto_const_nhds.mul H₂_tendsto_atImInfty
  have hSum :
      Tendsto
        (fun z : ℍ ↦ 2 * H₂ z + H₄ z)
        atImInfty (𝓝 ((2 : ℂ) * 0 + 1)) :=
    hTwoH₂.add H₄_tendsto_atImInfty
  have hProduct :
      Tendsto
        (fun z : ℍ ↦
          H₄ z * (2 * H₂ z + H₄ z))
        atImInfty (𝓝 1) := by
    convert H₄_tendsto_atImInfty.mul hSum using 1
    ring
  have hScaled :
      Tendsto
        (fun z : ℍ ↦
          (1 / 6 : ℂ) *
            (H₄ z * (2 * H₂ z + H₄ z)))
        atImInfty (𝓝 (1 / 6 : ℂ)) := by
    simpa using hProduct.const_mul (1 / 6 : ℂ)
  change
    Tendsto
      (fun z : ℍ ↦
        ∂[(2 : ℂ)] H₄ z +
          (1 / 6 : ℂ) *
            (H₄ z * (2 * H₂ z + H₄ z)))
      atImInfty (𝓝 0)
  simpa using hSerre.add hScaled

/-- The invariant of weight six vanishes at the cusp. -/
theorem theta_g_tendsto_atImInfty :
    Tendsto theta_g atImInfty (𝓝 0) := by
  have hTwoH₂ :
      Tendsto (fun z : ℍ ↦ (2 : ℂ) * H₂ z)
        atImInfty (𝓝 ((2 : ℂ) * 0)) :=
    tendsto_const_nhds.mul H₂_tendsto_atImInfty
  have hTwoH₄ :
      Tendsto (fun z : ℍ ↦ (2 : ℂ) * H₄ z)
        atImInfty (𝓝 ((2 : ℂ) * 1)) :=
    tendsto_const_nhds.mul H₄_tendsto_atImInfty
  have hFirstCoefficient :
      Tendsto
        (fun z : ℍ ↦ 2 * H₂ z + H₄ z)
        atImInfty (𝓝 1) := by
    convert hTwoH₂.add H₄_tendsto_atImInfty using 1
    ring
  have hSecondCoefficient :
      Tendsto
        (fun z : ℍ ↦ H₂ z + 2 * H₄ z)
        atImInfty (𝓝 2) := by
    convert H₂_tendsto_atImInfty.add hTwoH₄ using 1
    ring
  change
    Tendsto
      (fun z : ℍ ↦
        (2 * H₂ z + H₄ z) * f₂ z +
          (H₂ z + 2 * H₄ z) * f₄ z)
      atImInfty (𝓝 0)
  convert
    (hFirstCoefficient.mul f₂_tendsto_atImInfty).add
      (hSecondCoefficient.mul
        f₄_tendsto_atImInfty) using 1
  ring

/-- The invariant of weight eight vanishes at the cusp. -/
theorem theta_h_tendsto_atImInfty :
    Tendsto theta_h atImInfty (𝓝 0) := by
  change
    Tendsto
      (fun z : ℍ ↦
        f₂ z ^ 2 + f₂ z * f₄ z + f₄ z ^ 2)
      atImInfty (𝓝 0)
  convert
    ((f₂_tendsto_atImInfty.pow 2).add
      (f₂_tendsto_atImInfty.mul
        f₄_tendsto_atImInfty)).add
          (f₄_tendsto_atImInfty.pow 2) using 1
  ring

/-- There is no nonzero level-one cusp form of weight six, hence the
first invariant is identically zero. -/
theorem theta_g_eq_zero :
    theta_g = 0 :=
  eq_zero_of_ST_invariant_tendsto_zero
    (by norm_num) theta_g
    theta_g_S_action theta_g_T_action
    theta_g_mdifferentiable
    theta_g_tendsto_atImInfty

/-- There is no nonzero level-one cusp form of weight eight, hence the
second invariant is identically zero. -/
theorem theta_h_eq_zero :
    theta_h = 0 :=
  eq_zero_of_ST_invariant_tendsto_zero
    (by norm_num) theta_h
    theta_h_S_action theta_h_T_action
    theta_h_mdifferentiable
    theta_h_tendsto_atImInfty

/-! ## 5. Eliminating the errors -/

/-- The theta polynomial representing `E₄` is not the zero function,
because its cusp limit is one. -/
theorem thetaE4Polynomial_ne_zero :
    thetaE4Polynomial ≠ 0 := by
  intro hzero
  have hLimitZero :
      Tendsto thetaE4Polynomial
        atImInfty (𝓝 0) := by
    rw [hzero]
    exact tendsto_const_nhds
  have hOneZero : (1 : ℂ) = 0 :=
    tendsto_nhds_unique
      thetaE4Polynomial_tendsto_one hLimitZero
  exact one_ne_zero hOneZero

/-- Multiplying the theta realization of `E₄` by three still gives a
nonzero holomorphic function. -/
theorem three_thetaE4Polynomial_ne_zero :
    (fun z : ℍ ↦ (3 : ℂ) *
      thetaE4Polynomial z) ≠ 0 := by
  intro hzero
  apply thetaE4Polynomial_ne_zero
  funext z
  have hz := congrFun hzero z
  simp only [Pi.zero_apply] at hz
  exact
    (mul_eq_zero.mp hz).resolve_left
      (by norm_num)

/-- Holomorphy of the nonzero factor used to eliminate the errors. -/
theorem three_thetaE4Polynomial_mdifferentiable :
    MDiff
      (fun z : ℍ ↦
        (3 : ℂ) * thetaE4Polynomial z) := by
  intro z
  simpa [smul_eq_mul] using
    (thetaE4Polynomial_mdifferentiable z).const_smul
      (3 : ℂ)

/-- Pointwise elimination identity.  If the weight-six invariant vanishes,
then multiplying the weight-eight invariant by
`(2H₂+H₄)²` produces `3 E₄ f₄²`. -/
theorem f₄_sq_mul_eq
    (z : ℍ) (hg : theta_g z = 0) :
    f₄ z ^ 2 *
        (3 * thetaE4Polynomial z) =
      (2 * H₂ z + H₄ z) ^ 2 *
        theta_h z := by
  unfold thetaE4Polynomial
  set A : ℂ := 2 * H₂ z + H₄ z with hA
  set B : ℂ := H₂ z + 2 * H₄ z with hB
  have hRelation :
      A * f₂ z + B * f₄ z = 0 := by
    simp only [theta_g, hA, hB,
      Pi.smul_apply, Pi.mul_apply, Pi.add_apply,
      smul_eq_mul] at hg ⊢
    exact hg
  have hAf₂ :
      A * f₂ z = -(B * f₄ z) := by
    linear_combination hRelation
  have hSquare :
      A ^ 2 * f₂ z ^ 2 =
        B ^ 2 * f₄ z ^ 2 := by
    have h :
        (A * f₂ z) ^ 2 =
          (B * f₄ z) ^ 2 := by
      rw [hAf₂]
      ring
    calc
      A ^ 2 * f₂ z ^ 2 =
          (A * f₂ z) ^ 2 := by ring
      _ = (B * f₄ z) ^ 2 := h
      _ = B ^ 2 * f₄ z ^ 2 := by ring
  have hMixed :
      A ^ 2 * (f₂ z * f₄ z) =
        -(A * B * f₄ z ^ 2) := by
    calc
      A ^ 2 * (f₂ z * f₄ z) =
          (A * f₂ z) * (A * f₄ z) := by
            ring
      _ = (-(B * f₄ z)) *
          (A * f₄ z) := by rw [hAf₂]
      _ = -(A * B * f₄ z ^ 2) := by
            ring
  have hCoefficient :
      A ^ 2 - A * B + B ^ 2 =
        3 *
          (H₂ z ^ 2 +
            H₂ z * H₄ z + H₄ z ^ 2) := by
    simp only [hA, hB]
    ring
  unfold theta_h
  calc
    f₄ z ^ 2 *
        (3 *
          (H₂ z ^ 2 +
            H₂ z * H₄ z + H₄ z ^ 2)) =
      f₄ z ^ 2 *
        (A ^ 2 - A * B + B ^ 2) := by
          rw [hCoefficient]
    _ =
      B ^ 2 * f₄ z ^ 2 +
        (-(A * B * f₄ z ^ 2)) +
          A ^ 2 * f₄ z ^ 2 := by
            ring
    _ =
      A ^ 2 * f₂ z ^ 2 +
        A ^ 2 * (f₂ z * f₄ z) +
          A ^ 2 * f₄ z ^ 2 := by
            rw [hSquare, hMixed]
    _ =
      A ^ 2 *
        (f₂ z ^ 2 +
          f₂ z * f₄ z + f₄ z ^ 2) := by
            ring

/-- The first error vanishes identically.  The key point is that the ring
of holomorphic functions on the connected upper half-plane has no zero
divisors. -/
theorem f₂_eq_zero :
    f₂ = 0 := by
  have hg := theta_g_eq_zero
  have hh := theta_h_eq_zero
  suffices hf₄ : f₄ = 0 by
    funext z
    have hz := congrFun hh z
    unfold theta_h at hz
    simp only [Pi.add_apply, Pi.pow_apply,
      Pi.mul_apply, Pi.zero_apply, hf₄] at hz
    simpa [sq_eq_zero_iff] using hz
  have hProduct :
      f₄ ^ 2 *
          (fun z : ℍ ↦
            (3 : ℂ) * thetaE4Polynomial z) =
        0 := by
    ext z
    simp only [Pi.mul_apply, Pi.pow_apply,
      Pi.zero_apply]
    have hhz : theta_h z = 0 :=
      congrFun hh z
    calc
      f₄ z ^ 2 *
          (3 * thetaE4Polynomial z) =
        (2 * H₂ z + H₄ z) ^ 2 *
          theta_h z :=
            f₄_sq_mul_eq z (congrFun hg z)
      _ = 0 := by rw [hhz, mul_zero]
  have hF₄SqHol :
      MDiff (f₄ ^ 2) :=
    f₄_mdifferentiable.pow 2
  have hF₄SqZero :
      f₄ ^ 2 = 0 :=
    ((UpperHalfPlane.mul_eq_zero_iff
      hF₄SqHol
      three_thetaE4Polynomial_mdifferentiable).mp
        hProduct).resolve_right
          three_thetaE4Polynomial_ne_zero
  exact
    (UpperHalfPlane.mul_eq_zero_iff
      f₄_mdifferentiable
      f₄_mdifferentiable).mp
        (pow_two f₄ ▸ hF₄SqZero)
      |>.elim id id

/-- The third error vanishes after substituting `f₂=0` in the
weight-eight invariant. -/
theorem f₄_eq_zero :
    f₄ = 0 := by
  funext z
  simpa [theta_h, sq_eq_zero_iff,
    f₂_eq_zero] using
      congrFun theta_h_eq_zero z

/-- The middle error vanishes by `f₃=f₂+f₄`. -/
theorem f₃_eq_zero :
    f₃ = 0 := by
  rw [← f₂_add_f₄_eq_f₃]
  simp [f₂_eq_zero, f₄_eq_zero]

/-! ## 6. The differential identities -/

/-- Serre derivative of `H₂`:
`∂₂ H₂ = (H₂² + 2 H₂ H₄)/6`. -/
theorem serreDerivative_H₂ :
    ∂[(2 : ℂ)] H₂ =
      fun z ↦
        (1 / 6 : ℂ) *
          (H₂ z ^ 2 +
            2 * H₂ z * H₄ z) := by
  funext z
  have hz := congrFun f₂_eq_zero z
  simp only [f₂, Pi.sub_apply, Pi.smul_apply,
    Pi.mul_apply, Pi.add_apply, smul_eq_mul,
    Pi.zero_apply, sub_eq_zero] at hz
  convert hz using 1
  ring

/-- Serre derivative of `H₃`:
`∂₂ H₃ = (H₂² - H₄²)/6`. -/
theorem serreDerivative_H₃ :
    ∂[(2 : ℂ)] H₃ =
      fun z ↦
        (1 / 6 : ℂ) *
          (H₂ z ^ 2 - H₄ z ^ 2) := by
  funext z
  have hz := congrFun f₃_eq_zero z
  simpa only [f₃, Pi.sub_apply, Pi.smul_apply,
    Pi.pow_apply, smul_eq_mul, Pi.zero_apply,
    sub_eq_zero] using hz

/-- Serre derivative of `H₄`:
`∂₂ H₄ = -(2 H₂ H₄ + H₄²)/6`. -/
theorem serreDerivative_H₄ :
    ∂[(2 : ℂ)] H₄ =
      fun z ↦
        -(1 / 6 : ℂ) *
          (2 * H₂ z * H₄ z +
            H₄ z ^ 2) := by
  funext z
  have hz := congrFun f₄_eq_zero z
  simp only [f₄, Pi.add_apply, Pi.smul_apply,
    Pi.mul_apply, smul_eq_mul, Pi.zero_apply,
    add_eq_zero_iff_eq_neg] at hz
  convert hz using 1
  ring

/-- Ordinary normalized derivative of `H₂`. -/
theorem normalizedDeriv_H₂ :
    D H₂ =
      (1 / 6 : ℂ) •
          (H₂ ^ 2 +
            (2 : ℂ) • (H₂ * H₄)) +
        (1 / 6 : ℂ) •
          (EisensteinSeries.E2 * H₂) := by
  ext z
  have hRecover :
      D H₂ z =
        ∂[(2 : ℂ)] H₂ z +
          2 * 12⁻¹ *
            EisensteinSeries.E2 z * H₂ z := by
    simp only [Derivative.serreDerivative_apply]
    ring
  rw [hRecover, congrFun serreDerivative_H₂]
  simp only [Pi.add_apply, Pi.mul_apply,
    Pi.pow_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Ordinary normalized derivative of `H₃`. -/
theorem normalizedDeriv_H₃ :
    D H₃ =
      (1 / 6 : ℂ) •
          (H₂ ^ 2 - H₄ ^ 2) +
        (1 / 6 : ℂ) •
          (EisensteinSeries.E2 * H₃) := by
  ext z
  have hRecover :
      D H₃ z =
        ∂[(2 : ℂ)] H₃ z +
          2 * 12⁻¹ *
            EisensteinSeries.E2 z * H₃ z := by
    simp only [Derivative.serreDerivative_apply]
    ring
  rw [hRecover, congrFun serreDerivative_H₃]
  simp only [Pi.add_apply, Pi.sub_apply,
    Pi.mul_apply, Pi.pow_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

/-- Ordinary normalized derivative of `H₄`. -/
theorem normalizedDeriv_H₄ :
    D H₄ =
      (-(1 / 6 : ℂ)) •
          ((2 : ℂ) • (H₂ * H₄) +
            H₄ ^ 2) +
        (1 / 6 : ℂ) •
          (EisensteinSeries.E2 * H₄) := by
  ext z
  have hRecover :
      D H₄ z =
        ∂[(2 : ℂ)] H₄ z +
          2 * 12⁻¹ *
            EisensteinSeries.E2 z * H₄ z := by
    simp only [Derivative.serreDerivative_apply]
    ring
  rw [hRecover, congrFun serreDerivative_H₄]
  simp only [Pi.add_apply, Pi.mul_apply,
    Pi.pow_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-! The following aliases retain the conventional names used in the
Sphere-Packing formalization while the primary theorems above follow
Mathlib's native API names. -/

alias serre_D_H₂ := serreDerivative_H₂
alias serre_D_H₃ := serreDerivative_H₃
alias serre_D_H₄ := serreDerivative_H₄

alias D_H₂ := normalizedDeriv_H₂
alias D_H₃ := normalizedDeriv_H₃
alias D_H₄ := normalizedDeriv_H₄

end

end HGAS.Modular
