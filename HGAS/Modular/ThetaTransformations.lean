import HGAS.Modular.LevelOneSlashGenerators
import HGAS.Modular.ThetaHolomorphy
import Mathlib.Tactic

/-!
# `S` and `T` transformations of the even theta fourth powers

This file proves the six transformations needed by the Jacobi identity
and the theta differential equations.  Raising to the fourth power removes
the square-root ambiguity in the usual weight-one-half theta
transformations:

```
H₂ |₂ T = -H₂,   H₃ |₂ T = H₄,   H₄ |₂ T = H₃,
H₂ |₂ S = -H₄,   H₃ |₂ S = -H₃,  H₄ |₂ S = -H₂.
```

The `T` identities are obtained directly from the defining series.  The
`S` identities use Mathlib's Poisson-summation functional equation for
`jacobiTheta₂`.  The calculation follows the fully formal proof in
`Sphere-Packing-Lean`, with names and imports adapted to this project.
-/

namespace HGAS.Modular

open scoped Real MatrixGroups ModularForm
open UpperHalfPlane hiding I
open Complex Real Matrix ModularGroup ModularForm SlashAction

noncomputable section

/-- Translation by one acts by `-1` on `H₂`. -/
theorem H₂_T_action :
    (H₂ ∣[(2 : ℤ)] T) = -H₂ := by
  ext x
  suffices htheta :
      theta₂ ((1 : ℝ) +ᵥ x) =
        cexp (π * I / 4) * theta₂ x by
    simp_rw [modularSlashT_apply, Pi.neg_apply, H₂,
      htheta, mul_pow, ← Complex.exp_nat_mul,
      mul_comm ((4 : ℕ) : ℂ), Nat.cast_ofNat,
      div_mul_cancel₀ (b := (4 : ℂ)) _
        (by simp), Complex.exp_pi_mul_I,
      neg_one_mul]
  calc
    _ = ∑' n : ℤ,
        cexp
          (π * I * (n + 1 / 2) ^ 2 *
            ((1 : ℝ) +ᵥ x)) := by
          simp_rw [theta₂, theta₂Term]
    _ = ∑' n : ℤ,
        cexp (π * I / 4) *
          cexp
            (π * I * (n ^ 2 + n) +
              π * I * (n + 1 / 2) ^ 2 * x) := by
          apply tsum_congr
          intro n
          rw [coe_vadd, ofReal_one]
          repeat rw [← Complex.exp_add]
          congr
          ring_nf
    _ = cexp (π * I / 4) *
        ∑' n : ℤ,
          cexp
            (π * I * (n ^ 2 + n) +
              π * I * (n + 1 / 2) ^ 2 * x) := by
          rw [tsum_mul_left]
    _ = _ := by
          simp_rw [theta₂, theta₂Term]
          congr 1
          apply tsum_congr
          intro n
          have hn : Even (n ^ 2 + n) := by
            convert Int.even_mul_succ_self n using 1
            ring_nf
          norm_cast
          rw [Complex.exp_add]
          rw [mul_comm (π * I),
            Complex.exp_int_mul,
            Complex.exp_pi_mul_I,
            hn.neg_one_zpow, one_mul]

/-- Translation by one interchanges `H₃` and `H₄`. -/
theorem H₃_T_action :
    (H₃ ∣[(2 : ℤ)] T) = H₄ := by
  ext x
  simp_rw [modularSlashT_apply, H₃, H₄,
    theta₃, theta₄, theta₃Term, theta₄Term]
  congr 1
  apply tsum_congr
  intro n
  rw [coe_vadd, ofReal_one, mul_add,
    Complex.exp_add, mul_one, mul_comm (π * I),
    ← Int.cast_pow, Complex.exp_int_mul,
    Complex.exp_pi_mul_I]
  congr 1
  rcases Int.even_or_odd n with hn | hn
  · rw [hn.neg_one_zpow, Even.neg_one_zpow]
    simp [sq, hn]
  · rw [hn.neg_one_zpow, Odd.neg_one_zpow]
    simp [sq, hn]

/-- Translation by one interchanges `H₄` and `H₃`. -/
theorem H₄_T_action :
    (H₄ ∣[(2 : ℤ)] T) = H₃ := by
  ext x
  simp_rw [← H₃_T_action, modularSlashT_apply,
    H₃, theta₃_eq_jacobiTheta₂, coe_vadd,
    ← add_assoc]
  norm_num
  rw [add_comm, jacobiTheta₂_add_right]

/-- Inversion interchanges `H₂` and `H₄`, with sign `-1`. -/
theorem H₂_S_action :
    (H₂ ∣[(2 : ℤ)] S) = -H₄ := by
  ext ⟨x, hx⟩
  have hxne : x ≠ 0 := by
    simp [Complex.ext_iff, hx.ne.symm]
  calc
    _ = cexp (-π * I / x) *
          jacobiTheta₂ (-1 / (2 * x)) (-1 / x) ^ 4 *
          x ^ (-2 : ℤ) := by
      rw [modularSlashS_apply, H₂,
        theta₂_eq_jacobiTheta₂]
      simp only [inv_neg, mul_neg, mul_pow,
        ← Complex.exp_nat_mul, Nat.cast_ofNat,
        Int.reduceNeg, _root_.zpow_neg, neg_mul,
        mul_eq_mul_right_iff, inv_eq_zero]
      rw [mul_comm 4,
        div_mul_cancel₀ _ (by norm_num)]
      left
      congr 3
      · rw [← div_eq_mul_inv, neg_div]
      · rw [← one_div, neg_div, div_div,
          mul_comm, neg_div]
      · rw [← one_div, neg_div]
    _ = cexp (-π * I / x) * x ^ (-2 : ℤ) *
          (1 / (I / x) ^ ((1 : ℂ) / 2) *
            cexp (π * I / (4 * x)) *
            jacobiTheta₂ (1 / 2) x) ^ 4 := by
      rw [mul_right_comm,
        jacobiTheta₂_functional_equation]
      congr 4
      · ring_nf
      · congr 1
        rw [neg_mul, neg_div, one_div, neg_div,
          div_neg, neg_mul, neg_div, neg_neg]
        ring_nf
        simp [sq, ← mul_assoc,
          inv_mul_cancel_right₀ hxne]
      · ring_nf
        simp [hxne]
      · ring_nf
        simp [inv_inv]
    _ = cexp (-π * I / x) * x ^ (-2 : ℤ) *
          ((1 / (I / x) ^ ((1 : ℂ) / 2)) ^ 4 *
            cexp (π * I / (4 * x)) ^ 4 *
            jacobiTheta₂ (1 / 2) x ^ 4) := by
      simp [mul_pow]
    _ = cexp (-π * I / x) * x ^ (-2 : ℤ) *
          ((1 / (I / x) ^ (2 : ℂ)) *
            cexp (π * I / (4 * x)) ^ 4 *
            jacobiTheta₂ (1 / 2) x ^ 4) := by
      congr 3
      simp only [div_pow, one_pow,
        ← cpow_mul_nat]
      ring_nf
    _ = cexp (-π * I / x) *
          (x ^ (-2 : ℤ) * (-x ^ (2 : ℤ))) *
          cexp (π * I / (4 * x)) ^ 4 *
          jacobiTheta₂ (1 / 2) x ^ 4 := by
      repeat rw [← mul_assoc]
      congr 4
      rw [cpow_ofNat, div_pow, one_div_div,
        I_sq, div_neg, div_one]
      rfl
    _ = -cexp (-π * I / x) *
          cexp (π * I / x) *
          jacobiTheta₂ (1 / 2) x ^ 4 := by
      rw [mul_neg, ← zpow_add₀ hxne,
        neg_add_cancel, mul_neg, zpow_zero,
        mul_one]
      congr 2
      rw [← Complex.exp_nat_mul]
      ring_nf
    _ = -jacobiTheta₂ (1 / 2) x ^ 4 := by
      rw [neg_mul, ← Complex.exp_add,
        neg_mul (π : ℂ), neg_div,
        neg_add_cancel, Complex.exp_zero,
        neg_one_mul]
    _ = -H₄ ⟨x, hx⟩ := by
      simp [H₄, theta₄_eq_jacobiTheta₂]

/-- Inversion acts by `-1` on `H₃`. -/
theorem H₃_S_action :
    (H₃ ∣[(2 : ℤ)] S) = -H₃ := by
  ext x
  have hxne : (x : ℂ) ≠ 0 := by
    obtain ⟨x, hx⟩ := x
    change x ≠ 0
    simp [Complex.ext_iff, hx.ne.symm]
  have hfunctional :
      jacobiTheta₂ 0 (x : ℂ) =
        1 / (-(I * (x : ℂ))) ^ ((1 : ℂ) / 2) *
          jacobiTheta₂ 0 (-1 / (x : ℂ)) := by
    simpa using
      jacobiTheta₂_functional_equation
        0 (x : ℂ)
  rw [modularSlashS_apply]
  simp only [Pi.neg_apply, H₃,
    theta₃_eq_jacobiTheta₂]
  rw [hfunctional, mul_pow]
  have harg :
      (-(x : ℂ))⁻¹ = -(1 / (x : ℂ)) := by
    rw [inv_neg, one_div]
  rw [harg]
  have harg' :
      -1 / (x : ℂ) = -(1 / (x : ℂ)) := by
    ring
  rw [harg']
  rw [_root_.zpow_neg]
  have hcoef :
      ((x : ℂ) ^ (2 : ℤ))⁻¹ =
        -(1 / (-(I * (x : ℂ))) ^
          ((1 : ℂ) / 2)) ^ 4 := by
    rw [div_pow, ← cpow_mul_nat]
    norm_num
    field_simp [hxne]
    exact Complex.I_sq
  rw [hcoef]
  ring

/-- Inversion interchanges `H₄` and `H₂`, with sign `-1`. -/
theorem H₄_S_action :
    (H₄ ∣[(2 : ℤ)] S) = -H₂ := by
  have hSS : S * S = (-1 : SL(2, ℤ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [S, Matrix.mul_apply]
  rw [← neg_eq_iff_eq_neg.mpr H₂_S_action,
    neg_slash, ← slash_mul, hSS,
    slashNegOne_of_even _ (by decide)]

end

end HGAS.Modular
