import HGAS.Modular.JacobiThetaReducedCompact
import Mathlib.Algebra.Order.Round
import Mathlib.Tactic

/-!
# Horizontal level-two reduction for the Jacobi theta vector

The modular translation `τ ↦ τ + 2k`, `k ∈ ℤ`, preserves the norm of the
four-coordinate Jacobi theta vector.  At fixed `z`, the coordinates
`θ₃,θ₄` are unchanged, while `θ₁,θ₂` acquire the common unit multiplier

```
                    exp (π i k / 2).
```

This file proves that statement directly from the theta series and then
packages the canonical nearest-integer reduction

```
  k(τ) = round (Re τ / 2),       τred = τ - 2 k(τ).
```

It follows that `|Re τred| ≤ 1`, `Im τred = Im τ`, and every positive
lower bound for the reduced theta vector transports unchanged to the
original parameter.  No transformation of `z` is needed.
-/

namespace HGAS.Modular

open Complex Real
open UpperHalfPlane hiding I

noncomputable section

/-! ## Exact translation formulas -/

/-- The unit multiplier on `θ₁,θ₂` under `τ ↦ τ+2k`. -/
def horizontalThetaMultiplier (k : ℤ) : ℂ :=
  cexp (π * I * (k : ℂ) / 2)

theorem horizontalThetaMultiplier_ne_zero (k : ℤ) :
    horizontalThetaMultiplier k ≠ 0 :=
  Complex.exp_ne_zero _

theorem norm_horizontalThetaMultiplier (k : ℤ) :
    ‖horizontalThetaMultiplier k‖ = 1 := by
  simp [horizontalThetaMultiplier, Complex.norm_exp]

/-- Mathlib's basic two-variable theta series is periodic under every
integral multiple of the modular period `2`. -/
theorem jacobiTheta₂_tau_add_two_int
    (z τ : ℂ) (k : ℤ) :
    jacobiTheta₂ z (τ + 2 * (k : ℂ)) =
      jacobiTheta₂ z τ := by
  have hperiod :
      Function.Periodic
        (fun u : ℂ ↦ jacobiTheta₂ z u) 2 :=
    fun u ↦ jacobiTheta₂_add_right z u
  have hk := (hperiod.int_mul k) τ
  simpa only [Int.cast_ofNat, mul_comm] using hk

/-- The theta series is periodic in `z` under every integral shift. -/
theorem jacobiTheta₂_add_int_left
    (z τ : ℂ) (k : ℤ) :
    jacobiTheta₂ (z + (k : ℂ)) τ =
      jacobiTheta₂ z τ := by
  have hperiod :
      Function.Periodic
        (fun u : ℂ ↦ jacobiTheta₂ u τ) 1 :=
    fun u ↦ jacobiTheta₂_add_left u τ
  have hk := (hperiod.int_mul k) z
  simpa only [Int.cast_one, mul_one] using hk

/-- `θ₃` is unchanged by an integral level-two modular translation. -/
theorem jacobiTheta3_tau_add_two_int
    (z τ : ℂ) (k : ℤ) :
    jacobiTheta3 z (τ + 2 * (k : ℂ)) =
      jacobiTheta3 z τ := by
  exact jacobiTheta₂_tau_add_two_int z τ k

/-- `θ₄` is unchanged by an integral level-two modular translation. -/
theorem jacobiTheta4_tau_add_two_int
    (z τ : ℂ) (k : ℤ) :
    jacobiTheta4 z (τ + 2 * (k : ℂ)) =
      jacobiTheta4 z τ := by
  unfold jacobiTheta4
  exact jacobiTheta₂_tau_add_two_int _ τ k

/-- `θ₂` acquires the unit multiplier `exp(πik/2)`. -/
theorem jacobiTheta2_tau_add_two_int
    (z τ : ℂ) (k : ℤ) :
    jacobiTheta2 z (τ + 2 * (k : ℂ)) =
      horizontalThetaMultiplier k *
        jacobiTheta2 z τ := by
  unfold jacobiTheta2 horizontalThetaMultiplier
  rw [jacobiTheta₂_tau_add_two_int]
  have harg :
      z + (τ + 2 * (k : ℂ)) / 2 =
        (z + τ / 2) + (k : ℂ) := by
    ring
  rw [harg, jacobiTheta₂_add_int_left]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- `θ₁` has the same multiplier as `θ₂`. -/
theorem jacobiTheta1_tau_add_two_int
    (z τ : ℂ) (k : ℤ) :
    jacobiTheta1 z (τ + 2 * (k : ℂ)) =
      horizontalThetaMultiplier k *
        jacobiTheta1 z τ := by
  unfold jacobiTheta1
  rw [jacobiTheta2_tau_add_two_int]
  ring

/-- Coordinatewise multiplier for the four-coordinate vector. -/
def horizontalThetaVectorMultiplier
    (k : ℤ) : Fin 4 → ℂ :=
  ![horizontalThetaMultiplier k,
    horizontalThetaMultiplier k, 1, 1]

/-- Exact vector transformation under `τ ↦ τ+2k`. -/
theorem jacobiThetaVector_tau_add_two_int
    (z τ : ℂ) (k : ℤ) :
    jacobiThetaVector z (τ + 2 * (k : ℂ)) =
      horizontalThetaVectorMultiplier k *
        jacobiThetaVector z τ := by
  funext j
  fin_cases j
  · simpa [horizontalThetaVectorMultiplier,
      jacobiThetaVector] using
        jacobiTheta1_tau_add_two_int z τ k
  · simpa [horizontalThetaVectorMultiplier,
      jacobiThetaVector] using
        jacobiTheta2_tau_add_two_int z τ k
  · simpa [horizontalThetaVectorMultiplier,
      jacobiThetaVector] using
        jacobiTheta3_tau_add_two_int z τ k
  · simpa [horizontalThetaVectorMultiplier,
      jacobiThetaVector] using
        jacobiTheta4_tau_add_two_int z τ k

/-- Every coordinate multiplier has norm one. -/
theorem norm_horizontalThetaVectorMultiplier
    (k : ℤ) (j : Fin 4) :
    ‖horizontalThetaVectorMultiplier k j‖ = 1 := by
  fin_cases j <;>
    simp [horizontalThetaVectorMultiplier,
      norm_horizontalThetaMultiplier]

/-- The sup norm of the theta vector is exactly invariant under all
horizontal level-two translations. -/
theorem norm_jacobiThetaVector_tau_add_two_int
    (z τ : ℂ) (k : ℤ) :
    ‖jacobiThetaVector z (τ + 2 * (k : ℂ))‖ =
      ‖jacobiThetaVector z τ‖ := by
  have hcoord :
      ∀ j : Fin 4,
        ‖jacobiThetaVector z
            (τ + 2 * (k : ℂ)) j‖ =
          ‖jacobiThetaVector z τ j‖ := by
    intro j
    rw [jacobiThetaVector_tau_add_two_int]
    simp only [Pi.mul_apply, norm_mul,
      norm_horizontalThetaVectorMultiplier,
      one_mul]
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg
      (norm_nonneg (jacobiThetaVector z τ))]
    intro j
    rw [hcoord j]
    exact norm_le_pi_norm _ j
  · rw [pi_norm_le_iff_of_nonneg
      (norm_nonneg
        (jacobiThetaVector z
          (τ + 2 * (k : ℂ))))]
    intro j
    rw [← hcoord j]
    exact norm_le_pi_norm _ j

/-! ## Canonical nearest-integer reduction -/

/-- The canonical integer that reduces the real part of `τ` modulo `2`. -/
def horizontalLevelTwoIndex (τ : ℂ) : ℤ :=
  round (τ.re / 2)

/-- Subtract the corresponding horizontal level-two period. -/
def horizontalLevelTwoReduce (τ : ℂ) : ℂ :=
  τ - 2 * (horizontalLevelTwoIndex τ : ℂ)

/-- The nearest-integer error before rescaling by the period `2`. -/
theorem abs_sub_horizontalLevelTwoIndex_le_half
    (τ : ℂ) :
    |τ.re / 2 - (horizontalLevelTwoIndex τ : ℝ)| ≤
      (1 : ℝ) / 2 := by
  simpa only [horizontalLevelTwoIndex] using
    abs_sub_round (τ.re / 2)

@[simp]
theorem horizontalLevelTwoReduce_re (τ : ℂ) :
    (horizontalLevelTwoReduce τ).re =
      τ.re -
        2 * (horizontalLevelTwoIndex τ : ℝ) := by
  simp [horizontalLevelTwoReduce]

@[simp]
theorem horizontalLevelTwoReduce_im (τ : ℂ) :
    (horizontalLevelTwoReduce τ).im = τ.im := by
  simp [horizontalLevelTwoReduce]

/-- Reconstruction of the original parameter from its reduced
representative and canonical index. -/
theorem horizontalLevelTwoReduce_add_period (τ : ℂ) :
    horizontalLevelTwoReduce τ +
        2 * (horizontalLevelTwoIndex τ : ℂ) =
      τ := by
  unfold horizontalLevelTwoReduce
  ring

/-- The canonical representative has real part in `[-1,1]`. -/
theorem abs_horizontalLevelTwoReduce_re_le_one
    (τ : ℂ) :
    |(horizontalLevelTwoReduce τ).re| ≤ 1 := by
  have h :=
    abs_sub_horizontalLevelTwoIndex_le_half τ
  rw [horizontalLevelTwoReduce_re]
  have heq :
      τ.re -
          2 * (horizontalLevelTwoIndex τ : ℝ) =
        2 *
          (τ.re / 2 -
            (horizontalLevelTwoIndex τ : ℝ)) := by
    ring
  rw [heq, abs_mul, abs_of_nonneg
    (show (0 : ℝ) ≤ 2 by norm_num)]
  nlinarith

/-- Upper-half-plane version of the canonical reduction. -/
def horizontalLevelTwoReduceUpperHalfPlane
    (τ : ℍ) : ℍ :=
  ⟨horizontalLevelTwoReduce (τ : ℂ), by
    rw [horizontalLevelTwoReduce_im]
    exact τ.im_pos⟩

@[simp]
theorem coe_horizontalLevelTwoReduceUpperHalfPlane
    (τ : ℍ) :
    (horizontalLevelTwoReduceUpperHalfPlane τ : ℂ) =
      horizontalLevelTwoReduce (τ : ℂ) :=
  rfl

@[simp]
theorem horizontalLevelTwoReduceUpperHalfPlane_re
    (τ : ℍ) :
    (horizontalLevelTwoReduceUpperHalfPlane τ).re =
      τ.re -
        2 *
          (horizontalLevelTwoIndex (τ : ℂ) : ℝ) := by
  exact horizontalLevelTwoReduce_re (τ : ℂ)

@[simp]
theorem horizontalLevelTwoReduceUpperHalfPlane_im
    (τ : ℍ) :
    (horizontalLevelTwoReduceUpperHalfPlane τ).im =
      τ.im := by
  exact horizontalLevelTwoReduce_im (τ : ℂ)

theorem abs_horizontalLevelTwoReduceUpperHalfPlane_re_le_one
    (τ : ℍ) :
    |(horizontalLevelTwoReduceUpperHalfPlane τ).re| ≤
      1 := by
  exact abs_horizontalLevelTwoReduce_re_le_one
    (τ : ℂ)

/-- Complex parameters with positive imaginary part have a canonical
representative in the horizontal level-two strip. -/
theorem exists_horizontal_levelTwo_reduction
    (τ : ℂ) :
    ∃ k : ℤ, ∃ τred : ℂ,
      τ = τred + 2 * (k : ℂ) ∧
      |τred.re| ≤ 1 ∧
      τred.im = τ.im := by
  refine
    ⟨horizontalLevelTwoIndex τ,
      horizontalLevelTwoReduce τ, ?_, ?_,
      horizontalLevelTwoReduce_im τ⟩
  · exact (horizontalLevelTwoReduce_add_period τ).symm
  · exact abs_horizontalLevelTwoReduce_re_le_one τ

/-- Re-expressing a doubled-period lattice point after translating `τ`
only changes the horizontal lattice index.  This is the algebraic
compatibility needed by escape arguments. -/
theorem levelTwo_lattice_rebase_horizontal
    (z τ : ℂ) (m n k : ℤ) :
    z + 2 * (m : ℂ) +
          2 * (n : ℂ) *
            (τ + 2 * (k : ℂ)) =
      z + 2 * (m + 2 * n * k : ℤ) +
          2 * (n : ℂ) * τ := by
  push_cast
  ring

/-! ## Norm and lower-bound transport -/

/-- Reducing the modular parameter horizontally leaves the vector norm
unchanged, at the same elliptic coordinate `z`. -/
theorem norm_jacobiThetaVector_horizontalLevelTwoReduce
    (z τ : ℂ) :
    ‖jacobiThetaVector z τ‖ =
      ‖jacobiThetaVector z
        (horizontalLevelTwoReduce τ)‖ := by
  have h :=
    norm_jacobiThetaVector_tau_add_two_int
      z (horizontalLevelTwoReduce τ)
        (horizontalLevelTwoIndex τ)
  rwa [horizontalLevelTwoReduce_add_period] at h

/-- Upper-half-plane form of norm preservation. -/
theorem norm_jacobiThetaVector_horizontalLevelTwoReduceUpperHalfPlane
    (z : ℂ) (τ : ℍ) :
    ‖jacobiThetaVector z (τ : ℂ)‖ =
      ‖jacobiThetaVector z
        (horizontalLevelTwoReduceUpperHalfPlane τ : ℂ)‖ := by
  exact
    norm_jacobiThetaVector_horizontalLevelTwoReduce
      z (τ : ℂ)

/-- Any numerical lower bound transports in both directions. -/
theorem le_norm_jacobiThetaVector_horizontalLevelTwoReduce_iff
    (c : ℝ) (z τ : ℂ) :
    c ≤ ‖jacobiThetaVector z τ‖ ↔
      c ≤
        ‖jacobiThetaVector z
          (horizontalLevelTwoReduce τ)‖ := by
  rw [norm_jacobiThetaVector_horizontalLevelTwoReduce]

/-- A single positive lower bound works at every real part of `τ` on a
fixed-height strip, once `z` has been reduced.  This removes the
horizontal modular-reduction hypothesis from applications of the compact
reduced-domain estimate. -/
theorem exists_uniform_pos_le_norm_jacobiThetaVector_fixed_height
    (γ : ℝ) (hγ : 0 < γ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ z : ℂ, ∀ τ : ℍ,
        |z.re| ≤ 1 →
        |z.im| ≤ γ →
        τ.im = γ →
        c ≤ ‖jacobiThetaVector z (τ : ℂ)‖ := by
  obtain ⟨c, hc, hred⟩ :=
    exists_uniform_pos_le_norm_jacobiThetaVector_reduced_global
      γ hγ
  refine ⟨c, hc, ?_⟩
  intro z τ hzre hzim hτim
  have hbound :
      c ≤
        ‖jacobiThetaVector z
          (horizontalLevelTwoReduceUpperHalfPlane τ :
            ℂ)‖ := by
    exact hred z
      (horizontalLevelTwoReduceUpperHalfPlane τ)
      hzre hzim
      (abs_horizontalLevelTwoReduceUpperHalfPlane_re_le_one τ)
      (by
        rw [horizontalLevelTwoReduceUpperHalfPlane_im]
        exact hτim)
  rwa [
    norm_jacobiThetaVector_horizontalLevelTwoReduceUpperHalfPlane]

end

end HGAS.Modular
