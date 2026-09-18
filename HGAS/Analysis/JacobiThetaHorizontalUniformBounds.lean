import HGAS.Modular.JacobiThetaVectorNonvanishing
import HGAS.Modular.JacobiThetaInitialRank
import Mathlib.Tactic

/-!
# Uniform bounds for horizontal Jacobi-theta families

The detector uses Jacobi theta functions on horizontal affine lines:
the imaginary parts of both the elliptic and modular arguments stay
fixed, while their real parts may be quasiperiodic.  Compactification
therefore needs bounds which do not depend on those real parts.

This file packages the standard Gaussian majorants already proved in
Mathlib into explicit bounds for the theta series and its first elliptic
derivative.  It also exposes the quantitative central-strip estimate
hidden inside the usual nonvanishing proof.  The latter is what bounds
the reciprocal `1 / theta_3` coordinate uniformly.
-/

noncomputable section

open scoped BigOperators

namespace HGAS.Analysis.JacobiThetaHorizontalUniformBounds

open HGAS
open HGAS.Modular
open Complex Real

/-- Gaussian majorant for a theta summand when `|Im z| ≤ S` and
`T ≤ Im τ`. -/
def thetaMajorant (S T : ℝ) (n : ℤ) : ℝ :=
  Real.exp
    (-Real.pi *
      (T * (n : ℝ) ^ 2 - 2 * S * |(n : ℝ)|))

/-- The corresponding majorant for the first elliptic derivative. -/
def thetaPrimeMajorant (S T : ℝ) (n : ℤ) : ℝ :=
  2 * Real.pi * |(n : ℝ)| * thetaMajorant S T n

/-- Total uniform theta bound on one horizontal strip. -/
def thetaBound (S T : ℝ) : ℝ :=
  ∑' n : ℤ, thetaMajorant S T n

/-- Total uniform first-derivative bound on one horizontal strip. -/
def thetaPrimeBound (S T : ℝ) : ℝ :=
  ∑' n : ℤ, thetaPrimeMajorant S T n

theorem summable_thetaMajorant
    (S : ℝ) {T : ℝ} (hT : 0 < T) :
    Summable (thetaMajorant S T) := by
  apply
    (summable_pow_mul_jacobiTheta₂_term_bound S hT 0).congr
  intro n
  unfold thetaMajorant
  simp only [pow_zero, one_mul]
  rw [Int.cast_abs]

theorem summable_thetaPrimeMajorant
    (S : ℝ) {T : ℝ} (hT : 0 < T) :
    Summable (thetaPrimeMajorant S T) := by
  have h :=
    (summable_pow_mul_jacobiTheta₂_term_bound S hT 1).mul_left
      (2 * Real.pi)
  apply h.congr
  intro n
  unfold thetaPrimeMajorant thetaMajorant
  simp only [pow_one]
  rw [Int.cast_abs]
  ring

theorem thetaMajorant_nonneg
    (S T : ℝ) (n : ℤ) :
    0 ≤ thetaMajorant S T n :=
  (Real.exp_pos _).le

theorem thetaPrimeMajorant_nonneg
    (S T : ℝ) (n : ℤ) :
    0 ≤ thetaPrimeMajorant S T n := by
  unfold thetaPrimeMajorant
  exact mul_nonneg
    (mul_nonneg (by positivity) (abs_nonneg _))
    (thetaMajorant_nonneg S T n)

theorem thetaBound_nonneg
    (S T : ℝ) :
    0 ≤ thetaBound S T :=
  tsum_nonneg (thetaMajorant_nonneg S T)

theorem thetaPrimeBound_nonneg
    (S T : ℝ) :
    0 ≤ thetaPrimeBound S T :=
  tsum_nonneg (thetaPrimeMajorant_nonneg S T)

/-- Uniform norm bound for Mathlib's two-variable theta function. -/
theorem norm_jacobiTheta₂_le_thetaBound
    {S T : ℝ} (hT : 0 < T) {z τ : ℂ}
    (hz : |z.im| ≤ S) (hτ : T ≤ τ.im) :
    ‖jacobiTheta₂ z τ‖ ≤ thetaBound S T := by
  have hτpos : 0 < τ.im := hT.trans_le hτ
  have hterm :
      Summable fun n : ℤ ↦ ‖jacobiTheta₂_term n z τ‖ :=
    ((summable_jacobiTheta₂_term_iff z τ).2 hτpos).norm
  calc
    ‖jacobiTheta₂ z τ‖ =
        ‖∑' n : ℤ, jacobiTheta₂_term n z τ‖ := by
          rw [jacobiTheta₂]
    _ ≤ ∑' n : ℤ, ‖jacobiTheta₂_term n z τ‖ :=
      norm_tsum_le_tsum_norm hterm
    _ ≤ ∑' n : ℤ, thetaMajorant S T n :=
      hterm.tsum_le_tsum
        (fun n ↦ by
          simpa only [thetaMajorant, Int.cast_abs] using
            (norm_jacobiTheta₂_term_le hT hz hτ n))
        (summable_thetaMajorant S hT)
    _ = thetaBound S T := rfl

/-- Uniform norm bound for the first elliptic derivative of Mathlib's
two-variable theta function. -/
theorem norm_jacobiTheta₂'_le_thetaPrimeBound
    {S T : ℝ} (hT : 0 < T) {z τ : ℂ}
    (hz : |z.im| ≤ S) (hτ : T ≤ τ.im) :
    ‖jacobiTheta₂' z τ‖ ≤ thetaPrimeBound S T := by
  have hτpos : 0 < τ.im := hT.trans_le hτ
  have hterm :
      Summable fun n : ℤ ↦ ‖jacobiTheta₂'_term n z τ‖ :=
    ((summable_jacobiTheta₂'_term_iff z τ).2 hτpos).norm
  calc
    ‖jacobiTheta₂' z τ‖ =
        ‖∑' n : ℤ, jacobiTheta₂'_term n z τ‖ := by
          rw [jacobiTheta₂']
    _ ≤ ∑' n : ℤ, ‖jacobiTheta₂'_term n z τ‖ :=
      norm_tsum_le_tsum_norm hterm
    _ ≤ ∑' n : ℤ, thetaPrimeMajorant S T n :=
      hterm.tsum_le_tsum
        (fun n ↦ by
          simpa only [thetaPrimeMajorant, thetaMajorant,
            Int.cast_abs] using
            (norm_jacobiTheta₂'_term_le hT hz hτ n))
        (summable_thetaPrimeMajorant S hT)
    _ = thetaPrimeBound S T := rfl

/-! ## An explicit reciprocal bound in the central strip -/

/-- Total geometric bound for the two nonconstant theta tails in the
central strip used by the detector chart. -/
def centralThetaTail : ℝ :=
  2 * (thetaTailRatio * (1 - thetaTailRatio)⁻¹)

/-- Positive distance left between the constant theta term and the two
nonconstant tails. -/
def centralThetaGap : ℝ :=
  1 - centralThetaTail

theorem centralThetaTail_nonneg :
    0 ≤ centralThetaTail := by
  unfold centralThetaTail
  have hden : 0 ≤ (1 - thetaTailRatio)⁻¹ := by
    exact inv_nonneg.mpr (sub_nonneg.mpr thetaTailRatio_lt_one.le)
  exact mul_nonneg (by norm_num)
    (mul_nonneg thetaTailRatio_nonneg hden)

theorem centralThetaTail_lt_one :
    centralThetaTail < 1 := by
  have hden :
      0 < 1 - thetaTailRatio :=
    sub_pos.mpr thetaTailRatio_lt_one
  have hdiv :
      (2 * thetaTailRatio) /
          (1 - thetaTailRatio) < 1 := by
    rw [div_lt_iff₀ hden]
    nlinarith [thetaTailRatio_lt_one_third]
  unfold centralThetaTail
  rw [show
      2 * (thetaTailRatio * (1 - thetaTailRatio)⁻¹) =
        (2 * thetaTailRatio) / (1 - thetaTailRatio) by
      rw [div_eq_mul_inv]
      ring]
  exact hdiv

theorem centralThetaGap_pos :
    0 < centralThetaGap := by
  unfold centralThetaGap
  exact sub_pos.mpr centralThetaTail_lt_one

/-- Quantitative version of the central-strip theta estimate.  The
proof deliberately exposes the same two geometric tails as the
nonvanishing theorem, because compactification needs their common
strict margin rather than only pointwise nonvanishing. -/
theorem norm_jacobiTheta₂_sub_one_le_centralThetaTail
    {z τ : ℂ}
    (hy : 4 / 5 ≤ τ.im)
    (hz : |z.im| ≤ τ.im / 4) :
    ‖jacobiTheta₂ z τ - 1‖ ≤ centralThetaTail := by
  have hypos : 0 < τ.im :=
    (show (0 : ℝ) < 4 / 5 by norm_num).trans_le hy
  have hs :
      Summable (jacobiTheta₂_term · z τ) :=
    (summable_jacobiTheta₂_term_iff z τ).2 hypos
  have hspos :
      Summable
        (fun n : ℕ ↦
          jacobiTheta₂_term (n : ℤ) z τ) :=
    hs.comp_injective Nat.cast_injective
  have hsneg :
      Summable
        (fun n : ℕ ↦
          jacobiTheta₂_term (-(n + 1 : ℤ)) z τ) :=
    hs.comp_injective (by
      intro m n hmn
      have hadd :
          (m : ℤ) + 1 = (n : ℤ) + 1 :=
        neg_inj.mp hmn
      have hcast : (m : ℤ) = (n : ℤ) :=
        add_right_cancel hadd
      exact Int.ofNat_inj.mp hcast)
  have hIntSplit :
      (∑' k : ℤ, jacobiTheta₂_term k z τ) =
        (∑' n : ℕ,
          jacobiTheta₂_term (n : ℤ) z τ) +
        ∑' n : ℕ,
          jacobiTheta₂_term (-(n + 1 : ℤ)) z τ :=
    tsum_of_nat_of_neg_add_one hspos hsneg
  have hPosSplit :
      (∑' n : ℕ,
          jacobiTheta₂_term (n : ℤ) z τ) =
        jacobiTheta₂_term 0 z τ +
          ∑' n : ℕ,
            jacobiTheta₂_term
              ((n + 1 : ℕ) : ℤ) z τ :=
    hspos.tsum_eq_zero_add
  have hsplit :
      jacobiTheta₂ z τ - 1 =
        (∑' n : ℕ,
            jacobiTheta₂_term
              ((n + 1 : ℕ) : ℤ) z τ) +
          (∑' n : ℕ,
            jacobiTheta₂_term
              (-(n + 1 : ℤ)) z τ) := by
    rw [jacobiTheta₂, hIntSplit, hPosSplit]
    have hterm0 :
        jacobiTheta₂_term 0 z τ = 1 := by
      simp [jacobiTheta₂_term]
    rw [hterm0]
    abel
  have hsposTail :
      Summable
        (fun n : ℕ ↦
          jacobiTheta₂_term
            ((n + 1 : ℕ) : ℤ) z τ) :=
    hspos.comp_injective Nat.succ_injective
  have hsnegTail :
      Summable
        (fun n : ℕ ↦
          jacobiTheta₂_term
            (-(n + 1 : ℤ)) z τ) :=
    hsneg
  have hgeom :
      Summable
        (fun n : ℕ ↦
          thetaTailRatio ^ (n + 1)) :=
    (summable_geometric_of_lt_one
      thetaTailRatio_nonneg thetaTailRatio_lt_one).comp_injective
        Nat.succ_injective
  have hpos :
      ‖∑' n : ℕ,
          jacobiTheta₂_term
            ((n + 1 : ℕ) : ℤ) z τ‖ ≤
        ∑' n : ℕ,
          thetaTailRatio ^ (n + 1) := by
    calc
      ‖∑' n : ℕ,
          jacobiTheta₂_term
            ((n + 1 : ℕ) : ℤ) z τ‖ ≤
          ∑' n : ℕ,
            ‖jacobiTheta₂_term
              ((n + 1 : ℕ) : ℤ) z τ‖ :=
        norm_tsum_le_tsum_norm hsposTail.norm
      _ ≤ ∑' n : ℕ,
          thetaTailRatio ^ (n + 1) :=
        hsposTail.norm.tsum_le_tsum
          (fun n ↦ by
            simpa only [Int.natAbs_natCast] using
              (norm_jacobiTheta₂_term_le_thetaTailRatio_pow
                hy hz
                (show ((n + 1 : ℕ) : ℤ) ≠ 0 by omega)))
          hgeom
  have hneg :
      ‖∑' n : ℕ,
          jacobiTheta₂_term
            (-(n + 1 : ℤ)) z τ‖ ≤
        ∑' n : ℕ,
          thetaTailRatio ^ (n + 1) := by
    calc
      ‖∑' n : ℕ,
          jacobiTheta₂_term
            (-(n + 1 : ℤ)) z τ‖ ≤
          ∑' n : ℕ,
            ‖jacobiTheta₂_term
              (-(n + 1 : ℤ)) z τ‖ :=
        norm_tsum_le_tsum_norm hsnegTail.norm
      _ ≤ ∑' n : ℕ,
          thetaTailRatio ^ (n + 1) :=
        hsnegTail.norm.tsum_le_tsum
          (fun n ↦ by
            simpa only [Int.natAbs_neg,
              Int.natAbs_natCast] using
              (norm_jacobiTheta₂_term_le_thetaTailRatio_pow
                hy hz
                (show -(n + 1 : ℤ) ≠ 0 by omega)))
          hgeom
  have hratio :
      ∑' n : ℕ,
          thetaTailRatio ^ (n + 1) =
        thetaTailRatio *
          (1 - thetaTailRatio)⁻¹ := by
    have hrnorm :
        ‖thetaTailRatio‖ < 1 := by
      rw [Real.norm_eq_abs,
        abs_of_nonneg thetaTailRatio_nonneg]
      exact thetaTailRatio_lt_one
    calc
      (∑' n : ℕ,
          thetaTailRatio ^ (n + 1)) =
          thetaTailRatio *
            ∑' n : ℕ, thetaTailRatio ^ n :=
        (geom_series_mul_shift
          thetaTailRatio hrnorm).symm
      _ = thetaTailRatio *
          (1 - thetaTailRatio)⁻¹ := by
        rw [tsum_geometric_of_lt_one
          thetaTailRatio_nonneg thetaTailRatio_lt_one]
  rw [hsplit]
  calc
    ‖(∑' n : ℕ,
          jacobiTheta₂_term
            ((n + 1 : ℕ) : ℤ) z τ) +
        ∑' n : ℕ,
          jacobiTheta₂_term
            (-(n + 1 : ℤ)) z τ‖
        ≤
      ‖∑' n : ℕ,
          jacobiTheta₂_term
            ((n + 1 : ℕ) : ℤ) z τ‖ +
        ‖∑' n : ℕ,
          jacobiTheta₂_term
            (-(n + 1 : ℤ)) z τ‖ :=
      norm_add_le _ _
    _ ≤
      2 *
        (∑' n : ℕ,
          thetaTailRatio ^ (n + 1)) := by
      nlinarith
    _ = centralThetaTail := by
      rw [hratio]
      rfl

/-- Uniform positive lower bound for the centered theta coordinate. -/
theorem centralThetaGap_le_norm_jacobiTheta₂
    {z τ : ℂ}
    (hy : 4 / 5 ≤ τ.im)
    (hz : |z.im| ≤ τ.im / 4) :
    centralThetaGap ≤ ‖jacobiTheta₂ z τ‖ := by
  have htail :=
    norm_jacobiTheta₂_sub_one_le_centralThetaTail hy hz
  have htriangle :
      ‖(1 : ℂ)‖ ≤
        ‖jacobiTheta₂ z τ‖ +
          ‖jacobiTheta₂ z τ - 1‖ := by
    have h :=
      norm_sub_le (jacobiTheta₂ z τ)
        (jacobiTheta₂ z τ - 1)
    simpa only [sub_sub_cancel, norm_one] using h
  have htriangle' :
      (1 : ℝ) ≤
        ‖jacobiTheta₂ z τ‖ +
          ‖jacobiTheta₂ z τ - 1‖ := by
    simpa using htriangle
  unfold centralThetaGap
  linarith

/-- Consequently the reciprocal is bounded by the inverse of the common
central-strip gap. -/
theorem norm_jacobiTheta₂_inv_le_centralThetaGap_inv
    {z τ : ℂ}
    (hy : 4 / 5 ≤ τ.im)
    (hz : |z.im| ≤ τ.im / 4) :
    ‖(jacobiTheta₂ z τ)⁻¹‖ ≤ centralThetaGap⁻¹ := by
  have hlower :=
    centralThetaGap_le_norm_jacobiTheta₂ hy hz
  have hnormpos :
      0 < ‖jacobiTheta₂ z τ‖ :=
    centralThetaGap_pos.trans_le hlower
  rw [norm_inv]
  exact
    (inv_le_inv₀ hnormpos centralThetaGap_pos).2 hlower

end HGAS.Analysis.JacobiThetaHorizontalUniformBounds
