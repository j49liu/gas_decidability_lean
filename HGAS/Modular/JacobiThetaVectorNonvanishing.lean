import HGAS.Modular.JacobiThetaVector
import Mathlib.NumberTheory.Modular
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Nonvanishing of the four-coordinate Jacobi theta vector

This file develops an elementary, product-free proof that the four standard
Jacobi theta functions have no common zero.  The quantitative core is a
large-imaginary-part estimate.  If

```
             Im τ ≥ 4/5,       |Im z| ≤ Im τ / 4,
```

then the `n = 0` term in `θ₃(z|τ)` strictly dominates all remaining terms.
Indeed the two tails are bounded by a geometric series with ratio
`exp (-6/5) < 1/3`.

The global argument transports a hypothetical common zero by the modular
generators `S,T`, moves `τ` to the standard fundamental domain, and then
uses one of the two imaginary half-characteristics to center `Im z`.
Unlike the classical proof via the Jacobi triple product, this route uses
only the theta series, Poisson summation (already present in Mathlib), and
the standard modular fundamental-domain reduction.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I
open Complex Real ModularGroup Filter Topology
open scoped MatrixGroups Topology

noncomputable section

/-- The geometric ratio used in the theta-tail estimate. -/
def thetaTailRatio : ℝ := Real.exp (-(6 / 5 : ℝ))

/-- A convenient explicit numerical estimate, proved from the first four
nonnegative terms of the exponential series. -/
theorem thetaTailRatio_lt_one_third :
    thetaTailRatio < 1 / 3 := by
  have hseries :=
    Real.sum_le_exp_of_nonneg
      (show (0 : ℝ) ≤ 6 / 5 by norm_num) 4
  have hexp : (3 : ℝ) < Real.exp (6 / 5) := by
    norm_num [Finset.sum_range_succ] at hseries ⊢
    linarith
  have hmul :=
    mul_lt_mul_of_pos_right hexp
      (Real.exp_pos (-(6 / 5 : ℝ)))
  have hone :
      Real.exp (6 / 5) *
          Real.exp (-(6 / 5 : ℝ)) =
        1 := by
    rw [← Real.exp_add]
    norm_num
  rw [hone] at hmul
  unfold thetaTailRatio
  rw [lt_div_iff₀ (show (0 : ℝ) < 3 by norm_num)]
  nlinarith

theorem thetaTailRatio_nonneg :
    0 ≤ thetaTailRatio :=
  (Real.exp_pos _).le

theorem thetaTailRatio_lt_one :
    thetaTailRatio < 1 :=
  thetaTailRatio_lt_one_third.trans (by norm_num)

/-- Every nonconstant theta summand is bounded by the geometric majorant
used below. -/
theorem norm_jacobiTheta₂_term_le_thetaTailRatio_pow
    {z τ : ℂ}
    (hy : 4 / 5 ≤ τ.im)
    (hz : |z.im| ≤ τ.im / 4)
    {k : ℤ} (hk : k ≠ 0) :
    ‖jacobiTheta₂_term k z τ‖ ≤
      thetaTailRatio ^ k.natAbs := by
  have hypos : 0 < τ.im :=
    (show (0 : ℝ) < 4 / 5 by norm_num).trans_le hy
  have hkabs : (1 : ℝ) ≤ |(k : ℝ)| := by
    rw [← Int.cast_abs, ← Int.cast_one, Int.cast_le]
    exact Int.one_le_abs hk
  have hterm :=
    norm_jacobiTheta₂_term_le
      hypos hz le_rfl k
  have hterm' :
      ‖jacobiTheta₂_term k z τ‖ ≤
        Real.exp
          (-π *
            (τ.im * (k : ℝ) ^ 2 -
              2 * (τ.im / 4) * |(k : ℝ)|)) := by
    simpa only [Int.cast_abs] using hterm
  apply hterm'.trans
  unfold thetaTailRatio
  rw [← Real.exp_nat_mul]
  rw [Real.exp_le_exp]
  have habs_nat :
      ((k.natAbs : ℕ) : ℝ) = |(k : ℝ)| := by
    simp only [Nat.cast_natAbs, Int.cast_abs]
  rw [habs_nat]
  have hpi_y :
      (12 / 5 : ℝ) ≤ π * τ.im := by
    nlinarith [pi_gt_three]
  have hsq :
      |(k : ℝ)| ≤ (k : ℝ) ^ 2 := by
    have hmul :=
      mul_nonneg
        (sub_nonneg.mpr hkabs)
        (abs_nonneg (k : ℝ))
    nlinarith [sq_abs (k : ℝ)]
  have hy_nonneg : 0 ≤ τ.im := hypos.le
  have habs_nonneg : 0 ≤ |(k : ℝ)| := abs_nonneg _
  have hcore :
      (6 / 5 : ℝ) * |(k : ℝ)| ≤
        π *
          (τ.im * (k : ℝ) ^ 2 -
            2 * (τ.im / 4) * |(k : ℝ)|) := by
    have hhalf :
        |(k : ℝ)| / 2 ≤
          (k : ℝ) ^ 2 -
            |(k : ℝ)| / 2 := by
      nlinarith
    calc
      (6 / 5 : ℝ) * |(k : ℝ)| =
          (12 / 5 : ℝ) * (|(k : ℝ)| / 2) := by ring
      _ ≤ (π * τ.im) * (|(k : ℝ)| / 2) :=
        mul_le_mul_of_nonneg_right hpi_y
          (by positivity)
      _ ≤ (π * τ.im) *
          ((k : ℝ) ^ 2 -
            |(k : ℝ)| / 2) :=
        mul_le_mul_of_nonneg_left hhalf
          (mul_nonneg pi_pos.le hy_nonneg)
      _ = π *
          (τ.im * (k : ℝ) ^ 2 -
            2 * (τ.im / 4) * |(k : ℝ)|) := by
        ring
  nlinarith

/-- In the central imaginary half-strip and above height `4/5`, the
constant term strictly dominates both nonconstant tails. -/
theorem norm_jacobiTheta₂_sub_one_lt_one
    {z τ : ℂ}
    (hy : 4 / 5 ≤ τ.im)
    (hz : |z.im| ≤ τ.im / 4) :
    ‖jacobiTheta₂ z τ - 1‖ < 1 := by
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
            (-(n + 1 : ℤ)) z τ) := by
    exact hsneg
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
  have htwo :
      2 * (thetaTailRatio *
          (1 - thetaTailRatio)⁻¹) < 1 := by
    have hden :
        0 < 1 - thetaTailRatio :=
      sub_pos.mpr thetaTailRatio_lt_one
    have hdiv :
        (2 * thetaTailRatio) /
            (1 - thetaTailRatio) < 1 := by
      rw [div_lt_iff₀ hden]
      nlinarith [thetaTailRatio_lt_one_third]
    have heq :
        2 * (thetaTailRatio *
            (1 - thetaTailRatio)⁻¹) =
          (2 * thetaTailRatio) /
            (1 - thetaTailRatio) := by
      rw [div_eq_mul_inv]
      ring
    rw [heq]
    exact hdiv
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
    _ < 1 := by
      rw [hratio]
      exact htwo

/-- Quantitative nonvanishing of `θ₃` in the central half-strip. -/
theorem jacobiTheta₂_ne_zero_of_im_large_of_im_centered
    {z τ : ℂ}
    (hy : 4 / 5 ≤ τ.im)
    (hz : |z.im| ≤ τ.im / 4) :
    jacobiTheta₂ z τ ≠ 0 := by
  intro hzero
  have h :=
    norm_jacobiTheta₂_sub_one_lt_one hy hz
  rw [hzero, zero_sub, norm_neg, norm_one] at h
  exact (lt_irrefl 1 h)

/-- By shifting by an integral imaginary half-period, every point can be
placed in the central imaginary half-strip. -/
theorem exists_int_half_tau_shift_im_centered
    (z τ : ℂ) (hy : 0 < τ.im) :
    ∃ n : ℤ,
      |(z + ((n : ℂ) / 2) * τ).im| ≤
        τ.im / 4 := by
  let x : ℝ := -2 * z.im / τ.im
  let n : ℤ := round x
  have hround :
      |x - (n : ℝ)| ≤ 1 / 2 :=
    abs_sub_round x
  refine ⟨n, ?_⟩
  have hcoef_re :
      (((n : ℂ) / 2)).re = (n : ℝ) / 2 := by
    norm_num
  have hcoef_im :
      (((n : ℂ) / 2)).im = 0 := by
    norm_num
  have him :
      (z + ((n : ℂ) / 2) * τ).im =
        τ.im / 2 * ((n : ℝ) - x) := by
    rw [add_im, mul_im, hcoef_re, hcoef_im,
      zero_mul, add_zero]
    dsimp only [x]
    field_simp [hy.ne']
    ring
  rw [him, abs_mul,
    abs_of_pos (half_pos hy), abs_sub_comm]
  calc
    τ.im / 2 * |x - (n : ℝ)| ≤
        τ.im / 2 * (1 / 2) :=
      mul_le_mul_of_nonneg_left hround
        (half_pos hy).le
    _ = τ.im / 4 := by ring

/-- Above height `4/5`, the four theta coordinates cannot vanish
simultaneously.  Only `θ₂` and `θ₃` are needed: one of their imaginary
half-period translates lies in the dominance strip. -/
theorem jacobiThetaVector_ne_zero_of_im_ge
    (z τ : ℂ) (hy : 4 / 5 ≤ τ.im) :
    jacobiThetaVector z τ ≠ 0 := by
  intro hzero
  have hθ2 :
      jacobiTheta2 z τ = 0 := by
    have h := congrFun hzero 1
    simpa [jacobiThetaVector] using h
  have hθ3 :
      jacobiTheta3 z τ = 0 := by
    have h := congrFun hzero 2
    simpa [jacobiThetaVector] using h
  have hypos : 0 < τ.im :=
    (show (0 : ℝ) < 4 / 5 by norm_num).trans_le hy
  obtain ⟨n, hncenter⟩ :=
    exists_int_half_tau_shift_im_centered z τ hypos
  rcases Int.even_or_odd' n with ⟨k, hk | hk⟩
  · subst n
    let w : ℂ :=
      z + (((2 * k : ℤ) : ℂ) / 2) * τ
    have hwcenter :
        |w.im| ≤ τ.im / 4 :=
      hncenter
    have hwzero :
        jacobiTheta₂ w τ = 0 := by
      have hshift :=
        jacobiTheta₂_add_int_lattice
          z τ 0 k
      have hbase :
          jacobiTheta₂ z τ = 0 := by
        exact hθ3
      rw [hbase, mul_zero] at hshift
      have harg :
          w =
            z + (0 : ℂ) + (k : ℂ) * τ := by
        simp only [w]
        push_cast
        ring
      rw [harg]
      simpa using hshift
    exact
      (jacobiTheta₂_ne_zero_of_im_large_of_im_centered
        hy hwcenter) hwzero
  · subst n
    let zhalf : ℂ := z + τ / 2
    have hzhalf_zero :
        jacobiTheta₂ zhalf τ = 0 := by
      unfold jacobiTheta2 at hθ2
      have hfactor :
          cexp (π * I * (τ / 4 + z)) ≠ 0 :=
        Complex.exp_ne_zero _
      exact (mul_eq_zero.mp hθ2).resolve_left hfactor
    let w : ℂ :=
      z + (((2 * k + 1 : ℤ) : ℂ) / 2) * τ
    have hwcenter :
        |w.im| ≤ τ.im / 4 :=
      hncenter
    have hwzero :
        jacobiTheta₂ w τ = 0 := by
      have hshift :=
        jacobiTheta₂_add_int_lattice
          zhalf τ 0 k
      rw [hzhalf_zero, mul_zero] at hshift
      have harg :
          w =
            zhalf + (0 : ℂ) +
              (k : ℂ) * τ := by
        simp only [w, zhalf]
        push_cast
        ring
      rw [harg]
      simpa using hshift
    exact
      (jacobiTheta₂_ne_zero_of_im_large_of_im_centered
        hy hwcenter) hwzero

/-- The four theta coordinates have no common zero when the modular
parameter lies in the closed standard fundamental domain. -/
theorem jacobiThetaVector_ne_zero_of_mem_fd
    (z : ℂ) (τ : ℍ)
    (hτ : τ ∈ ModularGroup.fd) :
    jacobiThetaVector z τ ≠ 0 := by
  apply jacobiThetaVector_ne_zero_of_im_ge
  change (4 / 5 : ℝ) ≤ τ.im
  have hsq :=
    ModularGroup.three_le_four_mul_im_sq_of_mem_fd hτ
  have him := τ.im_pos
  by_contra hnot
  have hlt : τ.im < 4 / 5 :=
    lt_of_not_ge hnot
  have hsqlt :
      τ.im ^ 2 < (4 / 5 : ℝ) ^ 2 :=
    (sq_lt_sq₀ him.le (by norm_num)).2 hlt
  nlinarith

/-! ## Transport of common zeros by the modular generators -/

/-- Under `τ ↦ τ+1`, Mathlib's `θ₃` becomes `θ₄`. -/
theorem jacobiTheta₂_tau_add_one
    (z τ : ℂ) :
    jacobiTheta₂ z (τ + 1) =
      jacobiTheta₂ (z + 1 / 2) τ := by
  unfold jacobiTheta₂
  apply tsum_congr
  intro n
  unfold jacobiTheta₂_term
  rw [Complex.exp_eq_exp_iff_exists_int]
  obtain ⟨k, hk⟩ :=
    Int.even_mul_succ_self (n - 1)
  refine ⟨k, ?_⟩
  have hk' :
      (n - 1) * n = 2 * k := by
    simpa [two_mul] using hk
  have hkC :
      ((n : ℂ) - 1) * (n : ℂ) =
        2 * (k : ℂ) := by
    exact_mod_cast hk'
  linear_combination (π * I) * hkC

/-- The `T` transformation of `θ₃`. -/
theorem jacobiTheta3_tau_add_one
    (z τ : ℂ) :
    jacobiTheta3 z (τ + 1) =
      jacobiTheta4 z τ := by
  exact jacobiTheta₂_tau_add_one z τ

/-- The `T` transformation of `θ₄`. -/
theorem jacobiTheta4_tau_add_one
    (z τ : ℂ) :
    jacobiTheta4 z (τ + 1) =
      jacobiTheta3 z τ := by
  rw [jacobiTheta4, jacobiTheta3,
    jacobiTheta₂_tau_add_one]
  convert jacobiTheta₂_add_left z τ using 1
  ring_nf

/-- The common eighth-root multiplier of `θ₁,θ₂` under `T`. -/
def thetaTMultiplier : ℂ :=
  cexp (π * I / 4)

theorem thetaTMultiplier_ne_zero :
    thetaTMultiplier ≠ 0 :=
  Complex.exp_ne_zero _

/-- The `T` transformation of `θ₂`. -/
theorem jacobiTheta2_tau_add_one
    (z τ : ℂ) :
    jacobiTheta2 z (τ + 1) =
      thetaTMultiplier * jacobiTheta2 z τ := by
  unfold jacobiTheta2 thetaTMultiplier
  rw [jacobiTheta₂_tau_add_one]
  have harg :
      z + (τ + 1) / 2 + 1 / 2 =
        (z + τ / 2) + 1 := by
    ring
  rw [harg, jacobiTheta₂_add_left]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- The `T` transformation of `θ₁`. -/
theorem jacobiTheta1_tau_add_one
    (z τ : ℂ) :
    jacobiTheta1 z (τ + 1) =
      thetaTMultiplier * jacobiTheta1 z τ := by
  unfold jacobiTheta1
  rw [jacobiTheta2_tau_add_one]
  ring

/-- A common zero is carried forward by the modular translation `T`. -/
theorem jacobiThetaVector_commonZero_T_forward
    {z τ : ℂ}
    (hzero : jacobiThetaVector z τ = 0) :
    jacobiThetaVector z (τ + 1) = 0 := by
  funext j
  fin_cases j
  · change jacobiTheta1 z (τ + 1) = 0
    rw [jacobiTheta1_tau_add_one]
    have h := congrFun hzero 0
    simpa [jacobiThetaVector] using
      congrArg (thetaTMultiplier * ·) h
  · change jacobiTheta2 z (τ + 1) = 0
    rw [jacobiTheta2_tau_add_one]
    have h := congrFun hzero 1
    simpa [jacobiThetaVector] using
      congrArg (thetaTMultiplier * ·) h
  · change jacobiTheta3 z (τ + 1) = 0
    rw [jacobiTheta3_tau_add_one]
    have h := congrFun hzero 3
    simpa [jacobiThetaVector] using h
  · change jacobiTheta4 z (τ + 1) = 0
    rw [jacobiTheta4_tau_add_one]
    have h := congrFun hzero 2
    simpa [jacobiThetaVector] using h

/-- Common-zero existence is invariant under `T`. -/
theorem exists_jacobiThetaVector_commonZero_tau_add_one
    (τ : ℂ) :
    (∃ z : ℂ, jacobiThetaVector z (τ + 1) = 0) ↔
      ∃ z : ℂ, jacobiThetaVector z τ = 0 := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    funext j
    fin_cases j
    · change jacobiTheta1 z τ = 0
      have h := congrFun hz 0
      change jacobiTheta1 z (τ + 1) = 0 at h
      rw [jacobiTheta1_tau_add_one] at h
      exact
        (mul_eq_zero.mp h).resolve_left
          thetaTMultiplier_ne_zero
    · change jacobiTheta2 z τ = 0
      have h := congrFun hz 1
      change jacobiTheta2 z (τ + 1) = 0 at h
      rw [jacobiTheta2_tau_add_one] at h
      exact
        (mul_eq_zero.mp h).resolve_left
          thetaTMultiplier_ne_zero
    · change jacobiTheta3 z τ = 0
      have h := congrFun hz 3
      change jacobiTheta4 z (τ + 1) = 0 at h
      rw [jacobiTheta4_tau_add_one] at h
      exact h
    · change jacobiTheta4 z τ = 0
      have h := congrFun hz 2
      change jacobiTheta3 z (τ + 1) = 0 at h
      rw [jacobiTheta3_tau_add_one] at h
      exact h
  · rintro ⟨z, hz⟩
    exact ⟨z,
      jacobiThetaVector_commonZero_T_forward hz⟩

/-! ### Inversion -/

/-- The nowhere-zero scalar in the Poisson-summation formula for
`θ₃`.  Giving it a name makes the common-zero transport independent of
the particular normalization of the other three theta coordinates. -/
def jacobiThetaSFactor (z τ : ℂ) : ℂ :=
  1 / (-I * τ) ^ (1 / 2 : ℂ) *
    cexp (-π * I * z ^ 2 / τ)

theorem jacobiThetaSFactor_ne_zero
    {τ : ℂ} (hτ : τ ≠ 0) (z : ℂ) :
    jacobiThetaSFactor z τ ≠ 0 := by
  unfold jacobiThetaSFactor
  apply mul_ne_zero
  · exact div_ne_zero one_ne_zero <|
      Complex.cpow_ne_zero_iff.mpr <|
        Or.inl (mul_ne_zero
          (neg_ne_zero.mpr I_ne_zero) hτ)
  · exact Complex.exp_ne_zero _

/-- A zero of `θ₃` is carried through the inversion formula. -/
theorem jacobiTheta3_zero_S_forward
    {z τ : ℂ} (hτ : τ ≠ 0)
    (hz : jacobiTheta3 z τ = 0) :
    jacobiTheta3 (z / τ) (-1 / τ) = 0 := by
  have hfunctional :=
    jacobiTheta₂_functional_equation z τ
  change jacobiTheta₂ z τ = 0 at hz
  rw [hz] at hfunctional
  have hproduct :
      jacobiThetaSFactor z τ *
          jacobiTheta₂ (z / τ) (-1 / τ) =
        0 := by
    simpa only [jacobiThetaSFactor] using
      hfunctional.symm
  change jacobiTheta₂ (z / τ) (-1 / τ) = 0
  exact
    (mul_eq_zero.mp hproduct).resolve_left
      (jacobiThetaSFactor_ne_zero hτ z)

/-- A simultaneous zero of all four theta coordinates is carried by
`(z,τ) ↦ (z/τ,-1/τ)`.  The proof exposes the geometric reason for the
permutation of characteristics: the four half-periods
`0, 1/2, τ/2, (1+τ)/2` are permuted modulo the new period lattice. -/
theorem jacobiThetaVector_commonZero_S_forward
    {z τ : ℂ} (hτ : τ ≠ 0)
    (hzero : jacobiThetaVector z τ = 0) :
    jacobiThetaVector (z / τ) (-1 / τ) = 0 := by
  have hz :
      jacobiTheta₂ z τ = 0 := by
    have h := congrFun hzero 2
    simpa [jacobiThetaVector, jacobiTheta3] using h
  have hzR :
      jacobiTheta₂ (z + 1 / 2) τ = 0 := by
    have h := congrFun hzero 3
    simpa [jacobiThetaVector, jacobiTheta4] using h
  have hzI :
      jacobiTheta₂ (z + τ / 2) τ = 0 := by
    have h := congrFun hzero 1
    change jacobiTheta2 z τ = 0 at h
    unfold jacobiTheta2 at h
    exact
      (mul_eq_zero.mp h).resolve_left
        (Complex.exp_ne_zero _)
  have hzRI :
      jacobiTheta₂ ((z + 1 / 2) + τ / 2) τ =
        0 := by
    have h := congrFun hzero 0
    change jacobiTheta1 z τ = 0 at h
    unfold jacobiTheta1 at h
    have h2 :
        jacobiTheta2 (z + 1 / 2) τ = 0 :=
      neg_eq_zero.mp h
    unfold jacobiTheta2 at h2
    exact
      (mul_eq_zero.mp h2).resolve_left
        (Complex.exp_ne_zero _)
  let w : ℂ := z / τ
  let τ' : ℂ := -1 / τ
  have hw :
      jacobiTheta₂ w τ' = 0 := by
    simpa only [jacobiTheta3, w, τ'] using
      jacobiTheta3_zero_S_forward hτ
        (show jacobiTheta3 z τ = 0 by
          exact hz)
  have hw_minus_I :
      jacobiTheta₂ (w - τ' / 2) τ' = 0 := by
    have h :=
      jacobiTheta3_zero_S_forward hτ
        (show jacobiTheta3 (z + 1 / 2) τ = 0 by
          exact hzR)
    change
      jacobiTheta₂ ((z + 1 / 2) / τ) τ' = 0
        at h
    have harg :
        (z + 1 / 2) / τ = w - τ' / 2 := by
      dsimp only [w, τ']
      field_simp [hτ]
      ring
    rwa [harg] at h
  have hw_R :
      jacobiTheta₂ (w + 1 / 2) τ' = 0 := by
    have h :=
      jacobiTheta3_zero_S_forward hτ
        (show
          jacobiTheta3 (z + τ / 2) τ = 0 by
            exact hzI)
    change
      jacobiTheta₂ ((z + τ / 2) / τ) τ' = 0
        at h
    have harg :
        (z + τ / 2) / τ = w + 1 / 2 := by
      dsimp only [w]
      field_simp [hτ]
    rwa [harg] at h
  have hw_R_minus_I :
      jacobiTheta₂
          (w + 1 / 2 - τ' / 2) τ' =
        0 := by
    have h :=
      jacobiTheta3_zero_S_forward hτ
        (show
          jacobiTheta3
              ((z + 1 / 2) + τ / 2) τ =
            0 by
          exact hzRI)
    change
      jacobiTheta₂
          (((z + 1 / 2) + τ / 2) / τ) τ' =
        0 at h
    have harg :
        ((z + 1 / 2) + τ / 2) / τ =
          w + 1 / 2 - τ' / 2 := by
      dsimp only [w, τ']
      field_simp [hτ]
      ring
    rwa [harg] at h
  have hw_I :
      jacobiTheta₂ (w + τ' / 2) τ' = 0 := by
    calc
      jacobiTheta₂ (w + τ' / 2) τ' =
          jacobiTheta₂
            ((w - τ' / 2) + τ') τ' := by
              congr 1
              ring
      _ =
          cexp
              (-π * I *
                (τ' + 2 * (w - τ' / 2))) *
            jacobiTheta₂ (w - τ' / 2) τ' :=
        jacobiTheta₂_add_left' _ _
      _ = 0 := by rw [hw_minus_I, mul_zero]
  have hw_RI :
      jacobiTheta₂
          ((w + 1 / 2) + τ' / 2) τ' =
        0 := by
    calc
      jacobiTheta₂
          ((w + 1 / 2) + τ' / 2) τ' =
          jacobiTheta₂
            ((w + 1 / 2 - τ' / 2) + τ') τ' := by
              congr 1
              ring
      _ =
          cexp
              (-π * I *
                (τ' +
                  2 * (w + 1 / 2 - τ' / 2))) *
            jacobiTheta₂
              (w + 1 / 2 - τ' / 2) τ' :=
        jacobiTheta₂_add_left' _ _
      _ = 0 := by rw [hw_R_minus_I, mul_zero]
  funext j
  fin_cases j
  · change jacobiTheta1 w τ' = 0
    simp only [jacobiTheta1, jacobiTheta2,
      hw_RI, mul_zero, neg_zero]
  · change jacobiTheta2 w τ' = 0
    simp only [jacobiTheta2, hw_I, mul_zero]
  · change jacobiTheta3 w τ' = 0
    exact hw
  · change jacobiTheta4 w τ' = 0
    exact hw_R

/-- Common-zero existence is invariant under modular inversion. -/
theorem exists_jacobiThetaVector_commonZero_neg_one_div
    {τ : ℂ} (hτ : τ ≠ 0) :
    (∃ z : ℂ,
        jacobiThetaVector z (-1 / τ) = 0) ↔
      ∃ z : ℂ, jacobiThetaVector z τ = 0 := by
  constructor
  · rintro ⟨z, hz⟩
    have hτ' : -1 / τ ≠ 0 :=
      div_ne_zero
        (neg_ne_zero.mpr one_ne_zero) hτ
    have h :=
      jacobiThetaVector_commonZero_S_forward
        hτ' hz
    have hdouble :
        -1 / (-1 / τ) = τ := by
      field_simp [hτ]
    refine ⟨z / (-1 / τ), ?_⟩
    rwa [hdouble] at h
  · rintro ⟨z, hz⟩
    exact
      ⟨z / τ,
        jacobiThetaVector_commonZero_S_forward
          hτ hz⟩

/-! ### Global modular reduction -/

/-- The modular parameter admits a common zero of all four theta
coordinates.  The final theorem says that this predicate is always
false; isolating it is useful because its modular invariance has no
square-root or multiplier ambiguity. -/
def JacobiThetaVectorHasCommonZero (τ : ℍ) : Prop :=
  ∃ z : ℂ,
    jacobiThetaVector z (τ : ℂ) = 0

theorem jacobiThetaVectorHasCommonZero_T_smul
    (τ : ℍ) :
    JacobiThetaVectorHasCommonZero (T • τ) ↔
      JacobiThetaVectorHasCommonZero τ := by
  unfold JacobiThetaVectorHasCommonZero
  simpa only [UpperHalfPlane.modular_T_smul,
    UpperHalfPlane.coe_vadd, Complex.ofReal_one,
    add_comm] using
      exists_jacobiThetaVector_commonZero_tau_add_one
        (τ : ℂ)

theorem jacobiThetaVectorHasCommonZero_S_smul
    (τ : ℍ) :
    JacobiThetaVectorHasCommonZero (S • τ) ↔
      JacobiThetaVectorHasCommonZero τ := by
  have hτ : (τ : ℂ) ≠ 0 := by
    intro h
    have him :
        (τ : ℂ).im = 0 := by rw [h]; simp
    exact ne_of_gt τ.im_pos him
  unfold JacobiThetaVectorHasCommonZero
  simpa only [UpperHalfPlane.modular_S_smul,
    UpperHalfPlane.coe_mk, inv_neg, neg_div,
    one_div] using
      exists_jacobiThetaVector_commonZero_neg_one_div
        hτ

/-- The subgroup of modular transformations under which common-zero
existence is invariant. -/
def jacobiThetaVectorCommonZeroInvariantSubgroup :
    Subgroup SL(2, ℤ) where
  carrier :=
    {g | ∀ τ : ℍ,
      JacobiThetaVectorHasCommonZero (g • τ) ↔
        JacobiThetaVectorHasCommonZero τ}
  one_mem' := by
    intro τ
    rw [one_smul]
  mul_mem' := by
    intro g h hg hh τ
    simpa only [mul_smul] using
      (hg (h • τ)).trans (hh τ)
  inv_mem' := by
    intro g hg τ
    have h := hg (g⁻¹ • τ)
    simpa only [smul_inv_smul] using h.symm

/-- Common-zero existence is invariant under every integral modular
transformation.  Passing through the predicate avoids ever choosing a
branch of the square root in the weight-one-half multiplier. -/
theorem jacobiThetaVectorHasCommonZero_smul
    (g : SL(2, ℤ)) (τ : ℍ) :
    JacobiThetaVectorHasCommonZero (g • τ) ↔
      JacobiThetaVectorHasCommonZero τ := by
  have hS :
      S ∈
        jacobiThetaVectorCommonZeroInvariantSubgroup := by
    exact jacobiThetaVectorHasCommonZero_S_smul
  have hT :
      T ∈
        jacobiThetaVectorCommonZeroInvariantSubgroup := by
    exact jacobiThetaVectorHasCommonZero_T_smul
  have hle :
      Subgroup.closure ({S, T} : Set SL(2, ℤ)) ≤
        jacobiThetaVectorCommonZeroInvariantSubgroup := by
    apply
      (Subgroup.closure_le
        jacobiThetaVectorCommonZeroInvariantSubgroup).2
    intro a ha
    simp only [Set.mem_insert_iff,
      Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact hS
    · exact hT
  exact hle (by
    rw [SpecialLinearGroup.SL2Z_generators]
    exact Subgroup.mem_top g) τ

/-- **Global no-common-zero theorem.**  At every point of
`ℂ × ℍ`, at least one of `θ₁,θ₂,θ₃,θ₄` is nonzero. -/
theorem jacobiThetaVector_ne_zero
    (z : ℂ) (τ : ℍ) :
    jacobiThetaVector z (τ : ℂ) ≠ 0 := by
  intro hzero
  have hbad :
      JacobiThetaVectorHasCommonZero τ :=
    ⟨z, hzero⟩
  obtain ⟨g, hg⟩ :=
    ModularGroup.exists_smul_mem_fd τ
  have hbad_fd :
      JacobiThetaVectorHasCommonZero (g • τ) :=
    (jacobiThetaVectorHasCommonZero_smul g τ).2
      hbad
  obtain ⟨w, hw⟩ := hbad_fd
  exact
    (jacobiThetaVector_ne_zero_of_mem_fd
      w (g • τ) hg) hw

/-- Complex-parameter form of the global theorem. -/
theorem jacobiThetaVector_ne_zero_of_im_pos
    (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaVector z τ ≠ 0 := by
  let τH : ℍ := ⟨τ, hτ⟩
  exact jacobiThetaVector_ne_zero z τH

/-- On every nonempty compact subset of `ℂ × ℍ`, the norm of the
theta vector has a uniform positive lower bound. -/
theorem exists_uniform_pos_le_norm_jacobiThetaVector_global
    {K : Set (ℂ × ℍ)}
    (hK : IsCompact K)
    (hKne : K.Nonempty) :
    ∃ c : ℝ, 0 < c ∧
      ∀ p ∈ K, c ≤
        ‖jacobiThetaVector p.1 (p.2 : ℂ)‖ := by
  exact
    exists_uniform_pos_le_norm_jacobiThetaVector
      hK hKne
      (fun p _ ↦
        jacobiThetaVector_ne_zero p.1 p.2)

end

end HGAS.Modular
