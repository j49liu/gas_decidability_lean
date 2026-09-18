import HGAS.Analysis.ExplicitPolynomialGeometricBudget
import HGAS.Arithmetic.CanonicalFixedDetectorRawOrbitBound
import Mathlib.Tactic

/-!
# A natural-number bound for the canonical raw orbit

The original central-chart estimate is written using convergent theta and
Eisenstein majorant sums.  For an effective many-one reduction we replace
those analytic constants by deliberately coarse natural numbers.

The key elementary estimate is

```text
 thetaMajorant(y,y,n) ≤ 65536 · 2^(-|n|),
```

at the canonical height `y = log(256)/π`.  It follows from
`|n|² - 2|n| ≥ |n| - 2` and the exact identity
`exp(-πy)=1/256`.  The reusable polynomial/geometric budgets then bound
the theta series, its first derivative, and the `E₂` majorant.
-/

noncomputable section

open scoped BigOperators

namespace HGAS.CanonicalRawOrbitEffectiveBudget

open HGAS
open HGAS.Analysis
open HGAS.Analysis.JacobiThetaHorizontalUniformBounds
open HGAS.CanonicalFixedDetectorRawOrbitBound
open HGAS.Modular

/-- Coarse natural bound for the canonical horizontal theta majorant. -/
def thetaNatBudget : ℕ :=
  65536 * halfPolynomialIntBudget 0

/-- Coarse natural bound for its first elliptic derivative majorant. -/
def thetaPrimeNatBudget : ℕ :=
  8 * 65536 * halfPolynomialIntBudget 1

/-- Coarse natural bound for the canonical `E₂` majorant. -/
def e2NatBudget : ℕ :=
  1 + 24 * ((2 : ℕ).factorial * 2 ^ (2 + 1))

/-- Coarse natural bound for `Delta = theta₁'/π`. -/
def deltaNatBudget : ℕ :=
  thetaNatBudget + thetaPrimeNatBudget

/-- Coarse natural bound for every complex linked-block coordinate. -/
def linkedCoordinateNatBudget : ℕ :=
  1 + thetaNatBudget +
    thetaNatBudget ^ 2 +
    thetaNatBudget ^ 4 +
    e2NatBudget +
    deltaNatBudget +
    11

/-- Coarse natural bound for every real raw-state coordinate. -/
def rawCoordinateNatBudget : ℕ :=
  2 + linkedCoordinateNatBudget

/-- Fully effective squared-norm budget for the raw canonical state. -/
def rawNormSqNatBudget (eqs vars : ℕ) : ℕ :=
  FixedDetectorPolynomialCode.dimension eqs vars *
    rawCoordinateNatBudget ^ 2

private theorem abs_intCast_eq_natAbs_cast (n : ℤ) :
    |(n : ℝ)| = (n.natAbs : ℝ) := by
  calc
    |(n : ℝ)| = ((|n| : ℤ) : ℝ) := Int.cast_abs.symm
    _ = ((((n.natAbs : ℕ) : ℤ)) : ℝ) := by
      rw [Int.natCast_natAbs]
    _ = (n.natAbs : ℝ) := by norm_num

private theorem nat_sub_two_quadratic_le (m : ℕ) :
    (m : ℝ) - 2 ≤ (m : ℝ) ^ 2 - 2 * (m : ℝ) := by
  cases m with
  | zero => norm_num
  | succ k =>
      cases k with
      | zero => norm_num
      | succ k =>
          push_cast
          nlinarith [show 0 ≤ (k : ℝ) from Nat.cast_nonneg k]

theorem exp_two_pi_mul_thetaGaugeHeight :
    Real.exp (2 * Real.pi * thetaGaugeHeight) = 65536 := by
  unfold thetaGaugeHeight
  rw [show
      2 * Real.pi * (Real.log 256 / Real.pi) =
        (2 : ℕ) * Real.log 256 by
      push_cast
      field_simp [Real.pi_ne_zero]]
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 256)]
  norm_num

/-- The canonical strip majorant is bounded by a two-sided geometric
sequence with an integer prefactor. -/
theorem thetaMajorant_canonical_le_halfGeometric
    (n : ℤ) :
    thetaMajorant thetaGaugeHeight thetaGaugeHeight n ≤
      65536 * (1 / 2 : ℝ) ^ n.natAbs := by
  let m := n.natAbs
  have habs : |(n : ℝ)| = (m : ℝ) :=
    abs_intCast_eq_natAbs_cast n
  have hsq : (n : ℝ) ^ 2 = (m : ℝ) ^ 2 := by
    calc
      (n : ℝ) ^ 2 = |(n : ℝ)| ^ 2 := by
        rw [sq_abs]
      _ = (m : ℝ) ^ 2 := by rw [habs]
  have hquad :
      (m : ℝ) - 2 ≤
        (n : ℝ) ^ 2 - 2 * |(n : ℝ)| := by
    rw [hsq, habs]
    exact nat_sub_two_quadratic_le m
  have hnegative :
      -Real.pi * thetaGaugeHeight ≤ 0 := by
    nlinarith [
      mul_nonneg Real.pi_pos.le thetaGaugeHeight_pos.le]
  have hexponent :
      -Real.pi *
          (thetaGaugeHeight * (n : ℝ) ^ 2 -
            2 * thetaGaugeHeight * |(n : ℝ)|) ≤
        (m : ℝ) * (-Real.pi * thetaGaugeHeight) +
          2 * Real.pi * thetaGaugeHeight := by
    have hmul :=
      mul_le_mul_of_nonpos_left hquad hnegative
    nlinarith
  calc
    thetaMajorant thetaGaugeHeight thetaGaugeHeight n ≤
        Real.exp
          ((m : ℝ) * (-Real.pi * thetaGaugeHeight) +
            2 * Real.pi * thetaGaugeHeight) := by
      unfold thetaMajorant
      exact Real.exp_le_exp.mpr hexponent
    _ =
        (1 / 256 : ℝ) ^ m * 65536 := by
      rw [Real.exp_add, Real.exp_nat_mul,
        exp_neg_pi_mul_thetaGaugeHeight,
        exp_two_pi_mul_thetaGaugeHeight]
    _ ≤ (1 / 2 : ℝ) ^ m * 65536 := by
      gcongr
      norm_num
    _ = 65536 * (1 / 2 : ℝ) ^ n.natAbs := by
      simp [m, mul_comm]

/-- The analytic theta bound is below the explicit natural budget. -/
theorem canonicalThetaBound_le_thetaNatBudget :
    canonicalThetaBound ≤ (thetaNatBudget : ℕ) := by
  have htheta :
      Summable
        (thetaMajorant thetaGaugeHeight thetaGaugeHeight) :=
    summable_thetaMajorant thetaGaugeHeight thetaGaugeHeight_pos
  have hgeom :
      Summable fun n : ℤ ↦
        65536 * halfPolynomialIntWeight 0 n :=
    (summable_halfPolynomialIntWeight 0).mul_left 65536
  calc
    canonicalThetaBound =
        ∑' n : ℤ,
          thetaMajorant thetaGaugeHeight thetaGaugeHeight n := rfl
    _ ≤
        ∑' n : ℤ,
          65536 * halfPolynomialIntWeight 0 n := by
      exact htheta.tsum_le_tsum
        (fun n ↦ by
          simpa [halfPolynomialIntWeight] using
            thetaMajorant_canonical_le_halfGeometric n)
        hgeom
    _ =
        65536 *
          ∑' n : ℤ, halfPolynomialIntWeight 0 n := by
      exact tsum_mul_left
    _ ≤
        65536 * (halfPolynomialIntBudget 0 : ℝ) := by
      gcongr
      exact tsum_halfPolynomialIntWeight_le 0
    _ = (thetaNatBudget : ℕ) := by
      simp [thetaNatBudget]

/-- Pointwise geometric bound for the first-derivative majorant. -/
theorem thetaPrimeMajorant_canonical_le_halfPolynomial
    (n : ℤ) :
    thetaPrimeMajorant thetaGaugeHeight thetaGaugeHeight n ≤
      8 * 65536 * halfPolynomialIntWeight 1 n := by
  have htheta :=
    thetaMajorant_canonical_le_halfGeometric n
  have hpi : 2 * Real.pi ≤ 8 := by
    nlinarith [Real.pi_le_four]
  have hm : 0 ≤ (n.natAbs : ℝ) :=
    Nat.cast_nonneg _
  unfold thetaPrimeMajorant
  rw [abs_intCast_eq_natAbs_cast]
  calc
    2 * Real.pi * (n.natAbs : ℝ) *
        thetaMajorant thetaGaugeHeight thetaGaugeHeight n ≤
      8 * (n.natAbs : ℝ) *
        (65536 * (1 / 2 : ℝ) ^ n.natAbs) := by
      exact mul_le_mul
        (mul_le_mul hpi le_rfl hm (by norm_num))
        htheta
        (thetaMajorant_nonneg _ _ _)
        (by positivity)
    _ ≤
      8 * 65536 *
        ((1 + (n.natAbs : ℝ)) *
          (1 / 2 : ℝ) ^ n.natAbs) := by
      have hmle :
          (n.natAbs : ℝ) ≤ 1 + (n.natAbs : ℝ) := by
        linarith
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
        n.natAbs]
    _ =
      8 * 65536 * halfPolynomialIntWeight 1 n := by
      simp [halfPolynomialIntWeight]

/-- The analytic first-derivative bound is below its natural budget. -/
theorem canonicalThetaPrimeBound_le_thetaPrimeNatBudget :
    canonicalThetaPrimeBound ≤ (thetaPrimeNatBudget : ℕ) := by
  have htheta :
      Summable
        (thetaPrimeMajorant thetaGaugeHeight thetaGaugeHeight) :=
    summable_thetaPrimeMajorant thetaGaugeHeight thetaGaugeHeight_pos
  have hgeom :
      Summable fun n : ℤ ↦
        (8 * 65536 : ℝ) * halfPolynomialIntWeight 1 n :=
    (summable_halfPolynomialIntWeight 1).mul_left (8 * 65536)
  calc
    canonicalThetaPrimeBound =
        ∑' n : ℤ,
          thetaPrimeMajorant thetaGaugeHeight thetaGaugeHeight n := rfl
    _ ≤
        ∑' n : ℤ,
          (8 * 65536 : ℝ) * halfPolynomialIntWeight 1 n := by
      exact htheta.tsum_le_tsum
        thetaPrimeMajorant_canonical_le_halfPolynomial hgeom
    _ =
        (8 * 65536 : ℝ) *
          ∑' n : ℤ, halfPolynomialIntWeight 1 n := by
      exact tsum_mul_left
    _ ≤
        (8 * 65536 : ℝ) *
          (halfPolynomialIntBudget 1 : ℝ) := by
      gcongr
      exact tsum_halfPolynomialIntWeight_le 1
    _ = (thetaPrimeNatBudget : ℕ) := by
      norm_num [thetaPrimeNatBudget, halfPolynomialIntBudget]

theorem exp_neg_two_pi_le_half :
    Real.exp (-2 * Real.pi) ≤ 1 / 2 := by
  have hexp : (2 : ℝ) ≤ Real.exp (2 * Real.pi) := by
    have hbase := Real.add_one_le_exp (2 * Real.pi)
    nlinarith [Real.pi_gt_three]
  rw [show -2 * Real.pi = -(2 * Real.pi) by ring,
    Real.exp_neg]
  simpa [one_div] using
    (one_div_le_one_div_of_le
      (by norm_num : (0 : ℝ) < 2) hexp)

theorem e2Majorant_le_halfPolynomialNatWeight
    (n : ℕ+) :
    e2Majorant n ≤ halfPolynomialNatWeight 2 n := by
  unfold e2Majorant halfPolynomialNatWeight
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hpow :
      Real.exp (-2 * Real.pi) ^ (n : ℕ) ≤
        (1 / 2 : ℝ) ^ (n : ℕ) :=
    pow_le_pow_left₀ (Real.exp_pos _).le
      exp_neg_two_pi_le_half (n : ℕ)
  exact mul_le_mul
    (by nlinarith)
    hpow
    (pow_nonneg (Real.exp_pos _).le _)
    (by positivity)

theorem tsum_e2Majorant_le_halfPolynomialNatBudget :
    (∑' n : ℕ+, e2Majorant n) ≤
      (((2 : ℕ).factorial * 2 ^ (2 + 1) : ℕ) : ℝ) := by
  have hsub : Summable e2Majorant :=
    summable_e2Majorant
  have hbase : Summable (halfPolynomialNatWeight 2) :=
    summable_halfPolynomialNatWeight 2
  calc
    (∑' n : ℕ+, e2Majorant n) ≤
        ∑' n : ℕ, halfPolynomialNatWeight 2 n := by
      exact
        Summable.tsum_le_tsum_of_inj
          (fun n : ℕ+ ↦ (n : ℕ))
          Subtype.val_injective
          (fun n _ ↦ halfPolynomialNatWeight_nonneg 2 n)
          e2Majorant_le_halfPolynomialNatWeight
          hsub hbase
    _ ≤
        (((2 : ℕ).factorial * 2 ^ (2 + 1) : ℕ) : ℝ) :=
      tsum_halfPolynomialNatWeight_le 2

/-- The analytic `E₂` bound is below its natural budget. -/
theorem canonicalE2Bound_le_e2NatBudget :
    canonicalE2Bound ≤ (e2NatBudget : ℕ) := by
  unfold canonicalE2Bound e2NatBudget
  push_cast
  gcongr
  convert tsum_e2Majorant_le_halfPolynomialNatBudget using 1
  norm_num

/-! ## A rational reciprocal bound for the central theta gap -/

theorem thetaTailRatio_lt_five_sixteenths :
    thetaTailRatio < 5 / 16 := by
  have hseries :=
    Real.sum_le_exp_of_nonneg
      (show (0 : ℝ) ≤ 6 / 5 by norm_num) 4
  have hexp : (16 / 5 : ℝ) < Real.exp (6 / 5) := by
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
  nlinarith

theorem centralThetaTail_le_ten_elevenths :
    centralThetaTail ≤ 10 / 11 := by
  have hr :
      thetaTailRatio ≤ 5 / 16 :=
    thetaTailRatio_lt_five_sixteenths.le
  have hden :
      0 < 1 - thetaTailRatio :=
    sub_pos.mpr thetaTailRatio_lt_one
  unfold centralThetaTail
  rw [show
      2 * (thetaTailRatio * (1 - thetaTailRatio)⁻¹) =
        (2 * thetaTailRatio) / (1 - thetaTailRatio) by
      rw [div_eq_mul_inv]
      ring]
  rw [div_le_iff₀ hden]
  nlinarith

theorem one_eleventh_le_centralThetaGap :
    (1 / 11 : ℝ) ≤ centralThetaGap := by
  unfold centralThetaGap
  linarith [centralThetaTail_le_ten_elevenths]

theorem centralThetaGap_inv_le_eleven :
    centralThetaGap⁻¹ ≤ 11 := by
  have h :=
    (inv_le_inv₀ centralThetaGap_pos
      (by norm_num : (0 : ℝ) < 1 / 11)).2
      one_eleventh_le_centralThetaGap
  norm_num at h ⊢
  exact h

/-! ## Assembly of the natural orbit budget -/

theorem canonicalDeltaBound_le_deltaNatBudget :
    canonicalDeltaBound ≤ (deltaNatBudget : ℕ) := by
  have hpiOne : (1 : ℝ) ≤ Real.pi :=
    by linarith [Real.pi_gt_three]
  have hprimeDiv :
      canonicalThetaPrimeBound / Real.pi ≤
        canonicalThetaPrimeBound := by
    rw [div_le_iff₀ Real.pi_pos]
    exact le_mul_of_one_le_right
      canonicalThetaPrimeBound_nonneg hpiOne
  calc
    canonicalDeltaBound =
        canonicalThetaBound +
          canonicalThetaPrimeBound / Real.pi := by
      unfold canonicalDeltaBound
      field_simp [Real.pi_ne_zero]
    _ ≤
        canonicalThetaBound +
          canonicalThetaPrimeBound :=
      add_le_add_right hprimeDiv canonicalThetaBound
    _ ≤
        (thetaNatBudget : ℝ) +
          (thetaPrimeNatBudget : ℝ) :=
      add_le_add
        canonicalThetaBound_le_thetaNatBudget
        canonicalThetaPrimeBound_le_thetaPrimeNatBudget
    _ = (deltaNatBudget : ℕ) := by
      simp [deltaNatBudget]

theorem canonicalLinkedCoordinateBound_le_linkedCoordinateNatBudget :
    canonicalLinkedCoordinateBound ≤
      (linkedCoordinateNatBudget : ℕ) := by
  unfold canonicalLinkedCoordinateBound linkedCoordinateNatBudget
  push_cast
  have htheta :=
    canonicalThetaBound_le_thetaNatBudget
  have htheta0 := canonicalThetaBound_nonneg
  have he2 := canonicalE2Bound_le_e2NatBudget
  have hdelta := canonicalDeltaBound_le_deltaNatBudget
  have hgap := centralThetaGap_inv_le_eleven
  gcongr

theorem canonicalRawCoordinateBound_le_rawCoordinateNatBudget :
    canonicalRawCoordinateBound ≤
      (rawCoordinateNatBudget : ℕ) := by
  unfold canonicalRawCoordinateBound rawCoordinateNatBudget
  push_cast
  linarith [
    canonicalLinkedCoordinateBound_le_linkedCoordinateNatBudget]

/-- The analytic raw-orbit norm bound is dominated by a natural number
computed only from the finite dimensions. -/
theorem canonicalRawNormSqBound_le_rawNormSqNatBudget
    (eqs vars : ℕ) :
    canonicalRawNormSqBound eqs vars ≤
      (rawNormSqNatBudget eqs vars : ℕ) := by
  unfold canonicalRawNormSqBound rawNormSqNatBudget
  push_cast
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ canonicalRawCoordinateBound_nonneg
      canonicalRawCoordinateBound_le_rawCoordinateNatBudget 2)
    (by positivity)

end HGAS.CanonicalRawOrbitEffectiveBudget
