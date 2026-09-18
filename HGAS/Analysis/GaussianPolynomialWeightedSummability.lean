import HGAS.Analysis.PolynomialWeightedLatticeSummability
import Mathlib.Tactic

/-!
# Polynomial losses absorbed by one- and two-dimensional Gaussian decay

Selector moments use one or two integer theta indices rather than the
full detector lattice.  This module gives reusable domination theorems
for those shapes.

The decay exponent need not literally be a square.  It is enough that it
dominates ordinary `ℓ¹` energy.  This includes the odd-square exponent
`|2n+1|²` occurring in the `θ₂` root moment.
-/

noncomputable section

namespace HGAS.Analysis

/-- A decay exponent dominating `|n|` absorbs an arbitrary fixed
polynomial height loss. -/
theorem summable_intDecay_mul_height_pow_of_polynomial_bound
    {q C : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (decayEnergy : ℤ → ℕ)
    (hdecay : ∀ z, z.natAbs ≤ decayEnergy z)
    (heightPower growthPower : ℕ)
    (height : ℤ → ℝ)
    (hheight0 : ∀ z, 0 ≤ height z)
    (hheight :
      ∀ z,
        height z ≤
          C * (1 + (z.natAbs : ℝ)) ^ growthPower) :
    Summable fun z : ℤ ↦
      q ^ decayEnergy z * height z ^ heightPower := by
  have hbase :=
    summable_polynomialGeometricIntWeight
      hq0 hq1 (growthPower * heightPower)
  have hmajor :
      Summable fun z : ℤ ↦
        C ^ heightPower *
          polynomialGeometricIntWeight
            q (growthPower * heightPower) z :=
    hbase.mul_left (C ^ heightPower)
  apply Summable.of_nonneg_of_le
  · intro z
    exact mul_nonneg (pow_nonneg hq0.le _)
      (pow_nonneg (hheight0 z) _)
  · intro z
    have hp :
        height z ^ heightPower ≤
          (C *
            (1 + (z.natAbs : ℝ)) ^ growthPower) ^
              heightPower :=
      pow_le_pow_left₀ (hheight0 z)
        (hheight z) heightPower
    have hdecayPow :
        q ^ decayEnergy z ≤ q ^ z.natAbs :=
      pow_le_pow_of_le_one hq0.le hq1.le (hdecay z)
    calc
      q ^ decayEnergy z * height z ^ heightPower ≤
          q ^ z.natAbs *
            (C *
              (1 + (z.natAbs : ℝ)) ^ growthPower) ^
                heightPower :=
        mul_le_mul hdecayPow hp
          (pow_nonneg (hheight0 z) _)
          (pow_nonneg hq0.le _)
      _ =
          C ^ heightPower *
            polynomialGeometricIntWeight
              q (growthPower * heightPower) z := by
        rw [mul_pow, ← pow_mul]
        unfold polynomialGeometricIntWeight
        ring
  · exact hmajor

/-- Discrete Gaussian specialization on `ℤ`. -/
theorem summable_gaussian_mul_height_pow_of_polynomial_bound
    {q C : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (heightPower growthPower : ℕ)
    (height : ℤ → ℝ)
    (hheight0 : ∀ z, 0 ≤ height z)
    (hheight :
      ∀ z,
        height z ≤
          C * (1 + (z.natAbs : ℝ)) ^ growthPower) :
    Summable fun z : ℤ ↦
      q ^ (z.natAbs ^ 2) * height z ^ heightPower := by
  apply
    summable_intDecay_mul_height_pow_of_polynomial_bound
      hq0 hq1 (fun z : ℤ ↦ z.natAbs ^ 2)
      (fun z ↦ by
        simpa only [pow_two] using z.natAbs.le_mul_self)
      heightPower growthPower height hheight0 hheight

/-- Ordinary `ℓ¹` energy of a pair of integers. -/
def integerPairAbsEnergy (z : ℤ × ℤ) : ℕ :=
  z.1.natAbs + z.2.natAbs

/-- A polynomially weighted geometric sequence is summable on
`ℤ × ℤ`. -/
theorem summable_polynomialGeometricIntPairWeight
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (r : ℕ) :
    Summable fun z : ℤ × ℤ ↦
      (1 + (integerPairAbsEnergy z : ℝ)) ^ r *
        q ^ integerPairAbsEnergy z := by
  let weight : ℤ → ℝ :=
    polynomialGeometricIntWeight q r
  have hweight : Summable weight :=
    summable_polynomialGeometricIntWeight hq0 hq1 r
  have hweight0 : ∀ z, 0 ≤ weight z :=
    fun z ↦
      polynomialGeometricIntWeight_nonneg hq0.le r z
  have hproduct :
      Summable fun z : ℤ × ℤ ↦
        weight z.1 * weight z.2 :=
    Summable.mul_of_nonneg hweight hweight
      hweight0 hweight0
  apply Summable.of_nonneg_of_le
  · intro z
    exact mul_nonneg (pow_nonneg (by positivity) _)
      (pow_nonneg hq0.le _)
  · intro z
    have hlinear :
        1 + (integerPairAbsEnergy z : ℝ) ≤
          (1 + (z.1.natAbs : ℝ)) *
            (1 + (z.2.natAbs : ℝ)) := by
      unfold integerPairAbsEnergy
      push_cast
      have ha : 0 ≤ (z.1.natAbs : ℝ) :=
        Nat.cast_nonneg _
      have hb : 0 ≤ (z.2.natAbs : ℝ) :=
        Nat.cast_nonneg _
      nlinarith [mul_nonneg ha hb]
    have hpow :
        (1 + (integerPairAbsEnergy z : ℝ)) ^ r ≤
          ((1 + (z.1.natAbs : ℝ)) *
            (1 + (z.2.natAbs : ℝ))) ^ r := by
      gcongr
    calc
      (1 + (integerPairAbsEnergy z : ℝ)) ^ r *
          q ^ integerPairAbsEnergy z ≤
        ((1 + (z.1.natAbs : ℝ)) *
            (1 + (z.2.natAbs : ℝ))) ^ r *
          q ^ integerPairAbsEnergy z :=
        mul_le_mul_of_nonneg_right hpow
          (pow_nonneg hq0.le _)
      _ = weight z.1 * weight z.2 := by
        simp only [weight, polynomialGeometricIntWeight,
          integerPairAbsEnergy, pow_add, mul_pow]
        ring
  · exact hproduct

/-- Any pair decay exponent dominating `|n|+|m|` absorbs an arbitrary
fixed polynomial height loss. -/
theorem summable_intPairDecay_mul_height_pow_of_polynomial_bound
    {q C : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (decayEnergy : ℤ × ℤ → ℕ)
    (hdecay : ∀ z, integerPairAbsEnergy z ≤ decayEnergy z)
    (heightPower growthPower : ℕ)
    (height : ℤ × ℤ → ℝ)
    (hheight0 : ∀ z, 0 ≤ height z)
    (hheight :
      ∀ z,
        height z ≤
          C *
            (1 + (integerPairAbsEnergy z : ℝ)) ^
              growthPower) :
    Summable fun z : ℤ × ℤ ↦
      q ^ decayEnergy z * height z ^ heightPower := by
  have hbase :=
    summable_polynomialGeometricIntPairWeight
      hq0 hq1 (growthPower * heightPower)
  have hmajor :
      Summable fun z : ℤ × ℤ ↦
        C ^ heightPower *
          ((1 + (integerPairAbsEnergy z : ℝ)) ^
              (growthPower * heightPower) *
            q ^ integerPairAbsEnergy z) :=
    hbase.mul_left (C ^ heightPower)
  apply Summable.of_nonneg_of_le
  · intro z
    exact mul_nonneg (pow_nonneg hq0.le _)
      (pow_nonneg (hheight0 z) _)
  · intro z
    have hp :
        height z ^ heightPower ≤
          (C *
            (1 + (integerPairAbsEnergy z : ℝ)) ^
              growthPower) ^ heightPower :=
      pow_le_pow_left₀ (hheight0 z)
        (hheight z) heightPower
    have hdecayPow :
        q ^ decayEnergy z ≤
          q ^ integerPairAbsEnergy z :=
      pow_le_pow_of_le_one hq0.le hq1.le (hdecay z)
    calc
      q ^ decayEnergy z * height z ^ heightPower ≤
        q ^ integerPairAbsEnergy z *
          (C *
            (1 + (integerPairAbsEnergy z : ℝ)) ^
              growthPower) ^ heightPower :=
        mul_le_mul hdecayPow hp
          (pow_nonneg (hheight0 z) _)
          (pow_nonneg hq0.le _)
      _ =
        C ^ heightPower *
          ((1 + (integerPairAbsEnergy z : ℝ)) ^
              (growthPower * heightPower) *
            q ^ integerPairAbsEnergy z) := by
        rw [mul_pow, ← pow_mul]
        ring
  · exact hmajor

/-- Product-Gaussian specialization on `ℤ × ℤ`. -/
theorem summable_pairGaussian_mul_height_pow_of_polynomial_bound
    {q C : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (heightPower growthPower : ℕ)
    (height : ℤ × ℤ → ℝ)
    (hheight0 : ∀ z, 0 ≤ height z)
    (hheight :
      ∀ z,
        height z ≤
          C *
            (1 + (integerPairAbsEnergy z : ℝ)) ^
              growthPower) :
    Summable fun z : ℤ × ℤ ↦
      q ^ (z.1.natAbs ^ 2 + z.2.natAbs ^ 2) *
        height z ^ heightPower := by
  apply
    summable_intPairDecay_mul_height_pow_of_polynomial_bound
      hq0 hq1
      (fun z : ℤ × ℤ ↦
        z.1.natAbs ^ 2 + z.2.natAbs ^ 2)
      (fun z ↦ by
        unfold integerPairAbsEnergy
        exact Nat.add_le_add
          (by simpa only [pow_two] using
            z.1.natAbs.le_mul_self)
          (by simpa only [pow_two] using
            z.2.natAbs.le_mul_self))
      heightPower growthPower height hheight0 hheight

end HGAS.Analysis
