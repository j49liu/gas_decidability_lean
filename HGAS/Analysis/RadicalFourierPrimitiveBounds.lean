import HGAS.Analysis.TorusCohomologicalPrimitive
import HGAS.Clocks.RadicalSmallDivisor
import Mathlib.Tactic

/-!
# Weighted summability of Fourier primitives for radical clocks

`RadicalSmallDivisor` proves that the inverse of a nonzero signed
prime-square-root frequency has at most fixed polynomial growth.  This file
connects that arithmetic estimate to the Fourier primitive construction.

If the original Fourier coefficients remain summable after multiplication
by the corresponding fixed power of the weighted exponent height, then the
inverse-frequency coefficients are absolutely summable.  This is the exact
interface needed for a continuous bounded cohomological primitive on the
clock torus.
-/

noncomputable section

open scoped BigOperators

namespace HGAS.Analysis

open HGAS.Clocks

variable {d ι : Type*} [Fintype d]

/-- Exact norm of the complex angular frequency. -/
theorem norm_torusAngularFrequency
    (n : d → ℤ) (ω : d → ℝ) :
    ‖torusAngularFrequency n ω‖ =
      2 * Real.pi *
        |RadicalClock.frequencyPairing n ω| := by
  unfold torusAngularFrequency
  simp only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
    Real.norm_eq_abs]
  rw [abs_of_pos (by positivity : 0 < (2 : ℝ)),
    abs_of_pos Real.pi_pos]

/-- The coefficient majorant supplied by the radical small-divisor bound. -/
def radicalPrimitiveCoefficientMajorant
    (scale : ℝ) (p : d → ℕ)
    (coefficient : ℂ) (exponent : d → ℤ) : ℝ :=
  ‖coefficient‖ *
      RadicalSmallDivisor.radicalConjugateHeight p exponent ^
        (RadicalSmallDivisor.radicalDegree p - 1) /
    (2 * Real.pi * |scale|)

theorem radicalPrimitiveCoefficientMajorant_nonneg
    (scale : ℝ) (p : d → ℕ)
    (coefficient : ℂ) (exponent : d → ℤ) :
    0 ≤ radicalPrimitiveCoefficientMajorant
      scale p coefficient exponent := by
  unfold radicalPrimitiveCoefficientMajorant
  apply div_nonneg
  · exact mul_nonneg (norm_nonneg _)
      (pow_nonneg
        (RadicalSmallDivisor.radicalConjugateHeight_nonneg
          p exponent) _)
  · exact mul_nonneg
      (mul_nonneg (by norm_num) Real.pi_pos.le)
      (abs_nonneg scale)

/-- Pointwise inverse-frequency estimate for one Fourier coefficient.

The zero exponent is harmless because the centered primitive deletes its
resonant coefficient.  For every nonzero exponent, the quantitative
radical bound controls the denominator. -/
theorem norm_cohomologicalPrimitiveCoefficient_le_radicalMajorant
    (scale : ℝ) (hscale : scale ≠ 0)
    (p : d → ℕ)
    (hp : ∀ i : d, (p i).Prime)
    (hinjective : Function.Injective p)
    (sign : d → ℤ)
    (hsign : ∀ i, sign i = 1 ∨ sign i = -1)
    (coefficient : ℂ) (exponent : d → ℤ) :
    ‖cohomologicalPrimitiveCoefficient
        (fun _ : Unit ↦ coefficient)
        (fun _ : Unit ↦ exponent)
        (fun i ↦ scale *
          RadicalIndependence.signedPrimeSqrtFrequency p sign i)
        ()‖ ≤
      radicalPrimitiveCoefficientMajorant
        scale p coefficient exponent := by
  by_cases hexponent : exponent = 0
  · subst exponent
    have hpair :
        RadicalClock.frequencyPairing
          (0 : d → ℤ)
          (fun i ↦ scale *
            RadicalIndependence.signedPrimeSqrtFrequency p sign i) =
          0 := by
      simp [RadicalClock.frequencyPairing]
    rw [cohomologicalPrimitiveCoefficient, if_pos hpair, norm_zero]
    exact radicalPrimitiveCoefficientMajorant_nonneg
      scale p coefficient 0
  · let height : ℝ :=
      RadicalSmallDivisor.radicalConjugateHeight p exponent
    let degree : ℕ :=
      RadicalSmallDivisor.radicalDegree p - 1
    let pairing : ℝ :=
      RadicalClock.frequencyPairing exponent
        (fun i ↦ scale *
          RadicalIndependence.signedPrimeSqrtFrequency p sign i)
    have hheight :
        0 < height :=
      RadicalSmallDivisor.radicalConjugateHeight_pos
        p hp exponent hexponent
    have hscaleAbs : 0 < |scale| :=
      abs_pos.mpr hscale
    have hsmall :
        |scale| / height ^ degree ≤ |pairing| := by
      exact
        RadicalSmallDivisor.abs_scale_div_height_pow_le_abs_frequencyPairing_scaled
          scale p hp hinjective sign hsign exponent hexponent
    have hpairAbs : 0 < |pairing| := by
      have hleft :
          0 < |scale| / height ^ degree := by
        positivity
      exact hleft.trans_le hsmall
    have hpair : pairing ≠ 0 :=
      (abs_pos.mp hpairAbs)
    have hheightPair :
        |scale| ≤ |pairing| * height ^ degree :=
      (div_le_iff₀ (pow_pos hheight degree)).mp hsmall
    have hdenPair :
        0 < 2 * Real.pi * |pairing| := by
      positivity
    have hdenScale :
        0 < 2 * Real.pi * |scale| := by
      positivity
    unfold cohomologicalPrimitiveCoefficient
    rw [if_neg hpair]
    rw [norm_div, norm_torusAngularFrequency]
    change
      ‖coefficient‖ / (2 * Real.pi * |pairing|) ≤
        ‖coefficient‖ * height ^ degree /
          (2 * Real.pi * |scale|)
    rw [div_le_div_iff₀ hdenPair hdenScale]
    calc
      ‖coefficient‖ * (2 * Real.pi * |scale|) =
          (2 * Real.pi * ‖coefficient‖) * |scale| := by
        ring
      _ ≤
          (2 * Real.pi * ‖coefficient‖) *
            (|pairing| * height ^ degree) := by
        exact mul_le_mul_of_nonneg_left hheightPair (by positivity)
      _ =
          ‖coefficient‖ * height ^ degree *
            (2 * Real.pi * |pairing|) := by
        ring

/-- Weighted coefficient summability implies absolute summability of all
inverse-frequency coefficients. -/
theorem summable_norm_cohomologicalPrimitiveCoefficient_of_radical
    (scale : ℝ) (hscale : scale ≠ 0)
    (p : d → ℕ)
    (hp : ∀ i : d, (p i).Prime)
    (hinjective : Function.Injective p)
    (sign : d → ℤ)
    (hsign : ∀ i, sign i = 1 ∨ sign i = -1)
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (hweighted :
      Summable fun j ↦
        ‖coefficient j‖ *
          RadicalSmallDivisor.radicalConjugateHeight
              p (exponent j) ^
            (RadicalSmallDivisor.radicalDegree p - 1)) :
    Summable fun j ↦
      ‖cohomologicalPrimitiveCoefficient
        coefficient exponent
        (fun i ↦ scale *
          RadicalIndependence.signedPrimeSqrtFrequency p sign i)
        j‖ := by
  let denominator : ℝ :=
    2 * Real.pi * |scale|
  have hmajorant :
      Summable fun j ↦
        (‖coefficient j‖ *
          RadicalSmallDivisor.radicalConjugateHeight
              p (exponent j) ^
            (RadicalSmallDivisor.radicalDegree p - 1)) /
          denominator :=
    hweighted.div_const denominator
  apply Summable.of_nonneg_of_le
  · intro j
    exact norm_nonneg _
  · intro j
    simpa only [denominator,
      radicalPrimitiveCoefficientMajorant] using
      norm_cohomologicalPrimitiveCoefficient_le_radicalMajorant
        scale hscale p hp hinjective sign hsign
        (coefficient j) (exponent j)
  · exact hmajorant

end HGAS.Analysis
