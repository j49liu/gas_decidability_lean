import HGAS.Modular.HorizontalThetaSeries
import HGAS.Analysis.CesaroExponentialSeriesArbitraryHorizon
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic

/-!
# Squares of theta constants on a horizontal line

The root coordinates `p₂` and `p₄` are theta squares.  Squaring an
absolutely convergent one-dimensional theta series gives an absolutely
convergent series indexed by `ℤ × ℤ`.  This file exposes its coefficients
and temporal frequencies explicitly.

The moment parameter `r` is real.  This is useful for the `p₂` selector:
the character `ζ⁻²` subtracts one half of the private modular frequency.
-/

namespace HGAS.Modular

open Complex

noncomputable section

/-- Sum of two integer-square frequencies, after subtracting a real
moment row `r`. -/
def integerSquarePairFrequency
    (Ω s r : ℝ) (nm : ℤ × ℤ) : ℝ :=
  Ω * (s * ((nm.1 : ℝ) ^ 2 + (nm.2 : ℝ) ^ 2) - r)

/-- Sum of two half-integer-square frequencies, after subtracting a real
moment row `r`. -/
def halfSquarePairFrequency
    (Ω s r : ℝ) (nm : ℤ × ℤ) : ℝ :=
  Ω *
    (s *
        (((nm.1 : ℝ) + 1 / 2) ^ 2 +
          ((nm.2 : ℝ) + 1 / 2) ^ 2) -
      r)

/-- Product coefficient used when an absolutely convergent series is
squared. -/
def pairCoefficient
    (coefficient : ℤ → ℂ) (nm : ℤ × ℤ) : ℂ :=
  coefficient nm.1 * coefficient nm.2

theorem summable_norm_pairCoefficient
    (coefficient : ℤ → ℂ)
    (hsum : Summable fun n ↦ ‖coefficient n‖) :
    Summable fun nm : ℤ × ℤ ↦
      ‖pairCoefficient coefficient nm‖ := by
  simpa only [pairCoefficient, norm_mul] using
    Summable.mul_of_nonneg hsum hsum
      (fun n ↦ norm_nonneg (coefficient n))
      (fun n ↦ norm_nonneg (coefficient n))

/-- Squaring an exponential series gives the product-indexed series with
product coefficients and summed frequencies. -/
theorem exponentialSeries_sq
    (coefficient : ℤ → ℂ)
    (frequency : ℤ → ℝ)
    (hsum : Summable fun n ↦ ‖coefficient n‖)
    (t : ℝ) :
    HGAS.Analysis.exponentialSeries coefficient frequency t ^ 2 =
      HGAS.Analysis.exponentialSeries
        (pairCoefficient coefficient)
        (fun nm ↦ frequency nm.1 + frequency nm.2) t := by
  unfold HGAS.Analysis.exponentialSeries
  rw [pow_two,
    tsum_mul_tsum_of_summable_norm
      (by
        simpa only [
          HGAS.Analysis.exponentialSeriesTerm,
          HGAS.Analysis.norm_realFrequencyExponential,
          norm_mul, mul_one] using hsum)
      (by
        simpa only [
          HGAS.Analysis.exponentialSeriesTerm,
          HGAS.Analysis.norm_realFrequencyExponential,
          norm_mul, mul_one] using hsum)]
  apply tsum_congr
  intro nm
  unfold HGAS.Analysis.exponentialSeriesTerm pairCoefficient
    HGAS.Analysis.realFrequencyExponential
  rw [show
      coefficient nm.1 *
            cexp ((frequency nm.1 : ℂ) * I * (t : ℂ)) *
          (coefficient nm.2 *
            cexp ((frequency nm.2 : ℂ) * I * (t : ℂ))) =
        coefficient nm.1 * coefficient nm.2 *
          (cexp ((frequency nm.1 : ℂ) * I * (t : ℂ)) *
            cexp ((frequency nm.2 : ℂ) * I * (t : ℂ))) by
        ring]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Exact double exponential series for `θ₂²`. -/
theorem theta₂_sq_horizontalLine_eq_exponentialSeries
    (x y s : ℝ) (hy : 0 < y) (t : ℝ) :
    theta₂ (horizontalLine x y s hy t) ^ 2 =
      HGAS.Analysis.exponentialSeries
        (pairCoefficient (theta2HorizontalCoefficient x y hy))
        (halfSquarePairFrequency Real.pi s 0) t := by
  rw [theta₂_horizontalLine_eq_halfSquareMomentSeries]
  unfold halfSquareMomentSeries
  rw [exponentialSeries_sq
    (theta2HorizontalCoefficient x y hy)
    (halfSquareMomentFrequency Real.pi s 0)
    (summable_norm_theta2HorizontalCoefficient x y hy)]
  congr 1
  funext nm
  unfold halfSquarePairFrequency halfSquareMomentFrequency
  push_cast
  ring

/-- Exact double exponential series for `θ₃²`. -/
theorem theta₃_sq_horizontalLine_eq_exponentialSeries
    (x y s : ℝ) (hy : 0 < y) (t : ℝ) :
    theta₃ (horizontalLine x y s hy t) ^ 2 =
      HGAS.Analysis.exponentialSeries
        (pairCoefficient (theta3HorizontalCoefficient x y hy))
        (integerSquarePairFrequency Real.pi s 0) t := by
  rw [theta₃_horizontalLine_eq_integerSquareMomentSeries]
  unfold integerSquareMomentSeries
  rw [exponentialSeries_sq
    (theta3HorizontalCoefficient x y hy)
    (integerSquareMomentFrequency Real.pi s 0)
    (summable_norm_theta3HorizontalCoefficient x y hy)]
  congr 1
  funext nm
  unfold integerSquarePairFrequency integerSquareMomentFrequency
  push_cast
  ring

/-- Exact double exponential series for `θ₄²`. -/
theorem theta₄_sq_horizontalLine_eq_exponentialSeries
    (x y s : ℝ) (hy : 0 < y) (t : ℝ) :
    theta₄ (horizontalLine x y s hy t) ^ 2 =
      HGAS.Analysis.exponentialSeries
        (pairCoefficient (theta4HorizontalCoefficient x y hy))
        (integerSquarePairFrequency Real.pi s 0) t := by
  rw [theta₄_horizontalLine_eq_integerSquareMomentSeries]
  unfold integerSquareMomentSeries
  rw [exponentialSeries_sq
    (theta4HorizontalCoefficient x y hy)
    (integerSquareMomentFrequency Real.pi s 0)
    (summable_norm_theta4HorizontalCoefficient x y hy)]
  congr 1
  funext nm
  unfold integerSquarePairFrequency integerSquareMomentFrequency
  push_cast
  ring

end

end HGAS.Modular
