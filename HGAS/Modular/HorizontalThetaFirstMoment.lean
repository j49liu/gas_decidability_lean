import HGAS.Modular.HorizontalThetaCesaro
import HGAS.Modular.CanonicalThetaGaugeHeight
import Mathlib.Tactic

/-!
# The first horizontal `θ₃` moment and the selected height

After the detector column is rescaled to the standard modular clock
`π i`, its private first-harmonic character is `exp(-π i t)`, up to one
constant unit phase.  At unit horizontal speed this character selects
exactly the two theta modes `n = ±1`.

Consequently the first moment of `θ₃` is

```text
             2 exp(π i x - π y).
```

Its norm is `2 exp(-π y)`.  The detector normalization `1/128` therefore
forces `exp(-π y)=1/256`, hence the canonical height
`y = log(256)/π`.
-/

namespace HGAS.Modular

open Complex Filter Topology

noncomputable section

/-- The standard negative first-harmonic character. -/
def standardUnaryFirstCharacter (t : ℝ) : ℂ :=
  HGAS.Analysis.realFrequencyExponential (-Real.pi) t

/-- Multiplying the horizontal `θ₃` series by the standard first
character subtracts the `r=1` moment frequency. -/
theorem theta₃_mul_standardUnaryFirstCharacter
    (x y s : ℝ) (hy : 0 < y) (t : ℝ) :
    theta₃ (horizontalLine x y s hy t) *
        standardUnaryFirstCharacter t =
      integerSquareMomentSeries
        (theta3HorizontalCoefficient x y hy)
        Real.pi s 1 t := by
  rw [theta₃_horizontalLine_eq_integerSquareMomentSeries]
  unfold integerSquareMomentSeries
    HGAS.Analysis.exponentialSeries
  rw [← tsum_mul_right]
  apply tsum_congr
  intro n
  unfold HGAS.Analysis.exponentialSeriesTerm
    HGAS.Analysis.realFrequencyExponential
    standardUnaryFirstCharacter
    integerSquareMomentFrequency
  unfold HGAS.Analysis.realFrequencyExponential
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem theta3HorizontalCoefficient_neg_one
    (x y : ℝ) (hy : 0 < y) :
    theta3HorizontalCoefficient x y hy (-1) =
      theta3HorizontalCoefficient x y hy 1 := by
  simp [theta3HorizontalCoefficient, theta₃Term]

/-- At unit speed, the standard first moment retains precisely the two
equal coefficients with indices `±1`. -/
theorem cesaroMeanAt_theta₃_first_horizontalLine_tendsto
    (x y : ℝ) (hy : 0 < y)
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) :
    Tendsto
      (fun n ↦ HGAS.Analysis.cesaroMeanAt
        (fun t ↦
          theta₃ (horizontalLine x y 1 hy t) *
            standardUnaryFirstCharacter t)
        (T n))
      atTop
      (𝓝 (2 * theta3HorizontalCoefficient x y hy 1)) := by
  have hseries :
      (fun t ↦
        theta₃ (horizontalLine x y 1 hy t) *
          standardUnaryFirstCharacter t) =
        integerSquareMomentSeries
          (theta3HorizontalCoefficient x y hy)
          Real.pi 1 1 := by
    funext t
    exact theta₃_mul_standardUnaryFirstCharacter x y 1 hy t
  rw [hseries]
  unfold integerSquareMomentSeries
  convert
    HGAS.Analysis.cesaroMeanAt_exponentialSeries_tendsto
      (theta3HorizontalCoefficient x y hy)
      (integerSquareMomentFrequency Real.pi 1 1)
      (summable_norm_theta3HorizontalCoefficient x y hy) hT using 1
  apply congrArg 𝓝
  simp_rw [
    integerSquareFirstFrequency_one_eq_zero_iff Real.pi_ne_zero]
  classical
  rw [tsum_eq_sum (s := ({1, -1} : Finset ℤ))]
  · simp [theta3HorizontalCoefficient_neg_one]
    ring
  · intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    simp [hn]

/-- The selected static coefficient has norm `exp(-πy)`. -/
theorem norm_theta3HorizontalCoefficient_one
    (x y : ℝ) (hy : 0 < y) :
    ‖theta3HorizontalCoefficient x y hy 1‖ =
      Real.exp (-Real.pi * y) := by
  unfold theta3HorizontalCoefficient theta₃Term
  rw [Complex.norm_exp]
  congr 1
  simp [horizontalLine, Complex.mul_re]

/-- A unit phase and the normalized first moment determine the canonical
theta height. -/
theorem thetaGaugeHeight_of_unitPhase_firstCoefficient
    (x y : ℝ) (hy : 0 < y)
    (η : ℂ) (hη : ‖η‖ = 1)
    (hfirst :
      η * (2 * theta3HorizontalCoefficient x y hy 1) =
        (1 / 128 : ℂ)) :
    y = thetaGaugeHeight := by
  have hnorm := congrArg norm hfirst
  rw [norm_mul, hη, one_mul, norm_mul,
    norm_ofNat, norm_theta3HorizontalCoefficient_one] at hnorm
  norm_num at hnorm
  have hexp :
      Real.exp (-Real.pi * y) = 1 / 256 := by
    calc
      Real.exp (-Real.pi * y) =
          Real.exp (-(Real.pi * y)) := by
            congr 1
            ring
      _ = 1 / 256 := by linarith
  have hcanonical := exp_neg_pi_mul_thetaGaugeHeight
  have harg :
      -Real.pi * y =
        -Real.pi * thetaGaugeHeight :=
    Real.exp_injective (hexp.trans hcanonical.symm)
  nlinarith [Real.pi_pos]

end

end HGAS.Modular
