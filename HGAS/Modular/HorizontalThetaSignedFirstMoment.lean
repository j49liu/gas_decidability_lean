import HGAS.Modular.HorizontalThetaFirstMoment
import Mathlib.Tactic

/-!
# The first horizontal theta moment at an arbitrary signed speed

The detector's physical clock need not have the same orientation as the
standard modular clock.  If the horizontal line has signed speed `s`, the
correct first character is the standard character evaluated at `s t`:

```text
  θ₃(x + s t + i y) · exp(-π i s t).
```

The two factors carry the same signed time scale.  Their product therefore
has frequencies `π s (n² - 1)`, so for every `s ≠ 0` the only resonant
indices remain `n = ±1`.  In particular, reversing time does not destroy
the first-moment height selector.
-/

namespace HGAS.Modular

open Complex Filter Topology

noncomputable section

/-- Multiplying by the first character with the same signed speed turns
the horizontal theta series into the first integer-square moment series. -/
theorem theta₃_mul_signedStandardUnaryFirstCharacter
    (x y s : ℝ) (hy : 0 < y) (t : ℝ) :
    theta₃ (horizontalLine x y s hy t) *
        standardUnaryFirstCharacter (s * t) =
      integerSquareMomentSeries
        (theta3HorizontalCoefficient x y hy)
        (Real.pi * s) 1 1 t := by
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

/-- At every nonzero signed speed, the matched first character retains
precisely the two equal theta coefficients indexed by `±1`. -/
theorem cesaroMeanAt_theta₃_signedFirst_horizontalLine_tendsto
    (x y s : ℝ) (hy : 0 < y) (hs : s ≠ 0)
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) :
    Tendsto
      (fun n ↦ HGAS.Analysis.cesaroMeanAt
        (fun t ↦
          theta₃ (horizontalLine x y s hy t) *
            standardUnaryFirstCharacter (s * t))
        (T n))
      atTop
      (𝓝 (2 * theta3HorizontalCoefficient x y hy 1)) := by
  have hseries :
      (fun t ↦
        theta₃ (horizontalLine x y s hy t) *
          standardUnaryFirstCharacter (s * t)) =
        integerSquareMomentSeries
          (theta3HorizontalCoefficient x y hy)
          (Real.pi * s) 1 1 := by
    funext t
    exact
      theta₃_mul_signedStandardUnaryFirstCharacter
        x y s hy t
  rw [hseries]
  unfold integerSquareMomentSeries
  convert
    HGAS.Analysis.cesaroMeanAt_exponentialSeries_tendsto
      (theta3HorizontalCoefficient x y hy)
      (integerSquareMomentFrequency (Real.pi * s) 1 1)
      (summable_norm_theta3HorizontalCoefficient x y hy) hT using 1
  apply congrArg 𝓝
  simp_rw [
    integerSquareFirstFrequency_one_eq_zero_iff
      (mul_ne_zero Real.pi_ne_zero hs)]
  classical
  rw [tsum_eq_sum (s := ({1, -1} : Finset ℤ))]
  · simp [theta3HorizontalCoefficient_neg_one]
    ring
  · intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    simp [hn]

/-- A unit initial phase and the normalized matched first moment select
the canonical height, independently of the sign of the speed. -/
theorem thetaGaugeHeight_of_horizontal_signed_firstMoment
    (x y s : ℝ) (hy : 0 < y) (hs : s ≠ 0)
    (η : ℂ) (hη : ‖η‖ = 1)
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop)
    (hmoment :
      Tendsto
        (fun n ↦
          HGAS.Analysis.cesaroMeanAt
            (fun t ↦
              theta₃ (horizontalLine x y s hy t) *
                (η * standardUnaryFirstCharacter (s * t)))
            (T n))
        atTop (𝓝 (1 / 128 : ℂ))) :
    y = thetaGaugeHeight := by
  have hbase :=
    cesaroMeanAt_theta₃_signedFirst_horizontalLine_tendsto
      x y s hy hs hT
  have hscaled :=
    hbase.const_mul η
  have hselected :
      Tendsto
        (fun n ↦
          HGAS.Analysis.cesaroMeanAt
            (fun t ↦
              theta₃ (horizontalLine x y s hy t) *
                (η * standardUnaryFirstCharacter (s * t)))
            (T n))
        atTop
        (𝓝
          (η *
            (2 * theta3HorizontalCoefficient x y hy 1))) := by
    simpa only [
      cesaroMeanAt_const_mul, mul_assoc, mul_left_comm, mul_comm] using
      hscaled
  apply thetaGaugeHeight_of_unitPhase_firstCoefficient
    x y hy η hη
  exact tendsto_nhds_unique hselected hmoment

end

end HGAS.Modular
