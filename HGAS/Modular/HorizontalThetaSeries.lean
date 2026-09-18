import HGAS.Modular.UnaryMomentResonance
import HGAS.Modular.HorizontalTrajectory
import HGAS.Modular.ThetaConstants
import Mathlib.Tactic

/-!
# Theta constants as explicit time series on a horizontal line

For

```text
                         τ(t) = x + s t + i y
```

the defining theta series split into a time-independent Gaussian
coefficient and a pure real-frequency exponential.  This file records
that split with the exact `π` normalization used by the unary selector.

The three identities are valid for arbitrary real `x`, positive `y`, and
signed nonzero or zero speed `s`; nonvanishing of `s` is needed only when
the later Cesàro resonance theorems are invoked.
-/

namespace HGAS.Modular

open Complex
open UpperHalfPlane hiding I

noncomputable section

/-- Static coefficient of `θ₂` along the horizontal line through
`x + i y`. -/
def theta2HorizontalCoefficient
    (x y : ℝ) (hy : 0 < y) (n : ℤ) : ℂ :=
  theta₂Term n (horizontalLine x y 0 hy 0)

/-- Static coefficient of `θ₃` along the horizontal line through
`x + i y`. -/
def theta3HorizontalCoefficient
    (x y : ℝ) (hy : 0 < y) (n : ℤ) : ℂ :=
  theta₃Term n (horizontalLine x y 0 hy 0)

/-- Static coefficient of `θ₄` along the horizontal line through
`x + i y`. -/
def theta4HorizontalCoefficient
    (x y : ℝ) (hy : 0 < y) (n : ℤ) : ℂ :=
  theta₄Term n (horizontalLine x y 0 hy 0)

theorem summable_norm_theta2HorizontalCoefficient
    (x y : ℝ) (hy : 0 < y) :
    Summable fun n : ℤ ↦
      ‖theta2HorizontalCoefficient x y hy n‖ := by
  let τ := horizontalLine x y 0 hy 0
  have hjacobi :
      Summable (jacobiTheta₂_term · ((τ : ℂ) / 2) (τ : ℂ)) :=
    (summable_jacobiTheta₂_term_iff
      ((τ : ℂ) / 2) (τ : ℂ)).2 (by
        simpa only [τ, horizontalLine_im] using hy)
  have hterm :
      Summable fun n : ℤ ↦ theta₂Term n τ := by
    simpa only [theta₂Term_eq_jacobiTheta₂_term] using
      hjacobi.mul_left (cexp (Real.pi * I * (τ : ℂ) / 4))
  simpa only [theta2HorizontalCoefficient, τ] using hterm.norm

theorem summable_norm_theta3HorizontalCoefficient
    (x y : ℝ) (hy : 0 < y) :
    Summable fun n : ℤ ↦
      ‖theta3HorizontalCoefficient x y hy n‖ := by
  let τ := horizontalLine x y 0 hy 0
  have hjacobi :
      Summable (jacobiTheta₂_term · (0 : ℂ) (τ : ℂ)) :=
    (summable_jacobiTheta₂_term_iff
      (0 : ℂ) (τ : ℂ)).2 (by
        simpa only [τ, horizontalLine_im] using hy)
  have hterm :
      Summable fun n : ℤ ↦ theta₃Term n τ := by
    simpa only [theta₃Term_eq_jacobiTheta₂_term] using hjacobi
  simpa only [theta3HorizontalCoefficient, τ] using hterm.norm

theorem summable_norm_theta4HorizontalCoefficient
    (x y : ℝ) (hy : 0 < y) :
    Summable fun n : ℤ ↦
      ‖theta4HorizontalCoefficient x y hy n‖ := by
  let τ := horizontalLine x y 0 hy 0
  have hjacobi :
      Summable
        (jacobiTheta₂_term · (1 / 2 : ℂ) (τ : ℂ)) :=
    (summable_jacobiTheta₂_term_iff
      (1 / 2 : ℂ) (τ : ℂ)).2 (by
        simpa only [τ, horizontalLine_im] using hy)
  have hterm :
      Summable fun n : ℤ ↦ theta₄Term n τ := by
    simpa only [theta₄Term_eq_jacobiTheta₂_term] using hjacobi
  simpa only [theta4HorizontalCoefficient, τ] using hterm.norm

/-- One `θ₂` term is its static Gaussian coefficient times the
half-square time character. -/
theorem theta₂Term_horizontalLine
    (x y s : ℝ) (hy : 0 < y) (n : ℤ) (t : ℝ) :
    theta₂Term n (horizontalLine x y s hy t) =
      theta2HorizontalCoefficient x y hy n *
        HGAS.Analysis.realFrequencyExponential
          (halfSquareMomentFrequency Real.pi s 0 n) t := by
  simp only [theta₂Term, theta2HorizontalCoefficient,
    HGAS.Analysis.realFrequencyExponential,
    halfSquareMomentFrequency]
  rw [← Complex.exp_add]
  congr 1
  simp only [Int.cast_zero, sub_zero]
  push_cast
  apply Complex.ext <;>
    simp [horizontalLine, Complex.mul_re, Complex.mul_im]
  · ring
  · ring

/-- One `θ₃` term is its static Gaussian coefficient times the
integer-square time character. -/
theorem theta₃Term_horizontalLine
    (x y s : ℝ) (hy : 0 < y) (n : ℤ) (t : ℝ) :
    theta₃Term n (horizontalLine x y s hy t) =
      theta3HorizontalCoefficient x y hy n *
        HGAS.Analysis.realFrequencyExponential
          (integerSquareMomentFrequency Real.pi s 0 n) t := by
  simp only [theta₃Term, theta3HorizontalCoefficient,
    HGAS.Analysis.realFrequencyExponential,
    integerSquareMomentFrequency]
  rw [← Complex.exp_add]
  congr 1
  simp only [Int.cast_zero, sub_zero]
  push_cast
  apply Complex.ext <;>
    simp [horizontalLine, Complex.mul_re, Complex.mul_im]
  · ring
  · ring

/-- One `θ₄` term has the same integer-square time character as `θ₃`;
its alternating sign is part of the static coefficient. -/
theorem theta₄Term_horizontalLine
    (x y s : ℝ) (hy : 0 < y) (n : ℤ) (t : ℝ) :
    theta₄Term n (horizontalLine x y s hy t) =
      theta4HorizontalCoefficient x y hy n *
        HGAS.Analysis.realFrequencyExponential
          (integerSquareMomentFrequency Real.pi s 0 n) t := by
  have h := theta₃Term_horizontalLine x y s hy n t
  simp only [theta₃Term, theta3HorizontalCoefficient] at h
  simp only [theta₄Term, theta4HorizontalCoefficient]
  rw [h]
  ring

/-- Exact `θ₂` half-square exponential series on a horizontal line. -/
theorem theta₂_horizontalLine_eq_halfSquareMomentSeries
    (x y s : ℝ) (hy : 0 < y) (t : ℝ) :
    theta₂ (horizontalLine x y s hy t) =
      halfSquareMomentSeries
        (theta2HorizontalCoefficient x y hy)
        Real.pi s 0 t := by
  unfold theta₂ halfSquareMomentSeries
    HGAS.Analysis.exponentialSeries
    HGAS.Analysis.exponentialSeriesTerm
  apply tsum_congr
  intro n
  exact theta₂Term_horizontalLine x y s hy n t

/-- Exact `θ₃` integer-square exponential series on a horizontal line. -/
theorem theta₃_horizontalLine_eq_integerSquareMomentSeries
    (x y s : ℝ) (hy : 0 < y) (t : ℝ) :
    theta₃ (horizontalLine x y s hy t) =
      integerSquareMomentSeries
        (theta3HorizontalCoefficient x y hy)
        Real.pi s 0 t := by
  unfold theta₃ integerSquareMomentSeries
    HGAS.Analysis.exponentialSeries
    HGAS.Analysis.exponentialSeriesTerm
  apply tsum_congr
  intro n
  exact theta₃Term_horizontalLine x y s hy n t

/-- Exact `θ₄` integer-square exponential series on a horizontal line. -/
theorem theta₄_horizontalLine_eq_integerSquareMomentSeries
    (x y s : ℝ) (hy : 0 < y) (t : ℝ) :
    theta₄ (horizontalLine x y s hy t) =
      integerSquareMomentSeries
        (theta4HorizontalCoefficient x y hy)
        Real.pi s 0 t := by
  unfold theta₄ integerSquareMomentSeries
    HGAS.Analysis.exponentialSeries
    HGAS.Analysis.exponentialSeriesTerm
  apply tsum_congr
  intro n
  exact theta₄Term_horizontalLine x y s hy n t

end

end HGAS.Modular
