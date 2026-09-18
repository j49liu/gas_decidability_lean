import HGAS.Analysis.TorusCohomologicalPrimitiveVector
import Mathlib.Tactic

/-!
# Realifying one complex torus Fourier family

The polynomial detector stores every complex observable in two adjacent
real coordinates.  The cohomological-primitive API, on the other hand,
represents a real coordinate as the real part of a complex Fourier
series.  This file gives the small reusable adapter between those two
conventions.

For a complex series `S`, its two real coordinates are represented by

```text
                 S.re = Re(S),
                 S.im = Re((-i) S).
```

Thus the imaginary coordinate is obtained by multiplying every Fourier
coefficient by `-i`; the exponent family and every summability estimate
are unchanged.
-/

noncomputable section

namespace HGAS.Analysis

universe u v

variable {d : Type u} [Fintype d]
variable {ι : Type v}

/-- Scalar multiplying the complex family for real (`b = 0`) or
imaginary (`b = 1`) output. -/
def realificationScalar (b : Fin 2) : ℂ :=
  ![(1 : ℂ), -Complex.I] b

/-- Coefficients of the real or imaginary coordinate family. -/
def realifiedCoefficient
    (b : Fin 2) (coefficient : ι → ℂ) :
    ι → ℂ :=
  fun i ↦ realificationScalar b * coefficient i

@[simp]
theorem realificationScalar_zero :
    realificationScalar (0 : Fin 2) = 1 := by
  rfl

@[simp]
theorem realificationScalar_one :
    realificationScalar (1 : Fin 2) = -Complex.I := by
  rfl

theorem norm_realificationScalar (b : Fin 2) :
    ‖realificationScalar b‖ = 1 := by
  fin_cases b <;> simp [realificationScalar]

theorem norm_realifiedCoefficient
    (b : Fin 2) (coefficient : ι → ℂ) (i : ι) :
    ‖realifiedCoefficient b coefficient i‖ =
      ‖coefficient i‖ := by
  rw [realifiedCoefficient, norm_mul,
    norm_realificationScalar, one_mul]

/-- Multiplying all coefficients multiplies the whole absolutely
convergent Fourier series. -/
theorem torusFourierSeries_realifiedCoefficient
    (b : Fin 2)
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (phase : UnitAddTorus d) :
    torusFourierSeries
        (realifiedCoefficient b coefficient) exponent phase =
      realificationScalar b *
        torusFourierSeries coefficient exponent phase := by
  unfold torusFourierSeries
  rw [← tsum_mul_left]
  apply tsum_congr
  intro i
  simp only [torusSeriesTerm, realifiedCoefficient]
  ring

/-- The real parts of the two adapted series are exactly the adjacent
real and imaginary coordinates of the original complex series. -/
theorem re_torusFourierSeries_realifiedCoefficient
    (b : Fin 2)
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (phase : UnitAddTorus d) :
    (torusFourierSeries
        (realifiedCoefficient b coefficient) exponent phase).re =
      ![(torusFourierSeries coefficient exponent phase).re,
        (torusFourierSeries coefficient exponent phase).im] b := by
  rw [torusFourierSeries_realifiedCoefficient]
  fin_cases b <;>
    simp [realificationScalar, Complex.mul_re]

/-- Ordinary absolute summability is invariant under realification. -/
theorem summable_norm_realifiedCoefficient
    (b : Fin 2)
    (coefficient : ι → ℂ)
    (h : Summable fun i ↦ ‖coefficient i‖) :
    Summable fun i ↦ ‖realifiedCoefficient b coefficient i‖ := by
  simpa only [norm_realifiedCoefficient] using h

/-- Every nonnegative weighted coefficient estimate is likewise
invariant under realification. -/
theorem summable_norm_realifiedCoefficient_mul_weight
    (b : Fin 2)
    (coefficient : ι → ℂ)
    (weight : ι → ℝ)
    (h :
      Summable fun i ↦
        ‖coefficient i‖ * weight i) :
    Summable fun i ↦
      ‖realifiedCoefficient b coefficient i‖ * weight i := by
  simpa only [norm_realifiedCoefficient] using h

omit [Fintype d] in
/-- Multiplication by the nonzero scalars `1` and `-i` preserves a
termwise zero-mode certificate. -/
theorem realifiedCoefficient_zero_of_zero
    (b : Fin 2)
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (hzero : ∀ i, exponent i = 0 → coefficient i = 0) :
    ∀ i, exponent i = 0 →
      realifiedCoefficient b coefficient i = 0 := by
  intro i hi
  simp [realifiedCoefficient, hzero i hi]

end HGAS.Analysis
