import HGAS.Analysis.TorusCohomologicalPrimitiveVector
import Mathlib.Tactic

/-!
# Scaling a real torus Fourier family

The compact accumulator multiplies every drift coordinate by one rational
gain `κ`.  Analytically this multiplies every complex Fourier coefficient
by the same real scalar.  This file records the exact consequences:

* the real Fourier vector is scaled by `κ`;
* zero-mode and weighted summability hypotheses are preserved; and
* every inverse-frequency primitive bound is multiplied by `|κ|`.

The last identity is what permits a sufficiently small nonzero rational
accumulator gain to fit the primitive graph inside a prescribed positive
central chart.
-/

noncomputable section

open scoped BigOperators

namespace HGAS.Analysis

universe u v

variable {d : Type u} [Fintype d]
variable {m : ℕ}
variable {ι : Fin m → Type v}

/-- Multiply a dependent complex coefficient family by one real scalar. -/
def scaledRealCoefficient
    (c : ℝ)
    (coefficient : ∀ q, ι q → ℂ) :
    ∀ q, ι q → ℂ :=
  fun q i ↦ (c : ℂ) * coefficient q i

theorem norm_scaledRealCoefficient
    (c : ℝ)
    (coefficient : ∀ q, ι q → ℂ)
    (q : Fin m) (i : ι q) :
    ‖scaledRealCoefficient c coefficient q i‖ =
      |c| * ‖coefficient q i‖ := by
  simp [scaledRealCoefficient, Real.norm_eq_abs]

/-- Scaling coefficients scales the real Fourier vector by the same real
number. -/
theorem realTorusFourierVector_scaledRealCoefficient
    (c : ℝ)
    (coefficient : ∀ q, ι q → ℂ)
    (exponent : ∀ q, ι q → d → ℤ)
    (phase : UnitAddTorus d) :
    realTorusFourierVector ι
        (scaledRealCoefficient c coefficient) exponent phase =
      c • realTorusFourierVector ι coefficient exponent phase := by
  funext q
  change
    (torusFourierSeries
      (scaledRealCoefficient c coefficient q)
      (exponent q) phase).re =
      c *
        (torusFourierSeries
          (coefficient q) (exponent q) phase).re
  have hseries :
      torusFourierSeries
          (scaledRealCoefficient c coefficient q)
          (exponent q) phase =
        (c : ℂ) *
          torusFourierSeries
            (coefficient q) (exponent q) phase := by
    unfold torusFourierSeries
    rw [← tsum_mul_left]
    apply tsum_congr
    intro i
    unfold torusSeriesTerm scaledRealCoefficient
    ring
  rw [hseries]
  simp

omit [Fintype d] in
/-- Termwise zero mode survives scalar multiplication. -/
theorem scaledRealCoefficient_zeroMode
    (c : ℝ)
    (coefficient : ∀ q, ι q → ℂ)
    (exponent : ∀ q, ι q → d → ℤ)
    (hzero : ∀ q i, exponent q i = 0 → coefficient q i = 0) :
    ∀ q i, exponent q i = 0 →
      scaledRealCoefficient c coefficient q i = 0 := by
  intro q i hi
  simp [scaledRealCoefficient, hzero q i hi]

/-- Ordinary absolute summability survives scalar multiplication. -/
theorem summable_norm_scaledRealCoefficient
    (c : ℝ)
    (coefficient : ∀ q, ι q → ℂ)
    (h : ∀ q, Summable fun i ↦ ‖coefficient q i‖) :
    ∀ q, Summable fun i ↦
      ‖scaledRealCoefficient c coefficient q i‖ := by
  intro q
  simpa only [norm_scaledRealCoefficient] using
    (h q).mul_left |c|

/-- Any weighted absolute estimate survives scalar multiplication. -/
theorem summable_norm_scaledRealCoefficient_mul_weight
    (c : ℝ)
    (coefficient : ∀ q, ι q → ℂ)
    (weight : ∀ q, ι q → ℝ)
    (h :
      ∀ q, Summable fun i ↦
        ‖coefficient q i‖ * weight q i) :
    ∀ q, Summable fun i ↦
      ‖scaledRealCoefficient c coefficient q i‖ *
        weight q i := by
  intro q
  have hscaled := (h q).mul_left |c|
  apply hscaled.congr
  intro i
  rw [norm_scaledRealCoefficient]
  ring

/-- Inverse-frequency coefficients commute exactly with real scalar
multiplication. -/
theorem cohomologicalPrimitiveCoefficient_scaledReal
    (c : ℝ)
    (coefficient : ∀ q, ι q → ℂ)
    (exponent : ∀ q, ι q → d → ℤ)
    (ω : d → ℝ)
    (q : Fin m) (i : ι q) :
    cohomologicalPrimitiveCoefficient
        (scaledRealCoefficient c coefficient q)
        (exponent q) ω i =
      (c : ℂ) *
        cohomologicalPrimitiveCoefficient
          (coefficient q) (exponent q) ω i := by
  unfold cohomologicalPrimitiveCoefficient
  split_ifs
  · simp
  · simp only [scaledRealCoefficient]
    ring

/-- Exact scaling law for one primitive-coordinate bound. -/
theorem primitiveCoordinateBound_scaledRealCoefficient
    (c : ℝ)
    (coefficient : ∀ q, ι q → ℂ)
    (exponent : ∀ q, ι q → d → ℤ)
    (ω : d → ℝ)
    (q : Fin m) :
    primitiveCoordinateBound ι
        (scaledRealCoefficient c coefficient) exponent ω q =
      |c| *
        primitiveCoordinateBound ι coefficient exponent ω q := by
  unfold primitiveCoordinateBound
  rw [← tsum_mul_left]
  apply tsum_congr
  intro i
  rw [cohomologicalPrimitiveCoefficient_scaledReal,
    norm_mul, Complex.norm_real, Real.norm_eq_abs]

/-- Consequently the finite sum of squared coordinate bounds scales by
`|c|²`. -/
theorem sum_sq_primitiveCoordinateBound_scaledRealCoefficient
    (c : ℝ)
    (coefficient : ∀ q, ι q → ℂ)
    (exponent : ∀ q, ι q → d → ℤ)
    (ω : d → ℝ) :
    (∑ q : Fin m,
      (primitiveCoordinateBound ι
        (scaledRealCoefficient c coefficient) exponent ω q) ^ 2) =
      |c| ^ 2 *
        ∑ q : Fin m,
          (primitiveCoordinateBound ι coefficient exponent ω q) ^ 2 := by
  simp_rw [primitiveCoordinateBound_scaledRealCoefficient]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  ring

end HGAS.Analysis
