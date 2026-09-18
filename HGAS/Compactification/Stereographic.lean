import HGAS.Algebra.FiniteEuclidean
import Mathlib.Tactic

/-!
# One-point compactification of a vector accumulator

Section 11 of the paper compactifies the *whole* affine accumulator at once.
For `z : ℝⁿ`, inverse stereographic projection is

```
U = 2 z / (1 + ‖z‖²),       W = (1 - ‖z‖²) / (1 + ‖z‖²).
```

The point omitted by the finite chart is `(0,-1)`.  Translation
`ż = g` becomes the polynomial vector field

```
U̇ = (1+W)g - (U·g)U,       Ẇ = -(1+W)(U·g).
```

This file proves the sphere identity, tangency, the chart derivative
identities, and the equilibrium property of the unique point at infinity.
All statements are pointwise algebraic, so later dynamical arguments can
reuse them without unfolding rational formulas.
-/

namespace HGAS

open scoped BigOperators

variable {n : ℕ}

noncomputable section

/-- Vector coordinate of inverse stereographic projection. -/
def stereoU (z : FinVector n ℝ) : FinVector n ℝ :=
  fun i ↦ 2 * z i / (1 + normSq z)

/-- Scalar coordinate of inverse stereographic projection. -/
def stereoW (z : FinVector n ℝ) : ℝ :=
  (1 - normSq z) / (1 + normSq z)

/-- The vector component of the compactified translation field. -/
def accumulatorUField
    (u : FinVector n ℝ) (w : ℝ) (g : FinVector n ℝ) :
    FinVector n ℝ :=
  fun i ↦ (1 + w) * g i - dot u g * u i

/-- The scalar component of the compactified translation field. -/
def accumulatorWField
    (u : FinVector n ℝ) (w : ℝ) (g : FinVector n ℝ) : ℝ :=
  -(1 + w) * dot u g

/-- The denominator in inverse stereographic projection is strictly
positive. -/
theorem stereo_denominator_pos (z : FinVector n ℝ) :
    0 < 1 + normSq z := by
  have hz := normSq_nonneg z
  linarith

/-- Inverse stereographic projection lands on the unit sphere. -/
theorem stereo_mem_sphere (z : FinVector n ℝ) :
    normSq (stereoU z) + stereoW z ^ 2 = 1 := by
  have hne : 1 + normSq z ≠ 0 := ne_of_gt (stereo_denominator_pos z)
  simp only [stereoU, stereoW, normSq, dot]
  rw [Finset.sum_congr rfl (fun i _ ↦ by
    change (2 * z i / (1 + ∑ j, z j * z j)) *
        (2 * z i / (1 + ∑ j, z j * z j)) =
      4 * (z i * z i) / (1 + ∑ j, z j * z j) ^ 2
    field_simp
    ring)]
  rw [← Finset.sum_div]
  rw [← Finset.mul_sum]
  field_simp
  ring

/-- The compactified field is tangent to the sphere.  The displayed
quantity is one half of the derivative of `‖U‖² + W²`. -/
theorem accumulator_tangent
    (u : FinVector n ℝ) (w : ℝ) (g : FinVector n ℝ)
    (hsphere : normSq u + w ^ 2 = 1) :
    dot u (accumulatorUField u w g) +
      w * accumulatorWField u w g = 0 := by
  simp only [dot, accumulatorUField, accumulatorWField, normSq] at *
  rw [Finset.sum_congr rfl (fun i _ ↦ by
    change u i * ((1 + w) * g i - (∑ j, u j * g j) * u i) =
      (1 + w) * (u i * g i) -
        (∑ j, u j * g j) * (u i * u i)
    ring)]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  calc
    (1 + w) * (∑ i, u i * g i) -
          (∑ j, u j * g j) * (∑ i, u i * u i) +
        w * (-(1 + w) * ∑ i, u i * g i) =
        (∑ i, u i * g i) *
          (1 - ((∑ i, u i * u i) + w ^ 2)) := by ring
    _ = 0 := by rw [hsphere]; ring

/-- The vector chart derivative obtained by differentiating `stereoU`
along the affine velocity `g`. -/
def stereoUDeriv (z g : FinVector n ℝ) : FinVector n ℝ :=
  fun i ↦
    2 * g i / (1 + normSq z) -
      4 * z i * dot z g / (1 + normSq z) ^ 2

/-- The scalar chart derivative obtained by differentiating `stereoW`
along the affine velocity `g`. -/
def stereoWDeriv (z g : FinVector n ℝ) : ℝ :=
  -4 * dot z g / (1 + normSq z) ^ 2

theorem dot_stereoU (z g : FinVector n ℝ) :
    dot (stereoU z) g = 2 * dot z g / (1 + normSq z) := by
  simp only [dot, stereoU]
  rw [Finset.sum_congr rfl (fun i _ ↦ by
    change (2 * z i / (1 + normSq z)) * g i =
      (2 / (1 + normSq z)) * (z i * g i)
    ring)]
  rw [← Finset.mul_sum]
  ring

/-- The polynomial vector field is exactly the differentiated
stereographic chart in its vector coordinates. -/
theorem stereoUDeriv_eq_field (z g : FinVector n ℝ) :
    stereoUDeriv z g =
      accumulatorUField (stereoU z) (stereoW z) g := by
  funext i
  have hne : 1 + normSq z ≠ 0 := ne_of_gt (stereo_denominator_pos z)
  simp only [stereoUDeriv, accumulatorUField, stereoU, stereoW,
    dot_stereoU]
  field_simp
  ring

/-- The polynomial vector field is exactly the differentiated
stereographic chart in its scalar coordinate. -/
theorem stereoWDeriv_eq_field (z g : FinVector n ℝ) :
    stereoWDeriv z g =
      accumulatorWField (stereoU z) (stereoW z) g := by
  have hne : 1 + normSq z ≠ 0 := ne_of_gt (stereo_denominator_pos z)
  simp only [stereoWDeriv, accumulatorWField, stereoW, dot_stereoU]
  field_simp
  ring

/-- Affine infinity is an equilibrium for every base velocity. -/
theorem accumulator_infinity_equilibrium (g : FinVector n ℝ) :
    accumulatorUField 0 (-1) g = 0 ∧
      accumulatorWField 0 (-1) g = 0 := by
  constructor
  · funext i
    simp [accumulatorUField]
  · simp [accumulatorWField]

end

end HGAS
