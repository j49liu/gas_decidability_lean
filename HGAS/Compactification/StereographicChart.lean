import HGAS.Compactification.Stereographic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

/-!
# The finite chart of the one-point accumulator sphere

`Stereographic.lean` gives the inverse stereographic formulas and the
compactified polynomial vector field.  Here we package the corresponding
finite chart as an actual homeomorphism:

```
       ℝⁿ  ≃  { (U,W) : ‖U‖² + W² = 1  |  W ≠ -1 }.
```

The chart coordinate is `Z = U / (1+W)`, and its inverse is the map
`(stereoU, stereoW)`.  Keeping this interface separate makes the
measure-restriction and affine-cocycle arguments independent of the
coordinate algebra.
-/

namespace HGAS

open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-- The algebraic unit sphere used for the compact vector accumulator. -/
abbrev AccumulatorSphere (n : ℕ) :=
  {p : FinVector n ℝ × ℝ // normSq p.1 + p.2 ^ 2 = 1}

/-- The sphere with its unique affine point at infinity removed. -/
abbrev FiniteAccumulatorChart (n : ℕ) :=
  {p : AccumulatorSphere n // p.1.2 ≠ -1}

/-- The affine coordinate `Z = U/(1+W)` on the finite accumulator chart. -/
def accumulatorChartCoordinate
    (p : FiniteAccumulatorChart n) :
    FinVector n ℝ :=
  fun i ↦ p.1.1.1 i / (1 + p.1.1.2)

/-- The inverse stereographic image never equals the point at infinity. -/
theorem stereoW_ne_neg_one (z : FinVector n ℝ) :
    stereoW z ≠ -1 := by
  have hden : 1 + normSq z ≠ 0 :=
    ne_of_gt (stereo_denominator_pos z)
  intro h
  simp only [stereoW] at h
  field_simp [hden] at h
  linarith

/-- Inverse stereographic projection, valued in the finite chart. -/
def accumulatorStereoChart
    (z : FinVector n ℝ) :
    FiniteAccumulatorChart n :=
  ⟨⟨(stereoU z, stereoW z), stereo_mem_sphere z⟩,
    stereoW_ne_neg_one z⟩

/-- The affine chart recovers the original vector after inverse
stereographic projection. -/
@[simp]
theorem accumulatorChartCoordinate_stereo
    (z : FinVector n ℝ) :
    accumulatorChartCoordinate (accumulatorStereoChart z) = z := by
  funext i
  have hden : 1 + normSq z ≠ 0 :=
    ne_of_gt (stereo_denominator_pos z)
  simp only [accumulatorChartCoordinate, accumulatorStereoChart,
    stereoU, stereoW]
  field_simp [hden]
  ring

/-- Squared norm of the affine chart coordinate, expressed in sphere
coordinates. -/
theorem normSq_accumulatorChartCoordinate
    (p : FiniteAccumulatorChart n) :
    normSq (accumulatorChartCoordinate p) =
      (1 - p.1.1.2) / (1 + p.1.1.2) := by
  let u : FinVector n ℝ := p.1.1.1
  let w : ℝ := p.1.1.2
  have hsphere : normSq u + w ^ 2 = 1 := p.1.2
  have hden : 1 + w ≠ 0 := by
    intro h
    apply p.2
    linarith
  simp only [accumulatorChartCoordinate, normSq, dot]
  rw [Finset.sum_congr rfl (fun i _ ↦ by
    change
      (p.1.1.1 i / (1 + p.1.1.2)) *
          (p.1.1.1 i / (1 + p.1.1.2)) =
        (p.1.1.1 i * p.1.1.1 i) /
          (1 + p.1.1.2) ^ 2
    field_simp)]
  rw [← Finset.sum_div]
  change normSq u / (1 + w) ^ 2 = (1 - w) / (1 + w)
  field_simp [hden]
  nlinarith

/-- On the finite sphere chart, the compactified accumulator vector field
pushes forward to the original affine velocity.  This is the quotient-rule
identity underlying the dynamic conjugacy. -/
theorem accumulatorChartFieldDerivative_eq
    (p : FiniteAccumulatorChart n)
    (g : FinVector n ℝ) (i : Fin n) :
    (accumulatorUField p.1.1.1 p.1.1.2 g i *
          (1 + p.1.1.2) -
        p.1.1.1 i *
          accumulatorWField p.1.1.1 p.1.1.2 g) /
        (1 + p.1.1.2) ^ 2 =
      g i := by
  have hden : 1 + p.1.1.2 ≠ 0 := by
    intro h
    apply p.2
    linarith
  simp only [accumulatorUField, accumulatorWField]
  field_simp [hden]
  ring

/-- Inverse stereographic projection recovers every point in the finite
chart. -/
@[simp]
theorem accumulatorStereo_chartCoordinate
    (p : FiniteAccumulatorChart n) :
    accumulatorStereoChart (accumulatorChartCoordinate p) = p := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · funext i
    have hden : 1 + p.1.1.2 ≠ 0 := by
      intro h
      apply p.2
      linarith
    have hnew :
        1 + (1 - p.1.1.2) / (1 + p.1.1.2) =
          2 / (1 + p.1.1.2) := by
      field_simp [hden]
      ring
    change
      2 * accumulatorChartCoordinate p i /
          (1 + normSq (accumulatorChartCoordinate p)) =
        p.1.1.1 i
    rw [normSq_accumulatorChartCoordinate, hnew]
    simp only [accumulatorChartCoordinate]
    field_simp [hden]
  · have hden : 1 + p.1.1.2 ≠ 0 := by
      intro h
      apply p.2
      linarith
    have hnew :
        1 + (1 - p.1.1.2) / (1 + p.1.1.2) =
          2 / (1 + p.1.1.2) := by
      field_simp [hden]
      ring
    change
      (1 - normSq (accumulatorChartCoordinate p)) /
          (1 + normSq (accumulatorChartCoordinate p)) =
        p.1.1.2
    rw [normSq_accumulatorChartCoordinate, hnew]
    field_simp [hden]
    ring

/-- Continuity of inverse stereographic projection into the finite chart. -/
theorem continuous_accumulatorStereoChart :
    Continuous
      (accumulatorStereoChart :
        FinVector n ℝ → FiniteAccumulatorChart n) := by
  have hnorm :
      Continuous (normSq : FinVector n ℝ → ℝ) := by
    change Continuous
      (fun z : FinVector n ℝ ↦ ∑ i, z i * z i)
    fun_prop
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply Continuous.prodMk
  · apply continuous_pi
    intro i
    apply Continuous.div
    · exact continuous_const.mul (continuous_apply i)
    · exact continuous_const.add hnorm
    · intro z
      exact ne_of_gt (stereo_denominator_pos z)
  · apply Continuous.div
    · exact continuous_const.sub hnorm
    · exact continuous_const.add hnorm
    · intro z
      exact ne_of_gt (stereo_denominator_pos z)

/-- Continuity of the affine coordinate on the finite chart. -/
theorem continuous_accumulatorChartCoordinate :
    Continuous
      (accumulatorChartCoordinate :
        FiniteAccumulatorChart n → FinVector n ℝ) := by
  apply continuous_pi
  intro i
  unfold accumulatorChartCoordinate
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro p h
    apply p.2
    linarith

/-- The finite part of the one-point accumulator sphere is homeomorphic to
the original affine accumulator space. -/
def accumulatorStereoHomeomorph :
    FinVector n ℝ ≃ₜ FiniteAccumulatorChart n where
  toFun := accumulatorStereoChart
  invFun := accumulatorChartCoordinate
  left_inv := accumulatorChartCoordinate_stereo
  right_inv := accumulatorStereo_chartCoordinate
  continuous_toFun := continuous_accumulatorStereoChart
  continuous_invFun := continuous_accumulatorChartCoordinate

end

end HGAS
