import HGAS.Compactification.CentralSphere
import Mathlib.Tactic

/-!
# The positive central chart of affine Euclidean space

For an affine point `z : ℝⁿ`, its positive central compactification is

```text
        x = z / sqrt (1 + ‖z‖²),
        w = 1 / sqrt (1 + ‖z‖²).
```

Thus `‖x‖² + w² = 1`, the chart coordinate `x / w` is exactly `z`,
and `w` is positive.  This file packages that elementary construction
as a point of `FiniteCentralChart`.

The final two theorems are quantitative: if `‖z‖² ≤ B`, then both `w`
and `w²` have explicit positive lower bounds depending only on `B`.
They are useful whenever a bounded affine orbit must be kept uniformly
away from the central equator.
-/

noncomputable section

namespace HGAS

variable {n : ℕ}

/-- The positive normalizing scalar for central compactification. -/
def positiveCentralScale (z : FinVector n ℝ) : ℝ :=
  (Real.sqrt (1 + normSq z))⁻¹

theorem one_add_normSq_pos (z : FinVector n ℝ) :
    0 < 1 + normSq z := by
  linarith [normSq_nonneg z]

theorem positiveCentralScale_pos (z : FinVector n ℝ) :
    0 < positiveCentralScale z := by
  exact inv_pos.mpr (Real.sqrt_pos.2 (one_add_normSq_pos z))

theorem positiveCentralScale_ne_zero (z : FinVector n ℝ) :
    positiveCentralScale z ≠ 0 :=
  (positiveCentralScale_pos z).ne'

theorem positiveCentralScale_sq_mul (z : FinVector n ℝ) :
    positiveCentralScale z ^ 2 * (1 + normSq z) = 1 := by
  have hsqrt :
      Real.sqrt (1 + normSq z) ^ 2 = 1 + normSq z :=
    Real.sq_sqrt (one_add_normSq_pos z).le
  have hsqrt_ne :
      Real.sqrt (1 + normSq z) ≠ 0 :=
    (Real.sqrt_pos.2 (one_add_normSq_pos z)).ne'
  unfold positiveCentralScale
  rw [← hsqrt]
  rw [← mul_pow]
  simp [hsqrt_ne]

/-- The canonical positive point of the finite central chart. -/
def positiveCentralChartPoint
    (z : FinVector n ℝ) :
    FiniteCentralChart n := by
  let w := positiveCentralScale z
  let x : FinVector n ℝ := w • z
  refine ⟨⟨(x, w), ?_⟩, ?_⟩
  · rw [show normSq x = w ^ 2 * normSq z by
      exact normSq_smul w z]
    have h := positiveCentralScale_sq_mul z
    dsimp only [w] at h ⊢
    nlinarith
  · exact positiveCentralScale_ne_zero z

@[simp]
theorem positiveCentralChartPoint_x
    (z : FinVector n ℝ) :
    (positiveCentralChartPoint z).1.1.1 =
      positiveCentralScale z • z :=
  rfl

@[simp]
theorem positiveCentralChartPoint_w
    (z : FinVector n ℝ) :
    (positiveCentralChartPoint z).1.1.2 =
      positiveCentralScale z :=
  rfl

/-- Passing to the positive central chart and then dividing by its weight
recovers the original affine point exactly. -/
@[simp]
theorem centralChartCoordinate_positiveCentralChartPoint
    (z : FinVector n ℝ) :
    centralChartCoordinate (positiveCentralChartPoint z) = z := by
  funext i
  simp only [centralChartCoordinate, positiveCentralChartPoint_x,
    positiveCentralChartPoint_w, Pi.smul_apply, smul_eq_mul]
  field_simp [positiveCentralScale_ne_zero z]

/-- Exact squared-weight formula. -/
theorem positiveCentralChartPoint_w_sq
    (z : FinVector n ℝ) :
    (positiveCentralChartPoint z).1.1.2 ^ 2 =
      (1 + normSq z)⁻¹ := by
  rw [positiveCentralChartPoint_w]
  have hden : 1 + normSq z ≠ 0 :=
    (one_add_normSq_pos z).ne'
  exact
    (mul_eq_one_iff_eq_inv₀ hden).mp
      (positiveCentralScale_sq_mul z)

/-- Explicit lower bound for the positive central weight of any point in
the squared ball of radius bound `B`. -/
def positiveCentralWeightLowerBound (B : ℝ) : ℝ :=
  (Real.sqrt (1 + B))⁻¹

theorem positiveCentralWeightLowerBound_pos
    {B : ℝ} (hB : 0 ≤ B) :
    0 < positiveCentralWeightLowerBound B := by
  unfold positiveCentralWeightLowerBound
  exact inv_pos.mpr (Real.sqrt_pos.2 (by linarith))

theorem positiveCentralWeightLowerBound_le
    {B : ℝ} (hB : 0 ≤ B)
    (z : FinVector n ℝ)
    (hz : normSq z ≤ B) :
    positiveCentralWeightLowerBound B ≤
      (positiveCentralChartPoint z).1.1.2 := by
  rw [positiveCentralChartPoint_w]
  unfold positiveCentralWeightLowerBound positiveCentralScale
  apply
    (inv_le_inv₀
      (Real.sqrt_pos.2 (by linarith))
      (Real.sqrt_pos.2 (one_add_normSq_pos z))).2
  exact Real.sqrt_le_sqrt (by linarith)

/-- The corresponding explicit lower bound for the squared chart weight.
This is the form used by the one-block central-weight product. -/
def positiveCentralWeightSqLowerBound (B : ℝ) : ℝ :=
  (1 + B)⁻¹

theorem positiveCentralWeightSqLowerBound_pos
    {B : ℝ} (hB : 0 ≤ B) :
    0 < positiveCentralWeightSqLowerBound B := by
  unfold positiveCentralWeightSqLowerBound
  exact inv_pos.mpr (by
    linarith)

theorem positiveCentralWeightSqLowerBound_le
    {B : ℝ} (hB : 0 ≤ B)
    (z : FinVector n ℝ)
    (hz : normSq z ≤ B) :
    positiveCentralWeightSqLowerBound B ≤
      (positiveCentralChartPoint z).1.1.2 ^ 2 := by
  rw [positiveCentralChartPoint_w_sq]
  unfold positiveCentralWeightSqLowerBound
  exact
    (inv_le_inv₀
      (by linarith : 0 < 1 + B)
      (one_add_normSq_pos z)).2
      (by linarith)

end HGAS
