import HGAS.Compactification.PositiveCentralChart
import HGAS.Compactification.StereographicTrajectory
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Differentiating the positive central compactification

For a differentiable affine curve `z(t)` with velocity `f(t) p(t)`, the
positive central lift

```text
  w = (1 + ‖z‖²)^(-1/2),       x = w z
```

solves the central compactification equations with the same scalar speed
`f`.  This is the forward counterpart of
`centralChartCoordinate_hasDerivAt`: that earlier theorem recovers an
affine trajectory from a finite central chart, while this file lifts an
affine trajectory into the positive chart.
-/

noncomputable section

namespace HGAS

variable {n : ℕ}

/-- Derivative of the positive central scale along a coordinatewise
differentiable affine curve. -/
theorem positiveCentralScale_hasDerivAt
    (z p : ℝ → FinVector n ℝ)
    (f : ℝ → ℝ)
    (t : ℝ)
    (hz :
      ∀ i,
        HasDerivAt
          (fun s ↦ z s i)
          (f t * p t i) t) :
    HasDerivAt
      (fun s ↦ positiveCentralScale (z s))
      (-f t * positiveCentralScale (z t) ^ 3 *
        dot (z t) (p t)) t := by
  let g : ℝ → FinVector n ℝ :=
    fun s ↦ f s • p s
  have hnorm :=
    normSq_hasDerivAt_of_coordinates z g t (by
      intro i
      simpa only [g, Pi.smul_apply, smul_eq_mul] using hz i)
  have hN :
      HasDerivAt
        (fun s ↦ 1 + normSq (z s))
        (2 * dot (z t) (g t)) t :=
    hnorm.const_add 1
  have hNpos : 0 < 1 + normSq (z t) :=
    one_add_normSq_pos (z t)
  have hsqrt :
      HasDerivAt
        (fun s ↦ Real.sqrt (1 + normSq (z s)))
        ((1 / (2 * Real.sqrt (1 + normSq (z t)))) *
          (2 * dot (z t) (g t))) t :=
    (Real.hasDerivAt_sqrt hNpos.ne').comp t hN
  have hsqrtNe :
      Real.sqrt (1 + normSq (z t)) ≠ 0 :=
    (Real.sqrt_pos.2 hNpos).ne'
  have hinv := hsqrt.inv hsqrtNe
  convert hinv using 1
  have hdot :
      dot (z t) (g t) =
        f t * dot (z t) (p t) := by
    unfold g dot
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold positiveCentralScale
  rw [hdot]
  field_simp [hsqrtNe]

/-- The lifted old coordinates satisfy the central `x` equation. -/
theorem positiveCentralChartPoint_x_hasDerivAt
    (z p : ℝ → FinVector n ℝ)
    (f : ℝ → ℝ)
    (t : ℝ)
    (hz :
      ∀ i,
        HasDerivAt
          (fun s ↦ z s i)
          (f t * p t i) t) :
    ∀ i,
      HasDerivAt
        (fun s ↦
          (positiveCentralChartPoint (z s)).1.1.1 i)
        (centralCompactXField
          (f t)
          (positiveCentralChartPoint (z t)).1.1.2
          (positiveCentralChartPoint (z t)).1.1.1
          (p t) i) t := by
  intro i
  have hw :=
    positiveCentralScale_hasDerivAt z p f t hz
  have hmul := hw.mul (hz i)
  have hscaleSq :=
    positiveCentralScale_sq_mul (z t)
  convert hmul using 1
  simp only [positiveCentralChartPoint_x,
    positiveCentralChartPoint_w, centralCompactXField,
    Pi.smul_apply, smul_eq_mul]
  have hdot :
      dot (positiveCentralScale (z t) • z t) (p t) =
        positiveCentralScale (z t) * dot (z t) (p t) := by
    unfold dot
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hdot]
  nlinarith

/-- The lifted chart weight satisfies the central `w` equation. -/
theorem positiveCentralChartPoint_w_hasDerivAt
    (z p : ℝ → FinVector n ℝ)
    (f : ℝ → ℝ)
    (t : ℝ)
    (hz :
      ∀ i,
        HasDerivAt
          (fun s ↦ z s i)
          (f t * p t i) t) :
    HasDerivAt
      (fun s ↦
        (positiveCentralChartPoint (z s)).1.1.2)
      (centralCompactWField
        (f t)
        (positiveCentralChartPoint (z t)).1.1.2
        (positiveCentralChartPoint (z t)).1.1.1
        (p t)) t := by
  have hw :=
    positiveCentralScale_hasDerivAt z p f t hz
  convert hw using 1
  simp only [positiveCentralChartPoint_x,
    positiveCentralChartPoint_w, centralCompactWField]
  have hdot :
      dot (positiveCentralScale (z t) • z t) (p t) =
        positiveCentralScale (z t) * dot (z t) (p t) := by
    unfold dot
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hdot]
  ring

end HGAS
