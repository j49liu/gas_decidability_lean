import HGAS.Algebra.FiniteEuclidean
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

/-!
# Central compactification of one affine vector block

For an affine block `z ∈ ℝⁿ`, introduce sphere coordinates

```
z = x / w,                     ‖x‖² + w² = 1.
```

If the affine velocity is `p` and the common nonnegative slowdown is `f`,
the compactified equations used in the reduction are

```
x' = f w (p - (x · p) x),
w' = -f w² (x · p).
```

This file proves the pointwise facts on which the multi-block construction
rests:

* the field is tangent to the sphere;
* the equator `w = 0` is fixed in this block;
* in either chart `w ≠ 0`, differentiating `z = x/w` gives exactly
  `z' = f p`;
* the same quotient identity holds along differentiable trajectories.

The polynomial denominator-clearing compiler will instantiate `p` with the
cleared evaluation of an affine polynomial field.  The results here do not
depend on that syntax and are reusable for any velocity.
-/

namespace HGAS

open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-- Vector component of the central compactification field. -/
def centralCompactXField
    (f w : ℝ) (x p : FinVector n ℝ) :
    FinVector n ℝ :=
  fun i ↦ f * w * (p i - dot x p * x i)

/-- Scalar chart-coordinate component of the central compactification
field. -/
def centralCompactWField
    (f w : ℝ) (x p : FinVector n ℝ) : ℝ :=
  -f * w ^ 2 * dot x p

/-- The central compactification is tangent to the unit sphere.  The left
side is one half of the derivative of `‖x‖² + w²`. -/
theorem centralCompact_tangent
    (f w : ℝ) (x p : FinVector n ℝ)
    (hsphere : normSq x + w ^ 2 = 1) :
    dot x (centralCompactXField f w x p) +
      w * centralCompactWField f w x p = 0 := by
  simp only [dot, centralCompactXField,
    centralCompactWField, normSq] at *
  rw [Finset.sum_congr rfl (fun i _ ↦ by
    change
      x i * (f * w *
        (p i - (∑ j, x j * p j) * x i)) =
      f * w * (x i * p i) -
        f * w * (∑ j, x j * p j) * (x i * x i)
    ring)]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]
  calc
    f * w * (∑ i, x i * p i) -
          f * w * (∑ j, x j * p j) *
            (∑ i, x i * x i) +
        w * (-f * w ^ 2 * ∑ i, x i * p i) =
      f * w * (∑ i, x i * p i) *
        (1 - ((∑ i, x i * x i) + w ^ 2)) := by ring
    _ = 0 := by rw [hsphere]; ring

/-- Every point of the equator is stationary in this affine block,
independently of the displayed affine velocity. -/
@[simp]
theorem centralCompactXField_at_equator
    (f : ℝ) (x p : FinVector n ℝ) :
    centralCompactXField f 0 x p = 0 := by
  funext i
  simp [centralCompactXField]

@[simp]
theorem centralCompactWField_at_equator
    (f : ℝ) (x p : FinVector n ℝ) :
    centralCompactWField f 0 x p = 0 := by
  simp [centralCompactWField]

/-- Quotient-rule identity: in every nonzero central chart, the compact
field pushes forward to the slowed affine velocity `f p`. -/
theorem centralChartFieldDerivative_eq
    (f w : ℝ) (x p : FinVector n ℝ)
    (hw : w ≠ 0) (i : Fin n) :
    (centralCompactXField f w x p i * w -
        x i * centralCompactWField f w x p) /
        w ^ 2 =
      f * p i := by
  simp only [centralCompactXField, centralCompactWField]
  field_simp [hw]
  ring

/-- The algebraic sphere carrying one centrally compactified block. -/
abbrev CentralSphere (n : ℕ) :=
  {p : FinVector n ℝ × ℝ // normSq p.1 + p.2 ^ 2 = 1}

/-- Either finite central chart, with no sign choice imposed. -/
abbrev FiniteCentralChart (n : ℕ) :=
  {p : CentralSphere n // p.1.2 ≠ 0}

/-- Affine coordinate `z = x/w` on the union of the two finite central
charts. -/
def centralChartCoordinate
    (q : FiniteCentralChart n) :
    FinVector n ℝ :=
  fun i ↦ q.1.1.1 i / q.1.1.2

/-- The central chart coordinate is continuous. -/
theorem continuous_centralChartCoordinate :
    Continuous
      (centralChartCoordinate :
        FiniteCentralChart n → FinVector n ℝ) := by
  apply continuous_pi
  intro i
  unfold centralChartCoordinate
  apply Continuous.div
  · fun_prop
  · fun_prop
  · exact fun q ↦ q.2

/-- Along any differentiable central-compactification trajectory staying
in a finite chart, its affine coordinate has derivative `f p`. -/
theorem centralChartCoordinate_hasDerivAt
    (q : ℝ → FiniteCentralChart n)
    (f : ℝ → ℝ)
    (p : ℝ → FinVector n ℝ)
    (t : ℝ)
    (hX :
      ∀ i,
        HasDerivAt
          (fun s ↦ (q s).1.1.1 i)
          (centralCompactXField
            (f t) (q t).1.1.2 (q t).1.1.1 (p t) i) t)
    (hW :
      HasDerivAt
        (fun s ↦ (q s).1.1.2)
        (centralCompactWField
          (f t) (q t).1.1.2 (q t).1.1.1 (p t)) t) :
    ∀ i,
      HasDerivAt
        (fun s ↦ centralChartCoordinate (q s) i)
        (f t * p t i) t := by
  intro i
  have hquot := (hX i).div hW (q t).2
  change
    HasDerivAt
      (fun s ↦ (q s).1.1.1 i / (q s).1.1.2)
      (f t * p t i) t
  rw [← centralChartFieldDerivative_eq
    (f t) (q t).1.1.2 (q t).1.1.1 (p t)
    (q t).2 i]
  exact hquot

end

end HGAS
