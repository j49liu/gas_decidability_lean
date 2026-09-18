import HGAS.Compactification.CentralSphere
import Mathlib.Tactic

/-!
# Multi-block central compactification

The affine source in the reduction is a finite product of vector blocks of
possibly different dimensions.  Every block gets its own central sphere
coordinate `(x_b,w_b)`, while all blocks share one slowdown `f`.

This module packages the coordinatewise construction.  It proves sphere
tangency and, on the product of nonzero charts, the simultaneous identity

```
z_b' = f p_b
```

for every block and every coordinate.  Because the statement uses a
dependent dimension family `dims : Fin k → ℕ`, it can be reused without
padding all affine blocks to the same size.
-/

namespace HGAS

noncomputable section

variable {k : ℕ} {dims : Fin k → ℕ}

/-- A family of affine vectors with one dimension for each block. -/
abbrev BlockVector (dims : Fin k → ℕ) :=
  ∀ b : Fin k, FinVector (dims b) ℝ

/-- Vector components of the multi-block central compactification. -/
def centralProductXField
    (f : ℝ) (w : Fin k → ℝ)
    (x p : BlockVector dims) :
    BlockVector dims :=
  fun b ↦ centralCompactXField f (w b) (x b) (p b)

/-- Scalar chart components of the multi-block central compactification. -/
def centralProductWField
    (f : ℝ) (w : Fin k → ℝ)
    (x p : BlockVector dims) :
    Fin k → ℝ :=
  fun b ↦ centralCompactWField f (w b) (x b) (p b)

/-- Every block sphere is tangent to the common-time compactified field. -/
theorem centralProduct_tangent
    (f : ℝ) (w : Fin k → ℝ)
    (x p : BlockVector dims)
    (hsphere :
      ∀ b, normSq (x b) + w b ^ 2 = 1) :
    ∀ b,
      dot (x b) (centralProductXField f w x p b) +
        w b * centralProductWField f w x p b = 0 := by
  intro b
  exact centralCompact_tangent
    f (w b) (x b) (p b) (hsphere b)

/-- An equator in one block is invariant even when all other blocks keep
moving. -/
theorem centralProduct_equator_fixed_block
    (f : ℝ) (w : Fin k → ℝ)
    (x p : BlockVector dims)
    (b : Fin k) (hb : w b = 0) :
    centralProductXField f w x p b = 0 ∧
      centralProductWField f w x p b = 0 := by
  constructor
  · change centralCompactXField f (w b) (x b) (p b) = 0
    rw [hb]
    exact centralCompactXField_at_equator f (x b) (p b)
  · change centralCompactWField f (w b) (x b) (p b) = 0
    rw [hb]
    exact centralCompactWField_at_equator f (x b) (p b)

/-- Product of the algebraic central spheres. -/
abbrev CentralProductSphere (dims : Fin k → ℕ) :=
  {q : BlockVector dims × (Fin k → ℝ) //
    ∀ b, normSq (q.1 b) + q.2 b ^ 2 = 1}

/-- The union of all `2^k` open sign charts. -/
abbrev FiniteCentralProductChart (dims : Fin k → ℕ) :=
  {q : CentralProductSphere dims // ∀ b, q.1.2 b ≠ 0}

/-- Simultaneous affine coordinates `z_b=x_b/w_b`. -/
def centralProductChartCoordinate
    (q : FiniteCentralProductChart dims) :
    BlockVector dims :=
  fun b i ↦ q.1.1.1 b i / q.1.1.2 b

/-- The simultaneous chart map is continuous. -/
theorem continuous_centralProductChartCoordinate :
    Continuous
      (centralProductChartCoordinate :
        FiniteCentralProductChart dims → BlockVector dims) := by
  apply continuous_pi
  intro b
  apply continuous_pi
  intro i
  unfold centralProductChartCoordinate
  apply Continuous.div
  · fun_prop
  · fun_prop
  · exact fun q ↦ q.2 b

/-- Pointwise quotient-rule identity in every block. -/
theorem centralProductChartFieldDerivative_eq
    (f : ℝ) (w : Fin k → ℝ)
    (x p : BlockVector dims)
    (hw : ∀ b, w b ≠ 0)
    (b : Fin k) (i : Fin (dims b)) :
    (centralProductXField f w x p b i * w b -
        x b i * centralProductWField f w x p b) /
        (w b) ^ 2 =
      f * p b i := by
  exact centralChartFieldDerivative_eq
    f (w b) (x b) (p b) (hw b) i

/-- Along a differentiable trajectory in the finite product chart, every
affine coordinate has derivative `f p_b`. -/
theorem centralProductChartCoordinate_hasDerivAt
    (q : ℝ → FiniteCentralProductChart dims)
    (f : ℝ → ℝ)
    (p : ℝ → BlockVector dims)
    (t : ℝ)
    (hX :
      ∀ b i,
        HasDerivAt
          (fun s ↦ (q s).1.1.1 b i)
          (centralProductXField
            (f t) (q t).1.1.2 (q t).1.1.1 (p t) b i) t)
    (hW :
      ∀ b,
        HasDerivAt
          (fun s ↦ (q s).1.1.2 b)
          (centralProductWField
            (f t) (q t).1.1.2 (q t).1.1.1 (p t) b) t) :
    ∀ b i,
      HasDerivAt
        (fun s ↦ centralProductChartCoordinate (q s) b i)
        (f t * p t b i) t := by
  intro b i
  have hquot := (hX b i).div (hW b) ((q t).2 b)
  change
    HasDerivAt
      (fun s ↦ (q s).1.1.1 b i / (q s).1.1.2 b)
      (f t * p t b i) t
  rw [← centralProductChartFieldDerivative_eq
    (f t) (q t).1.1.2 (q t).1.1.1 (p t)
    (q t).2 b i]
  exact hquot

end

end HGAS
