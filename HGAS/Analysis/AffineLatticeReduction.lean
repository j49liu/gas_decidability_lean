import HGAS.Analysis.QuadraticEscape
import Mathlib.Algebra.Order.Round
import Mathlib.Tactic

/-!
# Nearest-integer reduction along a fixed-height lattice

Let `γ > 0` and suppose that a vertical coordinate `r(t)` has nonzero
asymptotic slope:

```
                    r(t) = b t + O(1),       b ≠ 0.
```

Reduction modulo the vertical period `2 γ` uses the nearest integer

```
                    n(t) = round (r(t) / (2 γ)).
```

This file proves the two estimates used in the nonreal-Bloch argument:

* the reduced vertical coordinate `r(t) - 2 n(t) γ` stays in the compact
  interval `[-γ, γ]`;
* `n(t) = (b / (2 γ)) t + O(1)`.

The second estimate feeds directly into `affine_boundedError_quadratic_escape`.
The development is independent of theta functions and can be reused for
any fixed-height complex lattice.
-/

namespace HGAS.Analysis

open Filter

noncomputable section

/-- The integer used to reduce a real coordinate modulo the period `2 γ`. -/
def verticalLatticeIndex
    (γ : ℝ) (r : ℝ → ℝ) (t : ℝ) : ℤ :=
  round (r t / (2 * γ))

/-- The real coercion of `verticalLatticeIndex`, convenient in estimates. -/
def verticalLatticeIndexReal
    (γ : ℝ) (r : ℝ → ℝ) (t : ℝ) : ℝ :=
  verticalLatticeIndex γ r t

/-- Nearest-integer reduction leaves a remainder of size at most one half. -/
theorem abs_sub_verticalLatticeIndexReal_le_half
    (γ : ℝ) (r : ℝ → ℝ) (t : ℝ) :
    |r t / (2 * γ) -
        verticalLatticeIndexReal γ r t| ≤ (1 : ℝ) / 2 := by
  simpa [verticalLatticeIndexReal, verticalLatticeIndex] using
    (abs_sub_round (r t / (2 * γ)))

/-- The unreduced and reduced coordinates differ by an integer multiple of
`2 γ`, and the reduced coordinate lies in `[-γ, γ]`. -/
theorem abs_verticalLatticeRemainder_le
    {γ : ℝ} (hγ : 0 < γ)
    (r : ℝ → ℝ) (t : ℝ) :
    |r t -
        2 * verticalLatticeIndexReal γ r t * γ| ≤ γ := by
  have hround :=
    abs_sub_verticalLatticeIndexReal_le_half γ r t
  have hfactor :
      r t - 2 * verticalLatticeIndexReal γ r t * γ =
        (2 * γ) *
          (r t / (2 * γ) -
            verticalLatticeIndexReal γ r t) := by
    field_simp [hγ.ne']
  rw [hfactor, abs_mul, abs_of_pos (by positivity : 0 < 2 * γ)]
  nlinarith

/-- If `r(t) = b t + O(1)`, then its nearest-integer lattice index has
slope `b / (2 γ)`, with an explicit bounded error. -/
theorem verticalLatticeIndexReal_boundedError
    {γ b err : ℝ} (hγ : 0 < γ)
    {r : ℝ → ℝ}
    (hr :
      ∀ᶠ t in atTop,
        |r t - b * t| ≤ err) :
    ∀ᶠ t in atTop,
      |verticalLatticeIndexReal γ r t -
          (b / (2 * γ)) * t| ≤
        (1 : ℝ) / 2 + err / (2 * γ) := by
  filter_upwards [hr] with t ht
  have hround :=
    abs_sub_verticalLatticeIndexReal_le_half γ r t
  have hscaled :
      |r t / (2 * γ) -
          (b / (2 * γ)) * t| ≤
        err / (2 * γ) := by
    have hden : 0 < 2 * γ := by positivity
    have heq :
        r t / (2 * γ) -
            (b / (2 * γ)) * t =
          (r t - b * t) / (2 * γ) := by
      field_simp [hγ.ne']
    rw [heq, abs_div, abs_of_pos hden]
    exact (div_le_div_iff_of_pos_right hden).2 ht
  calc
    |verticalLatticeIndexReal γ r t -
        (b / (2 * γ)) * t| =
        |(verticalLatticeIndexReal γ r t -
            r t / (2 * γ)) +
          (r t / (2 * γ) -
            (b / (2 * γ)) * t)| := by
          congr 1
          ring
    _ ≤
        |verticalLatticeIndexReal γ r t -
            r t / (2 * γ)| +
          |r t / (2 * γ) -
            (b / (2 * γ)) * t| :=
      abs_add_le _ _
    _ ≤ (1 : ℝ) / 2 + err / (2 * γ) :=
      add_le_add (by simpa [abs_sub_comm] using hround) hscaled

/-- A ready-to-use composition: a nonzero vertical slope makes every
positive quadratic gain in the lattice index dominate arbitrary linear
losses. -/
theorem verticalLatticeIndex_quadratic_escape
    {γ b growth loss scale err : ℝ}
    (hγ : 0 < γ) (hb : b ≠ 0)
    (hgrowth : 0 < growth) (hloss : 0 ≤ loss)
    {r : ℝ → ℝ}
    (hr :
      ∀ᶠ t in atTop,
        |r t - b * t| ≤ err) :
    Tendsto
      (fun t : ℝ ↦
        growth *
            (verticalLatticeIndexReal γ r t) ^ 2 -
          loss * |verticalLatticeIndexReal γ r t| -
          scale * (1 + t))
      atTop atTop := by
  apply affine_boundedError_quadratic_escape
      (a := b / (2 * γ))
      (err := (1 : ℝ) / 2 + err / (2 * γ))
      (gamma := growth)
      (div_ne_zero hb (by positivity))
      hgrowth hloss
  exact verticalLatticeIndexReal_boundedError
    hγ hr

end

end HGAS.Analysis
