import HGAS.Analysis.AffineLatticeReduction
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Canonical reduction in a fixed-height complex level-two lattice

For a curve of complex lattice parameters `τ(t)` with
`Im τ(t)=γ>0` and an arbitrary complex curve `ξ(t)`, this file constructs
the two nearest-integer indices

```
n(t) = round (Im ξ(t) / (2γ)),
m(t) = round (Re (ξ(t)-2n(t)τ(t)) / 2)
```

and the reduced elliptic coordinate

```
ξ₀(t) = ξ(t) - 2m(t) - 2n(t)τ(t).
```

The construction is canonical and gives, pointwise,

```
ξ = ξ₀ + 2m + 2nτ,
|Re ξ₀| ≤ 1,
|Im ξ₀| ≤ γ.
```

It is independent of theta functions and isolates all lattice
bookkeeping needed by the nonreal-Bloch escape proof.
-/

namespace HGAS.Analysis

open Complex

noncomputable section

/-- Canonical vertical level-two index of a complex curve. -/
def complexLevelTwoVerticalIndex
    (γ : ℝ) (ξ : ℝ → ℂ) (t : ℝ) : ℤ :=
  verticalLatticeIndex γ (fun s ↦ (ξ s).im) t

/-- Canonical horizontal index after subtracting the vertical period. -/
def complexLevelTwoHorizontalIndex
    (γ : ℝ) (ξ τ : ℝ → ℂ) (t : ℝ) : ℤ :=
  round
    (((ξ t -
        2 * (complexLevelTwoVerticalIndex γ ξ t : ℂ) *
          τ t).re) / 2)

/-- Canonically reduced elliptic coordinate. -/
def complexLevelTwoReducedCoordinate
    (γ : ℝ) (ξ τ : ℝ → ℂ) (t : ℝ) : ℂ :=
  ξ t -
    2 * (complexLevelTwoHorizontalIndex γ ξ τ t : ℂ) -
    2 * (complexLevelTwoVerticalIndex γ ξ t : ℂ) * τ t

/-- Exact reconstruction from the reduced coordinate and the two
level-two lattice indices. -/
theorem complexLevelTwo_decomposition
    (γ : ℝ) (ξ τ : ℝ → ℂ) (t : ℝ) :
    ξ t =
      complexLevelTwoReducedCoordinate γ ξ τ t +
        2 * (complexLevelTwoHorizontalIndex γ ξ τ t : ℂ) +
        2 * (complexLevelTwoVerticalIndex γ ξ t : ℂ) *
          τ t := by
  unfold complexLevelTwoReducedCoordinate
  ring

/-- The real part of the canonical elliptic representative lies in
`[-1,1]`. -/
theorem abs_complexLevelTwoReducedCoordinate_re_le_one
    (γ : ℝ) (ξ τ : ℝ → ℂ) (t : ℝ) :
    |(complexLevelTwoReducedCoordinate γ ξ τ t).re| ≤ 1 := by
  let r : ℝ :=
    (ξ t -
      2 * (complexLevelTwoVerticalIndex γ ξ t : ℂ) *
        τ t).re
  have hround :
      |r / 2 - (round (r / 2) : ℝ)| ≤ (1 : ℝ) / 2 :=
    abs_sub_round (r / 2)
  have hre :
      (complexLevelTwoReducedCoordinate γ ξ τ t).re =
        r - 2 * (round (r / 2) : ℝ) := by
    unfold complexLevelTwoReducedCoordinate
      complexLevelTwoHorizontalIndex
    dsimp only [r]
    simp only [sub_re, mul_re, re_ofNat, im_ofNat,
      intCast_re, intCast_im, zero_mul, sub_zero]
    ring
  rw [hre]
  have hfactor :
      r - 2 * (round (r / 2) : ℝ) =
        2 * (r / 2 - (round (r / 2) : ℝ)) := by
    ring
  rw [hfactor, abs_mul, abs_of_nonneg
    (show (0 : ℝ) ≤ 2 by norm_num)]
  nlinarith

/-- The imaginary part of the canonical elliptic representative lies in
`[-γ,γ]` whenever `τ` has the fixed positive height `γ`. -/
theorem abs_complexLevelTwoReducedCoordinate_im_le
    {γ : ℝ} (hγ : 0 < γ)
    (ξ τ : ℝ → ℂ)
    (hτim : ∀ t, (τ t).im = γ)
    (t : ℝ) :
    |(complexLevelTwoReducedCoordinate γ ξ τ t).im| ≤ γ := by
  have hrem :=
    abs_verticalLatticeRemainder_le
      hγ (fun s ↦ (ξ s).im) t
  have him :
      (complexLevelTwoReducedCoordinate γ ξ τ t).im =
        (ξ t).im -
          2 *
            (complexLevelTwoVerticalIndex γ ξ t : ℝ) *
            γ := by
    unfold complexLevelTwoReducedCoordinate
      complexLevelTwoHorizontalIndex
      complexLevelTwoVerticalIndex
    simp only [sub_im, mul_im, re_ofNat, intCast_re,
      im_ofNat, intCast_im, zero_mul, add_zero,
      hτim t]
    simp only [mul_re, re_ofNat, im_ofNat,
      intCast_re, intCast_im, zero_mul, sub_zero]
    ring
  rw [him]
  simpa only [verticalLatticeIndexReal] using hrem

end

end HGAS.Analysis
