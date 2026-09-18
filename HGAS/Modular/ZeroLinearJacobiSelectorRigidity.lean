import Mathlib.Tactic

/-!
# Rigidity of the Jacobi selector when the linear clock vanishes

## Legacy routing warning

This module is outside the public `HGAS.lean` import closure and is not
used by the completed endpoint.  Its algebraic lemmas are correct under
their explicit scalar hypotheses, but the raw three-moment equations at
`ρ = 0` do not in general justify those hypotheses: the manuscript gives
an explicit counterexample.  The live reduction instead augments every
DQL column to make the clock ratio irrational and uses
`JacobiThreeMomentTargetRigidity`.

When the linear DQL character is nonzero, the usual three-row Jacobi
selector uses an irrational clock ratio to isolate one resonant
coefficient in each row.  That argument does not apply when the entire
linear column is zero: the ratio is `ρ = 0`, and the `+1` row retains both
indices `n = 1` and `n = -1`.

The degeneration is nevertheless harmless after correcting the target
constant from `λ` to `2λ`.  Once the mean row has normalized the common
amplitude to `D = 1`, write `B ≠ 0` for the remaining elliptic multiplier.
The two resonant coefficients in the first row are

```text
                         λ B,       λ B⁻¹.
```

The corrected moment equation is therefore

```text
                       λ (B + B⁻¹) = 2 λ.
```

Since `λ ≠ 0`, this says `B + B⁻¹ = 2`, hence
`(B - 1)² = 0` and `B = 1`.  Thus the zero-linear case still rigidly
selects the canonical trace; it needs conditional centering, not an
additional clock or moment.

This file retains the conditional algebraic argument for audit history.
-/

noncomputable section

namespace HGAS.Modular

/-- A nonzero complex number with `B + B⁻¹ = 2` must equal one. -/
theorem eq_one_of_add_inv_eq_two
    {B : ℂ} (hB : B ≠ 0)
    (h : B + B⁻¹ = 2) :
    B = 1 := by
  have hinv : B⁻¹ * B = 1 :=
    inv_mul_cancel₀ hB
  have hsquare : (B - 1) ^ 2 = 0 := by
    calc
      (B - 1) ^ 2 =
          (B + B⁻¹) * B - 2 * B := by
        rw [pow_two]
        rw [add_mul, hinv]
        ring
      _ = 0 := by rw [h]; ring
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)

/-- The scalar equations supplied by the mean row and the corrected
two-resonance first row in the zero-linear case. -/
def ZeroLinearSelectorEquations
    (lambda : ℂ) (D B : ℂ) : Prop :=
  D = 1 ∧
    D * lambda * (B + B⁻¹) = 2 * lambda

/-- The corrected zero-linear selector equations are equivalent to the
canonical amplitude and multiplier. -/
theorem zeroLinearSelectorEquations_iff
    {lambda D B : ℂ}
    (hlambda : lambda ≠ 0)
    (hB : B ≠ 0) :
    ZeroLinearSelectorEquations lambda D B ↔
      D = 1 ∧ B = 1 := by
  constructor
  · rintro ⟨hD, hfirst⟩
    refine ⟨hD, ?_⟩
    subst D
    have hsum :
        B + B⁻¹ = 2 := by
      apply mul_left_cancel₀ hlambda
      calc
        lambda * (B + B⁻¹) =
            1 * lambda * (B + B⁻¹) := by ring
        _ = 2 * lambda := hfirst
        _ = lambda * 2 := by ring
    exact eq_one_of_add_inv_eq_two hB hsum
  · rintro ⟨rfl, rfl⟩
    constructor
    · rfl
    · norm_num
      ring

end HGAS.Modular
