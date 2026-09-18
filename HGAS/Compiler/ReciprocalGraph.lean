import Mathlib.Tactic

/-!
# Polynomial dynamics for reciprocal graphs

To keep the compiled vector field polynomial, a rational factor
`(1-ηw)⁻¹` is represented by an extra state `g` and the residual

```
R = (1-ηw)g - 1.
```

When `ẇ` is already supplied by the source field, set

```
ġ = η ẇ g².
```

Formal differentiation then gives `Ṙ = η ẇ g R`; hence the zero-residual
graph is invariant.  This module proves that identity over an arbitrary
commutative ring, independently of any particular clock realization.
-/

namespace HGAS

variable {R : Type*} [CommRing R]

/-- Algebraic residual defining the reciprocal graph. -/
def reciprocalResidual (η w g : R) : R :=
  (1 - η * w) * g - 1

/-- Polynomial velocity assigned to the reciprocal state. -/
def reciprocalVelocity (η wdot g : R) : R :=
  η * wdot * g ^ 2

/-- Formal product-rule derivative of the reciprocal residual. -/
def reciprocalResidualVelocity
    (η w wdot g gdot : R) : R :=
  (-η * wdot) * g + (1 - η * w) * gdot

/-- The residual evolves multiplicatively under the chosen reciprocal
velocity.  In particular its zero set is tangent to the enlarged field. -/
theorem reciprocalResidualVelocity_eq_mul_residual
    (η w wdot g : R) :
    reciprocalResidualVelocity η w wdot g
        (reciprocalVelocity η wdot g) =
      η * wdot * g * reciprocalResidual η w g := by
  simp only [reciprocalResidualVelocity, reciprocalVelocity,
    reciprocalResidual]
  ring

/-- The defining graph equation is equivalent to a right inverse equation. -/
theorem reciprocalResidual_eq_zero_iff
    (η w g : R) :
    reciprocalResidual η w g = 0 ↔ (1 - η * w) * g = 1 := by
  simp only [reciprocalResidual, sub_eq_zero]

/-- Over a field, a nonzero denominator makes the reciprocal state unique. -/
theorem reciprocalResidual_eq_zero_iff_eq_inv
    {K : Type*} [Field K] (η w g : K)
    (hden : 1 - η * w ≠ 0) :
    reciprocalResidual η w g = 0 ↔
      g = (1 - η * w)⁻¹ := by
  rw [reciprocalResidual_eq_zero_iff]
  constructor
  · intro h
    calc
      g = 1 * g := by ring
      _ = ((1 - η * w)⁻¹ * (1 - η * w)) * g := by
        rw [inv_mul_cancel₀ hden]
      _ = (1 - η * w)⁻¹ * ((1 - η * w) * g) := by ring
      _ = (1 - η * w)⁻¹ := by rw [h]; ring
  · intro h
    rw [h]
    exact mul_inv_cancel₀ hden

/-- If the residual is initially zero, its formal derivative is zero. -/
theorem reciprocalResidualVelocity_eq_zero_of_residual
    (η w wdot g : R) (hres : reciprocalResidual η w g = 0) :
    reciprocalResidualVelocity η w wdot g
        (reciprocalVelocity η wdot g) = 0 := by
  rw [reciprocalResidualVelocity_eq_mul_residual, hres, mul_zero]

end HGAS
