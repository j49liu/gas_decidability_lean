import Mathlib.Tactic

/-!
# The binary quadratic Veronese lift

This file formalizes the smallest Veronese gadget used in the cubicization
argument.  In ordinary mathematical notation,

```
ν₂(x₁,x₂) = (x₁², x₁x₂, x₂²),
Q(y)      = y₂₀² + 2 y₁₁² + y₀₂²,
q(y)      = y₂₀ y₀₂ - y₁₁²,
W(y)      = q(y)².
```

The diagonal coefficients `(1,2,1)` in `Q` also define the weighted inner
product.  The corresponding gradient of `W` is

```
grad_Q W = (2 q y₀₂, -2 q y₁₁, 2 q y₂₀).
```

Most identities are proved over an arbitrary commutative ring.  This keeps
the algebraic part reusable over both `ℚ` (exact coefficient calculations)
and `ℝ` (the dynamical application).  The positivity statement at the end
is, naturally, specialized to `ℝ`.
-/

namespace HGAS.Veronese.BinaryQuadratic

/-- Coordinates `(y₂₀,y₁₁,y₀₂)` for binary quadratic forms.

The names record the exponent vectors of the monomials
`x₁²`, `x₁x₂`, and `x₂²`. -/
@[ext]
structure Coordinates (R : Type*) where
  y20 : R
  y11 : R
  y02 : R
deriving Repr

variable {R : Type*} [CommRing R]

/-- The origin in binary-quadratic coordinate space. -/
def origin : Coordinates R :=
  ⟨0, 0, 0⟩

/-- The unscaled degree-two Veronese map. -/
def veronese (x₁ x₂ : R) : Coordinates R :=
  ⟨x₁ ^ 2, x₁ * x₂, x₂ ^ 2⟩

/-- The multinomially weighted quadratic form
`y₂₀² + 2 y₁₁² + y₀₂²`. -/
def Q (y : Coordinates R) : R :=
  y.y20 ^ 2 + 2 * y.y11 ^ 2 + y.y02 ^ 2

/-- The single quadratic equation cutting out the binary Veronese cone. -/
def q (y : Coordinates R) : R :=
  y.y20 * y.y02 - y.y11 ^ 2

/-- The squared constraint energy `W = q²`. -/
def W (y : Coordinates R) : R :=
  q y ^ 2

/-- The inner product whose diagonal matrix is `(1,2,1)`.

Over `ℝ`, this is the positive-definite inner product associated with `Q`.
The definition over a general ring is the same polynomial expression. -/
def weightedInner (u v : Coordinates R) : R :=
  u.y20 * v.y20 + 2 * u.y11 * v.y11 + u.y02 * v.y02

/-- The formal directional differential of the cone equation `q`. -/
def dq (y h : Coordinates R) : R :=
  h.y20 * y.y02 + y.y20 * h.y02 - 2 * y.y11 * h.y11

/-- The formal directional differential of `W = q²`. -/
def dW (y h : Coordinates R) : R :=
  2 * q y * dq y h

/-- The gradient of `W` for the weighted metric `(1,2,1)`.

The middle coordinate is `-2 q y₁₁`, rather than the Euclidean coordinate
`-4 q y₁₁`, because the middle metric weight is two. -/
def weightedGradientW (y : Coordinates R) : Coordinates R :=
  ⟨2 * q y * y.y02, -2 * q y * y.y11, 2 * q y * y.y20⟩

/-- The differential of the degree-two Veronese map in direction
`(v₁,v₂)`. -/
def dVeronese (x₁ x₂ v₁ v₂ : R) : Coordinates R :=
  ⟨2 * x₁ * v₁, x₁ * v₂ + x₂ * v₁, 2 * x₂ * v₂⟩

/-- The tangential gradient formula used on the weighted unit sphere.

When `Q y = 1`, subtracting `4 W(y) y` removes the weighted radial
component, by Euler's identity below. -/
def tangentialGradientW (y : Coordinates R) : Coordinates R :=
  ⟨(weightedGradientW y).y20 - 4 * W y * y.y20,
   (weightedGradientW y).y11 - 4 * W y * y.y11,
   (weightedGradientW y).y02 - 4 * W y * y.y02⟩

@[simp]
theorem origin_y20 : (origin : Coordinates R).y20 = 0 :=
  rfl

@[simp]
theorem origin_y11 : (origin : Coordinates R).y11 = 0 :=
  rfl

@[simp]
theorem origin_y02 : (origin : Coordinates R).y02 = 0 :=
  rfl

@[simp]
theorem veronese_y20 (x₁ x₂ : R) : (veronese x₁ x₂).y20 = x₁ ^ 2 :=
  rfl

@[simp]
theorem veronese_y11 (x₁ x₂ : R) : (veronese x₁ x₂).y11 = x₁ * x₂ :=
  rfl

@[simp]
theorem veronese_y02 (x₁ x₂ : R) : (veronese x₁ x₂).y02 = x₂ ^ 2 :=
  rfl

/-- The multinomial normalization
`Q(ν₂(x)) = (x₁²+x₂²)²`. -/
@[simp]
theorem Q_veronese (x₁ x₂ : R) :
    Q (veronese x₁ x₂) = (x₁ ^ 2 + x₂ ^ 2) ^ 2 := by
  simp only [Q, veronese_y20, veronese_y11, veronese_y02]
  ring

/-- Every Veronese point satisfies the defining cone equation. -/
@[simp]
theorem q_veronese (x₁ x₂ : R) :
    q (veronese x₁ x₂) = 0 := by
  simp only [q, veronese_y20, veronese_y11, veronese_y02]
  ring

/-- The constraint energy vanishes on the Veronese cone. -/
@[simp]
theorem W_veronese (x₁ x₂ : R) :
    W (veronese x₁ x₂) = 0 := by
  simp [W]

/-- The weighted norm-square is exactly `Q`. -/
theorem weightedInner_self (y : Coordinates R) :
    weightedInner y y = Q y := by
  simp only [weightedInner, Q]
  ring

@[simp]
theorem weightedGradientW_y20 (y : Coordinates R) :
    (weightedGradientW y).y20 = 2 * q y * y.y02 :=
  rfl

@[simp]
theorem weightedGradientW_y11 (y : Coordinates R) :
    (weightedGradientW y).y11 = -2 * q y * y.y11 :=
  rfl

@[simp]
theorem weightedGradientW_y02 (y : Coordinates R) :
    (weightedGradientW y).y02 = 2 * q y * y.y20 :=
  rfl

/-- The displayed vector really represents the differential of `W` in the
weighted metric: `⟪grad_Q W,h⟫_Q = dW(h)`. -/
theorem weightedInner_gradientW (y h : Coordinates R) :
    weightedInner (weightedGradientW y) h = dW y h := by
  simp only [weightedInner, weightedGradientW_y20, weightedGradientW_y11,
    weightedGradientW_y02, dW, dq]
  ring

/-- The weighted gradient vanishes identically on the Veronese cone. -/
@[simp]
theorem weightedGradientW_veronese (x₁ x₂ : R) :
    weightedGradientW (veronese x₁ x₂) = origin := by
  ext <;> simp [weightedGradientW]

/-- Weighted Euler identity for the quartic polynomial `W`. -/
theorem weightedEuler_W (y : Coordinates R) :
    weightedInner y (weightedGradientW y) = 4 * W y := by
  simp only [weightedInner, weightedGradientW_y20, weightedGradientW_y11,
    weightedGradientW_y02, W, q]
  ring

/-- Exact weighted norm-square of the ambient gradient:
`‖grad_Q W‖_Q² = 4 W Q`. -/
theorem weightedGradientW_normSq (y : Coordinates R) :
    weightedInner (weightedGradientW y) (weightedGradientW y) =
      4 * W y * Q y := by
  simp only [weightedInner, weightedGradientW_y20, weightedGradientW_y11,
    weightedGradientW_y02, W, Q]
  ring

/-- The basic dot-product identity behind the lifted angular dynamics. -/
theorem weightedInner_veronese_dVeronese (x₁ x₂ v₁ v₂ : R) :
    weightedInner (veronese x₁ x₂) (dVeronese x₁ x₂ v₁ v₂) =
      2 * (x₁ ^ 2 + x₂ ^ 2) * (x₁ * v₁ + x₂ * v₂) := by
  simp only [weightedInner, veronese_y20, veronese_y11, veronese_y02,
    dVeronese]
  ring

/-- On the ordinary unit circle, the previous dot product reduces to
`2 (x₁v₁+x₂v₂)`, which is the `k=2` case of the paper's general identity. -/
theorem weightedInner_veronese_dVeronese_of_unit
    (x₁ x₂ v₁ v₂ : R) (hunit : x₁ ^ 2 + x₂ ^ 2 = 1) :
    weightedInner (veronese x₁ x₂) (dVeronese x₁ x₂ v₁ v₂) =
      2 * (x₁ * v₁ + x₂ * v₂) := by
  rw [weightedInner_veronese_dVeronese, hunit]
  ring

/-- Before imposing `Q y = 1`, the radial component of the proposed
tangential gradient is `4 W(y) (1-Q(y))`. -/
theorem weightedInner_self_tangentialGradientW (y : Coordinates R) :
    weightedInner y (tangentialGradientW y) =
      4 * W y * (1 - Q y) := by
  simp only [weightedInner, tangentialGradientW, weightedGradientW_y20,
    weightedGradientW_y11, weightedGradientW_y02, W, Q, q]
  ring

/-- On the weighted unit sphere, `tangentialGradientW` is orthogonal to the
radial direction. -/
theorem weightedInner_self_tangentialGradientW_of_unit
    (y : Coordinates R) (hunit : Q y = 1) :
    weightedInner y (tangentialGradientW y) = 0 := by
  rw [weightedInner_self_tangentialGradientW, hunit]
  ring

/-- Expansion of the tangential-gradient norm before restricting to the
weighted unit sphere. -/
theorem tangentialGradientW_normSq (y : Coordinates R) :
    weightedInner (tangentialGradientW y) (tangentialGradientW y) =
      weightedInner (weightedGradientW y) (weightedGradientW y) -
        8 * W y * weightedInner y (weightedGradientW y) +
        16 * W y ^ 2 * Q y := by
  simp only [weightedInner, tangentialGradientW, weightedGradientW_y20,
    weightedGradientW_y11, weightedGradientW_y02, W, Q, q]
  ring

/-- On `Q y = 1`, the standard identity
`‖grad_{S_Q} W‖_Q² = ‖grad_Q W‖_Q² - 16 W²`. -/
theorem tangentialGradientW_normSq_of_unit
    (y : Coordinates R) (hunit : Q y = 1) :
    weightedInner (tangentialGradientW y) (tangentialGradientW y) =
      weightedInner (weightedGradientW y) (weightedGradientW y) -
        16 * W y ^ 2 := by
  rw [tangentialGradientW_normSq, weightedEuler_W, hunit]
  ring

/-- In this binary example the spherical dissipation has the particularly
simple closed form `4W-16W²`. -/
theorem tangentialGradientW_normSq_of_unit_eq
    (y : Coordinates R) (hunit : Q y = 1) :
    weightedInner (tangentialGradientW y) (tangentialGradientW y) =
      4 * W y - 16 * W y ^ 2 := by
  rw [tangentialGradientW_normSq_of_unit y hunit,
    weightedGradientW_normSq, hunit]
  ring

/-- Over the reals, the multinomial form `Q` is nonnegative. -/
theorem Q_nonneg (y : Coordinates ℝ) : 0 ≤ Q y := by
  simp only [Q]
  positivity

end HGAS.Veronese.BinaryQuadratic
