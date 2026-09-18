import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Tactic

/-!
# The three even Jacobi theta constants

This file fixes the theta conventions used by the unary modular block.
For `τ` in the upper half-plane we put

```
θ₂(τ) = ∑ n : ℤ, exp (π i (n + 1/2)² τ),
θ₃(τ) = ∑ n : ℤ, exp (π i n² τ),
θ₄(τ) = ∑ n : ℤ, (-1)ⁿ exp (π i n² τ).
```

Their fourth powers are denoted `H₂`, `H₃`, and `H₄`.  The last six
theorems identify these series with specializations of Mathlib's
two-variable `jacobiTheta₂`; this gives us Mathlib's convergence,
holomorphy, and functional-equation infrastructure without changing the
normalization used in the paper.

The definitions and specialization calculation follow the formal
development in the `Sphere-Packing-Lean` project, adapted here to
Mathlib 4.30 and the namespace of this formalization.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I
open Complex Real
open scoped Real

noncomputable section

/-- The `n`th summand of the second even theta constant. -/
def theta₂Term (n : ℤ) (τ : ℍ) : ℂ :=
  cexp (π * I * (n + 1 / 2 : ℂ) ^ 2 * τ)

/-- The `n`th summand of the third even theta constant. -/
def theta₃Term (n : ℤ) (τ : ℍ) : ℂ :=
  cexp (π * I * (n : ℂ) ^ 2 * τ)

/-- The `n`th summand of the fourth even theta constant. -/
def theta₄Term (n : ℤ) (τ : ℍ) : ℂ :=
  (-1) ^ n * cexp (π * I * (n : ℂ) ^ 2 * τ)

/-- Jacobi's second even theta constant. -/
def theta₂ (τ : ℍ) : ℂ :=
  ∑' n : ℤ, theta₂Term n τ

/-- Jacobi's third even theta constant. -/
def theta₃ (τ : ℍ) : ℂ :=
  ∑' n : ℤ, theta₃Term n τ

/-- Jacobi's fourth even theta constant. -/
def theta₄ (τ : ℍ) : ℂ :=
  ∑' n : ℤ, theta₄Term n τ

/-- The weight-two theta form `θ₂⁴`. -/
def H₂ (τ : ℍ) : ℂ := theta₂ τ ^ 4

/-- The weight-two theta form `θ₃⁴`. -/
def H₃ (τ : ℍ) : ℂ := theta₃ τ ^ 4

/-- The weight-two theta form `θ₄⁴`. -/
def H₄ (τ : ℍ) : ℂ := theta₄ τ ^ 4

/-- The `θ₂` summand as a specialization of Mathlib's two-variable theta
summand. -/
theorem theta₂Term_eq_jacobiTheta₂_term (τ : ℍ) (n : ℤ) :
    theta₂Term n τ =
      cexp (π * I * τ / 4) *
        jacobiTheta₂_term n (τ / 2) τ := by
  rw [theta₂Term, jacobiTheta₂_term, ← Complex.exp_add]
  ring_nf

/-- `θ₂` as a specialization of Mathlib's two-variable theta function. -/
theorem theta₂_eq_jacobiTheta₂ (τ : ℍ) :
    theta₂ τ =
      cexp (π * I * τ / 4) *
        jacobiTheta₂ (τ / 2) τ := by
  simp_rw [theta₂, theta₂Term_eq_jacobiTheta₂_term,
    tsum_mul_left, jacobiTheta₂]

/-- The `θ₃` summand as a specialization of Mathlib's two-variable theta
summand. -/
theorem theta₃Term_eq_jacobiTheta₂_term (τ : ℍ) (n : ℤ) :
    theta₃Term n τ = jacobiTheta₂_term n 0 τ := by
  simp [theta₃Term, jacobiTheta₂_term]

/-- `θ₃` as a specialization of Mathlib's two-variable theta function. -/
theorem theta₃_eq_jacobiTheta₂ (τ : ℍ) :
    theta₃ τ = jacobiTheta₂ (0 : ℂ) τ := by
  simp_rw [theta₃, theta₃Term_eq_jacobiTheta₂_term,
    jacobiTheta₂]

/-- The `θ₄` summand as a specialization of Mathlib's two-variable theta
summand. -/
theorem theta₄Term_eq_jacobiTheta₂_term (τ : ℍ) (n : ℤ) :
    theta₄Term n τ =
      jacobiTheta₂_term n (1 / 2 : ℂ) τ := by
  rw [theta₄Term, jacobiTheta₂_term, ← exp_pi_mul_I,
    ← exp_int_mul, ← Complex.exp_add]
  ring_nf

/-- `θ₄` as a specialization of Mathlib's two-variable theta function. -/
theorem theta₄_eq_jacobiTheta₂ (τ : ℍ) :
    theta₄ τ = jacobiTheta₂ (1 / 2 : ℂ) τ := by
  simp_rw [theta₄, theta₄Term_eq_jacobiTheta₂_term,
    jacobiTheta₂]

end

end HGAS.Modular
