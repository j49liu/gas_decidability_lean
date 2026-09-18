import HGAS.Modular.CanonicalUnaryTheta
import HGAS.Modular.HorizontalTrajectory
import HGAS.Modular.ThetaDerivativeIdentities

/-!
# The canonical theta state solves the unary modular system

The state

```
       (A,C,E,Y) = (θ₂⁴, θ₄⁴, E₂, θ₃)
```

was assembled in `CanonicalUnaryTheta`.  This file proves that it solves
the polynomial vector field of `UnaryAlgebra`.

There are two derivative normalizations in play:

```
Mathlib:  Dₘ = (2πi)⁻¹ d/dτ,
paper:    Dₚ = (πi)⁻¹ d/dτ = 2 Dₘ.
```

Accordingly, the Mathlib-normalized equation is
`Dₘ z = (1/2) vectorField z`; multiplying by two recovers exactly the
paper's polynomial system.  The factor is kept explicit in the theorem
types, rather than hidden in a redefinition of the vector field.

For the `Y=θ₃` coordinate we do not divide pointwise by `θ₃³`.
Instead, we first prove the differential equation for `θ₃⁴=H₃` and use
holomorphic fourth-power cancellation.  This remains valid at any
isolated zero of `θ₃`.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I
open Complex
open scoped Manifold

noncomputable section

local notation "Dₘ" =>
  Derivative.normalizedDerivOfComplex

/-! ## The `θ₃` equation without pointwise division -/

/-- The expected right-hand side of the Mathlib-normalized differential
equation for `θ₃`. -/
def theta₃NormalizedRHS (τ : ℍ) : ℂ :=
  (1 / 24 : ℂ) *
    (EisensteinSeries.E2 τ + H₂ τ - H₄ τ) *
      theta₃ τ

/-- Holomorphy of the proposed `θ₃` derivative. -/
theorem theta₃NormalizedRHS_mdifferentiable :
    MDiff theta₃NormalizedRHS := by
  intro τ
  exact
    ((E2_mdifferentiable τ).add
      (H₂_mdifferentiable τ)
      |>.sub (H₄_mdifferentiable τ)
      |>.const_smul (1 / 24 : ℂ)).mul
        (theta₃_mdifferentiable τ)

/-- The fourth-power differential identity has the exact form required
for holomorphic cancellation. -/
theorem normalizedDeriv_theta₃_fourthPower :
    Dₘ (theta₃ ^ 4) =
      fun τ ↦
        4 * theta₃ τ ^ 3 *
          theta₃NormalizedRHS τ := by
  have hPower : theta₃ ^ 4 = H₃ := by
    ext τ
    rfl
  rw [hPower, normalizedDeriv_H₃]
  funext τ
  have hJacobi :
      theta₃ τ ^ 4 = H₂ τ + H₄ τ := by
    have h :=
      congrFun jacobi_quartic_identity τ
    simpa [H₃] using h.symm
  simp only [theta₃NormalizedRHS, Pi.add_apply,
    Pi.sub_apply, Pi.mul_apply, Pi.pow_apply,
    Pi.smul_apply, smul_eq_mul, H₃]
  linear_combination
    (-(1 / 6 : ℂ) *
      (H₂ τ - H₄ τ)) * hJacobi

/-- The normalized first-order differential equation for `θ₃`.

The proof cancels a fourth power in the ring of holomorphic functions,
not pointwise, so no claim that `θ₃` is everywhere nonzero is needed. -/
theorem normalizedDeriv_theta₃ :
    Dₘ theta₃ = theta₃NormalizedRHS :=
  HGAS.Analysis.normalizedDeriv_eq_of_fourthPower
    theta₃ theta₃NormalizedRHS
    theta₃_mdifferentiable
    theta₃NormalizedRHS_mdifferentiable
    theta₃_ne_zero_function
    normalizedDeriv_theta₃_fourthPower

/-! ## Canonical solution in both normalizations -/

/-- The canonical theta--Eisenstein state solves the unary polynomial
system in Mathlib's normalization `Dₘ=(2πi)⁻¹d/dτ`. -/
theorem canonicalUnaryTheta_isMathlibNormalized :
    IsMathlibNormalizedUnarySolution
      canonicalUnaryTheta where
  A_eq τ := by
    change
      Dₘ H₂ τ =
        (1 / 2 : ℂ) *
          ((1 / 3 : ℂ) * H₂ τ *
            (EisensteinSeries.E2 τ +
              H₂ τ + 2 * H₄ τ))
    rw [congrFun normalizedDeriv_H₂ τ]
    simp only [Pi.add_apply, Pi.mul_apply,
      Pi.pow_apply, Pi.smul_apply, smul_eq_mul]
    ring
  C_eq τ := by
    change
      Dₘ H₄ τ =
        (1 / 2 : ℂ) *
          ((1 / 3 : ℂ) * H₄ τ *
            (EisensteinSeries.E2 τ -
              2 * H₂ τ - H₄ τ))
    rw [congrFun normalizedDeriv_H₄ τ]
    simp only [Pi.add_apply, Pi.mul_apply,
      Pi.pow_apply, Pi.smul_apply, smul_eq_mul]
    ring
  E_eq τ := by
    change
      Dₘ EisensteinSeries.E2 τ =
        (1 / 2 : ℂ) *
          ((1 / 6 : ℂ) *
            (EisensteinSeries.E2 τ ^ 2 -
              H₂ τ ^ 2 - H₂ τ * H₄ τ -
                H₄ τ ^ 2))
    rw [congrFun ramanujan_E2 τ,
      E4_apply_eq_theta]
    ring
  Y_eq τ := by
    change
      Dₘ theta₃ τ =
        (1 / 2 : ℂ) *
          ((1 / 12 : ℂ) *
            (EisensteinSeries.E2 τ +
              H₂ τ - H₄ τ) * theta₃ τ)
    rw [congrFun normalizedDeriv_theta₃ τ]
    simp only [theta₃NormalizedRHS]
    ring

/-- The same canonical state solves the paper-normalized equations
`Dₚ z = vectorField z`, where `Dₚ=2Dₘ`. -/
theorem canonicalUnaryTheta_isPaperNormalized :
    IsPaperNormalizedUnarySolution
      canonicalUnaryTheta :=
  canonicalUnaryTheta_isMathlibNormalized.toPaper

/-! ## Horizontal real-time trajectories -/

/-- Restrict the canonical modular solution to the horizontal line

```
τ(t) = x + (ω/π)t + i y,    y>0.
```

Its real-time derivative is the unary polynomial vector field multiplied
by `iω`, exactly the clock convention used in the paper. -/
theorem canonicalUnaryTheta_horizontalTrajectory
    (x y ω : ℝ) (hy : 0 < y) :
    IsScaledUnaryModularTrajectory
      (I * (ω : ℂ))
      (fun t ↦
        canonicalUnaryTheta
          (horizontalLine x y (ω / Real.pi) hy t)) :=
  canonicalUnaryTheta_isMathlibNormalized.horizontalTrajectory
    canonicalUnaryTheta_A_mdifferentiable
    canonicalUnaryTheta_C_mdifferentiable
    canonicalUnaryTheta_E_mdifferentiable
    canonicalUnaryTheta_Y_mdifferentiable
    x y ω hy

end

end HGAS.Modular
