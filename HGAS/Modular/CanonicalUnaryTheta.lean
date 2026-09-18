import HGAS.Analysis.HolomorphicPowerCancellation
import HGAS.Modular.EisensteinBounds
import HGAS.Modular.ThetaAsymptotics
import HGAS.Modular.ThetaJacobiIdentity
import HGAS.Modular.UnaryNormalizedSolution

/-!
# The canonical theta--Eisenstein state

This file assembles the four analytic functions used by the unary
polynomial block:

```
              A = θ₂⁴,   C = θ₄⁴,   E = E₂,   Y = θ₃.
```

The assembly is kept separate from the differential identities.  Here we
prove its holomorphy, cusp normalization, and Jacobi algebraic constraint.
The subsequent differential module proves that it solves the polynomial
vector field.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I
open Complex Filter Topology
open scoped Manifold

noncomputable section

/-- The canonical holomorphic state of the unary modular system. -/
def canonicalUnaryTheta (τ : ℍ) :
    UnaryModularState ℂ :=
  unaryStateOfFunctions H₂ H₄ EisensteinSeries.E2 theta₃ τ

@[simp] theorem canonicalUnaryTheta_A (τ : ℍ) :
    (canonicalUnaryTheta τ).A = H₂ τ := rfl

@[simp] theorem canonicalUnaryTheta_C (τ : ℍ) :
    (canonicalUnaryTheta τ).C = H₄ τ := rfl

@[simp] theorem canonicalUnaryTheta_E (τ : ℍ) :
    (canonicalUnaryTheta τ).E =
      EisensteinSeries.E2 τ := rfl

@[simp] theorem canonicalUnaryTheta_Y (τ : ℍ) :
    (canonicalUnaryTheta τ).Y = theta₃ τ := rfl

/-- Holomorphy of the `A` coordinate. -/
theorem canonicalUnaryTheta_A_mdifferentiable :
    MDiff (fun τ ↦ (canonicalUnaryTheta τ).A) :=
  H₂_mdifferentiable

/-- Holomorphy of the `C` coordinate. -/
theorem canonicalUnaryTheta_C_mdifferentiable :
    MDiff (fun τ ↦ (canonicalUnaryTheta τ).C) :=
  H₄_mdifferentiable

/-- Holomorphy of the `E` coordinate. -/
theorem canonicalUnaryTheta_E_mdifferentiable :
    MDiff (fun τ ↦ (canonicalUnaryTheta τ).E) :=
  E2_mdifferentiable

/-- Holomorphy of the `Y` coordinate. -/
theorem canonicalUnaryTheta_Y_mdifferentiable :
    MDiff (fun τ ↦ (canonicalUnaryTheta τ).Y) :=
  theta₃_mdifferentiable

/-- The canonical state lies on Jacobi's invariant hypersurface
`Y⁴=A+C`. -/
theorem canonicalUnaryTheta_jacobiResidual_eq_zero
    (τ : ℍ) :
    UnaryModularState.jacobiResidual
      (canonicalUnaryTheta τ) = 0 := by
  have hJacobi := congrFun jacobi_quartic_identity τ
  simp only [canonicalUnaryTheta,
    unaryStateOfFunctions_A, unaryStateOfFunctions_C,
    unaryStateOfFunctions_Y,
    UnaryModularState.jacobiResidual,
    H₃, Pi.add_apply] at hJacobi ⊢
  linear_combination -hJacobi

/-- The third theta constant is not identically zero.  Its cusp limit is
one, which is enough; no product formula or pointwise zero-free theorem is
required. -/
theorem theta₃_ne_zero_function :
    theta₃ ≠ 0 :=
  HGAS.Analysis.function_ne_zero_of_tendsto
    theta₃_tendsto_atImInfty
    (one_ne_zero : (1 : ℂ) ≠ 0)

/-- Cusp limit of the canonical `A` coordinate. -/
theorem canonicalUnaryTheta_A_tendsto :
    Tendsto (fun τ ↦ (canonicalUnaryTheta τ).A)
      atImInfty (𝓝 0) :=
  H₂_tendsto_atImInfty

/-- Cusp limit of the canonical `C` coordinate. -/
theorem canonicalUnaryTheta_C_tendsto :
    Tendsto (fun τ ↦ (canonicalUnaryTheta τ).C)
      atImInfty (𝓝 1) :=
  H₄_tendsto_atImInfty

/-- Cusp limit of the canonical `E` coordinate. -/
theorem canonicalUnaryTheta_E_tendsto :
    Tendsto (fun τ ↦ (canonicalUnaryTheta τ).E)
      atImInfty (𝓝 1) :=
  e2_tendsto_one_atImInfty

/-- Cusp limit of the canonical `Y` coordinate. -/
theorem canonicalUnaryTheta_Y_tendsto :
    Tendsto (fun τ ↦ (canonicalUnaryTheta τ).Y)
      atImInfty (𝓝 1) :=
  theta₃_tendsto_atImInfty

end

end HGAS.Modular
