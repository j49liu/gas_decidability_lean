import HGAS.Modular.CanonicalUnaryRoots
import HGAS.Modular.CanonicalUnaryThetaSolution
import HGAS.Modular.UnaryRootNormalizedSolution

/-!
# The canonical theta-root state solves the extended unary system

This file proves the differential equations for the canonical root
coordinates

```
p₂ = θ₂²,   p₃ = θ₃²,   p₄ = θ₄²,   H = E₂/12.
```

As in `CanonicalUnaryThetaSolution`, all equations initially use
Mathlib's normalization

```
                    Dₘ = (2πi)⁻¹ d/dτ.
```

The root vector field in `UnaryAlgebra` is written in the paper's
normalization `Dₚ=2Dₘ`, so the solution predicate contains the explicit
factor `1/2`.

The equations for `θ₂` and `θ₄` are recovered from their fourth powers by
global holomorphic cancellation.  We never divide by a theta value at a
point: `θ₄` is nonzero as a function because it tends to one at the cusp,
and `θ₂` is nonzero because its `S`-transform is `θ₄` after taking fourth
powers.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I
open Complex Filter Topology
open scoped Manifold ModularForm MatrixGroups

noncomputable section

local notation "Dₘ" =>
  Derivative.normalizedDerivOfComplex

/-! ## Nontriviality of the two remaining theta constants -/

/-- `θ₄` is not the zero function because its cusp limit is one. -/
theorem theta₄_ne_zero_function :
    theta₄ ≠ 0 :=
  HGAS.Analysis.function_ne_zero_of_tendsto
    theta₄_tendsto_atImInfty
    (one_ne_zero : (1 : ℂ) ≠ 0)

/-- The fourth power `H₄=θ₄⁴` is not the zero function. -/
theorem H₄_ne_zero_function :
    H₄ ≠ 0 :=
  HGAS.Analysis.function_ne_zero_of_tendsto
    H₄_tendsto_atImInfty
    (one_ne_zero : (1 : ℂ) ≠ 0)

/-- `θ₂` is not the zero function.

If it vanished identically, then `H₂=θ₂⁴` would vanish.  The modular
transformation `H₂|₂S=-H₄` would then force `H₄=0`, contradicting its cusp
limit. -/
theorem theta₂_ne_zero_function :
    theta₂ ≠ 0 := by
  intro hTheta₂
  have hH₂ : H₂ = 0 := by
    ext τ
    simp [H₂, hTheta₂]
  have hAction := H₂_S_action
  rw [hH₂] at hAction
  have hH₄ : H₄ = 0 := by
    simpa using hAction.symm
  exact H₄_ne_zero_function hH₄

/-! ## First-order theta equations by fourth-power cancellation -/

/-- Proposed Mathlib-normalized derivative of `θ₂`. -/
def theta₂NormalizedRHS (τ : ℍ) : ℂ :=
  (1 / 24 : ℂ) *
    (EisensteinSeries.E2 τ + H₂ τ + 2 * H₄ τ) *
      theta₂ τ

/-- Proposed Mathlib-normalized derivative of `θ₄`. -/
def theta₄NormalizedRHS (τ : ℍ) : ℂ :=
  (1 / 24 : ℂ) *
    (EisensteinSeries.E2 τ - 2 * H₂ τ - H₄ τ) *
      theta₄ τ

theorem theta₂NormalizedRHS_mdifferentiable :
    MDiff theta₂NormalizedRHS := by
  intro τ
  exact
    (((E2_mdifferentiable τ).add
      (H₂_mdifferentiable τ)).add
        ((H₄_mdifferentiable τ).const_smul
          (2 : ℂ))
      |>.const_smul (1 / 24 : ℂ)).mul
        (theta₂_mdifferentiable τ)

theorem theta₄NormalizedRHS_mdifferentiable :
    MDiff theta₄NormalizedRHS := by
  intro τ
  exact
    (((E2_mdifferentiable τ).sub
      ((H₂_mdifferentiable τ).const_smul
        (2 : ℂ))).sub
          (H₄_mdifferentiable τ)
      |>.const_smul (1 / 24 : ℂ)).mul
        (theta₄_mdifferentiable τ)

/-- Fourth-power identity used to recover the `θ₂` equation. -/
theorem normalizedDeriv_theta₂_fourthPower :
    Dₘ (theta₂ ^ 4) =
      fun τ ↦
        4 * theta₂ τ ^ 3 *
          theta₂NormalizedRHS τ := by
  have hPower : theta₂ ^ 4 = H₂ := by
    ext τ
    rfl
  rw [hPower, normalizedDeriv_H₂]
  funext τ
  simp only [theta₂NormalizedRHS, Pi.add_apply,
    Pi.mul_apply, Pi.pow_apply, Pi.smul_apply,
    smul_eq_mul, H₂]
  ring

/-- Fourth-power identity used to recover the `θ₄` equation. -/
theorem normalizedDeriv_theta₄_fourthPower :
    Dₘ (theta₄ ^ 4) =
      fun τ ↦
        4 * theta₄ τ ^ 3 *
          theta₄NormalizedRHS τ := by
  have hPower : theta₄ ^ 4 = H₄ := by
    ext τ
    rfl
  rw [hPower, normalizedDeriv_H₄]
  funext τ
  simp only [theta₄NormalizedRHS, Pi.add_apply,
    Pi.mul_apply, Pi.pow_apply, Pi.smul_apply,
    smul_eq_mul, H₄]
  ring

/-- Mathlib-normalized first-order equation for `θ₂`, proved without
pointwise division. -/
theorem normalizedDeriv_theta₂ :
    Dₘ theta₂ = theta₂NormalizedRHS :=
  HGAS.Analysis.normalizedDeriv_eq_of_fourthPower
    theta₂ theta₂NormalizedRHS
    theta₂_mdifferentiable
    theta₂NormalizedRHS_mdifferentiable
    theta₂_ne_zero_function
    normalizedDeriv_theta₂_fourthPower

/-- Mathlib-normalized first-order equation for `θ₄`, proved without
pointwise division. -/
theorem normalizedDeriv_theta₄ :
    Dₘ theta₄ = theta₄NormalizedRHS :=
  HGAS.Analysis.normalizedDeriv_eq_of_fourthPower
    theta₄ theta₄NormalizedRHS
    theta₄_mdifferentiable
    theta₄NormalizedRHS_mdifferentiable
    theta₄_ne_zero_function
    normalizedDeriv_theta₄_fourthPower

/-! ## The four added root-coordinate equations -/

/-- Normalized derivative of `p₂=θ₂²`. -/
theorem normalizedDeriv_canonicalUnaryRoots_p2
    (τ : ℍ) :
    Dₘ (fun w ↦ (canonicalUnaryRoots w).p2) τ =
      (1 / 2 : ℂ) *
        (UnaryRootState.vectorField
          (canonicalUnaryRoots τ)).p2 := by
  change
    Dₘ (theta₂ ^ 2) τ =
      (1 / 2 : ℂ) *
        ((1 / 6 : ℂ) *
          (12 * (EisensteinSeries.E2 τ / 12) +
            (theta₂ τ ^ 2) ^ 2 +
              2 * (theta₄ τ ^ 2) ^ 2) *
            theta₂ τ ^ 2)
  rw [congrFun
    (Derivative.normalizedDerivOfComplex_pow
      theta₂ 2 theta₂_mdifferentiable) τ]
  simp only [Pi.mul_apply,
    Nat.cast_ofNat, Nat.reduceSub, pow_one]
  rw [congrFun normalizedDeriv_theta₂ τ]
  simp only [theta₂NormalizedRHS]
  change
    2 * theta₂ τ *
        (1 / 24 *
          (EisensteinSeries.E2 τ +
            theta₂ τ ^ 4 +
              2 * theta₄ τ ^ 4) *
            theta₂ τ) =
      _
  ring

/-- Normalized derivative of `p₃=θ₃²`. -/
theorem normalizedDeriv_canonicalUnaryRoots_p3
    (τ : ℍ) :
    Dₘ (fun w ↦ (canonicalUnaryRoots w).p3) τ =
      (1 / 2 : ℂ) *
        (UnaryRootState.vectorField
          (canonicalUnaryRoots τ)).p3 := by
  change
    Dₘ (theta₃ ^ 2) τ =
      (1 / 2 : ℂ) *
        ((1 / 6 : ℂ) *
          (12 * (EisensteinSeries.E2 τ / 12) +
            (theta₂ τ ^ 2) ^ 2 -
              (theta₄ τ ^ 2) ^ 2) *
            theta₃ τ ^ 2)
  rw [congrFun
    (Derivative.normalizedDerivOfComplex_pow
      theta₃ 2 theta₃_mdifferentiable) τ]
  simp only [Pi.mul_apply,
    Nat.cast_ofNat, Nat.reduceSub, pow_one]
  rw [congrFun normalizedDeriv_theta₃ τ]
  simp only [theta₃NormalizedRHS]
  change
    2 * theta₃ τ *
        (1 / 24 *
          (EisensteinSeries.E2 τ +
            theta₂ τ ^ 4 -
              theta₄ τ ^ 4) *
            theta₃ τ) =
      _
  ring

/-- Normalized derivative of `p₄=θ₄²`. -/
theorem normalizedDeriv_canonicalUnaryRoots_p4
    (τ : ℍ) :
    Dₘ (fun w ↦ (canonicalUnaryRoots w).p4) τ =
      (1 / 2 : ℂ) *
        (UnaryRootState.vectorField
          (canonicalUnaryRoots τ)).p4 := by
  change
    Dₘ (theta₄ ^ 2) τ =
      (1 / 2 : ℂ) *
        ((1 / 6 : ℂ) *
          (12 * (EisensteinSeries.E2 τ / 12) -
            2 * (theta₂ τ ^ 2) ^ 2 -
              (theta₄ τ ^ 2) ^ 2) *
            theta₄ τ ^ 2)
  rw [congrFun
    (Derivative.normalizedDerivOfComplex_pow
      theta₄ 2 theta₄_mdifferentiable) τ]
  simp only [Pi.mul_apply,
    Nat.cast_ofNat, Nat.reduceSub, pow_one]
  rw [congrFun normalizedDeriv_theta₄ τ]
  simp only [theta₄NormalizedRHS]
  change
    2 * theta₄ τ *
        (1 / 24 *
          (EisensteinSeries.E2 τ -
            2 * theta₂ τ ^ 4 -
              theta₄ τ ^ 4) *
            theta₄ τ) =
      _
  ring

/-- Normalized derivative of `H=E₂/12`. -/
theorem normalizedDeriv_canonicalUnaryRoots_H
    (τ : ℍ) :
    Dₘ (fun w ↦ (canonicalUnaryRoots w).H) τ =
      (1 / 2 : ℂ) *
        (UnaryRootState.vectorField
          (canonicalUnaryRoots τ)).H := by
  have hFunction :
      (fun w : ℍ ↦ EisensteinSeries.E2 w / 12) =
        (1 / 12 : ℂ) • EisensteinSeries.E2 := by
    ext w
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  change
    Dₘ (fun w : ℍ ↦
      EisensteinSeries.E2 w / 12) τ =
      (1 / 2 : ℂ) *
        ((1 / 72 : ℂ) *
          ((12 * (EisensteinSeries.E2 τ / 12)) ^ 2 -
            (theta₂ τ ^ 2) ^ 4 -
              (theta₂ τ ^ 2) ^ 2 *
                (theta₄ τ ^ 2) ^ 2 -
              (theta₄ τ ^ 2) ^ 4))
  rw [hFunction,
    congrFun
      (Derivative.normalizedDerivOfComplex_smul
        (1 / 12 : ℂ) EisensteinSeries.E2
        E2_mdifferentiable) τ]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [congrFun ramanujan_E2 τ,
    E4_apply_eq_theta]
  simp only [H₂, H₄]
  ring

/-! ## Canonical root solution -/

/-- The canonical theta-root state solves all eight equations in
Mathlib's normalization. -/
theorem canonicalUnaryRoots_isMathlibNormalized :
    IsMathlibNormalizedUnaryRootSolution
      canonicalUnaryRoots where
  base := by
    simpa using
      canonicalUnaryTheta_isMathlibNormalized
  p2_eq :=
    normalizedDeriv_canonicalUnaryRoots_p2
  p3_eq :=
    normalizedDeriv_canonicalUnaryRoots_p3
  p4_eq :=
    normalizedDeriv_canonicalUnaryRoots_p4
  H_eq :=
    normalizedDeriv_canonicalUnaryRoots_H

/-- The same canonical root state solves the paper-normalized equations
after applying the explicit relation `Dₚ=2Dₘ`. -/
theorem canonicalUnaryRoots_isPaperNormalized :
    IsPaperNormalizedUnaryRootSolution
      canonicalUnaryRoots :=
  canonicalUnaryRoots_isMathlibNormalized.toPaper

end

end HGAS.Modular
