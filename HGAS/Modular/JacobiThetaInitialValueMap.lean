import HGAS.Modular.JacobiThetaInitialRank
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic

/-!
# The nonlinear Jacobi initial-value map

The saturation argument uses the three-parameter map

```
(S, ξ, L) ↦
  (S T(ξ), S (A(ξ) + L T₁(ξ))).
```

Here `T : ℂ → Fin 4 → ℂ` is the theta vector and `A` is its normalized
first derivative.  The preceding module proved the linear algebra of the
candidate derivative.  This file verifies that it really is the
Fréchet derivative of the nonlinear map, for arbitrary differentiable
`T` and `A`.

Keeping the calculus lemma abstract makes it reusable: the theta-specific
application only has to supply the derivative of `T` and of the scalar
function `A`.
-/

namespace HGAS.Modular

noncomputable section

/-- Three-parameter initial-value map used in equation (8.8). -/
def jacobiInitialValueMap
    (T : ℂ → Fin 4 → ℂ)
    (A : ℂ → ℂ)
    (v : ℂ × ℂ × ℂ) :
    (Fin 4 → ℂ) × ℂ :=
  (v.1 • T v.2.1,
    v.1 * (A v.2.1 + v.2.2 * T v.2.1 0))

/-- The unique Bloch slope that makes the last initial-value coordinate
equal to `Δ`, once the common scale and the first theta coordinate are
nonzero. -/
def jacobiInitialValueBlochSlope
    (S A θ₁ Δ : ℂ) : ℂ :=
  Δ / (S * θ₁) - A / θ₁

/-- Solving the last coordinate of the initial-value map is completely
explicit.  This is the algebraic core of formula (8.7), stated for an
arbitrary vector-valued function and scalar correction. -/
theorem jacobiInitialValueMap_at_blochSlope
    (T : ℂ → Fin 4 → ℂ)
    (A : ℂ → ℂ)
    (S ξ Δ : ℂ)
    (hS : S ≠ 0)
    (hT₁ : T ξ 0 ≠ 0) :
    jacobiInitialValueMap T A
        (S, ξ,
          jacobiInitialValueBlochSlope
            S (A ξ) (T ξ 0) Δ) =
      (S • T ξ, Δ) := by
  apply Prod.ext
  · rfl
  · simp only [jacobiInitialValueMap,
      jacobiInitialValueBlochSlope]
    field_simp
    ring

/-- Existence form of the explicit Bloch-slope calculation. -/
theorem exists_jacobiInitialValueMap_eq
    (T : ℂ → Fin 4 → ℂ)
    (A : ℂ → ℂ)
    (S ξ Δ : ℂ)
    (hS : S ≠ 0)
    (hT₁ : T ξ 0 ≠ 0) :
    ∃ L : ℂ,
      jacobiInitialValueMap T A (S, ξ, L) =
        (S • T ξ, Δ) :=
  ⟨jacobiInitialValueBlochSlope
      S (A ξ) (T ξ 0) Δ,
    jacobiInitialValueMap_at_blochSlope
      T A S ξ Δ hS hT₁⟩

/-- The algebraic initial-value linearization, equipped with the continuous
linear structure available in finite dimensions. -/
def jacobiInitialValueFDeriv
    (S A B : ℂ) (T Tξ : Fin 4 → ℂ) :
    (ℂ × ℂ × ℂ) →L[ℂ] ((Fin 4 → ℂ) × ℂ) :=
  LinearMap.toContinuousLinearMap
    (jacobiInitialValueLinearization S A B T Tξ)

@[simp] theorem jacobiInitialValueFDeriv_apply
    (S A B : ℂ) (T Tξ : Fin 4 → ℂ)
    (v : ℂ × ℂ × ℂ) :
    jacobiInitialValueFDeriv S A B T Tξ v =
      jacobiInitialValueLinearization S A B T Tξ v := rfl

/-- The rank-three linearization from `JacobiThetaInitialRank` is the
actual derivative of the nonlinear initial-value map. -/
theorem hasFDerivAt_jacobiInitialValueMap
    {T : ℂ → Fin 4 → ℂ}
    {A : ℂ → ℂ}
    {S ξ L Aξ Aξ' : ℂ}
    {Tξ : Fin 4 → ℂ}
    (hT : HasDerivAt T Tξ ξ)
    (hA : HasDerivAt A Aξ' ξ)
    (hAvalue : A ξ = Aξ) :
    HasFDerivAt
      (jacobiInitialValueMap T A)
      (jacobiInitialValueFDeriv
        S
        (Aξ + L * T ξ 0)
        (Aξ' + L * Tξ 0)
        (T ξ) Tξ)
      (S, ξ, L) := by
  let x : ℂ × ℂ × ℂ := (S, ξ, L)
  have hS :
      HasFDerivAt
        (fun v : ℂ × ℂ × ℂ ↦ v.1)
        (ContinuousLinearMap.fst ℂ ℂ (ℂ × ℂ)) x :=
    hasFDerivAt_fst
  have hpair :
      HasFDerivAt
        (fun v : ℂ × ℂ × ℂ ↦ v.2)
        (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ)) x :=
    hasFDerivAt_snd
  have hξ :
      HasFDerivAt
        (fun v : ℂ × ℂ × ℂ ↦ v.2.1)
        ((ContinuousLinearMap.fst ℂ ℂ ℂ).comp
          (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ))) x :=
    hpair.fst
  have hL :
      HasFDerivAt
        (fun v : ℂ × ℂ × ℂ ↦ v.2.2)
        ((ContinuousLinearMap.snd ℂ ℂ ℂ).comp
          (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ))) x :=
    hpair.snd
  have hTcomp :=
    hT.hasFDerivAt.comp x hξ
  have hAcomp :=
    hA.hasFDerivAt.comp x hξ
  have hTzero :=
    (hasFDerivAt_apply (𝕜 := ℂ) 0 (T ξ)).comp x hTcomp
  have hLTzero := hL.mul hTzero
  have hnormalized := hAcomp.add hLTzero
  have hfirst := hS.smul hTcomp
  have hlast := hS.mul hnormalized
  have hproduct := hfirst.prodMk hlast
  convert hproduct using 1
  apply ContinuousLinearMap.ext
  intro v
  rcases v with ⟨dS, dξ, dL⟩
  apply Prod.ext
  · funext k
    simp [jacobiInitialValueFDeriv,
      jacobiInitialValueLinearization, x,
      Function.comp_def]
    ring
  · simp [jacobiInitialValueFDeriv,
      jacobiInitialValueLinearization, x,
      Function.comp_def, hAvalue]
    ring

/-- Whenever the theta vector and its elliptic derivative are linearly
independent and `S*T₁` is nonzero, the nonlinear initial-value map has
complex rank three. -/
theorem jacobiInitialValueMap_derivative_range_finrank
    {T : ℂ → Fin 4 → ℂ}
    {A : ℂ → ℂ}
    {S ξ L Aξ Aξ' : ℂ}
    {Tξ : Fin 4 → ℂ}
    (hT : HasDerivAt T Tξ ξ)
    (hA : HasDerivAt A Aξ' ξ)
    (hAvalue : A ξ = Aξ)
    (hS : S ≠ 0)
    (hT1 : T ξ 0 ≠ 0)
    (hLI : LinearIndependent ℂ ![T ξ, Tξ]) :
    Module.finrank ℂ
      (fderiv ℂ (jacobiInitialValueMap T A)
        (S, ξ, L)).range = 3 := by
  rw [(hasFDerivAt_jacobiInitialValueMap
    hT hA hAvalue).fderiv]
  exact
    jacobiInitialValueLinearization_range_finrank
      hS hT1 hLI

end

end HGAS.Modular
