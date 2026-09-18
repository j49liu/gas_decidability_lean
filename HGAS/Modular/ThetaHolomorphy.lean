import HGAS.Analysis.UpperHalfPlaneRestriction
import HGAS.Modular.ThetaConstants
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Holomorphy of the even theta constants

The theta series in `ThetaConstants` were deliberately defined in the
normalization used by the reduction.  Here we transfer joint holomorphy of
Mathlib's two-variable Jacobi theta function to those three
specializations and to their fourth powers.

Keeping this bridge separate has two benefits: later differential
identities can use the concise `MDiff` hypotheses expected by Mathlib's
modular derivative API, while Fourier and moment arguments can unfold the
original series definitions directly.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I
open Complex Real
open scoped Manifold Real

noncomputable section

/-- The diagonal specialization `τ ↦ jacobiTheta₂(τ/2,τ)` is complex
differentiable at every point of the upper half-plane. -/
theorem differentiableAt_jacobiTheta₂_half (τ : ℍ) :
    DifferentiableAt ℂ
      (fun t : ℂ ↦ jacobiTheta₂ (t / 2) t) τ := by
  let f : ℂ → ℂ × ℂ := fun t ↦ (t / 2, t)
  have hf : DifferentiableAt ℂ f τ :=
    (differentiableAt_id.mul_const ((2 : ℂ)⁻¹)).prodMk
      differentiableAt_id
  have hg :
      DifferentiableAt ℂ
        (fun p : ℂ × ℂ ↦ jacobiTheta₂ p.1 p.2)
        (f τ) := by
    simpa [f] using
      (hasFDerivAt_jacobiTheta₂
        ((τ : ℂ) / 2) τ.im_pos).differentiableAt
  change DifferentiableAt ℂ
    (((fun p : ℂ × ℂ ↦ jacobiTheta₂ p.1 p.2) ∘ f)) τ
  exact hg.comp (τ : ℂ) hf

/-- Holomorphy of `θ₂` on the upper half-plane. -/
theorem theta₂_mdifferentiable : MDiff theta₂ := by
  intro τ
  let G : ℂ → ℂ := fun t ↦
    cexp ((π * I / 4) * t) *
      jacobiTheta₂ (t / 2) t
  have hG : DifferentiableAt ℂ G τ := by
    apply DifferentiableAt.mul
    · exact
        (differentiableAt_id.const_mul
          ((π : ℂ) * I / 4)).cexp
    · exact differentiableAt_jacobiTheta₂_half τ
  have heq :
      theta₂ = fun u : ℍ ↦ G u := by
    ext u
    simp only [theta₂_eq_jacobiTheta₂, G]
    congr 2
    ring
  rw [heq]
  exact HGAS.Analysis.mdifferentiableAt_restrict hG

/-- Holomorphy of `θ₃` on the upper half-plane. -/
theorem theta₃_mdifferentiable : MDiff theta₃ := by
  intro τ
  have hG :
      DifferentiableAt ℂ
        (fun t : ℂ ↦ jacobiTheta₂ 0 t) τ :=
    differentiableAt_jacobiTheta₂_snd 0 τ.im_pos
  have heq :
      theta₃ =
        fun u : ℍ ↦ jacobiTheta₂ 0 (u : ℂ) := by
    ext u
    exact theta₃_eq_jacobiTheta₂ u
  rw [heq]
  exact HGAS.Analysis.mdifferentiableAt_restrict hG

/-- Holomorphy of `θ₄` on the upper half-plane. -/
theorem theta₄_mdifferentiable : MDiff theta₄ := by
  intro τ
  have hG :
      DifferentiableAt ℂ
        (fun t : ℂ ↦ jacobiTheta₂ (1 / 2 : ℂ) t) τ :=
    differentiableAt_jacobiTheta₂_snd
      (1 / 2 : ℂ) τ.im_pos
  have heq :
      theta₄ =
        fun u : ℍ ↦
          jacobiTheta₂ (1 / 2 : ℂ) (u : ℂ) := by
    ext u
    exact theta₄_eq_jacobiTheta₂ u
  rw [heq]
  exact HGAS.Analysis.mdifferentiableAt_restrict hG

/-- Holomorphy of `H₂=θ₂⁴`. -/
theorem H₂_mdifferentiable : MDiff H₂ := by
  intro τ
  exact (theta₂_mdifferentiable τ).pow 4

/-- Holomorphy of `H₃=θ₃⁴`. -/
theorem H₃_mdifferentiable : MDiff H₃ := by
  intro τ
  exact (theta₃_mdifferentiable τ).pow 4

/-- Holomorphy of `H₄=θ₄⁴`. -/
theorem H₄_mdifferentiable : MDiff H₄ := by
  intro τ
  exact (theta₄_mdifferentiable τ).pow 4

end

end HGAS.Modular
