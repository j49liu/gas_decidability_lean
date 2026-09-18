import HGAS.Modular.UnaryDynamics
import HGAS.Modular.UnaryNormalizedSolution
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Horizontal lines and modular differential trajectories

A holomorphic modular function becomes a real-time ODE trajectory when it
is restricted to a horizontal line in the upper half-plane.  This module
proves the chain rule with all normalization constants visible.

For

```
                    τ(t) = x + v t + i y
```

and Mathlib's normalized derivative
`Dₘ = (2πi)⁻¹ d/dτ`, one has

```
                    d/dt f(τ(t)) = 2π i v Dₘf(τ(t)).
```

The paper takes `v = ω/π`.  Consequently the derivative is
`2 i ω Dₘf`; if `Dₘf` is one half of the unary polynomial vector field,
the resulting real-time multiplier is exactly `iω`.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I
open Complex Real
open scoped Manifold

noncomputable section

local notation "Dₘ" => Derivative.normalizedDerivOfComplex

/-- The complex affine map underlying a horizontal line. -/
def complexHorizontalAffine
    (x y v : ℝ) (s : ℂ) : ℂ :=
  (x : ℂ) + (v : ℂ) * s + (y : ℂ) * I

/-- A horizontal line in the upper half-plane. -/
def horizontalLine
    (x y v : ℝ) (hy : 0 < y) (t : ℝ) : ℍ :=
  ⟨Complex.mk (x + v * t) y, hy⟩

@[simp] theorem horizontalLine_re
    (x y v : ℝ) (hy : 0 < y) (t : ℝ) :
    (horizontalLine x y v hy t).re = x + v * t := rfl

@[simp] theorem horizontalLine_im
    (x y v : ℝ) (hy : 0 < y) (t : ℝ) :
    (horizontalLine x y v hy t).im = y := rfl

/-- On a real argument, the ambient complex affine map is the coercion of
`horizontalLine`. -/
@[simp] theorem complexHorizontalAffine_ofReal
    (x y v t : ℝ) (hy : 0 < y) :
    complexHorizontalAffine x y v (t : ℂ) =
      (horizontalLine x y v hy t : ℂ) := by
  apply Complex.ext
  · simp [complexHorizontalAffine]
  · simp [complexHorizontalAffine]

/-- Complex derivative of the ambient horizontal affine map. -/
theorem complexHorizontalAffine_hasDerivAt
    (x y v : ℝ) (s : ℂ) :
    HasDerivAt (complexHorizontalAffine x y v) (v : ℂ) s := by
  have hx :
      HasDerivAt (fun _ : ℂ ↦ (x : ℂ)) 0 s :=
    hasDerivAt_const s _
  have hv :
      HasDerivAt (fun w : ℂ ↦ (v : ℂ) * w) (v : ℂ) s := by
    simpa using
      HasDerivAt.const_mul (v : ℂ) (hasDerivAt_id s)
  have hyI :
      HasDerivAt (fun _ : ℂ ↦ (y : ℂ) * I) 0 s :=
    hasDerivAt_const s _
  simpa [complexHorizontalAffine] using (hx.add hv).add hyI

/-- Restricting a holomorphic upper-half-plane function to a horizontal
line gives the exact real derivative `2π i v Dₘf`. -/
theorem hasDerivAt_comp_horizontalLine
    (f : ℍ → ℂ) (hf : MDiff f)
    (x y v : ℝ) (hy : 0 < y) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ ↦ f (horizontalLine x y v hy s))
      ((2 * π * I) * (v : ℂ) *
        Dₘ f (horizontalLine x y v hy t)) t := by
  let τ := horizontalLine x y v hy t
  have houter :
      HasDerivAt (f ∘ ofComplex)
        (deriv (f ∘ ofComplex) (τ : ℂ)) (τ : ℂ) :=
    (UpperHalfPlane.mdifferentiableAt_iff.mp
      (hf τ)).hasDerivAt
  have hinner :=
    complexHorizontalAffine_hasDerivAt x y v (t : ℂ)
  have houter' :
      HasDerivAt (f ∘ ofComplex)
        (deriv (f ∘ ofComplex) (τ : ℂ))
        (complexHorizontalAffine x y v (t : ℂ)) := by
    rw [complexHorizontalAffine_ofReal x y v t hy]
    exact houter
  have hcomplex :
      HasDerivAt
        ((f ∘ ofComplex) ∘ complexHorizontalAffine x y v)
        (deriv (f ∘ ofComplex) (τ : ℂ) * (v : ℂ))
        (t : ℂ) := by
    exact houter'.comp (t : ℂ) hinner
  have hreal := hcomplex.comp_ofReal
  have hnorm :
      deriv (f ∘ ofComplex) (τ : ℂ) =
        (2 * π * I) * Dₘ f τ := by
    unfold Derivative.normalizedDerivOfComplex
    have hpi : (π : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp [hpi]
  convert hreal using 1
  · funext s
    simp only [Function.comp_apply,
      complexHorizontalAffine_ofReal x y v s hy,
      UpperHalfPlane.ofComplex_apply]
  · rw [hnorm]
    ring

/-- The paper's horizontal speed `v=ω/π` gives the simpler multiplier
`2iω` in Mathlib normalization. -/
theorem hasDerivAt_comp_horizontalLine_paperSpeed
    (f : ℍ → ℂ) (hf : MDiff f)
    (x y ω : ℝ) (hy : 0 < y) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ ↦
        f (horizontalLine x y (ω / π) hy s))
      ((2 * I * (ω : ℂ)) *
        Dₘ f (horizontalLine x y (ω / π) hy t)) t := by
  convert
    hasDerivAt_comp_horizontalLine
      f hf x y (ω / π) hy t using 1
  have hpi : (π : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp [hpi]

/-- A Mathlib-normalized unary modular solution, restricted at the paper's
horizontal speed, is a scaled trajectory of the polynomial vector field
with multiplier `iω`. -/
theorem IsMathlibNormalizedUnarySolution.horizontalTrajectory
    {z : ℍ → UnaryModularState ℂ}
    (hz : IsMathlibNormalizedUnarySolution z)
    (hA : MDiff (fun τ ↦ (z τ).A))
    (hC : MDiff (fun τ ↦ (z τ).C))
    (hE : MDiff (fun τ ↦ (z τ).E))
    (hY : MDiff (fun τ ↦ (z τ).Y))
    (x y ω : ℝ) (hy : 0 < y) :
    IsScaledUnaryModularTrajectory (I * (ω : ℂ))
      (fun t ↦ z (horizontalLine x y (ω / π) hy t)) where
  A t := by
    have h :=
      hasDerivAt_comp_horizontalLine_paperSpeed
        (fun τ ↦ (z τ).A) hA x y ω hy t
    convert h using 1
    rw [hz.A_eq]
    ring
  C t := by
    have h :=
      hasDerivAt_comp_horizontalLine_paperSpeed
        (fun τ ↦ (z τ).C) hC x y ω hy t
    convert h using 1
    rw [hz.C_eq]
    ring
  E t := by
    have h :=
      hasDerivAt_comp_horizontalLine_paperSpeed
        (fun τ ↦ (z τ).E) hE x y ω hy t
    convert h using 1
    rw [hz.E_eq]
    ring
  Y t := by
    have h :=
      hasDerivAt_comp_horizontalLine_paperSpeed
        (fun τ ↦ (z τ).Y) hY x y ω hy t
    convert h using 1
    rw [hz.Y_eq]
    ring

end

end HGAS.Modular
