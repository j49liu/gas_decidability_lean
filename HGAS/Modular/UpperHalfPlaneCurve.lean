import HGAS.Modular.HorizontalTrajectory

/-!
# Holomorphic functions along upper-half-plane curves

`HorizontalTrajectory` proves the chain rule for the particular affine
curves used by the canonical closed horocycles.  Reconstruction of an
arbitrary modular state needs the same rule for a general differentiable
curve `T : ℝ → ℍ`.

If the ambient complex derivative of `T` is `v`, then for Mathlib's
normalized derivative

```
                       Dₘ = (2πi)⁻¹ d/dτ
```

we have

```
                    d/dt f(T(t)) = 2πi v Dₘf(T(t)).
```

The proof is a direct mixed-scalar chain rule: complex differentiability
of `f` is composed with real differentiability of the curve.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I
open Complex
open scoped Manifold

noncomputable section

local notation "Dₘ" =>
  Derivative.normalizedDerivOfComplex

/-- Chain rule for a holomorphic upper-half-plane function along an
arbitrary real differentiable curve. -/
theorem hasDerivAt_comp_upperHalfPlaneCurve
    (f : ℍ → ℂ) (hf : MDiff f)
    (T : ℝ → ℍ) (t : ℝ) {v : ℂ}
    (hT :
      HasDerivAt (fun s : ℝ ↦ (T s : ℂ)) v t) :
    HasDerivAt
      (fun s : ℝ ↦ f (T s))
      ((2 * (Real.pi : ℂ) * I) * v *
        Dₘ f (T t)) t := by
  have houter :
      HasDerivAt (f ∘ ofComplex)
        (deriv (f ∘ ofComplex) (T t : ℂ))
        (T t : ℂ) :=
    (UpperHalfPlane.mdifferentiableAt_iff.mp
      (hf (T t))).hasDerivAt
  have hcomp := houter.scomp t hT
  have hnorm :
      deriv (f ∘ ofComplex) (T t : ℂ) =
        (2 * (Real.pi : ℂ) * I) * Dₘ f (T t) := by
    unfold Derivative.normalizedDerivOfComplex
    have hpi : (Real.pi : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp [hpi]
  convert hcomp using 1
  · funext s
    simp only [Function.comp_apply,
      UpperHalfPlane.ofComplex_apply]
  · rw [hnorm]
    simp only [smul_eq_mul]
    ring

end

end HGAS.Modular
