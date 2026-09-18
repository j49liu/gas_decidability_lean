import HGAS.Modular.JacobiBlochSelectedContinuation

/-!
# Canonical residual continuation with a retained nonzero scale

The canonical-residual continuation theorem constructs its affine
Jacobi--Bloch parameters from a nonzero pointwise scale `S`.  Some later
detector interfaces need the resulting fact `p.c0 ≠ 0` explicitly.

This file supplies that slightly stronger packaging without changing the
original, geometrically natural interface.  The proof follows the same
two-stage construction:

1. pointwise saturation produces a nonzero Bloch scale and exact core
   equality;
2. affine continuation turns that equality into a globally regular
   Jacobi--Bloch path.

The selected-parameter formula records directly that its constant `c0`
is the product of `S` and a nonzero exponential.
-/

namespace HGAS.Modular

open Complex Real
open UpperHalfPlane hiding I

noncomputable section

/-- **Canonical residual trajectory classification, retaining
`c0 ≠ 0`.**

This is the strengthened detector-facing form of
`exists_affineBlochParameters_eq_of_canonical_residual_at`. -/
theorem
    exists_affineBlochParameters_with_c0_ne_zero_eq_of_canonical_residual_at
    (τ : ℍ) (w : ℂ) (ν κ : ℝ) (t₀ : ℝ)
    {z : ℝ → JacobiState ℂ}
    (hz :
      IsScaledJacobiTrajectory
        ((π : ℂ) * (ν : ℂ))
        ((π : ℂ) * I * (κ : ℂ)) z)
    (hp2 : (z t₀).p2 = (canonicalUnaryRoots τ).p2)
    (hp3 : (z t₀).p3 = (canonicalUnaryRoots τ).p3)
    (hp4 : (z t₀).p4 = (canonicalUnaryRoots τ).p4)
    (hH : (z t₀).H = (canonicalUnaryRoots τ).H)
    (hR1 : JacobiState.residualR1 (z t₀) = 0)
    (hR2 : JacobiState.residualR2 (z t₀) = 0)
    (hreciprocal :
      ∀ t, (z t).U * (z t).T1 = 1) :
    ∃ p : AffineBlochParameters,
      p.nu = ν ∧
      p.kappa = κ ∧
      p.tau t₀ = τ ∧
      p.w t₀ = w ∧
      p.c0 ≠ 0 ∧
      (∀ t,
        jacobiTheta1 (p.xi t) (p.tau t : ℂ) ≠ 0) ∧
      z = p.jacobiBlochPath := by
  obtain ⟨S, ξ, L, hS, hcore⟩ :=
    exists_blochGauge_core_eq_of_canonical_residual
      τ (z t₀) w hp2 hp3 hp4 hH hR1 hR2
        (hreciprocal t₀)
  let p :=
    selectedAffineBlochParameters
      τ w ν κ S ξ L t₀
  have hp0 :
      jacobiCorePoint (z t₀) =
        jacobiCorePoint (p.jacobiBlochPath t₀) := by
    rw [selectedAffineBlochParameters.corePoint_at]
    exact hcore
  have hcontinue :=
    p.regular_and_eq_jacobiBlochPath_of_core_eq_at
      hz
      (selectedAffineBlochParameters.c0_ne_zero
        τ w ν κ S ξ L t₀ hS)
      hreciprocal hp0
  exact
    ⟨p, rfl, rfl,
      selectedAffineBlochParameters.tau_at
        τ w ν κ S ξ L t₀,
      selectedAffineBlochParameters.w_at
        τ w ν κ S ξ L t₀,
      selectedAffineBlochParameters.c0_ne_zero
        τ w ν κ S ξ L t₀ hS,
      hcontinue⟩

end

end HGAS.Modular
