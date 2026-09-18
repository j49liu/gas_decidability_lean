import HGAS.Modular.JacobiPointwiseSaturation
import HGAS.Modular.JacobiThetaProjectiveSurjectivity

/-!
# Unconditional pointwise Jacobi--Bloch saturation

`JacobiPointwiseSaturation` isolates global projective theta coverage as
an abstract input.  `JacobiThetaProjectiveSurjectivity` now proves that
input.  This file is the deliberately small bridge between the reusable
abstract theorem and its canonical unconditional specialization.
-/

namespace HGAS.Modular

open Complex Real
open UpperHalfPlane hiding I

noncomputable section

/-- The canonical four-theta map has the affine-up-to-scale coverage
property expected by the abstract pointwise saturation theorem. -/
theorem canonicalJacobiProjectiveCoverage
    (τ : ℍ) :
    CanonicalJacobiProjectiveCoverage τ := by
  intro X hX hQ1 hQ2
  rcases
      exists_smul_jacobiThetaVector_eq_of_residual
        τ X hX hQ1 hQ2 with
    ⟨ξ, S, hS, hscale⟩
  exact ⟨ξ, S, hS, hscale.symm⟩

/-- **Unconditional pointwise Jacobi--Bloch saturation.**

Every nonzero canonical residual point whose first coordinate is nonzero
is realized by the explicit Bloch-theta family, with any prescribed
normalized first derivative. -/
theorem pointwiseJacobiBlochSaturation
    (τ : ℍ)
    (X : Fin 4 → ℂ)
    (Δ w : ℂ)
    (hX : X ≠ 0)
    (hX₁ : X 0 ≠ 0)
    (hQ1 :
      jacobiResidualQ1
          (canonicalUnaryRoots τ).p2
          (canonicalUnaryRoots τ).p3
          (canonicalUnaryRoots τ).p4 X = 0)
    (hQ2 :
      jacobiResidualQ2
          (canonicalUnaryRoots τ).p2
          (canonicalUnaryRoots τ).p3
          (canonicalUnaryRoots τ).p4 X = 0) :
    ∃ (S ξ L : ℂ),
      S ≠ 0 ∧
      X = S • jacobiThetaVector ξ (τ : ℂ) ∧
      jacobiInitialValueMap
          (fun z ↦ jacobiThetaVector z (τ : ℂ))
          (jacobiThetaNormalizedPrime1 (τ : ℂ))
          (S, ξ, L) =
        (X, Δ) ∧
      jacobiBlochThetaVector
          (jacobiBlochParameterC S w (τ : ℂ) L)
          (jacobiBlochParameterA L)
          (jacobiBlochParameterB ξ w (τ : ℂ) L)
          (τ : ℂ) w =
        X ∧
      jacobiBlochThetaVectorPrime
            (jacobiBlochParameterC S w (τ : ℂ) L)
            (jacobiBlochParameterA L)
            (jacobiBlochParameterB ξ w (τ : ℂ) L)
            (τ : ℂ) w 0 / π =
        Δ := by
  exact
    pointwiseJacobiBlochSaturation_of_projectiveCoverage
      τ (canonicalJacobiProjectiveCoverage τ)
      X Δ w hX hX₁ hQ1 hQ2

end

end HGAS.Modular
