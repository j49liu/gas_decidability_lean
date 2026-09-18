import HGAS.Modular.JacobiBlochInitialData
import HGAS.Modular.JacobiThetaResiduals

/-!
# Pointwise Jacobi saturation from projective theta coverage

The global geometric step in the Jacobi argument says that every nonzero
common zero of the two residual quadrics is a nonzero scalar multiple of a
four-theta vector.  This file isolates that statement as
`CanonicalJacobiProjectiveCoverage` and proves everything that follows from
it in the pointwise saturation proposition.

In particular, for any prescribed nonzero first theta coordinate and any
prescribed normalized derivative `Δ`, Lean constructs:

* an elliptic parameter `ξ`;
* a nonzero common scale `S`;
* the unique Bloch logarithmic slope `L`;
* the explicit Bloch parameters `a=L/(2i)`, `b`, and `C`;
* a theta-valued Bloch solution with the required value and derivative.

Thus the only hypothesis of the main theorem below is the genuinely global
projective-coverage assertion.  No dimension-count argument is used.
-/

namespace HGAS.Modular

open Complex Real
open UpperHalfPlane hiding I

noncomputable section

/-- The exact affine-cone form of surjectivity of the projective four-theta
map.  It avoids committing downstream modules to a particular construction
of projective space or the level-two elliptic quotient. -/
def CanonicalJacobiProjectiveCoverage
    (τ : ℍ) : Prop :=
  ∀ X : Fin 4 → ℂ,
    X ≠ 0 →
    jacobiResidualQ1
        (canonicalUnaryRoots τ).p2
        (canonicalUnaryRoots τ).p3
        (canonicalUnaryRoots τ).p4 X = 0 →
    jacobiResidualQ2
        (canonicalUnaryRoots τ).p2
        (canonicalUnaryRoots τ).p3
        (canonicalUnaryRoots τ).p4 X = 0 →
    ∃ (ξ S : ℂ),
      S ≠ 0 ∧
        X = S • jacobiThetaVector ξ (τ : ℂ)

/-- The scalar correction appearing in the last coordinate of the Jacobi
initial-value map. -/
def jacobiThetaNormalizedPrime1
    (τ : ℂ) (ξ : ℂ) : ℂ :=
  jacobiThetaVectorPrime ξ τ 0 / π

/-- **Pointwise Jacobi--Bloch saturation.**

Assuming global projective theta coverage, every regular residual point with
nonzero first coordinate is realized by the explicit Bloch solution, with an
arbitrarily prescribed normalized first derivative. -/
theorem pointwiseJacobiBlochSaturation_of_projectiveCoverage
    (τ : ℍ)
    (hcover : CanonicalJacobiProjectiveCoverage τ)
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
  obtain ⟨ξ, S, hS, hscale⟩ :=
    hcover X hX hQ1 hQ2
  have htheta1 :
      jacobiThetaVector ξ (τ : ℂ) 0 ≠ 0 := by
    intro hzero
    apply hX₁
    rw [hscale]
    simp [hzero]
  let L :=
    jacobiInitialValueBlochSlope
      S
      (jacobiThetaNormalizedPrime1 (τ : ℂ) ξ)
      (jacobiThetaVector ξ (τ : ℂ) 0)
      Δ
  have hinitial :=
    jacobiInitialValueMap_at_blochSlope
      (fun z ↦ jacobiThetaVector z (τ : ℂ))
      (jacobiThetaNormalizedPrime1 (τ : ℂ))
      S ξ Δ hS htheta1
  have hlast :
      S *
          (jacobiThetaNormalizedPrime1 (τ : ℂ) ξ +
            L * jacobiThetaVector ξ (τ : ℂ) 0) =
        Δ := by
    have hsnd := congrArg Prod.snd hinitial
    simpa [jacobiInitialValueMap, L] using hsnd
  refine ⟨S, ξ, L, hS, hscale, ?_, ?_, ?_⟩
  · simpa [L, ← hscale] using hinitial
  · rw [jacobiBlochThetaVector_selected, ← hscale]
  · rw [jacobiBlochThetaVectorPrime_selected_zero_div_pi]
    simpa [jacobiThetaNormalizedPrime1] using hlast

end

end HGAS.Modular
