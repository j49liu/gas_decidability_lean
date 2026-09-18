import HGAS.Modular.JacobiThetaReciprocalCovering
import HGAS.Modular.JacobiThetaInitialRankUnconditional

/-!
# Local rank of the reciprocal theta parametrization

On the chart `θ₁ ≠ 0`, the three normalized coordinates are

```
  θ₂/θ₁,  θ₃/θ₁,  θ₄/θ₁.
```

The unconditional Wronskian formulas compute all three derivatives.
The two residual quadrics imply that no two of the three even theta
coordinates can vanish simultaneously.  Therefore at least one of the
three displayed ratios has nonzero derivative at every reciprocal-chart
point.

This is the exact analytic input for the local-homeomorphism part of a
covering proof.  Indeed, the complex inverse-function theorem supplies a
local inverse for the selected ratio, while the two normalized residual
equations determine the other two coordinates locally (their signs are
fixed near the base point).
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I
open Complex Real

noncomputable section

/-- Every point of the normalized residual family is nonsingular in the
elementary sense needed below: no two of its three affine coordinates
vanish simultaneously. -/
theorem jacobiThetaReciprocalTotal_no_two_coordinates_zero
    (p : JacobiThetaReciprocalTotal) :
    ¬ (p.coordinates 0 = 0 ∧ p.coordinates 1 = 0) ∧
      ¬ (p.coordinates 0 = 0 ∧ p.coordinates 2 = 0) ∧
        ¬ (p.coordinates 1 = 0 ∧ p.coordinates 2 = 0) := by
  have hQ1 :
      jacobiResidualQ1
          (canonicalUnaryRoots p.modulus).p2
          (canonicalUnaryRoots p.modulus).p3
          (canonicalUnaryRoots p.modulus).p4
          (jacobiThetaReciprocalRepresentative
            p.coordinates) = 0 := by
    rw [jacobiResidualQ1_reciprocalRepresentative]
    exact p.q1
  have hQ2 :
      jacobiResidualQ2
          (canonicalUnaryRoots p.modulus).p2
          (canonicalUnaryRoots p.modulus).p3
          (canonicalUnaryRoots p.modulus).p4
          (jacobiThetaReciprocalRepresentative
            p.coordinates) = 0 := by
    rw [jacobiResidualQ2_reciprocalRepresentative]
    exact p.q2
  have hno :=
    jacobiResidual_no_two_even_zero
      (canonicalUnaryRoots_p_product_ne_zero p.modulus)
      (canonicalUnaryRoots_p3_sq_eq p.modulus)
      (jacobiThetaReciprocalRepresentative_ne_zero
        p.coordinates)
      hQ1 hQ2
  simpa [jacobiThetaReciprocalRepresentative] using hno

/-- At every reciprocal-chart point, one normalized theta coordinate
has a nonzero complex derivative.  The result returns both the derivative
and its `HasDerivAt` certificate so it can be fed directly to the complex
inverse-function theorem. -/
theorem exists_jacobiThetaReciprocalCoordinate_hasDerivAt_ne_zero
    (τ : ℍ) (z : ℂ)
    (h1 : jacobiTheta1 z (τ : ℂ) ≠ 0) :
    ∃ (k : Fin 3) (d : ℂ),
      d ≠ 0 ∧
        HasDerivAt
          (fun w =>
            jacobiThetaReciprocalCoordinates τ w k)
          d z := by
  let p2 := (canonicalUnaryRoots τ).p2
  let p3 := (canonicalUnaryRoots τ).p3
  let p4 := (canonicalUnaryRoots τ).p4
  have hp :=
    canonicalUnaryRoots_p_product_ne_zero τ
  have hp' : p2 * p3 * p4 ≠ 0 := by
    simpa only [p2, p3, p4] using hp
  have hp23 : p2 * p3 ≠ 0 :=
    (mul_ne_zero_iff.mp hp').1
  have hp2 : p2 ≠ 0 :=
    (mul_ne_zero_iff.mp hp23).1
  have hp3 : p3 ≠ 0 :=
    (mul_ne_zero_iff.mp hp23).2
  have hp4 : p4 ≠ 0 :=
    (mul_ne_zero_iff.mp hp').2
  have hpi : (π : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr pi_ne_zero
  have hno :=
    jacobiResidual_no_two_even_zero
      (canonicalUnaryRoots_p_product_ne_zero τ)
      (canonicalUnaryRoots_p3_sq_eq τ)
      (jacobiThetaVector_ne_zero z τ)
      (canonical_jacobiResidualQ1_jacobiThetaVector z τ)
      (canonical_jacobiResidualQ2_jacobiThetaVector z τ)
  by_cases h2 :
      jacobiTheta2 z (τ : ℂ) = 0
  · have h3 :
        jacobiTheta3 z (τ : ℂ) ≠ 0 := by
      intro hz
      apply hno.1
      simpa [jacobiThetaVector] using And.intro h2 hz
    have h4 :
        jacobiTheta4 z (τ : ℂ) ≠ 0 := by
      intro hz
      apply hno.2.1
      simpa [jacobiThetaVector] using And.intro h2 hz
    let d : ℂ :=
      -π * p2 *
          jacobiTheta3 z (τ : ℂ) *
            jacobiTheta4 z (τ : ℂ) /
        jacobiTheta1 z (τ : ℂ) ^ 2
    have hd : d ≠ 0 := by
      exact div_ne_zero
        (mul_ne_zero
          (mul_ne_zero
            (mul_ne_zero
              (neg_ne_zero.mpr hpi) hp2) h3) h4)
        (pow_ne_zero 2 h1)
    refine ⟨0, d, hd, ?_⟩
    simpa only [d, p2,
      jacobiThetaReciprocalCoordinates_zero] using
      hasDerivAt_jacobiTheta2_div_jacobiTheta1_unconditional
        z τ h1
  · by_cases h3 :
        jacobiTheta3 z (τ : ℂ) = 0
    · have h4 :
          jacobiTheta4 z (τ : ℂ) ≠ 0 := by
        intro hz
        apply hno.2.2
        simpa [jacobiThetaVector] using And.intro h3 hz
      let d : ℂ :=
        -π * p3 *
            jacobiTheta4 z (τ : ℂ) *
              jacobiTheta2 z (τ : ℂ) /
          jacobiTheta1 z (τ : ℂ) ^ 2
      have hd : d ≠ 0 := by
        exact div_ne_zero
          (mul_ne_zero
            (mul_ne_zero
              (mul_ne_zero
                (neg_ne_zero.mpr hpi) hp3) h4) h2)
          (pow_ne_zero 2 h1)
      refine ⟨1, d, hd, ?_⟩
      simpa only [d, p3,
        jacobiThetaReciprocalCoordinates_one] using
        hasDerivAt_jacobiTheta3_div_jacobiTheta1_unconditional
          z τ h1
    · let d : ℂ :=
        -π * p4 *
            jacobiTheta2 z (τ : ℂ) *
              jacobiTheta3 z (τ : ℂ) /
          jacobiTheta1 z (τ : ℂ) ^ 2
      have hd : d ≠ 0 := by
        exact div_ne_zero
          (mul_ne_zero
            (mul_ne_zero
              (mul_ne_zero
                (neg_ne_zero.mpr hpi) hp4) h2) h3)
          (pow_ne_zero 2 h1)
      refine ⟨2, d, hd, ?_⟩
      simpa only [d, p4,
        jacobiThetaReciprocalCoordinates_two] using
        hasDerivAt_jacobiTheta4_div_jacobiTheta1_unconditional
          z τ h1

/-- Derivative-only form of the local-rank theorem. -/
theorem exists_deriv_jacobiThetaReciprocalCoordinate_ne_zero
    (τ : ℍ) (z : ℂ)
    (h1 : jacobiTheta1 z (τ : ℂ) ≠ 0) :
    ∃ k : Fin 3,
      deriv
        (fun w =>
          jacobiThetaReciprocalCoordinates τ w k) z ≠ 0 := by
  obtain ⟨k, d, hd, hderiv⟩ :=
    exists_jacobiThetaReciprocalCoordinate_hasDerivAt_ne_zero
      τ z h1
  refine ⟨k, ?_⟩
  rwa [hderiv.deriv]

end

end HGAS.Modular
