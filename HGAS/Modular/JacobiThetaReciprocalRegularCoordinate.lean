import HGAS.Modular.JacobiThetaJointLocalInverse
import HGAS.Modular.JacobiThetaReciprocalFiberRigidity

/-!
# A regular reciprocal theta coordinate with rigid complementary signs

The local-rank theorem selects a normalized theta coordinate whose
vertical derivative is nonzero.  For the later local chart argument we
also need the other two coordinates to be nonzero: their signs can then
be fixed locally by the two residual quadrics.

These two facts are not independent.  The three Wronskian identities
say

```
  (θ₂/θ₁)' ∝ θ₃ θ₄,
  (θ₃/θ₁)' ∝ θ₄ θ₂,
  (θ₄/θ₁)' ∝ θ₂ θ₃.
```

Thus a nonzero derivative automatically certifies that the two
complementary reciprocal coordinates are nonzero.  This file records
that implication and packages the analytic local chart together with
the algebraic sign-rigidity hypothesis.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I
open Complex Real

noncomputable section

/-- A nonzero derivative of a selected reciprocal theta coordinate
forces both complementary coordinates to be nonzero. -/
theorem jacobiThetaReciprocalComplementNonzero_of_hasDerivAt_ne_zero
    (τ : ℍ) (z d : ℂ)
    (h1 : jacobiTheta1 z (τ : ℂ) ≠ 0)
    (k : Fin 3)
    (hd : d ≠ 0)
    (hderiv :
      HasDerivAt
        (fun w =>
          jacobiThetaReciprocalCoordinates τ w k)
        d z) :
    JacobiThetaReciprocalComplementNonzero k
      (jacobiThetaReciprocalTotalMap
        ⟨τ, z, h1⟩) := by
  fin_cases k
  · let d₀ : ℂ :=
      -π * (canonicalUnaryRoots τ).p2 *
          jacobiTheta3 z (τ : ℂ) *
            jacobiTheta4 z (τ : ℂ) /
        jacobiTheta1 z (τ : ℂ) ^ 2
    have hcanonical :
        HasDerivAt
          (fun w =>
            jacobiThetaReciprocalCoordinates τ w 0)
          d₀ z := by
      simpa only [d₀,
        jacobiThetaReciprocalCoordinates_zero] using
        hasDerivAt_jacobiTheta2_div_jacobiTheta1_unconditional
          z τ h1
    have hd₀ : d₀ ≠ 0 := by
      rwa [hderiv.unique hcanonical] at hd
    have hnum :
        -π * (canonicalUnaryRoots τ).p2 *
            jacobiTheta3 z (τ : ℂ) *
          jacobiTheta4 z (τ : ℂ) ≠ 0 :=
      (div_ne_zero_iff.mp hd₀).1
    have h34 :
        jacobiTheta3 z (τ : ℂ) *
          jacobiTheta4 z (τ : ℂ) ≠ 0 := by
      exact mul_ne_zero
        (mul_ne_zero_iff.mp
          (mul_ne_zero_iff.mp hnum).1).2
        (mul_ne_zero_iff.mp hnum).2
    exact
      ⟨div_ne_zero (mul_ne_zero_iff.mp h34).1 h1,
        div_ne_zero (mul_ne_zero_iff.mp h34).2 h1⟩
  · let d₀ : ℂ :=
      -π * (canonicalUnaryRoots τ).p3 *
          jacobiTheta4 z (τ : ℂ) *
            jacobiTheta2 z (τ : ℂ) /
        jacobiTheta1 z (τ : ℂ) ^ 2
    have hcanonical :
        HasDerivAt
          (fun w =>
            jacobiThetaReciprocalCoordinates τ w 1)
          d₀ z := by
      simpa only [d₀,
        jacobiThetaReciprocalCoordinates_one] using
        hasDerivAt_jacobiTheta3_div_jacobiTheta1_unconditional
          z τ h1
    have hd₀ : d₀ ≠ 0 := by
      rwa [hderiv.unique hcanonical] at hd
    have hnum :
        -π * (canonicalUnaryRoots τ).p3 *
            jacobiTheta4 z (τ : ℂ) *
          jacobiTheta2 z (τ : ℂ) ≠ 0 :=
      (div_ne_zero_iff.mp hd₀).1
    have h42 :
        jacobiTheta4 z (τ : ℂ) *
          jacobiTheta2 z (τ : ℂ) ≠ 0 := by
      exact mul_ne_zero
        (mul_ne_zero_iff.mp
          (mul_ne_zero_iff.mp hnum).1).2
        (mul_ne_zero_iff.mp hnum).2
    exact
      ⟨div_ne_zero (mul_ne_zero_iff.mp h42).2 h1,
        div_ne_zero (mul_ne_zero_iff.mp h42).1 h1⟩
  · let d₀ : ℂ :=
      -π * (canonicalUnaryRoots τ).p4 *
          jacobiTheta2 z (τ : ℂ) *
            jacobiTheta3 z (τ : ℂ) /
        jacobiTheta1 z (τ : ℂ) ^ 2
    have hcanonical :
        HasDerivAt
          (fun w =>
            jacobiThetaReciprocalCoordinates τ w 2)
          d₀ z := by
      simpa only [d₀,
        jacobiThetaReciprocalCoordinates_two] using
        hasDerivAt_jacobiTheta4_div_jacobiTheta1_unconditional
          z τ h1
    have hd₀ : d₀ ≠ 0 := by
      rwa [hderiv.unique hcanonical] at hd
    have hnum :
        -π * (canonicalUnaryRoots τ).p4 *
            jacobiTheta2 z (τ : ℂ) *
          jacobiTheta3 z (τ : ℂ) ≠ 0 :=
      (div_ne_zero_iff.mp hd₀).1
    have h23 :
        jacobiTheta2 z (τ : ℂ) *
          jacobiTheta3 z (τ : ℂ) ≠ 0 := by
      exact mul_ne_zero
        (mul_ne_zero_iff.mp
          (mul_ne_zero_iff.mp hnum).1).2
        (mul_ne_zero_iff.mp hnum).2
    exact
      ⟨div_ne_zero (mul_ne_zero_iff.mp h23).1 h1,
        div_ne_zero (mul_ne_zero_iff.mp h23).2 h1⟩

/-- Every reciprocal point admits one coordinate with nonzero
derivative and nonzero complementary coordinates. -/
theorem
    exists_jacobiThetaReciprocalRegularCoordinate_hasDerivAt :
    ∀ (τ : ℍ) (z : ℂ)
      (h1 : jacobiTheta1 z (τ : ℂ) ≠ 0),
      ∃ (k : Fin 3) (d : ℂ),
        JacobiThetaReciprocalComplementNonzero k
            (jacobiThetaReciprocalTotalMap
              ⟨τ, z, h1⟩) ∧
          d ≠ 0 ∧
            HasDerivAt
              (fun w =>
                jacobiThetaReciprocalCoordinates τ w k)
              d z := by
  intro τ z h1
  obtain ⟨k, d, hd, hderiv⟩ :=
    exists_jacobiThetaReciprocalCoordinate_hasDerivAt_ne_zero
      τ z h1
  exact
    ⟨k, d,
      jacobiThetaReciprocalComplementNonzero_of_hasDerivAt_ne_zero
        τ z d h1 k hd hderiv,
      hd, hderiv⟩

/-- Combined analytic and algebraic chart package: the selected
ambient coordinate map is locally invertible, and projection from the
residual family to that coordinate is locally injective. -/
theorem
    exists_jacobiThetaReciprocalRegularCoordinateAmbient_localHomeomorph
    (τ : ℍ) (z : ℂ)
    (h1 : jacobiTheta1 z (τ : ℂ) ≠ 0) :
    ∃ (k : Fin 3)
        (e : OpenPartialHomeomorph (ℂ × ℂ) (ℂ × ℂ)),
      JacobiThetaReciprocalComplementNonzero k
          (jacobiThetaReciprocalTotalMap
            ⟨τ, z, h1⟩) ∧
        ((τ : ℂ), z) ∈ e.source ∧
          (e : (ℂ × ℂ) → (ℂ × ℂ)) =
            fun q =>
              (q.1,
                jacobiThetaReciprocalCoordinateAmbient k q) := by
  obtain ⟨k, d, hcomplement, hd, hderiv⟩ :=
    exists_jacobiThetaReciprocalRegularCoordinate_hasDerivAt
      τ z h1
  obtain ⟨e, hp, he⟩ :=
    exists_jacobiThetaReciprocalCoordinateAmbient_localHomeomorph
      k τ z d h1 hd hderiv
  exact ⟨k, e, hcomplement, hp, he⟩

end

end HGAS.Modular
