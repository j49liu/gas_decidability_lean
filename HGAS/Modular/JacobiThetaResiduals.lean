import HGAS.Modular.JacobiThetaDuplication
import HGAS.Modular.JacobiThetaVectorNonvanishing
import HGAS.Modular.CanonicalUnaryRoots
import HGAS.Modular.ThetaZeroFree
import HGAS.Modular.JacobiResidualLocalRegularity

/-!
# The projective theta map lies on the Jacobi residual curve

The duplication formulas proved from the theta series in
`JacobiThetaDuplication` imply the two classical quadratic identities

```
 θ₂(0)² θ₄(z)² - θ₄(0)² θ₂(z)² - θ₃(0)² θ₁(z)² = 0,
 θ₂(0)² θ₃(z)² - θ₃(0)² θ₂(z)² - θ₄(0)² θ₁(z)² = 0.
```

These are exactly the residual equations `Q₁=Q₂=0` in the normalization
used by the selector.  This file proves the identities, identifies their
coefficients with `canonicalUnaryRoots`, and combines them with the
no-common-zero and Jacobian-rank theorems.  Consequently every value of
the four-theta map is an honest nonzero smooth point of the residual cone.

The remaining global saturation step is not hidden here: one still has to
prove that the induced map from the compact level-two elliptic curve is
surjective onto the complete projective residual curve.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I
open Complex Real

noncomputable section

/-! ## Theta constants in the two notational systems -/

theorem jacobiTheta2_zero_eq_theta₂
    (τ : ℍ) :
    jacobiTheta2 0 (τ : ℂ) = theta₂ τ := by
  rw [theta₂_eq_jacobiTheta₂, jacobiTheta2]
  simp only [zero_add]
  congr 1
  ring

theorem jacobiTheta3_zero_eq_theta₃
    (τ : ℍ) :
    jacobiTheta3 0 (τ : ℂ) = theta₃ τ := by
  simpa only [jacobiTheta3] using
    (theta₃_eq_jacobiTheta₂ τ).symm

theorem jacobiTheta4_zero_eq_theta₄
    (τ : ℍ) :
    jacobiTheta4 0 (τ : ℂ) = theta₄ τ := by
  simpa only [jacobiTheta4, zero_add] using
    (theta₄_eq_jacobiTheta₂ τ).symm

/-! ## The two quadratic theta identities -/

/-- The first quadratic Jacobi identity, derived solely from the four
duplication formulas. -/
theorem jacobiTheta_residualQ1_identity
    (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiTheta2 0 τ ^ 2 *
          jacobiTheta4 z τ ^ 2 -
        jacobiTheta4 0 τ ^ 2 *
          jacobiTheta2 z τ ^ 2 -
      jacobiTheta3 0 τ ^ 2 *
          jacobiTheta1 z τ ^ 2 =
      0 := by
  have h20 :=
    jacobiTheta2_sq_duplication (0 : ℂ) hτ
  have h30 :=
    jacobiTheta3_sq_duplication (0 : ℂ) hτ
  have h40 :=
    jacobiTheta4_sq_duplication (0 : ℂ) hτ
  have h1z :=
    jacobiTheta1_sq_duplication z hτ
  have h2z :=
    jacobiTheta2_sq_duplication z hτ
  have h4z :=
    jacobiTheta4_sq_duplication z hτ
  rw [h20, h30, h40, h1z, h2z, h4z]
  ring

/-- The second quadratic Jacobi identity. -/
theorem jacobiTheta_residualQ2_identity
    (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiTheta2 0 τ ^ 2 *
          jacobiTheta3 z τ ^ 2 -
        jacobiTheta3 0 τ ^ 2 *
          jacobiTheta2 z τ ^ 2 -
      jacobiTheta4 0 τ ^ 2 *
          jacobiTheta1 z τ ^ 2 =
      0 := by
  have h20 :=
    jacobiTheta2_sq_duplication (0 : ℂ) hτ
  have h30 :=
    jacobiTheta3_sq_duplication (0 : ℂ) hτ
  have h40 :=
    jacobiTheta4_sq_duplication (0 : ℂ) hτ
  have h1z :=
    jacobiTheta1_sq_duplication z hτ
  have h2z :=
    jacobiTheta2_sq_duplication z hτ
  have h3z :=
    jacobiTheta3_sq_duplication z hτ
  rw [h20, h30, h40, h1z, h2z, h3z]
  ring

/-- The fourth-power Jacobi identity for the three even theta constants,
also obtained directly from duplication. -/
theorem jacobiTheta_even_quartic_identity
    (τ : ℂ) (hτ : 0 < τ.im) :
    jacobiTheta3 0 τ ^ 4 =
      jacobiTheta2 0 τ ^ 4 +
        jacobiTheta4 0 τ ^ 4 := by
  have h20 :=
    jacobiTheta2_sq_duplication (0 : ℂ) hτ
  have h30 :=
    jacobiTheta3_sq_duplication (0 : ℂ) hτ
  have h40 :=
    jacobiTheta4_sq_duplication (0 : ℂ) hτ
  rw [show jacobiTheta3 0 τ ^ 4 =
      (jacobiTheta3 0 τ ^ 2) ^ 2 by ring,
    show jacobiTheta2 0 τ ^ 4 =
      (jacobiTheta2 0 τ ^ 2) ^ 2 by ring,
    show jacobiTheta4 0 τ ^ 4 =
      (jacobiTheta4 0 τ ^ 2) ^ 2 by ring,
    h20, h30, h40]
  ring

/-! ## Exact residual-curve packaging -/

/-- The theta vector satisfies the first residual quadric. -/
theorem jacobiResidualQ1_jacobiThetaVector
    (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiResidualQ1
        (jacobiTheta2 0 τ ^ 2)
        (jacobiTheta3 0 τ ^ 2)
        (jacobiTheta4 0 τ ^ 2)
        (jacobiThetaVector z τ) =
      0 := by
  simpa [jacobiResidualQ1, jacobiThetaVector] using
    jacobiTheta_residualQ1_identity z τ hτ

/-- The theta vector satisfies the second residual quadric. -/
theorem jacobiResidualQ2_jacobiThetaVector
    (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiResidualQ2
        (jacobiTheta2 0 τ ^ 2)
        (jacobiTheta3 0 τ ^ 2)
        (jacobiTheta4 0 τ ^ 2)
        (jacobiThetaVector z τ) =
      0 := by
  simpa [jacobiResidualQ2, jacobiThetaVector] using
    jacobiTheta_residualQ2_identity z τ hτ

/-- The coefficients occurring in the series identities are literally
the three coefficient fields of the canonical unary-root state. -/
theorem canonicalUnaryRoots_eq_jacobiTheta_constants
    (τ : ℍ) :
    ((canonicalUnaryRoots τ).p2,
      (canonicalUnaryRoots τ).p3,
      (canonicalUnaryRoots τ).p4) =
    (jacobiTheta2 0 (τ : ℂ) ^ 2,
      jacobiTheta3 0 (τ : ℂ) ^ 2,
      jacobiTheta4 0 (τ : ℂ) ^ 2) := by
  simp only [canonicalUnaryRoots_p2,
    canonicalUnaryRoots_p3, canonicalUnaryRoots_p4,
    jacobiTheta2_zero_eq_theta₂,
    jacobiTheta3_zero_eq_theta₃,
    jacobiTheta4_zero_eq_theta₄]

/-- Canonically normalized theta values satisfy `Q₁=0`. -/
theorem canonical_jacobiResidualQ1_jacobiThetaVector
    (z : ℂ) (τ : ℍ) :
    jacobiResidualQ1
        (canonicalUnaryRoots τ).p2
        (canonicalUnaryRoots τ).p3
        (canonicalUnaryRoots τ).p4
        (jacobiThetaVector z (τ : ℂ)) =
      0 := by
  rw [canonicalUnaryRoots_p2,
    canonicalUnaryRoots_p3,
    canonicalUnaryRoots_p4,
    ← jacobiTheta2_zero_eq_theta₂,
    ← jacobiTheta3_zero_eq_theta₃,
    ← jacobiTheta4_zero_eq_theta₄]
  exact jacobiResidualQ1_jacobiThetaVector
    z τ τ.im_pos

/-- Canonically normalized theta values satisfy `Q₂=0`. -/
theorem canonical_jacobiResidualQ2_jacobiThetaVector
    (z : ℂ) (τ : ℍ) :
    jacobiResidualQ2
        (canonicalUnaryRoots τ).p2
        (canonicalUnaryRoots τ).p3
        (canonicalUnaryRoots τ).p4
        (jacobiThetaVector z (τ : ℂ)) =
      0 := by
  rw [canonicalUnaryRoots_p2,
    canonicalUnaryRoots_p3,
    canonicalUnaryRoots_p4,
    ← jacobiTheta2_zero_eq_theta₂,
    ← jacobiTheta3_zero_eq_theta₃,
    ← jacobiTheta4_zero_eq_theta₄]
  exact jacobiResidualQ2_jacobiThetaVector
    z τ τ.im_pos

/-! ## Smoothness at every theta value -/

theorem canonicalUnaryRoots_p_product_ne_zero
    (τ : ℍ) :
    (canonicalUnaryRoots τ).p2 *
        (canonicalUnaryRoots τ).p3 *
      (canonicalUnaryRoots τ).p4 ≠ 0 := by
  have h2 : theta₂ τ ≠ 0 := by
    intro h
    apply H₂_ne_zero τ
    simp [H₂, h]
  have h3 : theta₃ τ ≠ 0 := by
    intro h
    apply H₃_ne_zero τ
    simp [H₃, h]
  have h4 : theta₄ τ ≠ 0 := by
    intro h
    apply H₄_ne_zero τ
    simp [H₄, h]
  simp only [canonicalUnaryRoots_p2,
    canonicalUnaryRoots_p3, canonicalUnaryRoots_p4]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 h2)
    (pow_ne_zero 2 h3)) (pow_ne_zero 2 h4)

/-- At every canonical theta value, the derivative of the paired
residual map has full rank two. -/
theorem canonical_jacobiTheta_residualPairFDeriv_surjective
    (z : ℂ) (τ : ℍ) :
    Function.Surjective
      (jacobiResidualPairFDeriv
        (canonicalUnaryRoots τ).p2
        (canonicalUnaryRoots τ).p3
        (canonicalUnaryRoots τ).p4
        (jacobiThetaVector z (τ : ℂ))) := by
  exact jacobiResidualPairFDeriv_surjective
    (canonicalUnaryRoots_p_product_ne_zero τ)
    (canonicalUnaryRoots_p3_sq_eq τ)
    (jacobiThetaVector_ne_zero z τ)
    (canonical_jacobiResidualQ1_jacobiThetaVector z τ)
    (canonical_jacobiResidualQ2_jacobiThetaVector z τ)

/-- The affine tangent kernel at a theta value has complex dimension two. -/
theorem canonical_jacobiTheta_residualPairFDeriv_ker_finrank
    (z : ℂ) (τ : ℍ) :
    Module.finrank ℂ
      (jacobiResidualPairFDeriv
        (canonicalUnaryRoots τ).p2
        (canonicalUnaryRoots τ).p3
        (canonicalUnaryRoots τ).p4
        (jacobiThetaVector z (τ : ℂ))).ker =
      2 := by
  exact jacobiResidualPairFDeriv_ker_finrank
    (canonicalUnaryRoots_p_product_ne_zero τ)
    (canonicalUnaryRoots_p3_sq_eq τ)
    (jacobiThetaVector_ne_zero z τ)
    (canonical_jacobiResidualQ1_jacobiThetaVector z τ)
    (canonical_jacobiResidualQ2_jacobiThetaVector z τ)

/-- After quotienting by common scale, the residual tangent at every theta
value is one-dimensional.  This is the exact tangent-space dimension used
in the local part of saturation. -/
theorem canonical_jacobiTheta_projectiveTangent_finrank
    (z : ℂ) (τ : ℍ) :
    Module.finrank ℂ
      ((jacobiResidualPairFDeriv
          (canonicalUnaryRoots τ).p2
          (canonicalUnaryRoots τ).p3
          (canonicalUnaryRoots τ).p4
          (jacobiThetaVector z (τ : ℂ))).ker ⧸
        ℂ ∙ jacobiResidualRadialVector
          (canonicalUnaryRoots τ).p2
          (canonicalUnaryRoots τ).p3
          (canonicalUnaryRoots τ).p4
          (canonical_jacobiResidualQ1_jacobiThetaVector z τ)
          (canonical_jacobiResidualQ2_jacobiThetaVector z τ)) =
      1 := by
  exact jacobiResidual_projectiveTangent_finrank
    (canonicalUnaryRoots_p_product_ne_zero τ)
    (canonicalUnaryRoots_p3_sq_eq τ)
    (jacobiThetaVector_ne_zero z τ)
    (canonical_jacobiResidualQ1_jacobiThetaVector z τ)
    (canonical_jacobiResidualQ2_jacobiThetaVector z τ)

end

end HGAS.Modular
