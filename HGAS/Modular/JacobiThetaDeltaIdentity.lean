import HGAS.Analysis.ComplexLevelTwoReduction
import HGAS.Modular.CanonicalUnaryRootsSolution
import HGAS.Modular.JacobiThetaEllipticTrajectory
import HGAS.Modular.JacobiThetaProjectiveSurjectivity
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Tactic

/-!
# The second-order Jacobi theta identity

This module proves the scalar identity isolated in
`JacobiThetaEllipticTrajectory`:

```
 θ₁ θ₁'' =
   θ₁'² - π² p₃p₄ θ₂² - 4π² K θ₁².
```

The proof is organized so that each analytic ingredient remains
reusable.

* Differentiating the three unconditional Wronskians, and using the two
  theta quadrics, shows that two local formulas for the same
  logarithmic second derivative agree.
* Since `θ₁` and `θ₂` have no common zero, those formulas patch to an
  entire function.
* Theta quasiperiodicity makes the patched function doubly periodic, so
  compact reduction and Liouville make it constant.
* A termwise heat-equation calculation at `z=0`, combined with the
  already proved modular differential equation for the theta constant
  `θ₂(τ)`, shows that the constant is zero.

No product formula and no external theta differential equation is
assumed.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I
open Complex Real Filter Topology
open HGAS.Analysis

noncomputable section

/-! ## Second derivatives and the two error expressions -/

/-- The second elliptic derivative of Jacobi's `θ₂`. -/
def jacobiTheta2Second (z : ℂ) (τ : ℍ) : ℂ :=
  deriv (fun w ↦ jacobiTheta2Prime w (τ : ℂ)) z

theorem hasDerivAt_jacobiTheta2Prime
    (z : ℂ) (τ : ℍ) :
    HasDerivAt
      (fun w ↦ jacobiTheta2Prime w (τ : ℂ))
      (jacobiTheta2Second z τ) z := by
  have hdiff :
      Differentiable ℂ
        (fun w ↦ jacobiTheta2Prime w (τ : ℂ)) := by
    rw [← analyticOnNhd_univ_iff_differentiable]
    exact analyticOnNhd_jacobiTheta2Prime_fixed τ
  exact (hdiff z).hasDerivAt

theorem differentiable_jacobiTheta1Second
    (τ : ℍ) :
    Differentiable ℂ (fun z ↦ jacobiTheta1Second z τ) := by
  have h :=
    (analyticOnNhd_jacobiTheta1Prime_fixed τ).deriv
  rw [analyticOnNhd_univ_iff_differentiable] at h
  simpa only [jacobiTheta1Second] using h

theorem differentiable_jacobiTheta2Second
    (τ : ℍ) :
    Differentiable ℂ (fun z ↦ jacobiTheta2Second z τ) := by
  have h :=
    (analyticOnNhd_jacobiTheta2Prime_fixed τ).deriv
  rw [analyticOnNhd_univ_iff_differentiable] at h
  simpa only [jacobiTheta2Second] using h

/-- Cross-multiplied error in the desired `θ₁` identity. -/
def jacobiThetaDeltaError
    (z : ℂ) (τ : ℍ) : ℂ :=
  jacobiTheta1 z (τ : ℂ) *
      jacobiTheta1Second z τ -
    jacobiTheta1Prime z (τ : ℂ) ^ 2 +
    π ^ 2 *
      (canonicalJacobiThetaState z τ).p3 *
      (canonicalJacobiThetaState z τ).p4 *
      jacobiTheta2 z (τ : ℂ) ^ 2 +
    4 * π ^ 2 *
      JacobiState.K (canonicalJacobiThetaState z τ) *
      jacobiTheta1 z (τ : ℂ) ^ 2

/-- The real-half-period companion error.  It is the same expression
with `θ₁` and `θ₂` interchanged. -/
def jacobiThetaDeltaCompanionError
    (z : ℂ) (τ : ℍ) : ℂ :=
  jacobiTheta2 z (τ : ℂ) *
      jacobiTheta2Second z τ -
    jacobiTheta2Prime z (τ : ℂ) ^ 2 +
    π ^ 2 *
      (canonicalJacobiThetaState z τ).p3 *
      (canonicalJacobiThetaState z τ).p4 *
      jacobiTheta1 z (τ : ℂ) ^ 2 +
    4 * π ^ 2 *
      JacobiState.K (canonicalJacobiThetaState z τ) *
      jacobiTheta2 z (τ : ℂ) ^ 2

theorem differentiable_jacobiThetaDeltaError
    (τ : ℍ) :
    Differentiable ℂ (fun z ↦ jacobiThetaDeltaError z τ) := by
  intro z
  unfold jacobiThetaDeltaError
  simp only [canonicalJacobiThetaState_p3,
    canonicalJacobiThetaState_p4, JacobiState.K,
    canonicalJacobiThetaState_H]
  have hA :=
    (hasDerivAt_jacobiTheta1 z (τ : ℂ)
      τ.im_pos).differentiableAt.mul
        (differentiable_jacobiTheta1Second τ z)
  have hB :=
    (hasDerivAt_jacobiTheta1Prime z τ).differentiableAt.pow 2
  have hC :=
    ((hasDerivAt_jacobiTheta2 z (τ : ℂ)
      τ.im_pos).differentiableAt.pow 2).const_mul
        (π ^ 2 * (canonicalUnaryRoots τ).p3 *
          (canonicalUnaryRoots τ).p4)
  have hD :=
    ((hasDerivAt_jacobiTheta1 z (τ : ℂ)
      τ.im_pos).differentiableAt.pow 2).const_mul
        (4 * π ^ 2 *
          ((canonicalUnaryRoots τ).H +
            ((canonicalUnaryRoots τ).p3 ^ 2 +
              (canonicalUnaryRoots τ).p4 ^ 2) / 12))
  exact ((hA.sub hB).add hC).add hD

theorem differentiable_jacobiThetaDeltaCompanionError
    (τ : ℍ) :
    Differentiable ℂ
      (fun z ↦ jacobiThetaDeltaCompanionError z τ) := by
  intro z
  unfold jacobiThetaDeltaCompanionError
  simp only [canonicalJacobiThetaState_p3,
    canonicalJacobiThetaState_p4, JacobiState.K,
    canonicalJacobiThetaState_H]
  have hA :=
    (hasDerivAt_jacobiTheta2 z (τ : ℂ)
      τ.im_pos).differentiableAt.mul
        (differentiable_jacobiTheta2Second τ z)
  have hB :=
    (hasDerivAt_jacobiTheta2Prime z τ).differentiableAt.pow 2
  have hC :=
    ((hasDerivAt_jacobiTheta1 z (τ : ℂ)
      τ.im_pos).differentiableAt.pow 2).const_mul
        (π ^ 2 * (canonicalUnaryRoots τ).p3 *
          (canonicalUnaryRoots τ).p4)
  have hD :=
    ((hasDerivAt_jacobiTheta2 z (τ : ℂ)
      τ.im_pos).differentiableAt.pow 2).const_mul
        (4 * π ^ 2 *
          ((canonicalUnaryRoots τ).H +
            ((canonicalUnaryRoots τ).p3 ^ 2 +
              (canonicalUnaryRoots τ).p4 ^ 2) / 12))
  exact ((hA.sub hB).add hC).add hD

/-! ## A differentiated Wronskian and the patching identity -/

/-- Derivative of the `θ₂,θ₁` Wronskian. -/
theorem jacobiTheta_wronskian2_second
    (z : ℂ) (τ : ℍ) :
    jacobiTheta2Second z τ *
          jacobiTheta1 z (τ : ℂ) -
        jacobiTheta2 z (τ : ℂ) *
          jacobiTheta1Second z τ +
      π * (canonicalUnaryRoots τ).p2 *
        (jacobiTheta3Prime z (τ : ℂ) *
            jacobiTheta4 z (τ : ℂ) +
          jacobiTheta3 z (τ : ℂ) *
            jacobiTheta4Prime z (τ : ℂ)) =
      0 := by
  let W : ℂ → ℂ := fun w ↦
    jacobiTheta2Prime w (τ : ℂ) *
          jacobiTheta1 w (τ : ℂ) -
        jacobiTheta2 w (τ : ℂ) *
          jacobiTheta1Prime w (τ : ℂ) +
      π * (canonicalUnaryRoots τ).p2 *
        (jacobiTheta3 w (τ : ℂ) *
          jacobiTheta4 w (τ : ℂ))
  have hW : W = 0 := by
    funext w
    change W w = (0 : ℂ)
    unfold W
    have hw := jacobiTheta_wronskian2 w τ.im_pos
    rw [canonicalUnaryRoots_p2,
      ← jacobiTheta2_zero_eq_theta₂]
    linear_combination hw
  have hderiv :
      HasDerivAt W
        (jacobiTheta2Second z τ *
              jacobiTheta1 z (τ : ℂ) +
            jacobiTheta2Prime z (τ : ℂ) *
              jacobiTheta1Prime z (τ : ℂ) -
          (jacobiTheta2Prime z (τ : ℂ) *
                jacobiTheta1Prime z (τ : ℂ) +
              jacobiTheta2 z (τ : ℂ) *
                jacobiTheta1Second z τ) +
          π * (canonicalUnaryRoots τ).p2 *
            (jacobiTheta3Prime z (τ : ℂ) *
                jacobiTheta4 z (τ : ℂ) +
              jacobiTheta3 z (τ : ℂ) *
                jacobiTheta4Prime z (τ : ℂ))) z := by
    unfold W
    have h2p := hasDerivAt_jacobiTheta2Prime z τ
    have h1 :=
      hasDerivAt_jacobiTheta1 z (τ : ℂ) τ.im_pos
    have h2 :=
      hasDerivAt_jacobiTheta2 z (τ : ℂ) τ.im_pos
    have h1p := hasDerivAt_jacobiTheta1Prime z τ
    have h3 :=
      hasDerivAt_jacobiTheta3 z (τ : ℂ) τ.im_pos
    have h4 :=
      hasDerivAt_jacobiTheta4 z (τ : ℂ) τ.im_pos
    convert
      (((h2p.mul h1).sub (h2.mul h1p)).add
        ((h3.mul h4).const_mul
          (π * (canonicalUnaryRoots τ).p2))) using 1
  have hzero : HasDerivAt W 0 z := by
    rw [hW]
    exact hasDerivAt_const z 0
  have heq := hderiv.unique hzero
  linear_combination heq

/-- The two local logarithmic-second-derivative formulas agree after
cross multiplication.  This is a polynomial consequence of:

* the derivative of the first Wronskian;
* all three first-order Wronskians; and
* the two quadratic theta identities.
-/
theorem jacobiThetaDeltaError_patch
    (z : ℂ) (τ : ℍ) :
    jacobiTheta1 z (τ : ℂ) ^ 2 *
        jacobiThetaDeltaCompanionError z τ =
      jacobiTheta2 z (τ : ℂ) ^ 2 *
        jacobiThetaDeltaError z τ := by
  have hD := jacobiTheta_wronskian2_second z τ
  have hW2 :
      jacobiTheta2Prime z (τ : ℂ) *
            jacobiTheta1 z (τ : ℂ) -
          jacobiTheta2 z (τ : ℂ) *
            jacobiTheta1Prime z (τ : ℂ) =
        -π * (canonicalUnaryRoots τ).p2 *
          jacobiTheta3 z (τ : ℂ) *
            jacobiTheta4 z (τ : ℂ) := by
    rw [canonicalUnaryRoots_p2,
      ← jacobiTheta2_zero_eq_theta₂]
    exact jacobiTheta_wronskian2 z τ.im_pos
  have hW3 :
      jacobiTheta3Prime z (τ : ℂ) *
            jacobiTheta1 z (τ : ℂ) -
          jacobiTheta3 z (τ : ℂ) *
            jacobiTheta1Prime z (τ : ℂ) =
        -π * (canonicalUnaryRoots τ).p3 *
          jacobiTheta4 z (τ : ℂ) *
            jacobiTheta2 z (τ : ℂ) := by
    rw [canonicalUnaryRoots_p3,
      ← jacobiTheta3_zero_eq_theta₃]
    exact jacobiTheta_wronskian3 z τ
  have hW4 :
      jacobiTheta4Prime z (τ : ℂ) *
            jacobiTheta1 z (τ : ℂ) -
          jacobiTheta4 z (τ : ℂ) *
            jacobiTheta1Prime z (τ : ℂ) =
        -π * (canonicalUnaryRoots τ).p4 *
          jacobiTheta2 z (τ : ℂ) *
            jacobiTheta3 z (τ : ℂ) := by
    rw [canonicalUnaryRoots_p4,
      ← jacobiTheta4_zero_eq_theta₄]
    exact jacobiTheta_wronskian4 z τ
  have hR1 :
      (canonicalUnaryRoots τ).p2 *
            jacobiTheta4 z (τ : ℂ) ^ 2 -
          (canonicalUnaryRoots τ).p4 *
            jacobiTheta2 z (τ : ℂ) ^ 2 -
        (canonicalUnaryRoots τ).p3 *
            jacobiTheta1 z (τ : ℂ) ^ 2 =
        0 := by
    simpa [jacobiResidualQ1, jacobiThetaVector] using
      canonical_jacobiResidualQ1_jacobiThetaVector z τ
  have hR2 :
      (canonicalUnaryRoots τ).p2 *
            jacobiTheta3 z (τ : ℂ) ^ 2 -
          (canonicalUnaryRoots τ).p3 *
            jacobiTheta2 z (τ : ℂ) ^ 2 -
        (canonicalUnaryRoots τ).p4 *
            jacobiTheta1 z (τ : ℂ) ^ 2 =
        0 := by
    simpa [jacobiResidualQ2, jacobiThetaVector] using
      canonical_jacobiResidualQ2_jacobiThetaVector z τ
  unfold jacobiThetaDeltaError
    jacobiThetaDeltaCompanionError
  simp only [canonicalJacobiThetaState_p3,
    canonicalJacobiThetaState_p4]
  linear_combination
    (jacobiTheta1 z (τ : ℂ) *
      jacobiTheta2 z (τ : ℂ)) * hD -
    (π * (canonicalUnaryRoots τ).p2 *
      jacobiTheta2 z (τ : ℂ) *
      jacobiTheta4 z (τ : ℂ)) * hW3 -
    (π * (canonicalUnaryRoots τ).p2 *
      jacobiTheta2 z (τ : ℂ) *
      jacobiTheta3 z (τ : ℂ)) * hW4 -
    (jacobiTheta1 z (τ : ℂ) *
        jacobiTheta2Prime z (τ : ℂ) +
      jacobiTheta2 z (τ : ℂ) *
        jacobiTheta1Prime z (τ : ℂ) -
      π * (canonicalUnaryRoots τ).p2 *
        jacobiTheta3 z (τ : ℂ) *
        jacobiTheta4 z (τ : ℂ)) * hW2 +
    π ^ 2 *
      ((canonicalUnaryRoots τ).p3 *
          jacobiTheta2 z (τ : ℂ) ^ 2 -
        (canonicalUnaryRoots τ).p2 *
          jacobiTheta3 z (τ : ℂ) ^ 2) * hR1 -
    π ^ 2 * (canonicalUnaryRoots τ).p3 *
      jacobiTheta1 z (τ : ℂ) ^ 2 * hR2

/-! ## Real-half-period shift and the patched entire quotient -/

theorem jacobiTheta1_add_half
    (z τ : ℂ) :
    jacobiTheta1 (z + 1 / 2) τ =
      jacobiTheta2 z τ := by
  rw [jacobiTheta1,
    show z + 1 / 2 + 1 / 2 = z + 1 by ring_nf,
    jacobiTheta2_add_one]
  ring_nf

theorem jacobiTheta2_add_half
    (z τ : ℂ) :
    jacobiTheta2 (z + 1 / 2) τ =
      -jacobiTheta1 z τ := by
  rw [jacobiTheta1]
  ring_nf

theorem jacobiTheta1Prime_add_half
    (z : ℂ) (τ : ℍ) :
    jacobiTheta1Prime (z + 1 / 2) (τ : ℂ) =
      jacobiTheta2Prime z (τ : ℂ) := by
  have hleft :=
    (hasDerivAt_jacobiTheta1
      (z + 1 / 2) (τ : ℂ) τ.im_pos).comp z
        ((hasDerivAt_id z).add_const (1 / 2))
  have hfun :
      (fun w : ℂ ↦
        jacobiTheta1 (w + 1 / 2) (τ : ℂ)) =
      (fun w : ℂ ↦ jacobiTheta2 w (τ : ℂ)) := by
    funext w
    exact jacobiTheta1_add_half w (τ : ℂ)
  have hleft' :
      HasDerivAt
        (fun w : ℂ ↦
          jacobiTheta1 (w + 1 / 2) (τ : ℂ))
        (jacobiTheta1Prime (z + 1 / 2) (τ : ℂ)) z := by
    simpa only [Function.comp_apply, id_eq, mul_one] using hleft
  rw [hfun] at hleft'
  exact hleft'.unique
    (hasDerivAt_jacobiTheta2 z (τ : ℂ) τ.im_pos)

theorem jacobiTheta2Prime_add_half
    (z : ℂ) (τ : ℍ) :
    jacobiTheta2Prime (z + 1 / 2) (τ : ℂ) =
      -jacobiTheta1Prime z (τ : ℂ) := by
  have hleft :=
    (hasDerivAt_jacobiTheta2
      (z + 1 / 2) (τ : ℂ) τ.im_pos).comp z
        ((hasDerivAt_id z).add_const (1 / 2))
  have hfun :
      (fun w : ℂ ↦
        jacobiTheta2 (w + 1 / 2) (τ : ℂ)) =
      (fun w : ℂ ↦ -jacobiTheta1 w (τ : ℂ)) := by
    funext w
    exact jacobiTheta2_add_half w (τ : ℂ)
  have hleft' :
      HasDerivAt
        (fun w : ℂ ↦
          jacobiTheta2 (w + 1 / 2) (τ : ℂ))
        (jacobiTheta2Prime (z + 1 / 2) (τ : ℂ)) z := by
    simpa only [Function.comp_apply, id_eq, mul_one] using hleft
  rw [hfun] at hleft'
  exact hleft'.unique
    (hasDerivAt_jacobiTheta1 z (τ : ℂ)
      τ.im_pos).neg

theorem jacobiTheta1Second_add_half
    (z : ℂ) (τ : ℍ) :
    jacobiTheta1Second (z + 1 / 2) τ =
      jacobiTheta2Second z τ := by
  have hleft :=
    (hasDerivAt_jacobiTheta1Prime
      (z + 1 / 2) τ).comp z
        ((hasDerivAt_id z).add_const (1 / 2))
  have hfun :
      (fun w : ℂ ↦
        jacobiTheta1Prime (w + 1 / 2) (τ : ℂ)) =
      (fun w : ℂ ↦ jacobiTheta2Prime w (τ : ℂ)) := by
    funext w
    exact jacobiTheta1Prime_add_half w τ
  have hleft' :
      HasDerivAt
        (fun w : ℂ ↦
          jacobiTheta1Prime (w + 1 / 2) (τ : ℂ))
        (jacobiTheta1Second (z + 1 / 2) τ) z := by
    simpa only [Function.comp_apply, id_eq, mul_one] using hleft
  rw [hfun] at hleft'
  exact hleft'.unique (hasDerivAt_jacobiTheta2Prime z τ)

theorem jacobiTheta2Second_add_half
    (z : ℂ) (τ : ℍ) :
    jacobiTheta2Second (z + 1 / 2) τ =
      -jacobiTheta1Second z τ := by
  have hleft :=
    (hasDerivAt_jacobiTheta2Prime
      (z + 1 / 2) τ).comp z
        ((hasDerivAt_id z).add_const (1 / 2))
  have hfun :
      (fun w : ℂ ↦
        jacobiTheta2Prime (w + 1 / 2) (τ : ℂ)) =
      (fun w : ℂ ↦ -jacobiTheta1Prime w (τ : ℂ)) := by
    funext w
    exact jacobiTheta2Prime_add_half w τ
  have hleft' :
      HasDerivAt
        (fun w : ℂ ↦
          jacobiTheta2Prime (w + 1 / 2) (τ : ℂ))
        (jacobiTheta2Second (z + 1 / 2) τ) z := by
    simpa only [Function.comp_apply, id_eq, mul_one] using hleft
  rw [hfun] at hleft'
  exact hleft'.unique
    (hasDerivAt_jacobiTheta1Prime z τ).neg

theorem jacobiThetaDeltaError_add_half
    (z : ℂ) (τ : ℍ) :
    jacobiThetaDeltaError (z + 1 / 2) τ =
      jacobiThetaDeltaCompanionError z τ := by
  unfold jacobiThetaDeltaError
    jacobiThetaDeltaCompanionError
  rw [jacobiTheta1_add_half,
    jacobiTheta1Prime_add_half,
    jacobiTheta1Second_add_half,
    jacobiTheta2_add_half]
  simp only [canonicalJacobiThetaState_p3,
    canonicalJacobiThetaState_p4,
    JacobiState.K, canonicalJacobiThetaState_H]
  ring_nf

/-- The globally patched logarithmic-second-derivative error.  The
`θ₁` formula is used on its nonzero chart and the companion `θ₂`
formula is used at zeros of `θ₁`. -/
def jacobiThetaDeltaQuotient
    (z : ℂ) (τ : ℍ) : ℂ :=
  if jacobiTheta1 z (τ : ℂ) = 0 then
    jacobiThetaDeltaCompanionError z τ /
      jacobiTheta2 z (τ : ℂ) ^ 2
  else
    jacobiThetaDeltaError z τ /
      jacobiTheta1 z (τ : ℂ) ^ 2

theorem jacobiThetaDeltaQuotient_eq_error_div
    (z : ℂ) (τ : ℍ)
    (h1 : jacobiTheta1 z (τ : ℂ) ≠ 0) :
    jacobiThetaDeltaQuotient z τ =
      jacobiThetaDeltaError z τ /
        jacobiTheta1 z (τ : ℂ) ^ 2 := by
  simp [jacobiThetaDeltaQuotient, h1]

theorem jacobiThetaDeltaQuotient_eq_companion_div
    (z : ℂ) (τ : ℍ)
    (h2 : jacobiTheta2 z (τ : ℂ) ≠ 0) :
    jacobiThetaDeltaQuotient z τ =
      jacobiThetaDeltaCompanionError z τ /
        jacobiTheta2 z (τ : ℂ) ^ 2 := by
  by_cases h1 : jacobiTheta1 z (τ : ℂ) = 0
  · simp [jacobiThetaDeltaQuotient, h1]
  · rw [jacobiThetaDeltaQuotient, if_neg h1]
    have hpatch := jacobiThetaDeltaError_patch z τ
    field_simp [h1, h2] at hpatch ⊢
    linear_combination -hpatch

theorem differentiable_jacobiThetaDeltaQuotient
    (τ : ℍ) :
    Differentiable ℂ
      (fun z ↦ jacobiThetaDeltaQuotient z τ) := by
  intro z
  by_cases h1 : jacobiTheta1 z (τ : ℂ) = 0
  · have h2 : jacobiTheta2 z (τ : ℂ) ≠ 0 := by
      intro hz
      apply jacobiTheta12_pair_ne_zero z τ
      exact Prod.ext h1 hz
    have h2diff :=
      (hasDerivAt_jacobiTheta2 z (τ : ℂ)
        τ.im_pos).differentiableAt
    have hlocal :
        (fun w ↦ jacobiThetaDeltaQuotient w τ) =ᶠ[𝓝 z]
          (fun w ↦
            jacobiThetaDeltaCompanionError w τ /
              jacobiTheta2 w (τ : ℂ) ^ 2) := by
      filter_upwards [h2diff.continuousAt.eventually_ne h2]
        with w hw
      exact jacobiThetaDeltaQuotient_eq_companion_div w τ hw
    exact
      ((differentiable_jacobiThetaDeltaCompanionError τ z).div
        (h2diff.pow 2) (pow_ne_zero 2 h2))
        |>.congr_of_eventuallyEq hlocal
  · have h1diff :=
      (hasDerivAt_jacobiTheta1 z (τ : ℂ)
        τ.im_pos).differentiableAt
    have hlocal :
        (fun w ↦ jacobiThetaDeltaQuotient w τ) =ᶠ[𝓝 z]
          (fun w ↦
            jacobiThetaDeltaError w τ /
              jacobiTheta1 w (τ : ℂ) ^ 2) := by
      filter_upwards [h1diff.continuousAt.eventually_ne h1]
        with w hw
      exact jacobiThetaDeltaQuotient_eq_error_div w τ hw
    exact
      ((differentiable_jacobiThetaDeltaError τ z).div
        (h1diff.pow 2) (pow_ne_zero 2 h1))
        |>.congr_of_eventuallyEq hlocal

/-! ## Double periodicity of the patched quotient -/

theorem jacobiTheta1Prime_add_one
    (z : ℂ) (τ : ℍ) :
    jacobiTheta1Prime (z + 1) (τ : ℂ) =
      -jacobiTheta1Prime z (τ : ℂ) := by
  rw [show z + 1 = (z + 1 / 2) + 1 / 2 by ring_nf,
    jacobiTheta1Prime_add_half,
    jacobiTheta2Prime_add_half]

theorem jacobiTheta2Prime_add_one
    (z : ℂ) (τ : ℍ) :
    jacobiTheta2Prime (z + 1) (τ : ℂ) =
      -jacobiTheta2Prime z (τ : ℂ) := by
  rw [show z + 1 = (z + 1 / 2) + 1 / 2 by ring_nf,
    jacobiTheta2Prime_add_half,
    jacobiTheta1Prime_add_half]

theorem jacobiTheta1Second_add_one
    (z : ℂ) (τ : ℍ) :
    jacobiTheta1Second (z + 1) τ =
      -jacobiTheta1Second z τ := by
  rw [show z + 1 = (z + 1 / 2) + 1 / 2 by ring_nf,
    jacobiTheta1Second_add_half,
    jacobiTheta2Second_add_half]

theorem jacobiTheta2Second_add_one
    (z : ℂ) (τ : ℍ) :
    jacobiTheta2Second (z + 1) τ =
      -jacobiTheta2Second z τ := by
  rw [show z + 1 = (z + 1 / 2) + 1 / 2 by ring_nf,
    jacobiTheta2Second_add_half,
    jacobiTheta1Second_add_half]

theorem jacobiThetaDeltaError_add_one
    (z : ℂ) (τ : ℍ) :
    jacobiThetaDeltaError (z + 1) τ =
      jacobiThetaDeltaError z τ := by
  unfold jacobiThetaDeltaError
  rw [jacobiTheta1_add_one,
    jacobiTheta1Prime_add_one,
    jacobiTheta1Second_add_one,
    jacobiTheta2_add_one]
  simp only [canonicalJacobiThetaState_p3,
    canonicalJacobiThetaState_p4,
    JacobiState.K, canonicalJacobiThetaState_H]
  ring_nf

theorem jacobiThetaDeltaCompanionError_add_one
    (z : ℂ) (τ : ℍ) :
    jacobiThetaDeltaCompanionError (z + 1) τ =
      jacobiThetaDeltaCompanionError z τ := by
  unfold jacobiThetaDeltaCompanionError
  rw [jacobiTheta2_add_one,
    jacobiTheta2Prime_add_one,
    jacobiTheta2Second_add_one,
    jacobiTheta1_add_one]
  simp only [canonicalJacobiThetaState_p3,
    canonicalJacobiThetaState_p4,
    JacobiState.K, canonicalJacobiThetaState_H]
  ring_nf

theorem periodic_jacobiThetaDeltaQuotient_one
    (τ : ℍ) :
    Function.Periodic
      (fun z ↦ jacobiThetaDeltaQuotient z τ) 1 := by
  intro z
  change
    jacobiThetaDeltaQuotient (z + 1) τ =
      jacobiThetaDeltaQuotient z τ
  unfold jacobiThetaDeltaQuotient
  rw [jacobiTheta1_add_one,
    jacobiThetaDeltaError_add_one,
    jacobiThetaDeltaCompanionError_add_one,
    jacobiTheta2_add_one]
  by_cases h1 : jacobiTheta1 z (τ : ℂ) = 0
  · simp [h1]
  · simp [h1]

/-- Elliptic derivative of the common quasiperiod multiplier. -/
theorem thetaTauMultiplier_hasDerivAt
    (z τ : ℂ) :
    HasDerivAt (fun w ↦ thetaTauMultiplier w τ)
      ((-2 * π * I) * thetaTauMultiplier z τ) z := by
  have hlinear :
      HasDerivAt
        (fun w : ℂ ↦
          -π * I * τ + (-2 * π * I) * w)
        (-2 * π * I) z :=
    by
      simpa only [id_eq, mul_one] using
        ((hasDerivAt_id z).const_mul
          (-2 * π * I)).const_add (-π * I * τ)
  convert hlinear.cexp using 1
  all_goals
    simp [thetaTauMultiplier]
    ring_nf

theorem jacobiTheta1Prime_add_tau
    (z : ℂ) (τ : ℍ) :
    jacobiTheta1Prime (z + (τ : ℂ)) (τ : ℂ) =
      -thetaTauMultiplier z (τ : ℂ) *
        (jacobiTheta1Prime z (τ : ℂ) -
          2 * π * I * jacobiTheta1 z (τ : ℂ)) := by
  have hleft :=
    (hasDerivAt_jacobiTheta1
      (z + (τ : ℂ)) (τ : ℂ) τ.im_pos).comp z
        ((hasDerivAt_id z).add_const (τ : ℂ))
  have hleft' :
      HasDerivAt
        (fun w : ℂ ↦
          jacobiTheta1 (w + (τ : ℂ)) (τ : ℂ))
        (jacobiTheta1Prime
          (z + (τ : ℂ)) (τ : ℂ)) z := by
    simpa only [Function.comp_apply, id_eq, mul_one] using hleft
  have hfun :
      (fun w : ℂ ↦
        jacobiTheta1 (w + (τ : ℂ)) (τ : ℂ)) =
      (fun w : ℂ ↦
        -thetaTauMultiplier w (τ : ℂ) *
          jacobiTheta1 w (τ : ℂ)) := by
    funext w
    exact jacobiTheta1_add_tau w (τ : ℂ)
  rw [hfun] at hleft'
  have hright :=
    (thetaTauMultiplier_hasDerivAt z
      (τ : ℂ)).neg.mul
        (hasDerivAt_jacobiTheta1 z
          (τ : ℂ) τ.im_pos)
  have heq := hleft'.unique hright
  simp only [Pi.neg_apply] at heq
  linear_combination heq

theorem jacobiTheta2Prime_add_tau
    (z : ℂ) (τ : ℍ) :
    jacobiTheta2Prime (z + (τ : ℂ)) (τ : ℂ) =
      thetaTauMultiplier z (τ : ℂ) *
        (jacobiTheta2Prime z (τ : ℂ) -
          2 * π * I * jacobiTheta2 z (τ : ℂ)) := by
  have hleft :=
    (hasDerivAt_jacobiTheta2
      (z + (τ : ℂ)) (τ : ℂ) τ.im_pos).comp z
        ((hasDerivAt_id z).add_const (τ : ℂ))
  have hleft' :
      HasDerivAt
        (fun w : ℂ ↦
          jacobiTheta2 (w + (τ : ℂ)) (τ : ℂ))
        (jacobiTheta2Prime
          (z + (τ : ℂ)) (τ : ℂ)) z := by
    simpa only [Function.comp_apply, id_eq, mul_one] using hleft
  have hfun :
      (fun w : ℂ ↦
        jacobiTheta2 (w + (τ : ℂ)) (τ : ℂ)) =
      (fun w : ℂ ↦
        thetaTauMultiplier w (τ : ℂ) *
          jacobiTheta2 w (τ : ℂ)) := by
    funext w
    exact jacobiTheta2_add_tau w (τ : ℂ)
  rw [hfun] at hleft'
  have hright :=
    (thetaTauMultiplier_hasDerivAt z
      (τ : ℂ)).mul
        (hasDerivAt_jacobiTheta2 z
          (τ : ℂ) τ.im_pos)
  have heq := hleft'.unique hright
  linear_combination heq

theorem jacobiTheta1Second_add_tau
    (z : ℂ) (τ : ℍ) :
    jacobiTheta1Second (z + (τ : ℂ)) τ =
      -thetaTauMultiplier z (τ : ℂ) *
        (jacobiTheta1Second z τ -
          4 * π * I * jacobiTheta1Prime z (τ : ℂ) -
          4 * π ^ 2 * jacobiTheta1 z (τ : ℂ)) := by
  have hleft :=
    (hasDerivAt_jacobiTheta1Prime
      (z + (τ : ℂ)) τ).comp z
        ((hasDerivAt_id z).add_const (τ : ℂ))
  have hleft' :
      HasDerivAt
        (fun w : ℂ ↦
          jacobiTheta1Prime (w + (τ : ℂ)) (τ : ℂ))
        (jacobiTheta1Second
          (z + (τ : ℂ)) τ) z := by
    simpa only [Function.comp_apply, id_eq, mul_one] using hleft
  have hfun :
      (fun w : ℂ ↦
        jacobiTheta1Prime (w + (τ : ℂ)) (τ : ℂ)) =
      (fun w : ℂ ↦
        -thetaTauMultiplier w (τ : ℂ) *
          (jacobiTheta1Prime w (τ : ℂ) -
            2 * π * I * jacobiTheta1 w (τ : ℂ))) := by
    funext w
    exact jacobiTheta1Prime_add_tau w τ
  rw [hfun] at hleft'
  have hinner :=
    (hasDerivAt_jacobiTheta1Prime z τ).sub
      ((hasDerivAt_jacobiTheta1 z
        (τ : ℂ) τ.im_pos).const_mul
          (2 * π * I))
  have hright :=
    (thetaTauMultiplier_hasDerivAt z
      (τ : ℂ)).neg.mul hinner
  have heq := hleft'.unique hright
  simp only [Pi.neg_apply, Pi.sub_apply] at heq
  rw [heq]
  ring_nf
  simp [Complex.I_sq]

theorem jacobiTheta2Second_add_tau
    (z : ℂ) (τ : ℍ) :
    jacobiTheta2Second (z + (τ : ℂ)) τ =
      thetaTauMultiplier z (τ : ℂ) *
        (jacobiTheta2Second z τ -
          4 * π * I * jacobiTheta2Prime z (τ : ℂ) -
          4 * π ^ 2 * jacobiTheta2 z (τ : ℂ)) := by
  have hleft :=
    (hasDerivAt_jacobiTheta2Prime
      (z + (τ : ℂ)) τ).comp z
        ((hasDerivAt_id z).add_const (τ : ℂ))
  have hleft' :
      HasDerivAt
        (fun w : ℂ ↦
          jacobiTheta2Prime (w + (τ : ℂ)) (τ : ℂ))
        (jacobiTheta2Second
          (z + (τ : ℂ)) τ) z := by
    simpa only [Function.comp_apply, id_eq, mul_one] using hleft
  have hfun :
      (fun w : ℂ ↦
        jacobiTheta2Prime (w + (τ : ℂ)) (τ : ℂ)) =
      (fun w : ℂ ↦
        thetaTauMultiplier w (τ : ℂ) *
          (jacobiTheta2Prime w (τ : ℂ) -
            2 * π * I * jacobiTheta2 w (τ : ℂ))) := by
    funext w
    exact jacobiTheta2Prime_add_tau w τ
  rw [hfun] at hleft'
  have hinner :=
    (hasDerivAt_jacobiTheta2Prime z τ).sub
      ((hasDerivAt_jacobiTheta2 z
        (τ : ℂ) τ.im_pos).const_mul
          (2 * π * I))
  have hright :=
    (thetaTauMultiplier_hasDerivAt z
      (τ : ℂ)).mul hinner
  have heq := hleft'.unique hright
  simp only [Pi.sub_apply] at heq
  rw [heq]
  ring_nf
  simp [Complex.I_sq]
  ring_nf

theorem jacobiThetaDeltaError_add_tau
    (z : ℂ) (τ : ℍ) :
    jacobiThetaDeltaError (z + (τ : ℂ)) τ =
      thetaTauMultiplier z (τ : ℂ) ^ 2 *
        jacobiThetaDeltaError z τ := by
  unfold jacobiThetaDeltaError
  rw [jacobiTheta1_add_tau,
    jacobiTheta1Prime_add_tau,
    jacobiTheta1Second_add_tau,
    jacobiTheta2_add_tau]
  simp only [canonicalJacobiThetaState_p3,
    canonicalJacobiThetaState_p4,
    JacobiState.K, canonicalJacobiThetaState_H]
  ring_nf
  simp [Complex.I_sq]

theorem jacobiThetaDeltaCompanionError_add_tau
    (z : ℂ) (τ : ℍ) :
    jacobiThetaDeltaCompanionError (z + (τ : ℂ)) τ =
      thetaTauMultiplier z (τ : ℂ) ^ 2 *
        jacobiThetaDeltaCompanionError z τ := by
  unfold jacobiThetaDeltaCompanionError
  rw [jacobiTheta2_add_tau,
    jacobiTheta2Prime_add_tau,
    jacobiTheta2Second_add_tau,
    jacobiTheta1_add_tau]
  simp only [canonicalJacobiThetaState_p3,
    canonicalJacobiThetaState_p4,
    JacobiState.K, canonicalJacobiThetaState_H]
  ring_nf
  simp [Complex.I_sq]

theorem periodic_jacobiThetaDeltaQuotient_tau
    (τ : ℍ) :
    Function.Periodic
      (fun z ↦ jacobiThetaDeltaQuotient z τ) (τ : ℂ) := by
  intro z
  change
    jacobiThetaDeltaQuotient (z + (τ : ℂ)) τ =
      jacobiThetaDeltaQuotient z τ
  have hM := thetaTauMultiplier_ne_zero z (τ : ℂ)
  by_cases h1 : jacobiTheta1 z (τ : ℂ) = 0
  · have h1shift :
        jacobiTheta1 (z + (τ : ℂ)) (τ : ℂ) = 0 := by
      rw [jacobiTheta1_add_tau, h1, mul_zero]
    rw [jacobiThetaDeltaQuotient, if_pos h1shift,
      jacobiThetaDeltaQuotient, if_pos h1,
      jacobiThetaDeltaCompanionError_add_tau,
      jacobiTheta2_add_tau]
    field_simp [hM]
  · have h1shift :
        jacobiTheta1 (z + (τ : ℂ)) (τ : ℂ) ≠ 0 := by
      rw [jacobiTheta1_add_tau]
      exact mul_ne_zero (neg_ne_zero.mpr hM) h1
    rw [jacobiThetaDeltaQuotient, if_neg h1shift,
      jacobiThetaDeltaQuotient, if_neg h1,
      jacobiThetaDeltaError_add_tau,
      jacobiTheta1_add_tau]
    field_simp [hM, h1]

/-! ## Compact reduction and Liouville -/

/-- The range of the patched quotient is bounded.  The proof reduces
each complex number modulo the periods `1` and `τ` to the closed ball
of radius `1 + Im τ`. -/
theorem isBounded_range_jacobiThetaDeltaQuotient
    (τ : ℍ) :
    Bornology.IsBounded
      (Set.range (fun z ↦ jacobiThetaDeltaQuotient z τ)) := by
  let F : ℂ → ℂ := fun z ↦ jacobiThetaDeltaQuotient z τ
  have hFcont : Continuous F :=
    (differentiable_jacobiThetaDeltaQuotient τ).continuous
  have hcompact :
      IsCompact
        (F '' Metric.closedBall (0 : ℂ) (1 + τ.im)) :=
    (isCompact_closedBall (0 : ℂ) (1 + τ.im)).image hFcont
  apply hcompact.isBounded.subset
  rintro y ⟨z, rfl⟩
  let ξ : ℝ → ℂ := fun _ ↦ z
  let τc : ℝ → ℂ := fun _ ↦ (τ : ℂ)
  let q : ℂ :=
    complexLevelTwoReducedCoordinate τ.im ξ τc 0
  let m : ℤ :=
    complexLevelTwoHorizontalIndex τ.im ξ τc 0
  let n : ℤ :=
    complexLevelTwoVerticalIndex τ.im ξ 0
  have hz :
      z =
        q + 2 * (m : ℂ) +
          2 * (n : ℂ) * (τ : ℂ) := by
    simpa only [ξ, τc, q, m, n] using
      complexLevelTwo_decomposition τ.im ξ τc 0
  have hqre : |q.re| ≤ 1 := by
    simpa only [q] using
      abs_complexLevelTwoReducedCoordinate_re_le_one
        τ.im ξ τc 0
  have hqim : |q.im| ≤ τ.im := by
    simpa only [q] using
      abs_complexLevelTwoReducedCoordinate_im_le
        τ.im_pos ξ τc (by
          intro t
          simp only [τc, UpperHalfPlane.coe_im]) 0
  have hqnorm : ‖q‖ ≤ 1 + τ.im :=
    (Complex.norm_le_abs_re_add_abs_im q).trans
      (add_le_add hqre hqim)
  have hqball :
      q ∈ Metric.closedBall (0 : ℂ) (1 + τ.im) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hqnorm
  refine ⟨q, hqball, ?_⟩
  have hperiodOne :=
    (periodic_jacobiThetaDeltaQuotient_one τ).int_mul
      (2 * m)
  have hperiodTau :=
    (periodic_jacobiThetaDeltaQuotient_tau τ).int_mul
      (2 * n)
  have hperiod := hperiodOne.add_period hperiodTau
  have hq := hperiod q
  change
    jacobiThetaDeltaQuotient q τ =
      jacobiThetaDeltaQuotient z τ
  rw [hz]
  convert hq.symm using 1
  all_goals
    push_cast
    ring_nf

/-- The patched quotient is constant. -/
theorem jacobiThetaDeltaQuotient_eq_const
    (τ : ℍ) :
    ∃ c : ℂ, ∀ z : ℂ,
      jacobiThetaDeltaQuotient z τ = c := by
  exact Differentiable.exists_const_forall_eq_of_bounded
    (differentiable_jacobiThetaDeltaQuotient τ)
    (isBounded_range_jacobiThetaDeltaQuotient τ)

/-! ## The heat equation at the level of the defining series -/

/-- The termwise second derivative in the elliptic variable of
Mathlib's two-variable theta summand. -/
def jacobiTheta₂SecondTerm
    (n : ℤ) (z τ : ℂ) : ℂ :=
  (2 * π * I * (n : ℂ)) ^ 2 *
    jacobiTheta₂_term n z τ

/-- The second elliptic derivative series for Mathlib's theta
function. -/
def jacobiTheta₂Second
    (z τ : ℂ) : ℂ :=
  ∑' n : ℤ, jacobiTheta₂SecondTerm n z τ

theorem summable_jacobiTheta₂SecondTerm
    (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    Summable
      (fun n : ℤ ↦ jacobiTheta₂SecondTerm n z τ) := by
  let b : ℤ → ℝ := fun n ↦
    (|n| ^ 2 : ℝ) *
      Real.exp (-π *
        (τ.im * n ^ 2 - 2 * |z.im| * |n|))
  let u : ℤ → ℝ := fun n ↦
    4 * π ^ 2 * b n
  have hb : Summable b := by
    simpa only [b] using
      summable_pow_mul_jacobiTheta₂_term_bound
        |z.im| hτ 2
  have hu : Summable u := by
    exact hb.mul_left (4 * π ^ 2)
  apply hu.of_norm_bounded
  intro n
  calc
    ‖jacobiTheta₂SecondTerm n z τ‖ =
        4 * π ^ 2 * (↑|n| : ℝ) ^ 2 *
          ‖jacobiTheta₂_term n z τ‖ := by
      unfold jacobiTheta₂SecondTerm
      rw [norm_mul, norm_pow]
      simp only [norm_mul, Complex.norm_two, norm_I,
        Complex.norm_of_nonneg pi_pos.le, norm_intCast,
        ← Int.cast_abs]
      ring_nf
    _ ≤
        4 * π ^ 2 * (↑|n| : ℝ) ^ 2 *
          Real.exp
            (-π * (τ.im * (n : ℝ) ^ 2 -
              2 * |z.im| * (↑|n| : ℝ))) := by
      apply mul_le_mul_of_nonneg_left
      · exact norm_jacobiTheta₂_term_le
          (z := z) (τ := τ) hτ le_rfl le_rfl n
      · positivity
    _ = u n := by
      simp only [u, b]
      ring_nf

/-- Each differentiated theta summand has the expected second
derivative. -/
theorem hasDerivAt_jacobiTheta₂PrimeTerm
    (n : ℤ) (z τ : ℂ) :
    HasDerivAt
      (fun w ↦ jacobiTheta₂'_term n w τ)
      (jacobiTheta₂SecondTerm n z τ) z := by
  let a : ℂ := 2 * π * I * (n : ℂ)
  have hlinear :
      HasDerivAt
        (fun w : ℂ ↦
          a * w + π * I * (n : ℂ) ^ 2 * τ)
        a z := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id z).const_mul a).add_const
        (π * I * (n : ℂ) ^ 2 * τ)
  convert hlinear.cexp.const_mul a using 1
  all_goals
    simp only [a, jacobiTheta₂_term,
      jacobiTheta₂SecondTerm]
    ring_nf

/-- Termwise differentiation of the first elliptic derivative. -/
theorem hasDerivAt_jacobiTheta₂Prime_fst
    (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasDerivAt
      (fun w ↦ jacobiTheta₂' w τ)
      (jacobiTheta₂Second z τ) z := by
  obtain ⟨S, hS⟩ := exists_gt |z.im|
  let V : Set ℂ := {w | |w.im| < S}
  have hVo : IsOpen V := by
    exact
      (_root_.continuous_abs.comp Complex.continuous_im)
        |>.isOpen_preimage _ isOpen_Iio
  have hVp : IsPreconnected V := by
    simpa only [V, Set.mem_setOf_eq, abs_lt] using
      ((convex_halfSpace_im_gt (-S)).inter
        (convex_halfSpace_im_lt S)).isPreconnected
  have hzV : z ∈ V := hS
  let b : ℤ → ℝ := fun n ↦
    (|n| ^ 2 : ℝ) *
      Real.exp (-π *
        (τ.im * n ^ 2 - 2 * S * |n|))
  let u : ℤ → ℝ := fun n ↦
    4 * π ^ 2 * b n
  have hb : Summable b := by
    simpa only [b] using
      summable_pow_mul_jacobiTheta₂_term_bound
        S hτ 2
  have hu : Summable u := by
    exact hb.mul_left (4 * π ^ 2)
  have hbound :
      ∀ n w, w ∈ V →
        ‖jacobiTheta₂SecondTerm n w τ‖ ≤ u n := by
    intro n w hw
    calc
      ‖jacobiTheta₂SecondTerm n w τ‖ =
          4 * π ^ 2 * (↑|n| : ℝ) ^ 2 *
            ‖jacobiTheta₂_term n w τ‖ := by
        unfold jacobiTheta₂SecondTerm
        rw [norm_mul, norm_pow]
        simp only [norm_mul, Complex.norm_two, norm_I,
          Complex.norm_of_nonneg pi_pos.le, norm_intCast,
          ← Int.cast_abs]
        ring_nf
      _ ≤
          4 * π ^ 2 * (↑|n| : ℝ) ^ 2 *
            Real.exp
              (-π * (τ.im * (n : ℝ) ^ 2 -
                2 * S * (↑|n| : ℝ))) := by
        apply mul_le_mul_of_nonneg_left
        · exact norm_jacobiTheta₂_term_le
            (z := w) (τ := τ)
            hτ (le_of_lt hw) le_rfl n
        · positivity
      _ = u n := by
        simp only [u, b]
        ring_nf
  have hsum :
      Summable (fun n : ℤ ↦
        jacobiTheta₂'_term n z τ) :=
    (summable_jacobiTheta₂'_term_iff z τ).2 hτ
  simpa only [jacobiTheta₂', jacobiTheta₂Second] using
    hasDerivAt_tsum_of_isPreconnected
      (u := u) (t := V)
      (g := fun n w ↦ jacobiTheta₂'_term n w τ)
      (g' := fun n w ↦ jacobiTheta₂SecondTerm n w τ)
      (y₀ := z) (y := z)
      hu hVo hVp
      (fun n w _ ↦
        hasDerivAt_jacobiTheta₂PrimeTerm n w τ)
      hbound hzV hsum hzV

/-- The first coordinate of the joint derivative is the usual
elliptic derivative. -/
theorem jacobiTheta₂_fderiv_fst_eq
    (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    (jacobiTheta₂_fderiv z τ) (1, 0) =
      jacobiTheta₂' z τ := by
  have hcurve :
      HasDerivAt
        (fun w : ℂ ↦ (w, τ)) (1, 0) z :=
    (hasDerivAt_id z).prodMk
      (hasDerivAt_const z τ)
  have hjoint :=
    (hasFDerivAt_jacobiTheta₂ z hτ).comp_hasDerivAt
      z hcurve
  have hfixed :=
    hasDerivAt_jacobiTheta₂_fst z hτ
  exact hjoint.unique hfixed

/-- The formal heat equation for Mathlib's two-variable theta
function.  Both sides are obtained from the same normally convergent
series, so no theta differential identity is imported. -/
theorem jacobiTheta₂_heat_equation
    (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta₂Second z τ =
      4 * π * I *
        (jacobiTheta₂_fderiv z τ) (0, 1) := by
  have hsum :
      HasSum
        (fun n : ℤ ↦
          (jacobiTheta₂_term_fderiv n z τ) (0, 1))
        ((jacobiTheta₂_fderiv z τ) (0, 1)) := by
    simpa only [ContinuousLinearMap.apply_apply] using
      (ContinuousLinearMap.apply ℂ ℂ
        ((0, 1) : ℂ × ℂ)).hasSum
          (hasSum_jacobiTheta₂_term_fderiv z hτ)
  have hterm (n : ℤ) :
      (jacobiTheta₂_term_fderiv n z τ) (0, 1) =
        π * I * (n : ℂ) ^ 2 *
          jacobiTheta₂_term n z τ := by
    simp only [jacobiTheta₂_term_fderiv, smul_add,
      ContinuousLinearMap.add_apply,
      ContinuousLinearMap.coe_smul', Pi.smul_apply,
      smul_eq_mul, ContinuousLinearMap.coe_fst',
      mul_zero, ContinuousLinearMap.coe_snd',
      mul_one, zero_add]
    unfold jacobiTheta₂_term
    ring_nf
  have hsum' :
      HasSum
        (fun n : ℤ ↦
          π * I * (n : ℂ) ^ 2 *
            jacobiTheta₂_term n z τ)
        ((jacobiTheta₂_fderiv z τ) (0, 1)) :=
    HasSum.congr_fun hsum (fun n ↦ (hterm n).symm)
  rw [jacobiTheta₂Second, ← hsum'.tsum_eq,
    ← tsum_mul_left]
  apply tsum_congr
  intro n
  unfold jacobiTheta₂SecondTerm
  ring_nf

/-! ## Heat equation for the classical half-characteristic theta -/

/-- Express the second elliptic derivative of classical `θ₂` through
the second derivative series of Mathlib's theta. -/
theorem jacobiTheta2Second_eq_base
    (z : ℂ) (τ : ℍ) :
    jacobiTheta2Second z τ =
      cexp (π * I * ((τ : ℂ) / 4 + z)) *
        ((π * I) ^ 2 *
            jacobiTheta₂ (z + (τ : ℂ) / 2) (τ : ℂ) +
          2 * π * I *
            jacobiTheta₂' (z + (τ : ℂ) / 2) (τ : ℂ) +
          jacobiTheta₂Second
            (z + (τ : ℂ) / 2) (τ : ℂ)) := by
  have hlinear :
      HasDerivAt
        (fun w : ℂ ↦
          π * I * ((τ : ℂ) / 4 + w))
        (π * I) z := by
    convert
      ((hasDerivAt_id z).const_add
        ((τ : ℂ) / 4)).const_mul (π * I) using 1
    ring_nf
  have hE := hlinear.cexp
  have hTheta :=
    (hasDerivAt_jacobiTheta₂_fst
      (z + (τ : ℂ) / 2) τ.im_pos).comp z
        ((hasDerivAt_id z).add_const
          ((τ : ℂ) / 2))
  have hTheta' :
      HasDerivAt
        (fun w : ℂ ↦
          jacobiTheta₂
            (w + (τ : ℂ) / 2) (τ : ℂ))
        (jacobiTheta₂'
          (z + (τ : ℂ) / 2) (τ : ℂ)) z := by
    simpa only [Function.comp_apply, id_eq, mul_one] using hTheta
  have hThetaPrime :=
    (hasDerivAt_jacobiTheta₂Prime_fst
      (z + (τ : ℂ) / 2) τ.im_pos).comp z
        ((hasDerivAt_id z).add_const
          ((τ : ℂ) / 2))
  have hThetaPrime' :
      HasDerivAt
        (fun w : ℂ ↦
          jacobiTheta₂'
            (w + (τ : ℂ) / 2) (τ : ℂ))
        (jacobiTheta₂Second
          (z + (τ : ℂ) / 2) (τ : ℂ)) z := by
    simpa only [Function.comp_apply, id_eq, mul_one] using
      hThetaPrime
  have hinner :=
    hTheta'.const_mul (π * I) |>.add hThetaPrime'
  have hproduct :
      HasDerivAt
        (fun w ↦ jacobiTheta2Prime w (τ : ℂ))
        (cexp (π * I * ((τ : ℂ) / 4 + z)) *
          (π * I) *
            (π * I *
                jacobiTheta₂
                  (z + (τ : ℂ) / 2) (τ : ℂ) +
              jacobiTheta₂'
                (z + (τ : ℂ) / 2) (τ : ℂ)) +
          cexp (π * I * ((τ : ℂ) / 4 + z)) *
            (π * I *
                jacobiTheta₂'
                  (z + (τ : ℂ) / 2) (τ : ℂ) +
              jacobiTheta₂Second
                (z + (τ : ℂ) / 2) (τ : ℂ))) z := by
    unfold jacobiTheta2Prime
    exact hE.mul hinner
  have heq :=
    (hasDerivAt_jacobiTheta2Prime z τ).unique hproduct
  rw [heq]
  ring_nf

/-- Modular-parameter derivative of classical `θ₂`, before invoking
the heat equation. -/
theorem hasDerivAt_jacobiTheta2_snd
    (z : ℂ) (τ : ℍ) :
    HasDerivAt
      (fun w : ℂ ↦ jacobiTheta2 z w)
      (cexp (π * I * ((τ : ℂ) / 4 + z)) *
        (π * I / 4 *
            jacobiTheta₂
              (z + (τ : ℂ) / 2) (τ : ℂ) +
          (jacobiTheta₂_fderiv
              (z + (τ : ℂ) / 2) (τ : ℂ))
            (1 / 2, 1))) (τ : ℂ) := by
  have hlinear :
      HasDerivAt
        (fun w : ℂ ↦ π * I * (w / 4 + z))
        (π * I / 4) (τ : ℂ) := by
    have hdiv :=
      (hasDerivAt_id (τ : ℂ)).div_const 4
    have hadd := hdiv.add_const z
    convert
      hadd.const_mul (π * I) using 1
    ring_nf
  have hE := hlinear.cexp
  have hfirst :
      HasDerivAt
        (fun w : ℂ ↦ z + w / 2)
        (1 / 2) (τ : ℂ) := by
    have hdiv :=
      (hasDerivAt_id (τ : ℂ)).div_const 2
    simpa only [id_eq] using hdiv.const_add z
  have hcurve :
      HasDerivAt
        (fun w : ℂ ↦ (z + w / 2, w))
        (1 / 2, 1) (τ : ℂ) :=
    hfirst.prodMk (hasDerivAt_id (τ : ℂ))
  have hTheta :=
    (hasFDerivAt_jacobiTheta₂
      (z + (τ : ℂ) / 2) τ.im_pos)
      |>.comp_hasDerivAt
        (f := fun w : ℂ ↦ (z + w / 2, w))
        (τ : ℂ) hcurve
  have hTheta' :
      HasDerivAt
        (fun w : ℂ ↦
          jacobiTheta₂ (z + w / 2) w)
        ((jacobiTheta₂_fderiv
          (z + (τ : ℂ) / 2) (τ : ℂ))
            (1 / 2, 1)) (τ : ℂ) := by
    simpa only [Function.comp_apply] using hTheta
  unfold jacobiTheta2
  convert hE.mul hTheta' using 1
  all_goals ring_nf

theorem jacobiTheta₂_fderiv_half_one_eq
    (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    (jacobiTheta₂_fderiv z τ) (1 / 2, 1) =
      1 / 2 * jacobiTheta₂' z τ +
        (jacobiTheta₂_fderiv z τ) (0, 1) := by
  have hv :
      ((1 / 2, 1) : ℂ × ℂ) =
        (1 / 2 : ℂ) • ((1, 0) : ℂ × ℂ) +
          ((0, 1) : ℂ × ℂ) := by
    ext <;> norm_num
  rw [hv, map_add, map_smul,
    jacobiTheta₂_fderiv_fst_eq z hτ]
  simp only [smul_eq_mul]

/-- The classical heat equation in the exact normalization used by the
Jacobi trajectory. -/
theorem jacobiTheta2_heat_equation
    (z : ℂ) (τ : ℍ) :
    jacobiTheta2Second z τ =
      4 * π * I *
        deriv (fun w : ℂ ↦ jacobiTheta2 z w) (τ : ℂ) := by
  rw [jacobiTheta2Second_eq_base,
    (hasDerivAt_jacobiTheta2_snd z τ).deriv,
    jacobiTheta₂_heat_equation
      (z + (τ : ℂ) / 2) τ.im_pos,
    jacobiTheta₂_fderiv_half_one_eq
      (z + (τ : ℂ) / 2) τ.im_pos]
  ring_nf

/-! ## Evaluation at the origin -/

/-- The even theta function has vanishing first elliptic derivative at
the origin. -/
theorem jacobiTheta2Prime_zero
    (τ : ℍ) :
    jacobiTheta2Prime 0 (τ : ℂ) = 0 := by
  have hneg :
      HasDerivAt
        (fun w : ℂ ↦ -w) (-1) 0 := by
    simpa only [id_eq] using
      (hasDerivAt_id (0 : ℂ)).neg
  have hleft :=
    (hasDerivAt_jacobiTheta2
      0 (τ : ℂ) τ.im_pos).comp_of_eq
        0 hneg (by simp)
  have hleft' :
      HasDerivAt
        (fun w : ℂ ↦
          jacobiTheta2 (-w) (τ : ℂ))
        (-jacobiTheta2Prime 0 (τ : ℂ)) 0 := by
    convert hleft using 1
    all_goals ring_nf
  have hfun :
      (fun w : ℂ ↦ jacobiTheta2 (-w) (τ : ℂ)) =
        (fun w : ℂ ↦ jacobiTheta2 w (τ : ℂ)) := by
    funext w
    exact jacobiTheta2_neg w (τ : ℂ)
  rw [hfun] at hleft'
  have heq :=
    hleft'.unique
      (hasDerivAt_jacobiTheta2
        0 (τ : ℂ) τ.im_pos)
  linear_combination (-1 / 2 : ℂ) * heq

/-- At the origin, the heat equation is the normalized modular
derivative identity `θ₂'' = -8π² D θ₂`. -/
theorem jacobiTheta2Second_zero_eq_normalizedDeriv
    (τ : ℍ) :
    jacobiTheta2Second 0 τ =
      -8 * π ^ 2 *
        Derivative.normalizedDerivOfComplex theta₂ τ := by
  have hderiv :
      deriv (theta₂ ∘ ofComplex) (τ : ℂ) =
        deriv (fun w : ℂ ↦ jacobiTheta2 0 w)
          (τ : ℂ) := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards
      [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with w hw
    simpa only [Function.comp_apply,
      ofComplex_apply_of_im_pos hw] using
      (jacobiTheta2_zero_eq_theta₂
        (⟨w, hw⟩ : ℍ)).symm
  have hnormalized :
      deriv (fun w : ℂ ↦ jacobiTheta2 0 w)
          (τ : ℂ) =
        2 * π * I *
          Derivative.normalizedDerivOfComplex theta₂ τ := by
    rw [← hderiv]
    unfold Derivative.normalizedDerivOfComplex
    have hpi : (π : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp [hpi]
  rw [jacobiTheta2_heat_equation, hnormalized]
  ring_nf
  rw [Complex.I_sq]
  ring_nf

/-- The companion error vanishes at the origin.  This is precisely
where the modular differential equation for the theta constant enters
the elliptic proof. -/
theorem jacobiThetaDeltaCompanionError_zero
    (τ : ℍ) :
    jacobiThetaDeltaCompanionError 0 τ = 0 := by
  have hJacobi :=
    congrFun jacobi_quartic_identity τ
  have hDerivative :=
    congrFun normalizedDeriv_theta₂ τ
  unfold jacobiThetaDeltaCompanionError
  rw [jacobiTheta2Second_zero_eq_normalizedDeriv,
    jacobiTheta2Prime_zero, jacobiTheta1_zero,
    jacobiTheta2_zero_eq_theta₂, hDerivative]
  simp only [theta₂NormalizedRHS,
    canonicalJacobiThetaState_p3,
    canonicalJacobiThetaState_p4,
    JacobiState.K, canonicalJacobiThetaState_H,
    canonicalUnaryRoots_p3, canonicalUnaryRoots_p4,
    canonicalUnaryRoots_H, H₂, H₄]
  simp only [H₂, H₃, H₄, Pi.add_apply] at hJacobi
  ring_nf at hJacobi ⊢
  linear_combination
    (-π ^ 2 * theta₂ τ ^ 2 / 3) * hJacobi

/-! ## Vanishing of the error and the unconditional trajectory -/

theorem jacobiThetaDeltaQuotient_zero
    (τ : ℍ) :
    jacobiThetaDeltaQuotient 0 τ = 0 := by
  rw [jacobiThetaDeltaQuotient,
    if_pos (jacobiTheta1_zero (τ : ℂ)),
    jacobiThetaDeltaCompanionError_zero]
  exact zero_div _

theorem jacobiThetaDeltaQuotient_eq_zero
    (z : ℂ) (τ : ℍ) :
    jacobiThetaDeltaQuotient z τ = 0 := by
  calc
    jacobiThetaDeltaQuotient z τ =
        jacobiThetaDeltaQuotient 0 τ :=
      Differentiable.apply_eq_apply_of_bounded
        (differentiable_jacobiThetaDeltaQuotient τ)
        (isBounded_range_jacobiThetaDeltaQuotient τ)
        z 0
    _ = 0 := jacobiThetaDeltaQuotient_zero τ

/-- The cross-multiplied error vanishes everywhere, including at zeros
of `θ₁`. -/
theorem jacobiThetaDeltaError_eq_zero
    (z : ℂ) (τ : ℍ) :
    jacobiThetaDeltaError z τ = 0 := by
  by_cases h1 : jacobiTheta1 z (τ : ℂ) = 0
  · have h2 : jacobiTheta2 z (τ : ℂ) ≠ 0 := by
      intro h2zero
      apply jacobiTheta12_pair_ne_zero z τ
      exact Prod.ext h1 h2zero
    have hpatch :=
      jacobiThetaDeltaError_patch z τ
    rw [h1] at hpatch
    have hpatch' :
        jacobiTheta2 z (τ : ℂ) ^ 2 *
            jacobiThetaDeltaError z τ =
          0 := by
      calc
        jacobiTheta2 z (τ : ℂ) ^ 2 *
              jacobiThetaDeltaError z τ =
            (0 : ℂ) ^ 2 *
              jacobiThetaDeltaCompanionError z τ :=
          hpatch.symm
        _ = 0 := by ring_nf
    exact
      (mul_eq_zero.mp hpatch').resolve_left
        (pow_ne_zero 2 h2)
  · have hchart :=
      jacobiThetaDeltaQuotient_eq_error_div z τ h1
    have hzero :=
      jacobiThetaDeltaQuotient_eq_zero z τ
    have hdiv :
        jacobiThetaDeltaError z τ /
            jacobiTheta1 z (τ : ℂ) ^ 2 =
          0 := hchart.symm.trans hzero
    field_simp [h1] at hdiv
    simpa only [mul_zero] using hdiv

/-- The missing second-order Jacobi theta identity, now proved
unconditionally. -/
theorem jacobiThetaDeltaIdentity
    (z : ℂ) (τ : ℍ) :
    JacobiThetaDeltaIdentityAt z τ := by
  have herror :=
    jacobiThetaDeltaError_eq_zero z τ
  unfold jacobiThetaDeltaError at herror
  unfold JacobiThetaDeltaIdentityAt
  linear_combination herror

/-- The complete canonical Jacobi theta state satisfies the scaled
elliptic vector field wherever the reciprocal `θ₁` chart is defined. -/
theorem canonicalJacobiThetaState_elliptic_unconditional
    (z : ℂ) (τ : ℍ)
    (h1 : jacobiTheta1 z (τ : ℂ) ≠ 0) :
    IsScaledJacobiEllipticTrajectoryAt
      π (fun w ↦ canonicalJacobiThetaState w τ) z :=
  canonicalJacobiThetaState_elliptic
    z τ h1 (jacobiThetaDeltaIdentity z τ)

/-- Every real affine restriction avoiding the reciprocal divisor is
an unconditional scaled trajectory. -/
theorem
    canonicalJacobiThetaRealAffine_isScaledTrajectory_unconditional
    (z₀ v : ℂ) (τ : ℍ)
    (h1 : ∀ t : ℝ,
      jacobiTheta1
        (z₀ + (t : ℂ) * v) (τ : ℂ) ≠ 0) :
    IsScaledJacobiTrajectory (v * π) 0
      (canonicalJacobiThetaRealAffine z₀ v τ) :=
  canonicalJacobiThetaRealAffine_isScaledTrajectory
    z₀ v τ h1
      (fun t ↦
        jacobiThetaDeltaIdentity
          (z₀ + (t : ℂ) * v) τ)

end

end HGAS.Modular
