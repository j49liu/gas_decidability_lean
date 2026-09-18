import HGAS.Modular.JacobiResidualDynamics
import HGAS.Modular.JacobiThetaWronskians
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Tactic

/-!
# The Jacobi theta functions and the elliptic Jacobi vector field

This file is the analytic-to-algebraic bridge for the elliptic
(`w`-variable) part of the Jacobi chart.

For a fixed modulus `τ`, put

```
 p₂ = θ₂(0|τ)²,       p₃ = θ₃(0|τ)²,
 p₄ = θ₄(0|τ)²,       H  = E₂(τ)/12,
 Tⱼ = θⱼ(w|τ),        Δ  = θ₁'(w|τ)/π,
 U  = θ₁(w|τ)⁻¹.
```

The normalization in `JacobiState.ellipticVectorField` is
`𝒵 = π⁻¹ ∂/∂w`.  Thus the ordinary complex derivative of the displayed
state must be `π • 𝒵`.

The three unconditional Wronskian identities from
`JacobiThetaWronskians` prove the `T₂`, `T₃`, and `T₄` equations on the
reciprocal chart `θ₁ ≠ 0`.  The `T₁` and `U` equations are elementary
calculus, while the coefficient coordinates are constant.  We package
these nine unconditional equations separately.

There is one further, genuinely second-order theta identity:

```
 θ₁ θ₁'' =
   θ₁'² - π² p₃p₄ θ₂² - 4π² K θ₁²,
 K = H + (p₃²+p₄²)/12.
```

It is exactly equivalent, on `θ₁ ≠ 0`, to the remaining `Δ` equation.
The definition `JacobiThetaDeltaIdentityAt` records this single scalar
statement.  No assumption is hidden in the unconditional theorem:
the full trajectory theorem takes precisely this named identity as an
explicit hypothesis.

The trajectory structures introduced here use a complex parameter.  A
final reusable restriction theorem turns such a trajectory along a real
affine line into the real-time `IsScaledJacobiTrajectory` used by the
residual-invariance modules.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I
open Complex Real

noncomputable section

/-! ## The canonical reciprocal-chart state -/

/-- The canonical Jacobi theta state at elliptic argument `w` and modulus
`τ`.  At a zero of `θ₁`, Lean's field inverse makes `U=0`; all vector-field
statements below therefore explicitly work on the reciprocal chart
`θ₁ ≠ 0`. -/
def canonicalJacobiThetaState
    (w : ℂ) (τ : ℍ) : JacobiState ℂ where
  p2 := (canonicalUnaryRoots τ).p2
  p3 := (canonicalUnaryRoots τ).p3
  p4 := (canonicalUnaryRoots τ).p4
  H := (canonicalUnaryRoots τ).H
  T1 := jacobiTheta1 w (τ : ℂ)
  T2 := jacobiTheta2 w (τ : ℂ)
  T3 := jacobiTheta3 w (τ : ℂ)
  T4 := jacobiTheta4 w (τ : ℂ)
  Delta := jacobiTheta1Prime w (τ : ℂ) / π
  U := (jacobiTheta1 w (τ : ℂ))⁻¹

@[simp] theorem canonicalJacobiThetaState_p2
    (w : ℂ) (τ : ℍ) :
    (canonicalJacobiThetaState w τ).p2 =
      (canonicalUnaryRoots τ).p2 := rfl

@[simp] theorem canonicalJacobiThetaState_p3
    (w : ℂ) (τ : ℍ) :
    (canonicalJacobiThetaState w τ).p3 =
      (canonicalUnaryRoots τ).p3 := rfl

@[simp] theorem canonicalJacobiThetaState_p4
    (w : ℂ) (τ : ℍ) :
    (canonicalJacobiThetaState w τ).p4 =
      (canonicalUnaryRoots τ).p4 := rfl

@[simp] theorem canonicalJacobiThetaState_H
    (w : ℂ) (τ : ℍ) :
    (canonicalJacobiThetaState w τ).H =
      (canonicalUnaryRoots τ).H := rfl

@[simp] theorem canonicalJacobiThetaState_T1
    (w : ℂ) (τ : ℍ) :
    (canonicalJacobiThetaState w τ).T1 =
      jacobiTheta1 w (τ : ℂ) := rfl

@[simp] theorem canonicalJacobiThetaState_T2
    (w : ℂ) (τ : ℍ) :
    (canonicalJacobiThetaState w τ).T2 =
      jacobiTheta2 w (τ : ℂ) := rfl

@[simp] theorem canonicalJacobiThetaState_T3
    (w : ℂ) (τ : ℍ) :
    (canonicalJacobiThetaState w τ).T3 =
      jacobiTheta3 w (τ : ℂ) := rfl

@[simp] theorem canonicalJacobiThetaState_T4
    (w : ℂ) (τ : ℍ) :
    (canonicalJacobiThetaState w τ).T4 =
      jacobiTheta4 w (τ : ℂ) := rfl

@[simp] theorem canonicalJacobiThetaState_Delta
    (w : ℂ) (τ : ℍ) :
    (canonicalJacobiThetaState w τ).Delta =
      jacobiTheta1Prime w (τ : ℂ) / π := rfl

@[simp] theorem canonicalJacobiThetaState_U
    (w : ℂ) (τ : ℍ) :
    (canonicalJacobiThetaState w τ).U =
      (jacobiTheta1 w (τ : ℂ))⁻¹ := rfl

/-! ## The sole second-order scalar identity -/

/-- The second derivative of `θ₁` in its elliptic variable.  The
holomorphy theorem below shows that this `deriv` has its intended value
everywhere. -/
def jacobiTheta1Second
    (w : ℂ) (τ : ℍ) : ℂ :=
  deriv (fun z ↦ jacobiTheta1Prime z (τ : ℂ)) w

/-- `θ₁'` has derivative `jacobiTheta1Second`. -/
theorem hasDerivAt_jacobiTheta1Prime
    (w : ℂ) (τ : ℍ) :
    HasDerivAt
      (fun z ↦ jacobiTheta1Prime z (τ : ℂ))
      (jacobiTheta1Second w τ) w := by
  have hdiff :
      Differentiable ℂ
        (fun z ↦ jacobiTheta1Prime z (τ : ℂ)) := by
    rw [← analyticOnNhd_univ_iff_differentiable]
    exact analyticOnNhd_jacobiTheta1Prime_fixed τ
  exact (hdiff w).hasDerivAt

/-- The one scalar second-order identity needed for the `Δ` coordinate
of the elliptic vector field.  It is stated without division by `θ₁`, so
it makes sense at every elliptic argument. -/
def JacobiThetaDeltaIdentityAt
    (w : ℂ) (τ : ℍ) : Prop :=
  jacobiTheta1 w (τ : ℂ) *
      jacobiTheta1Second w τ =
    jacobiTheta1Prime w (τ : ℂ) ^ 2 -
        π ^ 2 *
          (canonicalJacobiThetaState w τ).p3 *
          (canonicalJacobiThetaState w τ).p4 *
          jacobiTheta2 w (τ : ℂ) ^ 2 -
      4 * π ^ 2 *
        JacobiState.K (canonicalJacobiThetaState w τ) *
        jacobiTheta1 w (τ : ℂ) ^ 2

/-! ## Complex-parameter trajectory structures -/

/-- All coordinate equations of a scaled elliptic Jacobi trajectory
except the `Δ` equation.  Keeping this structure separate makes the
unconditional analytic content available without pretending that the
second-order identity has already been proved. -/
structure IsScaledJacobiEllipticTrajectoryAtExceptDelta
    (κ : ℂ) (s : ℂ → JacobiState ℂ) (w : ℂ) : Prop where
  p2 : HasDerivAt (fun z ↦ (s z).p2)
    (κ * (JacobiState.ellipticVectorField (s w)).p2) w
  p3 : HasDerivAt (fun z ↦ (s z).p3)
    (κ * (JacobiState.ellipticVectorField (s w)).p3) w
  p4 : HasDerivAt (fun z ↦ (s z).p4)
    (κ * (JacobiState.ellipticVectorField (s w)).p4) w
  H : HasDerivAt (fun z ↦ (s z).H)
    (κ * (JacobiState.ellipticVectorField (s w)).H) w
  T1 : HasDerivAt (fun z ↦ (s z).T1)
    (κ * (JacobiState.ellipticVectorField (s w)).T1) w
  T2 : HasDerivAt (fun z ↦ (s z).T2)
    (κ * (JacobiState.ellipticVectorField (s w)).T2) w
  T3 : HasDerivAt (fun z ↦ (s z).T3)
    (κ * (JacobiState.ellipticVectorField (s w)).T3) w
  T4 : HasDerivAt (fun z ↦ (s z).T4)
    (κ * (JacobiState.ellipticVectorField (s w)).T4) w
  U : HasDerivAt (fun z ↦ (s z).U)
    (κ * (JacobiState.ellipticVectorField (s w)).U) w

/-- All ten coordinate equations of a scaled complex-parameter elliptic
Jacobi trajectory at one point. -/
structure IsScaledJacobiEllipticTrajectoryAt
    (κ : ℂ) (s : ℂ → JacobiState ℂ) (w : ℂ) : Prop
    extends IsScaledJacobiEllipticTrajectoryAtExceptDelta κ s w where
  Delta : HasDerivAt (fun z ↦ (s z).Delta)
    (κ * (JacobiState.ellipticVectorField (s w)).Delta) w

/-! ## The nine unconditional coordinate equations -/

theorem canonicalJacobiThetaState_p2_hasDerivAt
    (w : ℂ) (τ : ℍ) :
    HasDerivAt
      (fun z ↦ (canonicalJacobiThetaState z τ).p2)
      (π * (JacobiState.ellipticVectorField
        (canonicalJacobiThetaState w τ)).p2) w := by
  simpa [JacobiState.ellipticVectorField] using
    (hasDerivAt_const w (canonicalUnaryRoots τ).p2)

theorem canonicalJacobiThetaState_p3_hasDerivAt
    (w : ℂ) (τ : ℍ) :
    HasDerivAt
      (fun z ↦ (canonicalJacobiThetaState z τ).p3)
      (π * (JacobiState.ellipticVectorField
        (canonicalJacobiThetaState w τ)).p3) w := by
  simpa [JacobiState.ellipticVectorField] using
    (hasDerivAt_const w (canonicalUnaryRoots τ).p3)

theorem canonicalJacobiThetaState_p4_hasDerivAt
    (w : ℂ) (τ : ℍ) :
    HasDerivAt
      (fun z ↦ (canonicalJacobiThetaState z τ).p4)
      (π * (JacobiState.ellipticVectorField
        (canonicalJacobiThetaState w τ)).p4) w := by
  simpa [JacobiState.ellipticVectorField] using
    (hasDerivAt_const w (canonicalUnaryRoots τ).p4)

theorem canonicalJacobiThetaState_H_hasDerivAt
    (w : ℂ) (τ : ℍ) :
    HasDerivAt
      (fun z ↦ (canonicalJacobiThetaState z τ).H)
      (π * (JacobiState.ellipticVectorField
        (canonicalJacobiThetaState w τ)).H) w := by
  simpa [JacobiState.ellipticVectorField] using
    (hasDerivAt_const w (canonicalUnaryRoots τ).H)

theorem canonicalJacobiThetaState_T1_hasDerivAt
    (w : ℂ) (τ : ℍ) :
    HasDerivAt
      (fun z ↦ (canonicalJacobiThetaState z τ).T1)
      (π * (JacobiState.ellipticVectorField
        (canonicalJacobiThetaState w τ)).T1) w := by
  have heq :
      π * (JacobiState.ellipticVectorField
        (canonicalJacobiThetaState w τ)).T1 =
        jacobiTheta1Prime w (τ : ℂ) := by
    simp only [JacobiState.ellipticVectorField,
      canonicalJacobiThetaState_Delta]
    field_simp
  rw [heq]
  exact hasDerivAt_jacobiTheta1 w (τ : ℂ) τ.im_pos

/-- The first Wronskian, divided only after entering the reciprocal
chart, is exactly the `T₂` vector-field equation. -/
theorem canonicalJacobiThetaState_T2_derivative_eq
    (w : ℂ) (τ : ℍ)
    (h1 : jacobiTheta1 w (τ : ℂ) ≠ 0) :
    jacobiTheta2Prime w (τ : ℂ) =
      π * (JacobiState.ellipticVectorField
        (canonicalJacobiThetaState w τ)).T2 := by
  have hW :
      jacobiTheta2Prime w (τ : ℂ) *
            jacobiTheta1 w (τ : ℂ) -
          jacobiTheta2 w (τ : ℂ) *
            jacobiTheta1Prime w (τ : ℂ) =
        -π * (canonicalUnaryRoots τ).p2 *
          jacobiTheta3 w (τ : ℂ) *
            jacobiTheta4 w (τ : ℂ) := by
    simpa [jacobiThetaVector, jacobiThetaVectorPrime] using
      (canonicalJacobiThetaWronskiansAt w τ).1
  simp only [JacobiState.ellipticVectorField,
    canonicalJacobiThetaState_U,
    canonicalJacobiThetaState_Delta,
    canonicalJacobiThetaState_T2,
    canonicalJacobiThetaState_T3,
    canonicalJacobiThetaState_T4,
    canonicalJacobiThetaState_p2]
  field_simp [h1]
  linear_combination hW

theorem canonicalJacobiThetaState_T2_hasDerivAt
    (w : ℂ) (τ : ℍ)
    (h1 : jacobiTheta1 w (τ : ℂ) ≠ 0) :
    HasDerivAt
      (fun z ↦ (canonicalJacobiThetaState z τ).T2)
      (π * (JacobiState.ellipticVectorField
        (canonicalJacobiThetaState w τ)).T2) w := by
  rw [← canonicalJacobiThetaState_T2_derivative_eq w τ h1]
  exact hasDerivAt_jacobiTheta2 w (τ : ℂ) τ.im_pos

/-- The second Wronskian gives the `T₃` equation. -/
theorem canonicalJacobiThetaState_T3_derivative_eq
    (w : ℂ) (τ : ℍ)
    (h1 : jacobiTheta1 w (τ : ℂ) ≠ 0) :
    jacobiTheta3Prime w (τ : ℂ) =
      π * (JacobiState.ellipticVectorField
        (canonicalJacobiThetaState w τ)).T3 := by
  have hW :
      jacobiTheta3Prime w (τ : ℂ) *
            jacobiTheta1 w (τ : ℂ) -
          jacobiTheta3 w (τ : ℂ) *
            jacobiTheta1Prime w (τ : ℂ) =
        -π * (canonicalUnaryRoots τ).p3 *
          jacobiTheta4 w (τ : ℂ) *
            jacobiTheta2 w (τ : ℂ) := by
    simpa [jacobiThetaVector, jacobiThetaVectorPrime] using
      (canonicalJacobiThetaWronskiansAt w τ).2.1
  simp only [JacobiState.ellipticVectorField,
    canonicalJacobiThetaState_U,
    canonicalJacobiThetaState_Delta,
    canonicalJacobiThetaState_T2,
    canonicalJacobiThetaState_T3,
    canonicalJacobiThetaState_T4,
    canonicalJacobiThetaState_p3]
  field_simp [h1]
  linear_combination hW

theorem canonicalJacobiThetaState_T3_hasDerivAt
    (w : ℂ) (τ : ℍ)
    (h1 : jacobiTheta1 w (τ : ℂ) ≠ 0) :
    HasDerivAt
      (fun z ↦ (canonicalJacobiThetaState z τ).T3)
      (π * (JacobiState.ellipticVectorField
        (canonicalJacobiThetaState w τ)).T3) w := by
  rw [← canonicalJacobiThetaState_T3_derivative_eq w τ h1]
  exact hasDerivAt_jacobiTheta3 w (τ : ℂ) τ.im_pos

/-- The third Wronskian gives the `T₄` equation. -/
theorem canonicalJacobiThetaState_T4_derivative_eq
    (w : ℂ) (τ : ℍ)
    (h1 : jacobiTheta1 w (τ : ℂ) ≠ 0) :
    jacobiTheta4Prime w (τ : ℂ) =
      π * (JacobiState.ellipticVectorField
        (canonicalJacobiThetaState w τ)).T4 := by
  have hW :
      jacobiTheta4Prime w (τ : ℂ) *
            jacobiTheta1 w (τ : ℂ) -
          jacobiTheta4 w (τ : ℂ) *
            jacobiTheta1Prime w (τ : ℂ) =
        -π * (canonicalUnaryRoots τ).p4 *
          jacobiTheta2 w (τ : ℂ) *
            jacobiTheta3 w (τ : ℂ) := by
    simpa [jacobiThetaVector, jacobiThetaVectorPrime] using
      (canonicalJacobiThetaWronskiansAt w τ).2.2
  simp only [JacobiState.ellipticVectorField,
    canonicalJacobiThetaState_U,
    canonicalJacobiThetaState_Delta,
    canonicalJacobiThetaState_T2,
    canonicalJacobiThetaState_T3,
    canonicalJacobiThetaState_T4,
    canonicalJacobiThetaState_p4]
  field_simp [h1]
  linear_combination hW

theorem canonicalJacobiThetaState_T4_hasDerivAt
    (w : ℂ) (τ : ℍ)
    (h1 : jacobiTheta1 w (τ : ℂ) ≠ 0) :
    HasDerivAt
      (fun z ↦ (canonicalJacobiThetaState z τ).T4)
      (π * (JacobiState.ellipticVectorField
        (canonicalJacobiThetaState w τ)).T4) w := by
  rw [← canonicalJacobiThetaState_T4_derivative_eq w τ h1]
  exact hasDerivAt_jacobiTheta4 w (τ : ℂ) τ.im_pos

theorem canonicalJacobiThetaState_U_hasDerivAt
    (w : ℂ) (τ : ℍ)
    (h1 : jacobiTheta1 w (τ : ℂ) ≠ 0) :
    HasDerivAt
      (fun z ↦ (canonicalJacobiThetaState z τ).U)
      (π * (JacobiState.ellipticVectorField
        (canonicalJacobiThetaState w τ)).U) w := by
  have h :=
    (hasDerivAt_jacobiTheta1 w (τ : ℂ)
      τ.im_pos).inv h1
  have heq :
      π * (JacobiState.ellipticVectorField
        (canonicalJacobiThetaState w τ)).U =
        -jacobiTheta1Prime w (τ : ℂ) /
          jacobiTheta1 w (τ : ℂ) ^ 2 := by
    simp only [JacobiState.ellipticVectorField,
      canonicalJacobiThetaState_U,
      canonicalJacobiThetaState_Delta]
    field_simp [h1]
  rw [heq]
  exact h

/-- Unconditional elliptic evolution of every coordinate except `Δ`.
The only domain hypothesis is exactly the reciprocal-chart condition. -/
theorem canonicalJacobiThetaState_elliptic_exceptDelta
    (w : ℂ) (τ : ℍ)
    (h1 : jacobiTheta1 w (τ : ℂ) ≠ 0) :
    IsScaledJacobiEllipticTrajectoryAtExceptDelta
      π (fun z ↦ canonicalJacobiThetaState z τ) w where
  p2 := canonicalJacobiThetaState_p2_hasDerivAt w τ
  p3 := canonicalJacobiThetaState_p3_hasDerivAt w τ
  p4 := canonicalJacobiThetaState_p4_hasDerivAt w τ
  H := canonicalJacobiThetaState_H_hasDerivAt w τ
  T1 := canonicalJacobiThetaState_T1_hasDerivAt w τ
  T2 := canonicalJacobiThetaState_T2_hasDerivAt w τ h1
  T3 := canonicalJacobiThetaState_T3_hasDerivAt w τ h1
  T4 := canonicalJacobiThetaState_T4_hasDerivAt w τ h1
  U := canonicalJacobiThetaState_U_hasDerivAt w τ h1

/-! ## The `Δ` equation and exact gap equivalence -/

/-- On the reciprocal chart, the cross-multiplied second-order theta
identity implies precisely the `Δ` coordinate equation. -/
theorem canonicalJacobiThetaState_Delta_hasDerivAt
    (w : ℂ) (τ : ℍ)
    (h1 : jacobiTheta1 w (τ : ℂ) ≠ 0)
    (hDelta : JacobiThetaDeltaIdentityAt w τ) :
    HasDerivAt
      (fun z ↦ (canonicalJacobiThetaState z τ).Delta)
      (π * (JacobiState.ellipticVectorField
        (canonicalJacobiThetaState w τ)).Delta) w := by
  have h :=
    (hasDerivAt_jacobiTheta1Prime w τ).div_const π
  have heq :
      π * (JacobiState.ellipticVectorField
        (canonicalJacobiThetaState w τ)).Delta =
        jacobiTheta1Second w τ / π := by
    unfold JacobiThetaDeltaIdentityAt at hDelta
    simp only [JacobiState.ellipticVectorField,
      canonicalJacobiThetaState_U,
      canonicalJacobiThetaState_Delta,
      canonicalJacobiThetaState_T1,
      canonicalJacobiThetaState_T2]
    field_simp [h1]
    ring_nf at hDelta ⊢
    exact hDelta.symm
  rw [heq]
  exact h

/-- Conversely, the `Δ` coordinate equation implies the cross-multiplied
second-order identity.  Thus `JacobiThetaDeltaIdentityAt` is neither
stronger nor weaker than the missing vector-field component on the
reciprocal chart. -/
theorem jacobiThetaDeltaIdentityAt_of_Delta_hasDerivAt
    (w : ℂ) (τ : ℍ)
    (h1 : jacobiTheta1 w (τ : ℂ) ≠ 0)
    (hDelta :
      HasDerivAt
        (fun z ↦ (canonicalJacobiThetaState z τ).Delta)
        (π * (JacobiState.ellipticVectorField
          (canonicalJacobiThetaState w τ)).Delta) w) :
    JacobiThetaDeltaIdentityAt w τ := by
  have hcanonical :=
    (hasDerivAt_jacobiTheta1Prime w τ).div_const π
  have heq := hDelta.unique hcanonical
  unfold JacobiThetaDeltaIdentityAt
  simp only [JacobiState.ellipticVectorField,
    canonicalJacobiThetaState_U,
    canonicalJacobiThetaState_Delta,
    canonicalJacobiThetaState_T1,
    canonicalJacobiThetaState_T2] at heq
  field_simp [h1] at heq
  linear_combination -heq

/-- Full pointwise elliptic trajectory, conditional on exactly the one
named second-order scalar identity. -/
theorem canonicalJacobiThetaState_elliptic
    (w : ℂ) (τ : ℍ)
    (h1 : jacobiTheta1 w (τ : ℂ) ≠ 0)
    (hDelta : JacobiThetaDeltaIdentityAt w τ) :
    IsScaledJacobiEllipticTrajectoryAt
      π (fun z ↦ canonicalJacobiThetaState z τ) w where
  toIsScaledJacobiEllipticTrajectoryAtExceptDelta :=
    canonicalJacobiThetaState_elliptic_exceptDelta w τ h1
  Delta :=
    canonicalJacobiThetaState_Delta_hasDerivAt
      w τ h1 hDelta

/-! ## Restriction to a real affine line -/

/-- Restrict a complex derivative to the real affine line
`t ↦ w₀ + t v`. -/
theorem HasDerivAt.comp_realAffine
    {f : ℂ → ℂ} {f' w₀ v : ℂ} {t : ℝ}
    (hf : HasDerivAt f f' (w₀ + (t : ℂ) * v)) :
    HasDerivAt
      (fun s : ℝ ↦ f (w₀ + (s : ℂ) * v))
      (v * f') t := by
  have hg :
      HasDerivAt
        (fun s : ℝ ↦ w₀ + (s : ℂ) * v) v t := by
    simpa only [ofRealCLM_apply, ofReal_one, one_mul] using
      (Complex.ofRealCLM.hasDerivAt
        (x := t)).mul_const v |>.const_add w₀
  simpa only [Function.comp_apply, mul_comm] using
    hf.comp t hg

/-- A real affine restriction of the canonical theta state. -/
def canonicalJacobiThetaRealAffine
    (w₀ v : ℂ) (τ : ℍ) (t : ℝ) : JacobiState ℂ :=
  canonicalJacobiThetaState (w₀ + (t : ℂ) * v) τ

/-- A pointwise complex elliptic trajectory restricts to the real-time
combined-field convention with modular speed zero. -/
theorem canonicalJacobiThetaRealAffine_isScaledTrajectory
    (w₀ v : ℂ) (τ : ℍ)
    (h1 : ∀ t : ℝ,
      jacobiTheta1 (w₀ + (t : ℂ) * v) (τ : ℂ) ≠ 0)
    (hDelta : ∀ t : ℝ,
      JacobiThetaDeltaIdentityAt
        (w₀ + (t : ℂ) * v) τ) :
    IsScaledJacobiTrajectory (v * π) 0
      (canonicalJacobiThetaRealAffine w₀ v τ) := by
  let s : ℂ → JacobiState ℂ :=
    fun w ↦ canonicalJacobiThetaState w τ
  have hpoint (t : ℝ) :
      IsScaledJacobiEllipticTrajectoryAt
        π s (w₀ + (t : ℂ) * v) :=
    canonicalJacobiThetaState_elliptic
      (w₀ + (t : ℂ) * v) τ (h1 t) (hDelta t)
  constructor
  · intro t
    have h := HasDerivAt.comp_realAffine (hpoint t).p2
    simpa [canonicalJacobiThetaRealAffine, s,
      JacobiState.combinedVectorField, mul_assoc] using h
  · intro t
    have h := HasDerivAt.comp_realAffine (hpoint t).p3
    simpa [canonicalJacobiThetaRealAffine, s,
      JacobiState.combinedVectorField, mul_assoc] using h
  · intro t
    have h := HasDerivAt.comp_realAffine (hpoint t).p4
    simpa [canonicalJacobiThetaRealAffine, s,
      JacobiState.combinedVectorField, mul_assoc] using h
  · intro t
    have h := HasDerivAt.comp_realAffine (hpoint t).H
    simpa [canonicalJacobiThetaRealAffine, s,
      JacobiState.combinedVectorField, mul_assoc] using h
  · intro t
    have h := HasDerivAt.comp_realAffine (hpoint t).T1
    simpa [canonicalJacobiThetaRealAffine, s,
      JacobiState.combinedVectorField, mul_assoc] using h
  · intro t
    have h := HasDerivAt.comp_realAffine (hpoint t).T2
    simpa [canonicalJacobiThetaRealAffine, s,
      JacobiState.combinedVectorField, mul_assoc] using h
  · intro t
    have h := HasDerivAt.comp_realAffine (hpoint t).T3
    simpa [canonicalJacobiThetaRealAffine, s,
      JacobiState.combinedVectorField, mul_assoc] using h
  · intro t
    have h := HasDerivAt.comp_realAffine (hpoint t).T4
    simpa [canonicalJacobiThetaRealAffine, s,
      JacobiState.combinedVectorField, mul_assoc] using h
  · intro t
    have h := HasDerivAt.comp_realAffine (hpoint t).Delta
    simpa [canonicalJacobiThetaRealAffine, s,
      JacobiState.combinedVectorField, mul_assoc] using h
  · intro t
    have h := HasDerivAt.comp_realAffine (hpoint t).U
    simpa [canonicalJacobiThetaRealAffine, s,
      JacobiState.combinedVectorField, mul_assoc] using h

end

end HGAS.Modular
