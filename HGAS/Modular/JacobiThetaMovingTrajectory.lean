import HGAS.Modular.JacobiThetaModularDelta
import HGAS.Modular.TwoComplexRealChainRule

/-!
# The canonical theta state with two moving parameters

The elliptic and modular trajectory theorems describe the two coordinate
directions separately.  This file combines them along differentiable
real-time paths

```
                         t ↦ (ξ(t), T(t)).
```

The mixed-scalar chain rule gives the precise clocks:

```
  d/dt canonicalJacobiThetaState(ξ(t),T(t))
    = (π ξ'(t)) · Z + (π i T'(t)) · Phi.
```

This is the moving-modulus identity needed when a coherent theta lift is
compared with the polynomial Jacobi trajectory.  It is first stated
pointwise, allowing the two velocities to vary, and then packaged as an
ordinary fixed-clock `IsScaledJacobiTrajectory`.
-/

namespace HGAS.Modular

open Complex Real
open UpperHalfPlane hiding I

noncomputable section

/-- The canonical state evaluated along real elliptic and modular
paths. -/
def canonicalJacobiThetaMovingPath
    (ξ : ℝ → ℂ) (T : ℝ → ℍ) (t : ℝ) :
    JacobiState ℂ :=
  canonicalJacobiThetaState (ξ t) (T t)

/-- Pointwise version of a real-time Jacobi trajectory.  Unlike
`IsScaledJacobiTrajectory`, the clocks are only asserted at one time and
may therefore be supplied by the instantaneous velocities of two
parameter paths. -/
structure IsScaledJacobiRealTrajectoryAt
    (κZ κPhi : ℂ) (s : ℝ → JacobiState ℂ) (t : ℝ) : Prop where
  p2 : HasDerivAt (fun u => (s u).p2)
    (JacobiState.combinedVectorField κZ κPhi (s t)).p2 t
  p3 : HasDerivAt (fun u => (s u).p3)
    (JacobiState.combinedVectorField κZ κPhi (s t)).p3 t
  p4 : HasDerivAt (fun u => (s u).p4)
    (JacobiState.combinedVectorField κZ κPhi (s t)).p4 t
  H : HasDerivAt (fun u => (s u).H)
    (JacobiState.combinedVectorField κZ κPhi (s t)).H t
  T1 : HasDerivAt (fun u => (s u).T1)
    (JacobiState.combinedVectorField κZ κPhi (s t)).T1 t
  T2 : HasDerivAt (fun u => (s u).T2)
    (JacobiState.combinedVectorField κZ κPhi (s t)).T2 t
  T3 : HasDerivAt (fun u => (s u).T3)
    (JacobiState.combinedVectorField κZ κPhi (s t)).T3 t
  T4 : HasDerivAt (fun u => (s u).T4)
    (JacobiState.combinedVectorField κZ κPhi (s t)).T4 t
  Delta : HasDerivAt (fun u => (s u).Delta)
    (JacobiState.combinedVectorField κZ κPhi (s t)).Delta t
  U : HasDerivAt (fun u => (s u).U)
    (JacobiState.combinedVectorField κZ κPhi (s t)).U t

/-- The modular derivative of the reciprocal theta coordinate in its
ordinary two-complex-variable presentation. -/
theorem canonicalJacobiThetaState_U_modular_hasDerivAt
    (z : ℂ) (τ : ℍ)
    (h1 : jacobiTheta1 z (τ : ℂ) ≠ 0) :
    HasDerivAt
      (fun u : ℂ => (jacobiTheta1 z u)⁻¹)
      (π * I *
        (JacobiState.modularVectorField
          (canonicalJacobiThetaState z τ)).U)
      (τ : ℂ) := by
  have hraw :=
    (canonicalJacobiThetaState_T1_modular_hasDerivAt
      z τ h1).inv h1
  let q : JacobiState ℂ :=
    canonicalJacobiThetaState z τ
  let P : JacobiState ℂ :=
    JacobiState.modularVectorField q
  have hqT1 : q.T1 ≠ 0 := by
    simpa only [q, canonicalJacobiThetaState_T1] using h1
  have hqU : q.U = q.T1⁻¹ := by
    rfl
  have hPU : P.U = -(q.U ^ 2 * P.T1) := by
    rfl
  have hcoefficient :
      -(π * I * P.T1) / q.T1 ^ 2 =
        π * I * P.U := by
    rw [hPU, hqU]
    field_simp [hqT1]
  change
    HasDerivAt
      (fun u : ℂ => (jacobiTheta1 z u)⁻¹)
      (-(π * I * P.T1) / q.T1 ^ 2) (τ : ℂ)
      at hraw
  rw [hcoefficient] at hraw
  simpa only [q, P] using hraw

set_option maxHeartbeats 800000 in
-- Ten coordinatewise chain rules make elaboration larger than the default.
/-- **Two-parameter canonical Jacobi identity.**

At a time where `ξ' = a` and `T' = b`, the complete canonical theta state
has combined Jacobi clocks `πa` and `πib`. -/
theorem canonicalJacobiThetaMovingPath_isScaledAt
    {ξ : ℝ → ℂ} {T : ℝ → ℍ}
    {t : ℝ} {a b : ℂ}
    (hξ : HasDerivAt ξ a t)
    (hT :
      HasDerivAt
        (fun u : ℝ => (T u : ℂ)) b t)
    (h1 :
      jacobiTheta1 (ξ t) (T t : ℂ) ≠ 0) :
    IsScaledJacobiRealTrajectoryAt
      (π * a) (π * I * b)
      (canonicalJacobiThetaMovingPath ξ T) t := by
  let q : JacobiState ℂ :=
    canonicalJacobiThetaState (ξ t) (T t)
  let Z : JacobiState ℂ :=
    JacobiState.ellipticVectorField q
  let P : JacobiState ℂ :=
    JacobiState.modularVectorField q
  have helliptic :
      IsScaledJacobiEllipticTrajectoryAt
        π
        (fun z =>
          canonicalJacobiThetaState z (T t))
        (ξ t) :=
    canonicalJacobiThetaState_elliptic_unconditional
      (ξ t) (T t) h1
  have hmodular :
      IsScaledJacobiModularTrajectoryAt
        (π * I)
        (canonicalJacobiThetaModularPath (ξ t))
        (T t : ℂ) :=
    canonicalJacobiThetaState_modular_unconditional
      (ξ t) (T t) h1
  have hp2raw :=
    hmodular.p2.comp t hT
  have hp3raw :=
    hmodular.p3.comp t hT
  have hp4raw :=
    hmodular.p4.comp t hT
  have hHraw :=
    hmodular.H.comp t hT
  have hp2coeff :
      (π * I * P.p2) * b =
        (JacobiState.combinedVectorField
          (π * a) (π * I * b) q).p2 := by
    simp only [JacobiState.combinedVectorField,
      JacobiState.ellipticVectorField, P]
    ring
  have hp3coeff :
      (π * I * P.p3) * b =
        (JacobiState.combinedVectorField
          (π * a) (π * I * b) q).p3 := by
    simp only [JacobiState.combinedVectorField,
      JacobiState.ellipticVectorField, P]
    ring
  have hp4coeff :
      (π * I * P.p4) * b =
        (JacobiState.combinedVectorField
          (π * a) (π * I * b) q).p4 := by
    simp only [JacobiState.combinedVectorField,
      JacobiState.ellipticVectorField, P]
    ring
  have hHcoeff :
      (π * I * P.H) * b =
        (JacobiState.combinedVectorField
          (π * a) (π * I * b) q).H := by
    simp only [JacobiState.combinedVectorField,
      JacobiState.ellipticVectorField, P]
    ring
  simp only [
    canonicalJacobiThetaModularPath_at_upperHalfPlane]
    at hp2raw hp3raw hp4raw hHraw
  change
    HasDerivAt _
      (π * I * P.p2 * b) t at hp2raw
  change
    HasDerivAt _
      (π * I * P.p3 * b) t at hp3raw
  change
    HasDerivAt _
      (π * I * P.p4 * b) t at hp4raw
  change
    HasDerivAt _
      (π * I * P.H * b) t at hHraw
  rw [hp2coeff] at hp2raw
  rw [hp3coeff] at hp3raw
  rw [hp4coeff] at hp4raw
  rw [hHcoeff] at hHraw
  have hp2 :
      HasDerivAt
        (fun u =>
          (canonicalJacobiThetaMovingPath ξ T u).p2)
        (JacobiState.combinedVectorField
          (π * a) (π * I * b) q).p2 t := by
    have hfun :
        ((fun v =>
          (canonicalJacobiThetaModularPath
            (ξ t) v).p2) ∘
              fun u : ℝ => (T u : ℂ)) =
          (fun u =>
            (canonicalJacobiThetaMovingPath
              ξ T u).p2) := by
      funext u
      simp only [Function.comp_apply,
        canonicalJacobiThetaMovingPath,
        canonicalJacobiThetaModularPath,
        canonicalJacobiThetaState_p2,
        ofComplex_apply]
    rw [hfun] at hp2raw
    exact hp2raw
  have hp3 :
      HasDerivAt
        (fun u =>
          (canonicalJacobiThetaMovingPath ξ T u).p3)
        (JacobiState.combinedVectorField
          (π * a) (π * I * b) q).p3 t := by
    have hfun :
        ((fun v =>
          (canonicalJacobiThetaModularPath
            (ξ t) v).p3) ∘
              fun u : ℝ => (T u : ℂ)) =
          (fun u =>
            (canonicalJacobiThetaMovingPath
              ξ T u).p3) := by
      funext u
      simp only [Function.comp_apply,
        canonicalJacobiThetaMovingPath,
        canonicalJacobiThetaModularPath,
        canonicalJacobiThetaState_p3,
        ofComplex_apply]
    rw [hfun] at hp3raw
    exact hp3raw
  have hp4 :
      HasDerivAt
        (fun u =>
          (canonicalJacobiThetaMovingPath ξ T u).p4)
        (JacobiState.combinedVectorField
          (π * a) (π * I * b) q).p4 t := by
    have hfun :
        ((fun v =>
          (canonicalJacobiThetaModularPath
            (ξ t) v).p4) ∘
              fun u : ℝ => (T u : ℂ)) =
          (fun u =>
            (canonicalJacobiThetaMovingPath
              ξ T u).p4) := by
      funext u
      simp only [Function.comp_apply,
        canonicalJacobiThetaMovingPath,
        canonicalJacobiThetaModularPath,
        canonicalJacobiThetaState_p4,
        ofComplex_apply]
    rw [hfun] at hp4raw
    exact hp4raw
  have hH :
      HasDerivAt
        (fun u =>
          (canonicalJacobiThetaMovingPath ξ T u).H)
        (JacobiState.combinedVectorField
          (π * a) (π * I * b) q).H t := by
    have hfun :
        ((fun v =>
          (canonicalJacobiThetaModularPath
            (ξ t) v).H) ∘
              fun u : ℝ => (T u : ℂ)) =
          (fun u =>
            (canonicalJacobiThetaMovingPath
              ξ T u).H) := by
      funext u
      simp only [Function.comp_apply,
        canonicalJacobiThetaMovingPath,
        canonicalJacobiThetaModularPath,
        canonicalJacobiThetaState_H,
        ofComplex_apply]
    rw [hfun] at hHraw
    exact hHraw
  have hT1joint :
      DifferentiableAt ℂ
        (fun p : ℂ × ℂ =>
          jacobiTheta1 p.1 p.2)
        (ξ t, (T t : ℂ)) :=
    (contDiffAt_one_jacobiTheta1_joint
      (ξ t) (T t : ℂ) (T t).im_pos).differentiableAt_one
  have hT1raw :=
    HasDerivAt.comp_twoComplex
      hT1joint
      (by
        simpa only [canonicalJacobiThetaState_T1,
          q, Z] using helliptic.T1)
      (canonicalJacobiThetaState_T1_modular_hasDerivAt
        (ξ t) (T t) h1)
      hξ hT rfl rfl
  have hT1coeff :
      a * (π * Z.T1) +
          b * (π * I * P.T1) =
        (JacobiState.combinedVectorField
          (π * a) (π * I * b) q).T1 := by
    simp only [JacobiState.combinedVectorField, Z, P]
    ring
  rw [hT1coeff] at hT1raw
  have hT1 :
      HasDerivAt
        (fun u =>
          (canonicalJacobiThetaMovingPath ξ T u).T1)
        (JacobiState.combinedVectorField
          (π * a) (π * I * b) q).T1 t := by
    simpa only [canonicalJacobiThetaMovingPath,
      canonicalJacobiThetaState_T1] using hT1raw
  have hT2joint :
      DifferentiableAt ℂ
        (fun p : ℂ × ℂ =>
          jacobiTheta2 p.1 p.2)
        (ξ t, (T t : ℂ)) :=
    (contDiffAt_one_jacobiTheta2_joint
      (ξ t) (T t : ℂ) (T t).im_pos).differentiableAt_one
  have hT2raw :=
    HasDerivAt.comp_twoComplex
      hT2joint
      (by
        simpa only [canonicalJacobiThetaState_T2,
          q, Z] using helliptic.T2)
      (canonicalJacobiThetaState_T2_modular_hasDerivAt
        (ξ t) (T t) h1)
      hξ hT rfl rfl
  have hT2coeff :
      a * (π * Z.T2) +
          b * (π * I * P.T2) =
        (JacobiState.combinedVectorField
          (π * a) (π * I * b) q).T2 := by
    simp only [JacobiState.combinedVectorField, Z, P]
    ring
  rw [hT2coeff] at hT2raw
  have hT2 :
      HasDerivAt
        (fun u =>
          (canonicalJacobiThetaMovingPath ξ T u).T2)
        (JacobiState.combinedVectorField
          (π * a) (π * I * b) q).T2 t := by
    simpa only [canonicalJacobiThetaMovingPath,
      canonicalJacobiThetaState_T2] using hT2raw
  have hT3joint :
      DifferentiableAt ℂ
        (fun p : ℂ × ℂ =>
          jacobiTheta3 p.1 p.2)
        (ξ t, (T t : ℂ)) :=
    (contDiffAt_one_jacobiTheta3_joint
      (ξ t) (T t : ℂ) (T t).im_pos).differentiableAt_one
  have hT3raw :=
    HasDerivAt.comp_twoComplex
      hT3joint
      (by
        simpa only [canonicalJacobiThetaState_T3,
          q, Z] using helliptic.T3)
      (canonicalJacobiThetaState_T3_modular_hasDerivAt
        (ξ t) (T t) h1)
      hξ hT rfl rfl
  have hT3coeff :
      a * (π * Z.T3) +
          b * (π * I * P.T3) =
        (JacobiState.combinedVectorField
          (π * a) (π * I * b) q).T3 := by
    simp only [JacobiState.combinedVectorField, Z, P]
    ring
  rw [hT3coeff] at hT3raw
  have hT3 :
      HasDerivAt
        (fun u =>
          (canonicalJacobiThetaMovingPath ξ T u).T3)
        (JacobiState.combinedVectorField
          (π * a) (π * I * b) q).T3 t := by
    simpa only [canonicalJacobiThetaMovingPath,
      canonicalJacobiThetaState_T3] using hT3raw
  have hT4joint :
      DifferentiableAt ℂ
        (fun p : ℂ × ℂ =>
          jacobiTheta4 p.1 p.2)
        (ξ t, (T t : ℂ)) :=
    (contDiffAt_one_jacobiTheta4_joint
      (ξ t) (T t : ℂ) (T t).im_pos).differentiableAt_one
  have hT4raw :=
    HasDerivAt.comp_twoComplex
      hT4joint
      (by
        simpa only [canonicalJacobiThetaState_T4,
          q, Z] using helliptic.T4)
      (canonicalJacobiThetaState_T4_modular_hasDerivAt
        (ξ t) (T t) h1)
      hξ hT rfl rfl
  have hT4coeff :
      a * (π * Z.T4) +
          b * (π * I * P.T4) =
        (JacobiState.combinedVectorField
          (π * a) (π * I * b) q).T4 := by
    simp only [JacobiState.combinedVectorField, Z, P]
    ring
  rw [hT4coeff] at hT4raw
  have hT4 :
      HasDerivAt
        (fun u =>
          (canonicalJacobiThetaMovingPath ξ T u).T4)
        (JacobiState.combinedVectorField
          (π * a) (π * I * b) q).T4 t := by
    simpa only [canonicalJacobiThetaMovingPath,
      canonicalJacobiThetaState_T4] using hT4raw
  have hDeltajoint :
      DifferentiableAt ℂ
        (fun p : ℂ × ℂ =>
          jacobiTheta1Prime p.1 p.2 / π)
        (ξ t, (T t : ℂ)) := by
    simpa only [div_eq_mul_inv] using
      (differentiableAt_jacobiTheta1Prime_joint
        (ξ t) (T t : ℂ) (T t).im_pos).mul_const
          (π : ℂ)⁻¹
  have hDeltaraw :=
    HasDerivAt.comp_twoComplex
      hDeltajoint
      (by
        simpa only [canonicalJacobiThetaState_Delta,
          q, Z] using helliptic.Delta)
      (canonicalJacobiThetaState_Delta_modular_hasDerivAt
        (ξ t) (T t) h1)
      hξ hT rfl rfl
  have hDeltacoeff :
      a * (π * Z.Delta) +
          b * (π * I * P.Delta) =
        (JacobiState.combinedVectorField
          (π * a) (π * I * b) q).Delta := by
    simp only [JacobiState.combinedVectorField, Z, P]
    ring
  rw [hDeltacoeff] at hDeltaraw
  have hDelta :
      HasDerivAt
        (fun u =>
          (canonicalJacobiThetaMovingPath ξ T u).Delta)
        (JacobiState.combinedVectorField
          (π * a) (π * I * b) q).Delta t := by
    simpa only [canonicalJacobiThetaMovingPath,
      canonicalJacobiThetaState_Delta] using hDeltaraw
  have hUjoint :
      DifferentiableAt ℂ
        (fun p : ℂ × ℂ =>
          (jacobiTheta1 p.1 p.2)⁻¹)
        (ξ t, (T t : ℂ)) :=
    hT1joint.inv h1
  have hUraw :=
    HasDerivAt.comp_twoComplex
      hUjoint
      (by
        simpa only [canonicalJacobiThetaState_U,
          q, Z] using helliptic.U)
      (canonicalJacobiThetaState_U_modular_hasDerivAt
        (ξ t) (T t) h1)
      hξ hT rfl rfl
  have hUcoeff :
      a * (π * Z.U) +
          b * (π * I * P.U) =
        (JacobiState.combinedVectorField
          (π * a) (π * I * b) q).U := by
    simp only [JacobiState.combinedVectorField, Z, P]
    ring
  rw [hUcoeff] at hUraw
  have hU :
      HasDerivAt
        (fun u =>
          (canonicalJacobiThetaMovingPath ξ T u).U)
        (JacobiState.combinedVectorField
          (π * a) (π * I * b) q).U t := by
    simpa only [canonicalJacobiThetaMovingPath,
      canonicalJacobiThetaState_U] using hUraw
  simpa only [canonicalJacobiThetaMovingPath, q] using
    (show
      IsScaledJacobiRealTrajectoryAt
        (π * a) (π * I * b)
        (canonicalJacobiThetaMovingPath ξ T) t from
      {
        p2 := hp2
        p3 := hp3
        p4 := hp4
        H := hH
        T1 := hT1
        T2 := hT2
        T3 := hT3
        T4 := hT4
        Delta := hDelta
        U := hU
      })

/-- If the two parameter velocities are constant, the moving canonical
state is an ordinary fixed-clock Jacobi trajectory. -/
theorem canonicalJacobiThetaMovingPath_isScaledTrajectory
    {ξ : ℝ → ℂ} {T : ℝ → ℍ}
    {a b : ℂ}
    (hξ : ∀ t, HasDerivAt ξ a t)
    (hT :
      ∀ t,
        HasDerivAt
          (fun u : ℝ => (T u : ℂ)) b t)
    (h1 :
      ∀ t,
        jacobiTheta1 (ξ t) (T t : ℂ) ≠ 0) :
    IsScaledJacobiTrajectory
      (π * a) (π * I * b)
      (canonicalJacobiThetaMovingPath ξ T) := by
  have hpoint :
      ∀ t,
        IsScaledJacobiRealTrajectoryAt
          (π * a) (π * I * b)
          (canonicalJacobiThetaMovingPath ξ T) t :=
    fun t =>
      canonicalJacobiThetaMovingPath_isScaledAt
        (hξ t) (hT t) (h1 t)
  exact
    {
      p2 := fun t => (hpoint t).p2
      p3 := fun t => (hpoint t).p3
      p4 := fun t => (hpoint t).p4
      H := fun t => (hpoint t).H
      T1 := fun t => (hpoint t).T1
      T2 := fun t => (hpoint t).T2
      T3 := fun t => (hpoint t).T3
      T4 := fun t => (hpoint t).T4
      Delta := fun t => (hpoint t).Delta
      U := fun t => (hpoint t).U
    }

end

end HGAS.Modular
