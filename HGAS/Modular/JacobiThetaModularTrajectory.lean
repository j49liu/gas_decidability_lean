import HGAS.Modular.JacobiThetaCanonicalModularCoordinates
import HGAS.Modular.CanonicalUnaryRootsSolution

/-!
# The canonical theta state and the modular Jacobi vector field

This file upgrades the componentwise heat-equation calculations to a
trajectory statement.  We use the ambient path

```
     u ↦ canonicalJacobiThetaState z (UpperHalfPlane.ofComplex u).
```

Near an upper-half-plane point this is simply the usual holomorphic
dependence on `u`; `ofComplex` only makes the function total on `ℂ`.

All coordinates except `Delta` are established here.  The four
coefficient equations come from the already formalized normalized
theta-constant system, the four theta equations come from the heat
equation, and the reciprocal equation follows by differentiating an
inverse.  The remaining `Delta` component is the differentiated heat
equation and is isolated explicitly.
-/

namespace HGAS.Modular

open Complex Real Filter Topology
open UpperHalfPlane hiding I
open scoped Manifold

noncomputable section

/-- A total ambient version of the canonical state as the modular
variable moves. -/
def canonicalJacobiThetaModularPath
    (z : ℂ) (u : ℂ) : JacobiState ℂ :=
  canonicalJacobiThetaState z (UpperHalfPlane.ofComplex u)

@[simp]
theorem canonicalJacobiThetaModularPath_at_upperHalfPlane
    (z : ℂ) (τ : ℍ) :
    canonicalJacobiThetaModularPath z (τ : ℂ) =
      canonicalJacobiThetaState z τ := by
  simp only [canonicalJacobiThetaModularPath,
    ofComplex_apply]

/-- Converting a paper-normalized modular derivative into an ordinary
complex derivative of the ambient upper-half-plane restriction. -/
theorem hasDerivAt_comp_ofComplex_of_paperNormalized
    {F : ℍ → ℂ} (τ : ℍ) {P : ℂ}
    (hF : MDiff F)
    (hnormalized :
      2 * Derivative.normalizedDerivOfComplex F τ = P) :
    HasDerivAt
      (F ∘ UpperHalfPlane.ofComplex)
      (π * I * P) (τ : ℂ) := by
  have hdiff :
      DifferentiableAt ℂ
        (F ∘ UpperHalfPlane.ofComplex) (τ : ℂ) :=
    UpperHalfPlane.mdifferentiableAt_iff.mp (hF τ)
  have hpi :
      (π : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hderiv :
      deriv (F ∘ UpperHalfPlane.ofComplex) (τ : ℂ) =
        π * I * P := by
    unfold Derivative.normalizedDerivOfComplex at hnormalized
    field_simp [hpi, I_ne_zero] at hnormalized
    exact hnormalized
  rw [← hderiv]
  exact hdiff.hasDerivAt

/-! ## Matching the root and Jacobi coefficient fields -/

theorem canonical_rootVectorField_p2_eq_jacobiModular
    (z : ℂ) (τ : ℍ) :
    (UnaryRootState.vectorField
        (canonicalUnaryRoots τ)).p2 =
      (JacobiState.modularVectorField
        (canonicalJacobiThetaState z τ)).p2 := by
  have hJacobi :=
    canonicalUnaryRoots_p3_sq_eq τ
  simp only [UnaryRootState.vectorField,
    JacobiState.modularVectorField,
    canonicalJacobiThetaState_p2,
    canonicalJacobiThetaState_p3,
    canonicalJacobiThetaState_p4,
    canonicalJacobiThetaState_H]
  linear_combination
    (-(canonicalUnaryRoots τ).p2 / 6) * hJacobi

theorem canonical_rootVectorField_p3_eq_jacobiModular
    (z : ℂ) (τ : ℍ) :
    (UnaryRootState.vectorField
        (canonicalUnaryRoots τ)).p3 =
      (JacobiState.modularVectorField
        (canonicalJacobiThetaState z τ)).p3 := by
  simp only [UnaryRootState.vectorField,
    JacobiState.modularVectorField,
    canonicalJacobiThetaState_p2,
    canonicalJacobiThetaState_p3,
    canonicalJacobiThetaState_p4,
    canonicalJacobiThetaState_H]
  ring

theorem canonical_rootVectorField_p4_eq_jacobiModular
    (z : ℂ) (τ : ℍ) :
    (UnaryRootState.vectorField
        (canonicalUnaryRoots τ)).p4 =
      (JacobiState.modularVectorField
        (canonicalJacobiThetaState z τ)).p4 := by
  have hJacobi :=
    canonicalUnaryRoots_p3_sq_eq τ
  simp only [UnaryRootState.vectorField,
    JacobiState.modularVectorField,
    canonicalJacobiThetaState_p2,
    canonicalJacobiThetaState_p3,
    canonicalJacobiThetaState_p4,
    canonicalJacobiThetaState_H]
  linear_combination
    ((canonicalUnaryRoots τ).p4 / 6) * hJacobi

theorem canonical_rootVectorField_H_eq_jacobiModular
    (z : ℂ) (τ : ℍ) :
    (UnaryRootState.vectorField
        (canonicalUnaryRoots τ)).H =
      (JacobiState.modularVectorField
        (canonicalJacobiThetaState z τ)).H := by
  have hJacobi :=
    canonicalUnaryRoots_p3_sq_eq τ
  simp only [UnaryRootState.vectorField,
    JacobiState.modularVectorField,
    canonicalJacobiThetaState_p2,
    canonicalJacobiThetaState_p3,
    canonicalJacobiThetaState_p4,
    canonicalJacobiThetaState_H]
  linear_combination
    ((canonicalUnaryRoots τ).p3 ^ 2 +
      (canonicalUnaryRoots τ).p2 ^ 2 +
      (canonicalUnaryRoots τ).p4 ^ 2) / 144 *
        hJacobi

/-! ## Pointwise modular trajectory -/

/-- All modular coordinate equations except the derivative coordinate
`Delta`. -/
structure IsScaledJacobiModularTrajectoryAtExceptDelta
    (κ : ℂ) (s : ℂ → JacobiState ℂ) (u : ℂ) : Prop where
  p2 : HasDerivAt (fun v => (s v).p2)
    (κ * (JacobiState.modularVectorField (s u)).p2) u
  p3 : HasDerivAt (fun v => (s v).p3)
    (κ * (JacobiState.modularVectorField (s u)).p3) u
  p4 : HasDerivAt (fun v => (s v).p4)
    (κ * (JacobiState.modularVectorField (s u)).p4) u
  H : HasDerivAt (fun v => (s v).H)
    (κ * (JacobiState.modularVectorField (s u)).H) u
  T1 : HasDerivAt (fun v => (s v).T1)
    (κ * (JacobiState.modularVectorField (s u)).T1) u
  T2 : HasDerivAt (fun v => (s v).T2)
    (κ * (JacobiState.modularVectorField (s u)).T2) u
  T3 : HasDerivAt (fun v => (s v).T3)
    (κ * (JacobiState.modularVectorField (s u)).T3) u
  T4 : HasDerivAt (fun v => (s v).T4)
    (κ * (JacobiState.modularVectorField (s u)).T4) u
  U : HasDerivAt (fun v => (s v).U)
    (κ * (JacobiState.modularVectorField (s u)).U) u

/-- The complete pointwise modular trajectory predicate. -/
structure IsScaledJacobiModularTrajectoryAt
    (κ : ℂ) (s : ℂ → JacobiState ℂ) (u : ℂ) : Prop
    extends IsScaledJacobiModularTrajectoryAtExceptDelta κ s u where
  Delta : HasDerivAt (fun v => (s v).Delta)
    (κ * (JacobiState.modularVectorField (s u)).Delta) u

/-- The canonical state satisfies every modular coordinate equation
except `Delta`, unconditionally on the reciprocal chart. -/
theorem canonicalJacobiThetaState_modular_exceptDelta
    (z : ℂ) (τ : ℍ)
    (h1 : jacobiTheta1 z (τ : ℂ) ≠ 0) :
    IsScaledJacobiModularTrajectoryAtExceptDelta
      (π * I) (canonicalJacobiThetaModularPath z) (τ : ℂ) := by
  have hp2raw :=
    hasDerivAt_comp_ofComplex_of_paperNormalized
      τ canonicalUnaryRoots_p2_mdifferentiable
      (canonicalUnaryRoots_isPaperNormalized.p2_eq τ)
  have hp3raw :=
    hasDerivAt_comp_ofComplex_of_paperNormalized
      τ canonicalUnaryRoots_p3_mdifferentiable
      (canonicalUnaryRoots_isPaperNormalized.p3_eq τ)
  have hp4raw :=
    hasDerivAt_comp_ofComplex_of_paperNormalized
      τ canonicalUnaryRoots_p4_mdifferentiable
      (canonicalUnaryRoots_isPaperNormalized.p4_eq τ)
  have hHraw :=
    hasDerivAt_comp_ofComplex_of_paperNormalized
      τ canonicalUnaryRoots_H_mdifferentiable
      (canonicalUnaryRoots_isPaperNormalized.H_eq τ)
  have hT1raw :=
    canonicalJacobiThetaState_T1_modular_hasDerivAt
      z τ h1
  have hT2raw :=
    canonicalJacobiThetaState_T2_modular_hasDerivAt
      z τ h1
  have hT3raw :=
    canonicalJacobiThetaState_T3_modular_hasDerivAt
      z τ h1
  have hT4raw :=
    canonicalJacobiThetaState_T4_modular_hasDerivAt
      z τ h1
  have hupp :
      ∀ᶠ u : ℂ in nhds (τ : ℂ),
        u ∈ upperHalfPlaneSet :=
    isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos
  have hp2 :
      HasDerivAt
        (fun u =>
          (canonicalJacobiThetaModularPath z u).p2)
        (π * I *
          (JacobiState.modularVectorField
            (canonicalJacobiThetaState z τ)).p2)
        (τ : ℂ) := by
    have hlocal :
        (fun u =>
          (canonicalJacobiThetaModularPath z u).p2) =ᶠ[nhds (τ : ℂ)]
        ((fun σ : ℍ =>
          (canonicalUnaryRoots σ).p2) ∘
            UpperHalfPlane.ofComplex) := by
      filter_upwards [hupp] with u hu
      simp only [canonicalJacobiThetaModularPath,
        canonicalJacobiThetaState_p2,
        Function.comp_apply,
        ofComplex_apply_of_im_pos hu]
    have h := hp2raw.congr_of_eventuallyEq hlocal
    rw [canonical_rootVectorField_p2_eq_jacobiModular z τ]
      at h
    exact h
  have hp3 :
      HasDerivAt
        (fun u =>
          (canonicalJacobiThetaModularPath z u).p3)
        (π * I *
          (JacobiState.modularVectorField
            (canonicalJacobiThetaState z τ)).p3)
        (τ : ℂ) := by
    have hlocal :
        (fun u =>
          (canonicalJacobiThetaModularPath z u).p3) =ᶠ[nhds (τ : ℂ)]
        ((fun σ : ℍ =>
          (canonicalUnaryRoots σ).p3) ∘
            UpperHalfPlane.ofComplex) := by
      filter_upwards [hupp] with u hu
      simp only [canonicalJacobiThetaModularPath,
        canonicalJacobiThetaState_p3,
        Function.comp_apply,
        ofComplex_apply_of_im_pos hu]
    have h := hp3raw.congr_of_eventuallyEq hlocal
    rw [canonical_rootVectorField_p3_eq_jacobiModular z τ]
      at h
    exact h
  have hp4 :
      HasDerivAt
        (fun u =>
          (canonicalJacobiThetaModularPath z u).p4)
        (π * I *
          (JacobiState.modularVectorField
            (canonicalJacobiThetaState z τ)).p4)
        (τ : ℂ) := by
    have hlocal :
        (fun u =>
          (canonicalJacobiThetaModularPath z u).p4) =ᶠ[nhds (τ : ℂ)]
        ((fun σ : ℍ =>
          (canonicalUnaryRoots σ).p4) ∘
            UpperHalfPlane.ofComplex) := by
      filter_upwards [hupp] with u hu
      simp only [canonicalJacobiThetaModularPath,
        canonicalJacobiThetaState_p4,
        Function.comp_apply,
        ofComplex_apply_of_im_pos hu]
    have h := hp4raw.congr_of_eventuallyEq hlocal
    rw [canonical_rootVectorField_p4_eq_jacobiModular z τ]
      at h
    exact h
  have hH :
      HasDerivAt
        (fun u =>
          (canonicalJacobiThetaModularPath z u).H)
        (π * I *
          (JacobiState.modularVectorField
            (canonicalJacobiThetaState z τ)).H)
        (τ : ℂ) := by
    have hlocal :
        (fun u =>
          (canonicalJacobiThetaModularPath z u).H) =ᶠ[nhds (τ : ℂ)]
        ((fun σ : ℍ =>
          (canonicalUnaryRoots σ).H) ∘
            UpperHalfPlane.ofComplex) := by
      filter_upwards [hupp] with u hu
      simp only [canonicalJacobiThetaModularPath,
        canonicalJacobiThetaState_H,
        Function.comp_apply,
        ofComplex_apply_of_im_pos hu]
    have h := hHraw.congr_of_eventuallyEq hlocal
    rw [canonical_rootVectorField_H_eq_jacobiModular z τ]
      at h
    exact h
  have hT1 :
      HasDerivAt
        (fun u =>
          (canonicalJacobiThetaModularPath z u).T1)
        (π * I *
          (JacobiState.modularVectorField
            (canonicalJacobiThetaState z τ)).T1)
        (τ : ℂ) := by
    have hlocal :
        (fun u =>
          (canonicalJacobiThetaModularPath z u).T1) =ᶠ[nhds (τ : ℂ)]
        (fun u => jacobiTheta1 z u) := by
      filter_upwards [hupp] with u hu
      simp only [canonicalJacobiThetaModularPath,
        canonicalJacobiThetaState_T1,
        ofComplex_apply_of_im_pos hu]
    exact hT1raw.congr_of_eventuallyEq hlocal
  have hT2 :
      HasDerivAt
        (fun u =>
          (canonicalJacobiThetaModularPath z u).T2)
        (π * I *
          (JacobiState.modularVectorField
            (canonicalJacobiThetaState z τ)).T2)
        (τ : ℂ) := by
    have hlocal :
        (fun u =>
          (canonicalJacobiThetaModularPath z u).T2) =ᶠ[nhds (τ : ℂ)]
        (fun u => jacobiTheta2 z u) := by
      filter_upwards [hupp] with u hu
      simp only [canonicalJacobiThetaModularPath,
        canonicalJacobiThetaState_T2,
        ofComplex_apply_of_im_pos hu]
    exact hT2raw.congr_of_eventuallyEq hlocal
  have hT3 :
      HasDerivAt
        (fun u =>
          (canonicalJacobiThetaModularPath z u).T3)
        (π * I *
          (JacobiState.modularVectorField
            (canonicalJacobiThetaState z τ)).T3)
        (τ : ℂ) := by
    have hlocal :
        (fun u =>
          (canonicalJacobiThetaModularPath z u).T3) =ᶠ[nhds (τ : ℂ)]
        (fun u => jacobiTheta3 z u) := by
      filter_upwards [hupp] with u hu
      simp only [canonicalJacobiThetaModularPath,
        canonicalJacobiThetaState_T3,
        ofComplex_apply_of_im_pos hu]
    exact hT3raw.congr_of_eventuallyEq hlocal
  have hT4 :
      HasDerivAt
        (fun u =>
          (canonicalJacobiThetaModularPath z u).T4)
        (π * I *
          (JacobiState.modularVectorField
            (canonicalJacobiThetaState z τ)).T4)
        (τ : ℂ) := by
    have hlocal :
        (fun u =>
          (canonicalJacobiThetaModularPath z u).T4) =ᶠ[nhds (τ : ℂ)]
        (fun u => jacobiTheta4 z u) := by
      filter_upwards [hupp] with u hu
      simp only [canonicalJacobiThetaModularPath,
        canonicalJacobiThetaState_T4,
        ofComplex_apply_of_im_pos hu]
    exact hT4raw.congr_of_eventuallyEq hlocal
  have hU :
      HasDerivAt
        (fun u =>
          (canonicalJacobiThetaModularPath z u).U)
        (π * I *
          (JacobiState.modularVectorField
            (canonicalJacobiThetaState z τ)).U)
        (τ : ℂ) := by
    have h1path :
        (canonicalJacobiThetaModularPath z
          (τ : ℂ)).T1 ≠ 0 := by
      simpa only [
        canonicalJacobiThetaModularPath_at_upperHalfPlane,
        canonicalJacobiThetaState_T1] using h1
    have hinverse :=
      hT1.inv h1path
    have hfun :
        (fun u =>
          (canonicalJacobiThetaModularPath z u).U) =
        (fun u =>
          (canonicalJacobiThetaModularPath z u).T1)⁻¹ := by
      funext u
      rfl
    rw [← hfun] at hinverse
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
    have hderivative :
        -(π * I * P.T1) / q.T1 ^ 2 =
          π * I * P.U := by
      rw [hPU, hqU]
      field_simp [hqT1]
    simpa only [
      canonicalJacobiThetaModularPath_at_upperHalfPlane,
      q, P, hderivative] using hinverse
  exact
    {
      p2 := by
        simpa only [
          canonicalJacobiThetaModularPath_at_upperHalfPlane]
          using hp2
      p3 := by
        simpa only [
          canonicalJacobiThetaModularPath_at_upperHalfPlane]
          using hp3
      p4 := by
        simpa only [
          canonicalJacobiThetaModularPath_at_upperHalfPlane]
          using hp4
      H := by
        simpa only [
          canonicalJacobiThetaModularPath_at_upperHalfPlane]
          using hH
      T1 := by
        simpa only [
          canonicalJacobiThetaModularPath_at_upperHalfPlane]
          using hT1
      T2 := by
        simpa only [
          canonicalJacobiThetaModularPath_at_upperHalfPlane]
          using hT2
      T3 := by
        simpa only [
          canonicalJacobiThetaModularPath_at_upperHalfPlane]
          using hT3
      T4 := by
        simpa only [
          canonicalJacobiThetaModularPath_at_upperHalfPlane]
          using hT4
      U := by
        simpa only [
          canonicalJacobiThetaModularPath_at_upperHalfPlane]
          using hU
    }

end

end HGAS.Modular
