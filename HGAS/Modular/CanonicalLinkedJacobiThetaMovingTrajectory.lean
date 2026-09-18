import HGAS.Modular.JacobiThetaMovingTrajectory
import HGAS.Modular.CanonicalUnaryComparison
import HGAS.Modular.JacobiCoefficientLinkDynamics

/-!
# Canonical moving trajectories for linked Jacobi blocks

A linked block stores the unary modular state and the ten-coordinate
Jacobi state together.  The two sides use the same modular clock.  The
previous modules prove:

* `canonicalUnaryTheta (T(t))` has clock `π i T'`; and
* `canonicalJacobiThetaState (ξ(t),T(t))` has clocks
  `π ξ'` and `π i T'`.

This file packages those facts into the exact
`IsScaledLinkedJacobiTrajectory` interface used by the polynomial
compilers.  A finite-family version is included because the detector uses
one linked block per arithmetic variable.
-/

namespace HGAS.Modular

open Complex Real
open UpperHalfPlane hiding I

noncomputable section

/-- Canonical unary state along a real modular path. -/
def canonicalUnaryThetaMovingPath
    (T : ℝ → ℍ) (t : ℝ) :
    UnaryModularState ℂ :=
  canonicalUnaryTheta (T t)

/-- A constant-velocity modular path gives a fixed-clock canonical unary
trajectory. -/
theorem canonicalUnaryThetaMovingPath_isScaledTrajectory
    {T : ℝ → ℍ} {b : ℂ}
    (hT :
      ∀ t,
        HasDerivAt
          (fun u : ℝ => (T u : ℂ)) b t) :
    IsScaledUnaryModularTrajectory
      (π * I * b)
      (canonicalUnaryThetaMovingPath T) := by
  have hvariable :=
    canonicalUnaryTheta_comp_isVariableScaled
      T (fun _ => b) hT
  exact
    {
      A := fun t => by
        simpa only [canonicalUnaryThetaMovingPath,
          modularIndependentVariableClock] using
          hvariable.A t
      C := fun t => by
        simpa only [canonicalUnaryThetaMovingPath,
          modularIndependentVariableClock] using
          hvariable.C t
      E := fun t => by
        simpa only [canonicalUnaryThetaMovingPath,
          modularIndependentVariableClock] using
          hvariable.E t
      Y := fun t => by
        simpa only [canonicalUnaryThetaMovingPath,
          modularIndependentVariableClock] using
          hvariable.Y t
    }

/-- Canonical linked unary--Jacobi state with both the elliptic and
modular parameters moving. -/
def canonicalLinkedJacobiThetaMovingPath
    (ξ : ℝ → ℂ) (T : ℝ → ℍ) (t : ℝ) :
    LinkedJacobiState ℂ where
  unary := canonicalUnaryThetaMovingPath T t
  jacobi := canonicalJacobiThetaMovingPath ξ T t

@[simp]
theorem canonicalLinkedJacobiThetaMovingPath_unary
    (ξ : ℝ → ℂ) (T : ℝ → ℍ) (t : ℝ) :
    (canonicalLinkedJacobiThetaMovingPath ξ T t).unary =
      canonicalUnaryTheta (T t) :=
  rfl

@[simp]
theorem canonicalLinkedJacobiThetaMovingPath_jacobi
    (ξ : ℝ → ℂ) (T : ℝ → ℍ) (t : ℝ) :
    (canonicalLinkedJacobiThetaMovingPath ξ T t).jacobi =
      canonicalJacobiThetaState (ξ t) (T t) :=
  rfl

/-- The complete canonical linked block solves the exact combined
unary--Jacobi field. -/
theorem canonicalLinkedJacobiThetaMovingPath_isScaledTrajectory
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
    IsScaledLinkedJacobiTrajectory
      (π * a) (π * I * b)
      (canonicalLinkedJacobiThetaMovingPath ξ T) := by
  exact
    {
      unary := by
        simpa only [
          canonicalLinkedJacobiThetaMovingPath_unary] using
          canonicalUnaryThetaMovingPath_isScaledTrajectory hT
      jacobi := by
        simpa only [
          canonicalLinkedJacobiThetaMovingPath_jacobi] using
          canonicalJacobiThetaMovingPath_isScaledTrajectory
            hξ hT h1
    }

/-! ## Finite-family packaging -/

/-- A finite family of linked trajectories with block-dependent constant
clocks. -/
structure IsScaledLinkedJacobiFamilyTrajectory
    {b : ℕ}
    (κZ κPhi : Fin b → ℂ)
    (z : ℝ → Fin b → LinkedJacobiState ℂ) : Prop where
  block :
    ∀ j,
      IsScaledLinkedJacobiTrajectory
        (κZ j) (κPhi j) (fun t => z t j)

/-- Canonical state family, one moving theta block for each finite
index. -/
def canonicalLinkedJacobiThetaFamilyMovingPath
    {b : ℕ}
    (ξ : Fin b → ℝ → ℂ)
    (T : Fin b → ℝ → ℍ)
    (t : ℝ) (j : Fin b) :
    LinkedJacobiState ℂ :=
  canonicalLinkedJacobiThetaMovingPath
    (ξ j) (T j) t

@[simp]
theorem canonicalLinkedJacobiThetaFamilyMovingPath_apply
    {b : ℕ}
    (ξ : Fin b → ℝ → ℂ)
    (T : Fin b → ℝ → ℍ)
    (t : ℝ) (j : Fin b) :
    canonicalLinkedJacobiThetaFamilyMovingPath ξ T t j =
      canonicalLinkedJacobiThetaMovingPath
        (ξ j) (T j) t :=
  rfl

/-- All canonical blocks in a finite family solve their corresponding
linked fields simultaneously. -/
theorem
    canonicalLinkedJacobiThetaFamilyMovingPath_isScaledTrajectory
    {b : ℕ}
    {ξ : Fin b → ℝ → ℂ}
    {T : Fin b → ℝ → ℍ}
    {a c : Fin b → ℂ}
    (hξ :
      ∀ j t,
        HasDerivAt (ξ j) (a j) t)
    (hT :
      ∀ j t,
        HasDerivAt
          (fun u : ℝ => (T j u : ℂ))
          (c j) t)
    (h1 :
      ∀ j t,
        jacobiTheta1
          (ξ j t) (T j t : ℂ) ≠ 0) :
    IsScaledLinkedJacobiFamilyTrajectory
      (fun j => π * a j)
      (fun j => π * I * c j)
      (canonicalLinkedJacobiThetaFamilyMovingPath ξ T) where
  block j := by
    simpa only [
      canonicalLinkedJacobiThetaFamilyMovingPath_apply] using
      canonicalLinkedJacobiThetaMovingPath_isScaledTrajectory
        (fun t => hξ j t)
        (fun t => hT j t)
        (fun t => h1 j t)

end

end HGAS.Modular
