import HGAS.Analysis.AutonomousC1ODEUniqueness
import HGAS.Modular.JacobiPolynomialCode
import HGAS.Modular.JacobiResidualDynamics
import HGAS.Modular.JacobiThetaMovingTrajectory
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic

/-!
# Uniqueness for the polynomial Jacobi system

The Jacobi field is polynomial and hence `C¹`, but it is not globally
Lipschitz.  `AutonomousC1ODEUniqueness` supplies the correct
local-to-global theorem for precisely this situation.  Here we package
the ten structured complex coordinates as `Fin 10 → ℂ`, verify the
coordinate ODE, and obtain a reusable uniqueness principle for arbitrary
complex clock multipliers.
-/

namespace HGAS.Modular

open HGAS

noncomputable section

/-- Coordinate presentation of the combined Jacobi vector field. -/
def jacobiCoordinateVectorField
    (κZ κPhi : ℂ)
    (x : Fin JacobiPolynomialCode.dimension → ℂ) :
    Fin JacobiPolynomialCode.dimension → ℂ :=
  JacobiPolynomialCode.point
    (JacobiState.combinedVectorField κZ κPhi
      (JacobiPolynomialCode.state x))

set_option linter.flexible false in
/-- The coordinate Jacobi field is continuously differentiable over the
underlying real normed space.

The proof deliberately exposes all ten coordinates to `fun_prop`.  The
local linter setting only records that this coordinate normalization is
performed by `simp`; it does not weaken the theorem or add an assumption. -/
theorem contDiff_jacobiCoordinateVectorField
    (κZ κPhi : ℂ) :
    ContDiff ℝ 1
      (jacobiCoordinateVectorField κZ κPhi) := by
  rw [contDiff_pi]
  intro i
  fin_cases i <;>
    simp [jacobiCoordinateVectorField,
      JacobiPolynomialCode.point,
      JacobiPolynomialCode.state,
      JacobiPolynomialCode.p2Index,
      JacobiPolynomialCode.p3Index,
      JacobiPolynomialCode.p4Index,
      JacobiPolynomialCode.HIndex,
      JacobiPolynomialCode.T1Index,
      JacobiPolynomialCode.T2Index,
      JacobiPolynomialCode.T3Index,
      JacobiPolynomialCode.T4Index,
      JacobiPolynomialCode.DeltaIndex,
      JacobiPolynomialCode.UIndex,
      JacobiState.combinedVectorField,
      JacobiState.ellipticVectorField,
      JacobiState.modularVectorField,
      JacobiState.K] <;>
    fun_prop

/-- A structured Jacobi trajectory is an integral curve of the
coordinate vector field. -/
theorem IsScaledJacobiTrajectory.point_hasDerivAt
    {κZ κPhi : ℂ} {z : ℝ → JacobiState ℂ}
    (hz : IsScaledJacobiTrajectory κZ κPhi z)
    (t : ℝ) :
    HasDerivAt
      (fun s ↦ JacobiPolynomialCode.point (z s))
      (jacobiCoordinateVectorField κZ κPhi
        (JacobiPolynomialCode.point (z t))) t := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · simpa [jacobiCoordinateVectorField,
      JacobiPolynomialCode.point,
      JacobiPolynomialCode.p2Index] using hz.p2 t
  · simpa [jacobiCoordinateVectorField,
      JacobiPolynomialCode.point,
      JacobiPolynomialCode.p3Index] using hz.p3 t
  · simpa [jacobiCoordinateVectorField,
      JacobiPolynomialCode.point,
      JacobiPolynomialCode.p4Index] using hz.p4 t
  · simpa [jacobiCoordinateVectorField,
      JacobiPolynomialCode.point,
      JacobiPolynomialCode.HIndex] using hz.H t
  · simpa [jacobiCoordinateVectorField,
      JacobiPolynomialCode.point,
      JacobiPolynomialCode.T1Index] using hz.T1 t
  · simpa [jacobiCoordinateVectorField,
      JacobiPolynomialCode.point,
      JacobiPolynomialCode.T2Index] using hz.T2 t
  · simpa [jacobiCoordinateVectorField,
      JacobiPolynomialCode.point,
      JacobiPolynomialCode.T3Index] using hz.T3 t
  · simpa [jacobiCoordinateVectorField,
      JacobiPolynomialCode.point,
      JacobiPolynomialCode.T4Index] using hz.T4 t
  · simpa [jacobiCoordinateVectorField,
      JacobiPolynomialCode.point,
      JacobiPolynomialCode.DeltaIndex] using hz.Delta t
  · simpa [jacobiCoordinateVectorField,
      JacobiPolynomialCode.point,
      JacobiPolynomialCode.UIndex] using hz.U t

/-- Pointwise trajectories give the same coordinate-space integral-curve
identity.  This is the local counterpart of
`IsScaledJacobiTrajectory.point_hasDerivAt`. -/
theorem IsScaledJacobiRealTrajectoryAt.point_hasDerivAt
    {κZ κPhi : ℂ} {z : ℝ → JacobiState ℂ}
    {t : ℝ}
    (hz : IsScaledJacobiRealTrajectoryAt κZ κPhi z t) :
    HasDerivAt
      (fun s ↦ JacobiPolynomialCode.point (z s))
      (jacobiCoordinateVectorField κZ κPhi
        (JacobiPolynomialCode.point (z t))) t := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · simpa [jacobiCoordinateVectorField,
      JacobiPolynomialCode.point,
      JacobiPolynomialCode.p2Index] using hz.p2
  · simpa [jacobiCoordinateVectorField,
      JacobiPolynomialCode.point,
      JacobiPolynomialCode.p3Index] using hz.p3
  · simpa [jacobiCoordinateVectorField,
      JacobiPolynomialCode.point,
      JacobiPolynomialCode.p4Index] using hz.p4
  · simpa [jacobiCoordinateVectorField,
      JacobiPolynomialCode.point,
      JacobiPolynomialCode.HIndex] using hz.H
  · simpa [jacobiCoordinateVectorField,
      JacobiPolynomialCode.point,
      JacobiPolynomialCode.T1Index] using hz.T1
  · simpa [jacobiCoordinateVectorField,
      JacobiPolynomialCode.point,
      JacobiPolynomialCode.T2Index] using hz.T2
  · simpa [jacobiCoordinateVectorField,
      JacobiPolynomialCode.point,
      JacobiPolynomialCode.T3Index] using hz.T3
  · simpa [jacobiCoordinateVectorField,
      JacobiPolynomialCode.point,
      JacobiPolynomialCode.T4Index] using hz.T4
  · simpa [jacobiCoordinateVectorField,
      JacobiPolynomialCode.point,
      JacobiPolynomialCode.DeltaIndex] using hz.Delta
  · simpa [jacobiCoordinateVectorField,
      JacobiPolynomialCode.point,
      JacobiPolynomialCode.UIndex] using hz.U

/-- **Global uniqueness for the combined Jacobi system.** -/
theorem IsScaledJacobiTrajectory.eq_of_eq_at
    {κZ κPhi : ℂ}
    {z₁ z₂ : ℝ → JacobiState ℂ}
    (hz₁ : IsScaledJacobiTrajectory κZ κPhi z₁)
    (hz₂ : IsScaledJacobiTrajectory κZ κPhi z₂)
    {t₀ : ℝ}
    (heq : z₁ t₀ = z₂ t₀) :
    z₁ = z₂ := by
  have hpoint :
      (fun t ↦ JacobiPolynomialCode.point (z₁ t)) =
        (fun t ↦ JacobiPolynomialCode.point (z₂ t)) := by
    exact
      HGAS.Analysis.autonomousC1_ode_solution_unique
        (contDiff_jacobiCoordinateVectorField κZ κPhi)
        (fun t ↦ hz₁.point_hasDerivAt t)
        (fun t ↦ hz₂.point_hasDerivAt t)
        (congrArg JacobiPolynomialCode.point heq)
  funext t
  have ht := congrFun hpoint t
  have hstate :=
    congrArg JacobiPolynomialCode.state ht
  simpa using hstate

end

end HGAS.Modular
