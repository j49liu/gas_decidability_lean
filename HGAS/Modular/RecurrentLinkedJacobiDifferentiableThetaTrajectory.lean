import HGAS.Modular.LinkedJacobiThetaDifferentiableLift
import HGAS.Modular.RecurrentLinkedJacobiCoherentThetaTrajectory

/-!
# Recurrent linked trajectories have differentiable coherent theta lifts

The coherent recurrent representation was initially formulated with a
continuous elliptic parameter because covering-space path lifting is a
topological theorem.  The reciprocal theta map is locally a `C¹`
diffeomorphism, so the parameter is in fact differentiable along every
linked polynomial ODE trajectory.

This file records that stronger endpoint while retaining the exact
Riccati equations for the modular lift.
-/

namespace HGAS.Modular

open HGAS
open Complex
open UpperHalfPlane hiding I

noncomputable section

/-- A coherent moving-modulus theta representation whose elliptic
parameter is differentiable along real time. -/
structure DifferentiableCoherentMovingJacobiThetaRepresentation
    (T : ℝ → ℍ) (z : ℝ → LinkedJacobiState ℂ) where
  toCoherentRepresentation :
    CoherentMovingJacobiThetaRepresentation T z
  parameter_differentiable :
    Differentiable ℝ toCoherentRepresentation.parameter

namespace DifferentiableCoherentMovingJacobiThetaRepresentation

variable {T : ℝ → ℍ} {z : ℝ → LinkedJacobiState ℂ}

/-- The underlying continuous elliptic parameter. -/
def parameter
    (r : DifferentiableCoherentMovingJacobiThetaRepresentation T z) :
    ℝ → ℂ :=
  r.toCoherentRepresentation.parameter

theorem differentiable_parameter
    (r : DifferentiableCoherentMovingJacobiThetaRepresentation T z) :
    Differentiable ℝ r.parameter :=
  r.parameter_differentiable

theorem continuous_parameter
    (r : DifferentiableCoherentMovingJacobiThetaRepresentation T z) :
    Continuous r.parameter :=
  r.differentiable_parameter.continuous

end DifferentiableCoherentMovingJacobiThetaRepresentation

/-- A differentiable modular lift gives a differentiable coherent theta
representation, unconditionally. -/
theorem
    nonempty_differentiableCoherentMovingJacobiThetaRepresentation_unconditional
    {κZ κPhi : ℂ}
    {T : ℝ → ℍ} {z : ℝ → LinkedJacobiState ℂ}
    (hz : IsScaledLinkedJacobiTrajectory κZ κPhi z)
    {t₀ : ℝ}
    (hB : UnaryModularState.B (z t₀).unary ≠ 0)
    (hresidual :
      ∀ i : LinkedJacobiResidualIndex,
        linkedJacobiResidual i (z t₀) = 0)
    (hT : Continuous T)
    (hTdiff :
      ∀ t, ∃ v : ℂ,
        HasDerivAt (fun s : ℝ => (T s : ℂ)) v t)
    (hLambda :
      ∀ t,
        UnaryModularState.lambdaCoordinate (z t).unary =
          canonicalLambda (T t)) :
    Nonempty
      (DifferentiableCoherentMovingJacobiThetaRepresentation T z) := by
  obtain ⟨d⟩ :=
    nonempty_coherentJacobiCoefficientTwist_along_trajectory
      hz hB hresidual T hT hLambda
  obtain ⟨ξ, hξ, hξdiff⟩ :=
    exists_differentiable_coherentJacobiThetaProjectiveLift_unconditional
      hz hB hresidual hT hTdiff d
  exact
    ⟨{
      toCoherentRepresentation :=
        {
          twist := d
          parameter := ξ
          isProjectiveLift := hξ
        }
      parameter_differentiable := hξdiff
    }⟩

/-- **Strongest current recurrent trajectory endpoint.**

In the generic branch this theorem simultaneously returns:

* one differentiable canonical-lambda lift;
* its exact Riccati two-jet and fractional-linear dynamics;
* its horizontal-or-horocycle recurrent geometry;
* one constant finite coefficient twist; and
* one globally differentiable elliptic theta lift representing the actual
  linked ODE trajectory.

No covering, branch-selection, or differentiability hypothesis remains in
the conclusion. -/
theorem
    recurrentLinkedJacobi_equilibrium_or_differentiableCoherentMovingThetaTrajectory
    {κZ : ℂ}
    {z : ℝ → LinkedJacobiState ℂ}
    (hz :
      IsScaledLinkedJacobiTrajectory
        κZ modularIndependentVariableClock z)
    {t₀ : ℝ}
    (hrec :
      ForwardRecurrentAt
        (fun t ↦ LinkedJacobiPolynomialCode.point (z t)) t₀)
    (hresidual :
      ∀ i : LinkedJacobiResidualIndex,
        linkedJacobiResidual i (z t₀) = 0) :
    UnaryModularState.vectorField (z t₀).unary = 0 ∨
      ∃ T : ℝ → ℍ,
        Continuous T ∧
        (∀ t,
          UnaryModularState.lambdaCoordinate (z t).unary =
            canonicalLambda (T t)) ∧
        (∀ t,
          HasDerivAt
            (fun s : ℝ ↦ (T s : ℂ))
            (linkedJacobiThetaComparisonV T z t) t) ∧
        IsRiccatiJetTrajectory
          (linkedJacobiThetaComparisonU T z)
          (linkedJacobiThetaComparisonV T z)
          (fun t ↦ (T t : ℂ)) ∧
        IsHorizontalOrHorocycleLift
          (fun t ↦ (z t).unary) T t₀ ∧
        Nonempty
          (DifferentiableCoherentMovingJacobiThetaRepresentation
            T z) := by
  rcases
      recurrentLinkedJacobi_equilibrium_or_differentiableCoherentThetaTrajectory
        hz hrec hresidual with
    hequilibrium | hgeneric
  · exact Or.inl hequilibrium
  · right
    rcases hgeneric with
      ⟨T, hT, hLambda, hTvelocity, hjet,
        hgeometry, _hcontinuousRepresentation⟩
    have hTdiff :
        ∀ t, ∃ v : ℂ,
          HasDerivAt (fun s : ℝ => (T s : ℂ)) v t :=
      fun t => ⟨linkedJacobiThetaComparisonV T z t,
        hTvelocity t⟩
    have hB :
        UnaryModularState.B (z t₀).unary ≠ 0 := by
      intro hzero
      have hlambda := hLambda t₀
      unfold UnaryModularState.lambdaCoordinate at hlambda
      rw [hzero, div_zero] at hlambda
      exact canonicalLambda_ne_zero (T t₀) hlambda.symm
    exact
      ⟨T, hT, hLambda, hTvelocity, hjet, hgeometry,
        nonempty_differentiableCoherentMovingJacobiThetaRepresentation_unconditional
          hz hB hresidual hT hTdiff hLambda⟩

end

end HGAS.Modular
