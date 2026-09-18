import HGAS.Modular.JacobiThetaReciprocalCoveringUnconditional
import HGAS.Modular.JacobiThetaReciprocalLiftDifferentiability

/-!
# Differentiable coherent theta lifts for linked trajectories

The unconditional covering theorem supplies a continuous elliptic
parameter.  This file upgrades that parameter to a differentiable
function whenever the chosen modular lift is differentiable.

The argument does not differentiate a covering-space construction.
Instead, it observes that the normalized linked Jacobi coordinates are
quotients of differentiable ODE coordinates with a nonzero denominator.
The local inverse theorem from
`JacobiThetaReciprocalLiftDifferentiability` then upgrades the continuous
theta lift automatically.
-/

namespace HGAS.Modular

open HGAS
open Complex Real
open UpperHalfPlane hiding I

noncomputable section

/-- Every component of the coherently twisted homogeneous Jacobi vector is
differentiable along a linked ODE trajectory. -/
theorem
    differentiableAt_coherentTwistedJacobiProjectiveCoordinates
    {κZ κPhi : ℂ}
    {T : ℝ → ℍ} {z : ℝ → LinkedJacobiState ℂ}
    (hz : IsScaledLinkedJacobiTrajectory κZ κPhi z)
    (d : CoherentJacobiCoefficientTwist T z)
    (j : Fin 4) (t : ℝ) :
    DifferentiableAt ℝ
      (fun s =>
        coherentTwistedJacobiProjectiveCoordinates d s j) t := by
  fin_cases j
  · simpa only [coherentTwistedJacobiProjectiveCoordinates,
      jacobiCoefficientTwist_zero,
      jacobiResidualProjectiveCoordinates,
      Matrix.cons_val_zero] using
      (HasDerivAt.const_mul d.d₁
        (hz.jacobi.T1 t)).differentiableAt
  · simpa only [coherentTwistedJacobiProjectiveCoordinates,
      jacobiCoefficientTwist_one,
      jacobiResidualProjectiveCoordinates,
      Matrix.cons_val_one, Matrix.cons_val_zero] using
      (HasDerivAt.const_mul d.d₂
        (hz.jacobi.T2 t)).differentiableAt
  · simpa only [coherentTwistedJacobiProjectiveCoordinates,
      jacobiCoefficientTwist_two,
      jacobiResidualProjectiveCoordinates,
      Matrix.cons_val_one, Matrix.cons_val_zero] using
      (HasDerivAt.const_mul (d.d₁ * d.d₂)
        (hz.jacobi.T3 t)).differentiableAt
  · simpa only [coherentTwistedJacobiProjectiveCoordinates,
      jacobiCoefficientTwist_three,
      jacobiResidualProjectiveCoordinates,
      Matrix.cons_val_one, Matrix.cons_val_zero] using
      (hz.jacobi.T4 t).differentiableAt

/-- The three normalized twisted Jacobi coordinates are differentiable on
the propagated reciprocal chart. -/
theorem
    differentiableAt_coherentTwistedJacobiReciprocalCoordinates
    {κZ κPhi : ℂ}
    {T : ℝ → ℍ} {z : ℝ → LinkedJacobiState ℂ}
    (hz : IsScaledLinkedJacobiTrajectory κZ κPhi z)
    {t₀ : ℝ}
    (hresidual :
      ∀ i : LinkedJacobiResidualIndex,
        linkedJacobiResidual i (z t₀) = 0)
    (d : CoherentJacobiCoefficientTwist T z)
    (k : Fin 3) (t : ℝ) :
    DifferentiableAt ℝ
      (fun s =>
        jacobiReciprocalNormalize
          (coherentTwistedJacobiProjectiveCoordinates d s) k) t := by
  exact
    (differentiableAt_coherentTwistedJacobiProjectiveCoordinates
        hz d k.succ t).div
      (differentiableAt_coherentTwistedJacobiProjectiveCoordinates
        hz d 0 t)
      (coherentTwistedJacobiProjectiveCoordinates_zero_ne_zero
        hz hresidual d t)

/-- A coherent projective theta lift identifies each normalized theta
coordinate with the corresponding normalized linked coordinate. -/
theorem coherentJacobiThetaProjectiveLift_reciprocalCoordinate
    {T : ℝ → ℍ} {z : ℝ → LinkedJacobiState ℂ}
    (d : CoherentJacobiCoefficientTwist T z)
    {ξ : ℝ → ℂ}
    (hξ : IsCoherentJacobiThetaProjectiveLift T z d ξ)
    (t : ℝ) (k : Fin 3)
    (hX0 :
      coherentTwistedJacobiProjectiveCoordinates d t 0 ≠ 0) :
    jacobiThetaReciprocalCoordinates
        (T t) (ξ t) k =
      jacobiReciprocalNormalize
        (coherentTwistedJacobiProjectiveCoordinates d t) k := by
  let X :=
    coherentTwistedJacobiProjectiveCoordinates d t
  have hprojective := hξ.projective t k.succ
  have htheta0 := hξ.thetaOne_ne_zero t
  unfold jacobiThetaReciprocalCoordinates
    jacobiReciprocalNormalize
  apply (div_eq_div_iff htheta0 hX0).mpr
  simpa only [X] using
    (show
      jacobiThetaVector (ξ t) (T t : ℂ) k.succ * X 0 =
        X k.succ *
          jacobiThetaVector (ξ t) (T t : ℂ) 0 by
      calc
        jacobiThetaVector (ξ t) (T t : ℂ) k.succ * X 0 =
            X 0 *
              jacobiThetaVector (ξ t) (T t : ℂ) k.succ := by
          ring
        _ =
            jacobiThetaVector (ξ t) (T t : ℂ) 0 * X k.succ :=
          hprojective.symm
        _ =
            X k.succ *
              jacobiThetaVector (ξ t) (T t : ℂ) 0 := by
          ring)

/-- **Unconditional differentiable projective theta lift.**

If `T` has a real derivative at every time, then the globally selected
elliptic parameter can also be chosen differentiable at every time. -/
theorem
    exists_differentiable_coherentJacobiThetaProjectiveLift_unconditional
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
    (d : CoherentJacobiCoefficientTwist T z) :
    ∃ ξ : ℝ → ℂ,
      IsCoherentJacobiThetaProjectiveLift T z d ξ ∧
        Differentiable ℝ ξ := by
  obtain ⟨ξ, hξ⟩ :=
    exists_coherentJacobiThetaProjectiveLift_unconditional
      hz hB hresidual hT d
  let p : C(ℝ, JacobiThetaReciprocalDomain) :=
    ⟨fun t =>
      ⟨T t, ξ t, by
        simpa only [jacobiThetaVector,
          Matrix.cons_val_zero] using
          hξ.thetaOne_ne_zero t⟩,
      by
        rw [continuous_induced_rng]
        exact hT.prodMk hξ.continuous⟩
  refine ⟨ξ, hξ, ?_⟩
  intro t
  have hmodulus :
      DifferentiableAt ℝ
        (fun s : ℝ => ((p s).modulus : ℂ)) t := by
    obtain ⟨v, hv⟩ := hTdiff t
    simpa only [p] using hv.differentiableAt
  have hcoordinates :
      ∀ k : Fin 3,
        DifferentiableAt ℝ
          (fun s : ℝ =>
            jacobiThetaReciprocalCoordinates
              (p s).modulus (p s).parameter k) t := by
    intro k
    have heq :
        (fun s : ℝ =>
          jacobiThetaReciprocalCoordinates
            (p s).modulus (p s).parameter k) =
        (fun s : ℝ =>
          jacobiReciprocalNormalize
            (coherentTwistedJacobiProjectiveCoordinates d s) k) := by
      funext s
      simpa only [p] using
        coherentJacobiThetaProjectiveLift_reciprocalCoordinate
          d hξ s k
          (coherentTwistedJacobiProjectiveCoordinates_zero_ne_zero
            hz hresidual d s)
    rw [heq]
    exact
      differentiableAt_coherentTwistedJacobiReciprocalCoordinates
        hz hresidual d k t
  simpa only [p] using
    differentiableAt_jacobiThetaReciprocalLift_parameter
      p t hmodulus hcoordinates

end

end HGAS.Modular
