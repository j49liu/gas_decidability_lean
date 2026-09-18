import HGAS.Modular.RecurrentLinkedJacobiDifferentiableThetaTrajectory
import HGAS.Modular.JacobiThetaPrimeJointDifferentiability

/-!
# Differentiability of coherent moving theta parameters

After the reciprocal covering and local inverse theorem, both the modulus
and elliptic parameter of a coherent linked-Jacobi representation are
differentiable.  The common scale is an explicit nonvanishing quotient,
so it is differentiable as well.

This module isolates that chain-rule step.  It is useful independently of
the later integration of the logarithmic Bloch slope.
-/

namespace HGAS.Modular

open Complex
open UpperHalfPlane hiding I

noncomputable section

/-- The first Jacobi theta coordinate, composed with differentiable real
paths in the elliptic and modular variables, is differentiable. -/
theorem differentiableAt_jacobiThetaVector_zero_comp
    {T : ℝ → ℍ} {ξ : ℝ → ℂ} (t : ℝ)
    (hT :
      DifferentiableAt ℝ
        (fun s : ℝ => (T s : ℂ)) t)
    (hξ : DifferentiableAt ℝ ξ t) :
    DifferentiableAt ℝ
      (fun s : ℝ =>
        jacobiThetaVector (ξ s) (T s : ℂ) 0) t := by
  have houterComplex :
      DifferentiableAt ℂ
        (fun p : ℂ × ℂ =>
          jacobiTheta1 p.1 p.2)
        (ξ t, (T t : ℂ)) :=
    (contDiffAt_one_jacobiTheta1_joint
      (ξ t) (T t : ℂ) (T t).im_pos).differentiableAt_one
  have houterReal :
      DifferentiableAt ℝ
        (fun p : ℂ × ℂ =>
          jacobiTheta1 p.1 p.2)
        (ξ t, (T t : ℂ)) :=
    houterComplex.restrictScalars ℝ
  simpa only [jacobiThetaVector,
    Matrix.cons_val_zero] using
    houterReal.comp t (hξ.prodMk hT)

/-- The first elliptic derivative coordinate, composed with
differentiable real paths in the elliptic and modular variables, is
differentiable.  The nontrivial analytic input is the locally uniform
termwise differentiation theorem in
`JacobiThetaPrimeJointDifferentiability`. -/
theorem differentiableAt_jacobiThetaVectorPrime_zero_comp
    {T : ℝ → ℍ} {ξ : ℝ → ℂ} (t : ℝ)
    (hT :
      DifferentiableAt ℝ
        (fun s : ℝ => (T s : ℂ)) t)
    (hξ : DifferentiableAt ℝ ξ t) :
    DifferentiableAt ℝ
      (fun s : ℝ =>
        jacobiThetaVectorPrime
          (ξ s) (T s : ℂ) 0) t := by
  have houterComplex :
      DifferentiableAt ℂ
        (fun p : ℂ × ℂ =>
          jacobiThetaVectorPrime p.1 p.2 0)
        (ξ t, (T t : ℂ)) :=
    differentiableAt_jacobiThetaVectorPrime_component_joint
      0 (ξ t) (T t : ℂ) (T t).im_pos
  have houterReal :
      DifferentiableAt ℝ
        (fun p : ℂ × ℂ =>
          jacobiThetaVectorPrime p.1 p.2 0)
        (ξ t, (T t : ℂ)) :=
    houterComplex.restrictScalars ℝ
  simpa only [jacobiThetaVectorPrime,
    Matrix.cons_val_zero] using
    houterReal.comp t (hξ.prodMk hT)

/-- The normalized theta derivative in the reconstructed initial-value
map is differentiable along differentiable moving parameters. -/
theorem differentiable_coherentJacobiThetaNormalizedPrime
    {T : ℝ → ℍ} {ξ : ℝ → ℂ}
    (hT :
      Differentiable ℝ
        (fun t : ℝ => (T t : ℂ)))
    (hξ : Differentiable ℝ ξ) :
    Differentiable ℝ
      (coherentJacobiThetaNormalizedPrime T ξ) := by
  intro t
  exact
    (differentiableAt_jacobiThetaVectorPrime_zero_comp
      t (hT t) (hξ t)).div_const Real.pi

/-- The explicitly forced coherent scale is differentiable whenever the
modulus and elliptic lift are differentiable. -/
theorem differentiable_coherentJacobiBlochScale
    {κZ κPhi : ℂ}
    {T : ℝ → ℍ} {z : ℝ → LinkedJacobiState ℂ}
    (hz : IsScaledLinkedJacobiTrajectory κZ κPhi z)
    (d : CoherentJacobiCoefficientTwist T z)
    {ξ : ℝ → ℂ}
    (hξ : IsCoherentJacobiThetaProjectiveLift T z d ξ)
    (hTdiff :
      Differentiable ℝ
        (fun t : ℝ => (T t : ℂ)))
    (hξdiff : Differentiable ℝ ξ) :
    Differentiable ℝ
      (coherentJacobiBlochScale d ξ) := by
  intro t
  have hnumerator :
      DifferentiableAt ℝ
        (fun s : ℝ => d.d₁ * (z s).jacobi.T1) t :=
    (HasDerivAt.const_mul d.d₁
      (hz.jacobi.T1 t)).differentiableAt
  have hdenominator :
      DifferentiableAt ℝ
        (fun s : ℝ =>
          jacobiThetaVector (ξ s) (T s : ℂ) 0) t :=
    differentiableAt_jacobiThetaVector_zero_comp
      t (hTdiff t) (hξdiff t)
  exact
    hnumerator.div hdenominator
      (hξ.thetaOne_ne_zero t)

/-- The explicitly reconstructed Bloch slope is differentiable.  Its
formula contains only the polynomial `Delta` coordinate, the common
scale, the first theta coordinate, and its normalized elliptic
derivative; each of these has already been proved differentiable. -/
theorem differentiable_coherentJacobiBlochSlope
    {κZ κPhi : ℂ}
    {T : ℝ → ℍ} {z : ℝ → LinkedJacobiState ℂ}
    (hz : IsScaledLinkedJacobiTrajectory κZ κPhi z)
    {t₀ : ℝ}
    (hresidual :
      ∀ i : LinkedJacobiResidualIndex,
        linkedJacobiResidual i (z t₀) = 0)
    (d : CoherentJacobiCoefficientTwist T z)
    {ξ : ℝ → ℂ}
    (hξ : IsCoherentJacobiThetaProjectiveLift T z d ξ)
    (hTdiff :
      Differentiable ℝ
        (fun t : ℝ => (T t : ℂ)))
    (hξdiff : Differentiable ℝ ξ) :
    Differentiable ℝ
      (coherentJacobiBlochSlope d ξ) := by
  have hscale :
      Differentiable ℝ
        (coherentJacobiBlochScale d ξ) :=
    differentiable_coherentJacobiBlochScale
      hz d hξ hTdiff hξdiff
  have hprime :
      Differentiable ℝ
        (coherentJacobiThetaNormalizedPrime T ξ) :=
    differentiable_coherentJacobiThetaNormalizedPrime
      hTdiff hξdiff
  have htheta :
      Differentiable ℝ
        (fun t : ℝ =>
          jacobiThetaVector
            (ξ t) (T t : ℂ) 0) :=
    fun t =>
      differentiableAt_jacobiThetaVector_zero_comp
        t (hTdiff t) (hξdiff t)
  have hDelta :
      Differentiable ℝ
        (fun t : ℝ =>
          d.d₁ * (z t).jacobi.Delta) :=
    fun t =>
      (HasDerivAt.const_mul d.d₁
        (hz.jacobi.Delta t)).differentiableAt
  have hresidual_all :=
    linkedJacobiResiduals_eq_zero_along_trajectory
      hz hresidual
  have hscale_ne :
      ∀ t, coherentJacobiBlochScale d ξ t ≠ 0 :=
    fun t =>
      coherentJacobiBlochScale_ne_zero
        d hξ t (hresidual_all t)
  unfold coherentJacobiBlochSlope
    jacobiInitialValueBlochSlope
  exact
    (hDelta.div (hscale.mul htheta)
      (fun t =>
        mul_ne_zero (hscale_ne t)
          (hξ.thetaOne_ne_zero t))).sub
      (hprime.div htheta hξ.thetaOne_ne_zero)

/-- Structured differentiable representations have a differentiable
common scale. -/
theorem
    DifferentiableCoherentMovingJacobiThetaRepresentation.differentiable_scale
    {κZ κPhi : ℂ}
    {T : ℝ → ℍ} {z : ℝ → LinkedJacobiState ℂ}
    (r :
      DifferentiableCoherentMovingJacobiThetaRepresentation T z)
    (hz : IsScaledLinkedJacobiTrajectory κZ κPhi z)
    (hTdiff :
      Differentiable ℝ
        (fun t : ℝ => (T t : ℂ))) :
    Differentiable ℝ
      r.toCoherentRepresentation.scale :=
  differentiable_coherentJacobiBlochScale
    hz
    r.toCoherentRepresentation.twist
    r.toCoherentRepresentation.isProjectiveLift
    hTdiff
    r.parameter_differentiable

/-- Structured differentiable representations also have a
differentiable reconstructed Bloch slope. -/
theorem
    DifferentiableCoherentMovingJacobiThetaRepresentation.differentiable_slope
    {κZ κPhi : ℂ}
    {T : ℝ → ℍ} {z : ℝ → LinkedJacobiState ℂ}
    (r :
      DifferentiableCoherentMovingJacobiThetaRepresentation T z)
    (hz : IsScaledLinkedJacobiTrajectory κZ κPhi z)
    {t₀ : ℝ}
    (hresidual :
      ∀ i : LinkedJacobiResidualIndex,
        linkedJacobiResidual i (z t₀) = 0)
    (hTdiff :
      Differentiable ℝ
        (fun t : ℝ => (T t : ℂ))) :
    Differentiable ℝ
      r.toCoherentRepresentation.slope :=
  differentiable_coherentJacobiBlochSlope
    hz
    hresidual
    r.toCoherentRepresentation.twist
    r.toCoherentRepresentation.isProjectiveLift
    hTdiff
    r.parameter_differentiable

end

end HGAS.Modular
