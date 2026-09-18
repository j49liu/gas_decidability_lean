import HGAS.Modular.LinkedJacobiCoherentCoefficientTwist
import HGAS.Modular.JacobiThetaPrimeContinuity

/-!
# Continuous Bloch parameters from a projective theta lift

The finite coefficient branches are globally constant by
`LinkedJacobiCoherentCoefficientTwist`.  The next issue is to choose the
elliptic theta parameter coherently.

This file isolates that issue exactly.  Assume a continuous function
`ξ(t)` has been chosen whose projective theta vector represents the
twisted linked Jacobi coordinates.  Then no further choice is needed:

* the common scale `S(t)` is the quotient of the first twisted coordinate
  by `θ₁(ξ(t)|T(t))`;
* the Bloch slope `L(t)` is the explicit initial-value quotient from
  `JacobiThetaInitialValueMap`.

Both functions are continuous, and at every time they form an exact
`TwistedJacobiBlochSeed` with the already fixed coefficient twists.

Thus the only remaining *topological* selection problem is existence of
the continuous projective lift `ξ`.  This module does not assume or claim
the separate moving-modulus theta ODE identity needed to turn these
initial data into one simultaneous Bloch solution.
-/

namespace HGAS.Modular

open HGAS
open Complex
open Real
open UpperHalfPlane hiding I

noncomputable section

/-- A continuous lift of the twisted projective Jacobi coordinates
through the four-theta parametrization.

The cross-multiplied equality avoids choosing a scale.  Nonvanishing of
the first theta coordinate selects the same reciprocal chart as the
polynomial state. -/
structure IsCoherentJacobiThetaProjectiveLift
    (T : ℝ → ℍ) (z : ℝ → LinkedJacobiState ℂ)
    (d : CoherentJacobiCoefficientTwist T z)
    (ξ : ℝ → ℂ) : Prop where
  continuous : Continuous ξ
  thetaOne_ne_zero :
    ∀ t,
      jacobiThetaVector (ξ t) (T t : ℂ) 0 ≠ 0
  projective :
    ∀ t k,
      jacobiThetaVector (ξ t) (T t : ℂ) 0 *
          jacobiCoefficientTwist d.d₁ d.d₂
            (jacobiResidualProjectiveCoordinates
              (z t).jacobi) k =
        jacobiCoefficientTwist d.d₁ d.d₂
              (jacobiResidualProjectiveCoordinates
                (z t).jacobi) 0 *
            jacobiThetaVector (ξ t) (T t : ℂ) k

/-- The common scale forced by the first projective coordinate. -/
def coherentJacobiBlochScale
    {T : ℝ → ℍ} {z : ℝ → LinkedJacobiState ℂ}
    (d : CoherentJacobiCoefficientTwist T z)
    (ξ : ℝ → ℂ) (t : ℝ) : ℂ :=
  (d.d₁ * (z t).jacobi.T1) /
    jacobiThetaVector (ξ t) (T t : ℂ) 0

/-- The normalized theta derivative along a lifted parameter. -/
def coherentJacobiThetaNormalizedPrime
    (T : ℝ → ℍ) (ξ : ℝ → ℂ) (t : ℝ) : ℂ :=
  jacobiThetaVectorPrime (ξ t) (T t : ℂ) 0 / π

/-- The Bloch slope forced by the twisted `Delta` coordinate. -/
def coherentJacobiBlochSlope
    {T : ℝ → ℍ} {z : ℝ → LinkedJacobiState ℂ}
    (d : CoherentJacobiCoefficientTwist T z)
    (ξ : ℝ → ℂ) (t : ℝ) : ℂ :=
  jacobiInitialValueBlochSlope
    (coherentJacobiBlochScale d ξ t)
    (coherentJacobiThetaNormalizedPrime T ξ t)
    (jacobiThetaVector (ξ t) (T t : ℂ) 0)
    (d.d₁ * (z t).jacobi.Delta)

/-- The reciprocal residual `U*T₁=1` forces `T₁` to be nonzero. -/
theorem linkedJacobi_T1_ne_zero_of_residual
    (z : LinkedJacobiState ℂ)
    (hresidual :
      ∀ i : LinkedJacobiResidualIndex,
        linkedJacobiResidual i z = 0) :
    z.jacobi.T1 ≠ 0 := by
  intro hzero
  have h :=
    hresidual .reciprocalChart
  change z.jacobi.U * z.jacobi.T1 - 1 = 0 at h
  rw [hzero, mul_zero] at h
  norm_num at h

theorem continuous_coherentJacobiBlochScale
    {κZ κPhi : ℂ}
    {T : ℝ → ℍ} {z : ℝ → LinkedJacobiState ℂ}
    (hz : IsScaledLinkedJacobiTrajectory κZ κPhi z)
    (hT : Continuous T)
    (d : CoherentJacobiCoefficientTwist T z)
    {ξ : ℝ → ℂ}
    (hξ : IsCoherentJacobiThetaProjectiveLift T z d ξ) :
    Continuous (coherentJacobiBlochScale d ξ) := by
  have htheta :
      Continuous
        (fun t ↦
          jacobiThetaVector (ξ t) (T t : ℂ) 0) := by
    have hpair :
        Continuous (fun t ↦ (ξ t, T t)) :=
      hξ.continuous.prodMk hT
    simpa only [jacobiThetaVector,
      Matrix.cons_val_zero] using
      continuous_jacobiTheta1_upperHalfPlane.comp
        hpair
  exact
    (continuous_const.mul hz.jacobi.continuous_T1).div
      htheta hξ.thetaOne_ne_zero

theorem continuous_coherentJacobiThetaNormalizedPrime
    {T : ℝ → ℍ} {ξ : ℝ → ℂ}
    (hT : Continuous T) (hξ : Continuous ξ) :
    Continuous
      (coherentJacobiThetaNormalizedPrime T ξ) := by
  have hprime :
      Continuous
        (fun t ↦
          jacobiThetaVectorPrime
            (ξ t) (T t : ℂ) 0) := by
    have hpair :
        Continuous (fun t ↦ (ξ t, T t)) :=
      hξ.prodMk hT
    simpa only [jacobiThetaVectorPrime,
      Matrix.cons_val_zero] using
      continuous_jacobiTheta1Prime_upperHalfPlane.comp
        hpair
  exact hprime.div_const π

theorem continuous_coherentJacobiBlochSlope
    {κZ κPhi : ℂ}
    {T : ℝ → ℍ} {z : ℝ → LinkedJacobiState ℂ}
    (hz : IsScaledLinkedJacobiTrajectory κZ κPhi z)
    {t₀ : ℝ}
    (hresidual :
      ∀ i : LinkedJacobiResidualIndex,
        linkedJacobiResidual i (z t₀) = 0)
    (hT : Continuous T)
    (d : CoherentJacobiCoefficientTwist T z)
    {ξ : ℝ → ℂ}
    (hξ : IsCoherentJacobiThetaProjectiveLift T z d ξ) :
    Continuous (coherentJacobiBlochSlope d ξ) := by
  have hscale :=
    continuous_coherentJacobiBlochScale
      hz hT d hξ
  have hprime :=
    continuous_coherentJacobiThetaNormalizedPrime
      hT hξ.continuous
  have htheta :
      Continuous
        (fun t ↦
          jacobiThetaVector (ξ t) (T t : ℂ) 0) := by
    have hpair :
        Continuous (fun t ↦ (ξ t, T t)) :=
      hξ.continuous.prodMk hT
    simpa only [jacobiThetaVector,
      Matrix.cons_val_zero] using
      continuous_jacobiTheta1_upperHalfPlane.comp
        hpair
  have hDelta :
      Continuous
        (fun t ↦ d.d₁ * (z t).jacobi.Delta) :=
    continuous_const.mul hz.jacobi.continuous_Delta
  have hresidual_all :=
    linkedJacobiResiduals_eq_zero_along_trajectory
      hz hresidual
  have hscale_ne :
      ∀ t, coherentJacobiBlochScale d ξ t ≠ 0 :=
    fun t ↦ div_ne_zero
      (mul_ne_zero d.d₁_ne_zero
        (linkedJacobi_T1_ne_zero_of_residual
          (z t) (hresidual_all t)))
      (hξ.thetaOne_ne_zero t)
  unfold coherentJacobiBlochSlope
    jacobiInitialValueBlochSlope
  exact
    (hDelta.div (hscale.mul htheta)
      (fun t ↦ mul_ne_zero (hscale_ne t)
        (hξ.thetaOne_ne_zero t))).sub
      (hprime.div htheta hξ.thetaOne_ne_zero)

/-- The explicit scale recovers all four twisted coordinates from a
projective theta lift. -/
theorem coherentJacobiBlochScale_smul_theta
    {T : ℝ → ℍ} {z : ℝ → LinkedJacobiState ℂ}
    (d : CoherentJacobiCoefficientTwist T z)
    {ξ : ℝ → ℂ}
    (hξ : IsCoherentJacobiThetaProjectiveLift T z d ξ)
    (t : ℝ) :
    coherentJacobiBlochScale d ξ t •
        jacobiThetaVector (ξ t) (T t : ℂ) =
      jacobiCoefficientTwist d.d₁ d.d₂
        (jacobiResidualProjectiveCoordinates
          (z t).jacobi) := by
  funext k
  simp only [Pi.smul_apply, smul_eq_mul,
    coherentJacobiBlochScale]
  field_simp [hξ.thetaOne_ne_zero t]
  have hp := hξ.projective t k
  simpa only [jacobiCoefficientTwist_zero,
    jacobiResidualProjectiveCoordinates,
    Matrix.cons_val_zero] using hp.symm

/-- The reconstructed common scale never vanishes on the reciprocal
chart. -/
theorem coherentJacobiBlochScale_ne_zero
    {T : ℝ → ℍ} {z : ℝ → LinkedJacobiState ℂ}
    (d : CoherentJacobiCoefficientTwist T z)
    {ξ : ℝ → ℂ}
    (hξ : IsCoherentJacobiThetaProjectiveLift T z d ξ)
    (t : ℝ)
    (hresidual :
      ∀ i : LinkedJacobiResidualIndex,
        linkedJacobiResidual i (z t) = 0) :
    coherentJacobiBlochScale d ξ t ≠ 0 := by
  exact div_ne_zero
    (mul_ne_zero d.d₁_ne_zero
      (linkedJacobi_T1_ne_zero_of_residual
        (z t) hresidual))
    (hξ.thetaOne_ne_zero t)

/-- The reconstructed slope has exactly the prescribed twisted first
derivative. -/
theorem coherentJacobiBlochSlope_initialValue
    {T : ℝ → ℍ} {z : ℝ → LinkedJacobiState ℂ}
    (d : CoherentJacobiCoefficientTwist T z)
    {ξ : ℝ → ℂ}
    (hξ : IsCoherentJacobiThetaProjectiveLift T z d ξ)
    (t : ℝ)
    (hresidual :
      ∀ i : LinkedJacobiResidualIndex,
        linkedJacobiResidual i (z t) = 0) :
    coherentJacobiBlochScale d ξ t *
        (coherentJacobiThetaNormalizedPrime T ξ t +
          coherentJacobiBlochSlope d ξ t *
            jacobiThetaVector (ξ t) (T t : ℂ) 0) =
      d.d₁ * (z t).jacobi.Delta := by
  have hmap :=
    jacobiInitialValueMap_at_blochSlope
      (fun η ↦ jacobiThetaVector η (T t : ℂ))
      (fun η ↦
        jacobiThetaVectorPrime η (T t : ℂ) 0 / π)
      (coherentJacobiBlochScale d ξ t)
      (ξ t) (d.d₁ * (z t).jacobi.Delta)
      (coherentJacobiBlochScale_ne_zero
        d hξ t hresidual)
      (hξ.thetaOne_ne_zero t)
  have hlast := congrArg Prod.snd hmap
  simpa only [jacobiInitialValueMap,
    coherentJacobiBlochSlope,
    coherentJacobiThetaNormalizedPrime] using hlast

/-- At each time, the coherent projective lift and explicit continuous
parameters produce an exact pointwise twisted Bloch seed with the fixed
coefficient branches. -/
def coherentTwistedJacobiBlochSeed
    {T : ℝ → ℍ} {z : ℝ → LinkedJacobiState ℂ}
    (d : CoherentJacobiCoefficientTwist T z)
    {ξ : ℝ → ℂ}
    (hξ : IsCoherentJacobiThetaProjectiveLift T z d ξ)
    (w : ℝ → ℂ) (t : ℝ)
    (hresidual :
      ∀ i : LinkedJacobiResidualIndex,
        linkedJacobiResidual i (z t) = 0) :
    TwistedJacobiBlochSeed (T t) (z t) (w t) where
  d₁ := d.d₁
  d₂ := d.d₂
  S := coherentJacobiBlochScale d ξ t
  ξ := ξ t
  L := coherentJacobiBlochSlope d ξ t
  d₁_ne_zero := d.d₁_ne_zero
  d₂_ne_zero := d.d₂_ne_zero
  d₁_fourth := d.d₁_fourth
  d₂_fourth := d.d₂_fourth
  coefficientThree := d.coefficientThree t
  coefficientFour := d.coefficientFour t
  S_ne_zero :=
    coherentJacobiBlochScale_ne_zero
      d hξ t hresidual
  value := by
    rw [jacobiBlochThetaVector_selected]
    exact coherentJacobiBlochScale_smul_theta
      d hξ t
  firstDerivative := by
    rw [
      jacobiBlochThetaVectorPrime_selected_zero_div_pi]
    exact coherentJacobiBlochSlope_initialValue
      d hξ t hresidual

/-- Conditional completion of the continuous-parameter selection step.

Once a continuous projective theta lift exists, this theorem returns
continuous functions `S, ξ, L` and exact seeds whose fields are literally
those functions and the already fixed fourth-root branches. -/
theorem exists_continuous_twistedBlochSeed_parameters_of_projectiveLift
    {κZ κPhi : ℂ}
    {T : ℝ → ℍ} {z : ℝ → LinkedJacobiState ℂ}
    (hz : IsScaledLinkedJacobiTrajectory κZ κPhi z)
    {t₀ : ℝ}
    (hresidual :
      ∀ i : LinkedJacobiResidualIndex,
        linkedJacobiResidual i (z t₀) = 0)
    (hT : Continuous T)
    (d : CoherentJacobiCoefficientTwist T z)
    {ξ : ℝ → ℂ}
    (hξ : IsCoherentJacobiThetaProjectiveLift T z d ξ)
    (w : ℝ → ℂ) :
    ∃ S L : ℝ → ℂ,
      Continuous S ∧ Continuous ξ ∧ Continuous L ∧
      ∀ t,
        ∃ seed :
            TwistedJacobiBlochSeed (T t) (z t) (w t),
          seed.d₁ = d.d₁ ∧
          seed.d₂ = d.d₂ ∧
          seed.S = S t ∧
          seed.ξ = ξ t ∧
          seed.L = L t := by
  let S := coherentJacobiBlochScale d ξ
  let L := coherentJacobiBlochSlope d ξ
  have hresidual_all :=
    linkedJacobiResiduals_eq_zero_along_trajectory
      hz hresidual
  refine
    ⟨S, L,
      continuous_coherentJacobiBlochScale hz hT d hξ,
      hξ.continuous,
      continuous_coherentJacobiBlochSlope
        hz hresidual hT d hξ,
      ?_⟩
  intro t
  let seed :=
    coherentTwistedJacobiBlochSeed
      d hξ w t (hresidual_all t)
  exact ⟨seed, rfl, rfl, rfl, rfl, rfl⟩

end

end HGAS.Modular
