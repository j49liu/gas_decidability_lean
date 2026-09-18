import HGAS.Modular.JacobiThetaReciprocalRegularCoordinate
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Differentiability of reciprocal-theta path lifts

A covering-space lift is initially supplied only as a continuous path.
For the reciprocal theta covering this regularity improves
automatically.  The reason is local and reusable:

* at every reciprocal point, one normalized theta coordinate has a
  nonzero elliptic derivative;
* the joint map `(τ,z) ↦ (τ, θⱼ/θ₁)` is `C¹`;
* its derivative is block triangular and invertible;
* hence its local inverse is `C¹`.

Therefore a continuous lift of a differentiable reciprocal path is
differentiable.  The theorem below is stated directly for an arbitrary
lift; it is independent of how that lift was constructed globally.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I
open Complex Filter Real Set Topology
open scoped Topology

noncomputable section

/-- Ambient `(τ,z)` path underlying a reciprocal-theta lift. -/
def jacobiThetaReciprocalLiftAmbientPath
    (p : C(ℝ, JacobiThetaReciprocalDomain)) :
    ℝ → ℂ × ℂ :=
  fun t => ((p t).modulus, (p t).parameter)

theorem continuous_jacobiThetaReciprocalLiftAmbientPath
    (p : C(ℝ, JacobiThetaReciprocalDomain)) :
    Continuous (jacobiThetaReciprocalLiftAmbientPath p) := by
  have hbase :=
    continuous_jacobiThetaReciprocalDomain_toBase.comp
      p.continuous
  have hmodulus :
      Continuous (fun t : ℝ => (p t).modulus) := by
    simpa only [Function.comp_apply,
      JacobiThetaReciprocalDomain.toBase] using
      continuous_fst.comp hbase
  have hparameter :
      Continuous (fun t : ℝ => (p t).parameter) := by
    simpa only [Function.comp_apply,
      JacobiThetaReciprocalDomain.toBase] using
      continuous_snd.comp hbase
  exact
    (UpperHalfPlane.continuous_coe.comp hmodulus).prodMk
      hparameter

/-- **A continuous reciprocal-theta lift of a differentiable selected
coordinate path is differentiable.**

It is enough to know differentiability of the modulus and of all three
normalized theta coordinates.  At the point under consideration, the
inverse-function theorem selects the one coordinate whose elliptic
derivative is nonzero. -/
theorem
    differentiableAt_jacobiThetaReciprocalLiftAmbientPath
    (p : C(ℝ, JacobiThetaReciprocalDomain))
    (t : ℝ)
    (hmodulus :
      DifferentiableAt ℝ
        (fun s : ℝ => ((p s).modulus : ℂ)) t)
    (hcoordinates :
      ∀ k : Fin 3,
        DifferentiableAt ℝ
          (fun s : ℝ =>
            jacobiThetaReciprocalCoordinates
              (p s).modulus (p s).parameter k) t) :
    DifferentiableAt ℝ
      (jacobiThetaReciprocalLiftAmbientPath p) t := by
  let p₀ : ℂ × ℂ :=
    jacobiThetaReciprocalLiftAmbientPath p t
  obtain ⟨k, d, _hcomplement, hd, hderiv⟩ :=
    exists_jacobiThetaReciprocalRegularCoordinate_hasDerivAt
      (p t).modulus (p t).parameter
        (p t).thetaOne_ne_zero
  let r : ℂ × ℂ → ℂ :=
    jacobiThetaReciprocalCoordinateAmbient k
  let F : ℂ × ℂ → ℂ × ℂ :=
    fun q => (q.1, r q)
  let D : (ℂ × ℂ) →L[ℂ] ℂ :=
    fderiv ℂ r p₀
  have hrC1 :
      ContDiffAt ℂ 1 r p₀ := by
    simpa only [r, p₀,
      jacobiThetaReciprocalLiftAmbientPath] using
      contDiffAt_one_jacobiThetaReciprocalCoordinateAmbient
        k ((p t).modulus : ℂ) (p t).parameter
          (p t).modulus.im_pos (p t).thetaOne_ne_zero
  have hrD :
      HasFDerivAt r D p₀ :=
    hrC1.differentiableAt_one.hasFDerivAt
  have hvertical :
      HasDerivAt
        (fun w => r (((p t).modulus : ℂ), w))
        (D (0, 1)) (p t).parameter := by
    simpa only [p₀,
      jacobiThetaReciprocalLiftAmbientPath,
      Prod.fst_zero, Prod.snd_zero,
      Prod.fst_one, Prod.snd_one,
      ContinuousLinearMap.inr_apply,
      ContinuousLinearMap.one_apply] using
      (hrD.comp (p t).parameter
        (hasFDerivAt_prodMk_right
          ((p t).modulus : ℂ) (p t).parameter)).hasDerivAt
  have hderiv' :
      HasDerivAt
        (fun w => r (((p t).modulus : ℂ), w))
        d (p t).parameter := by
    simpa only [r,
      jacobiThetaReciprocalCoordinateAmbient_upperHalfPlane] using
      hderiv
  have hDvalue : D (0, 1) = d :=
    hvertical.unique hderiv'
  have hD : D (0, 1) ≠ 0 := by
    rw [hDvalue]
    exact hd
  let E : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) :=
    HGAS.Topology.parameterizedComplexCoordinateDerivativeEquiv
      D hD
  have hFC1 :
      ContDiffAt ℂ 1 F p₀ := by
    exact contDiffAt_fst.prodMk hrC1
  have hFderiv :
      HasFDerivAt F
        (E : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) p₀ := by
    have hraw :
        HasFDerivAt F
          (HGAS.Topology.parameterizedComplexCoordinateDerivative D)
          p₀ :=
      HasFDerivAt.prodMk hasFDerivAt_fst hrD
    simpa only [E,
      HGAS.Topology.parameterizedComplexCoordinateDerivativeEquiv_apply,
      HGAS.Topology.parameterizedComplexCoordinateDerivative_apply] using
      hraw
  have hstrict :
      HasStrictFDerivAt F
        (E : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) p₀ :=
    hFC1.hasStrictFDerivAt' hFderiv one_ne_zero
  let g : ℂ × ℂ → ℂ × ℂ :=
    hstrict.localInverse F E p₀
  have hgComplex :
      DifferentiableAt ℂ g (F p₀) :=
    hstrict.to_localInverse.differentiableAt
  have hgReal :
      DifferentiableAt ℝ g (F p₀) :=
    hgComplex.restrictScalars ℝ
  have hcurve :
      DifferentiableAt ℝ
        (fun s : ℝ =>
          F (jacobiThetaReciprocalLiftAmbientPath p s)) t := by
    simpa only [F, r,
      jacobiThetaReciprocalLiftAmbientPath,
      jacobiThetaReciprocalCoordinateAmbient_upperHalfPlane] using
      hmodulus.prodMk (hcoordinates k)
  have hcomposite :
      DifferentiableAt ℝ
        (fun s : ℝ =>
          g (F
            (jacobiThetaReciprocalLiftAmbientPath p s))) t :=
    hgReal.comp t hcurve
  have hpTendsto :
      Tendsto
        (jacobiThetaReciprocalLiftAmbientPath p)
        (nhds t) (nhds p₀) := by
    simpa only [p₀] using
      (continuous_jacobiThetaReciprocalLiftAmbientPath p).continuousAt
  have hleft :
      ∀ᶠ s in nhds t,
        g (F
              (jacobiThetaReciprocalLiftAmbientPath p s)) =
          jacobiThetaReciprocalLiftAmbientPath p s :=
    hpTendsto hstrict.eventually_left_inverse
  exact
    hcomposite.congr_of_eventuallyEq
      (hleft.mono fun _ hs => hs.symm)

/-- In particular, the elliptic parameter of the lift is differentiable
at the given time. -/
theorem differentiableAt_jacobiThetaReciprocalLift_parameter
    (p : C(ℝ, JacobiThetaReciprocalDomain))
    (t : ℝ)
    (hmodulus :
      DifferentiableAt ℝ
        (fun s : ℝ => ((p s).modulus : ℂ)) t)
    (hcoordinates :
      ∀ k : Fin 3,
        DifferentiableAt ℝ
          (fun s : ℝ =>
            jacobiThetaReciprocalCoordinates
              (p s).modulus (p s).parameter k) t) :
    DifferentiableAt ℝ
      (fun s : ℝ => (p s).parameter) t := by
  have hp :=
    differentiableAt_jacobiThetaReciprocalLiftAmbientPath
      p t hmodulus hcoordinates
  have hsnd :
      DifferentiableAt ℝ
        (fun q : ℂ × ℂ => q.2)
        (jacobiThetaReciprocalLiftAmbientPath p t) :=
    differentiableAt_snd
  simpa only [jacobiThetaReciprocalLiftAmbientPath] using
    hsnd.comp t hp

end

end HGAS.Modular
