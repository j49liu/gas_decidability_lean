import HGAS.Modular.JacobiThetaReciprocalLocalRank
import HGAS.Topology.ParameterizedComplexInverse
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Joint local inversion for normalized Jacobi theta coordinates

Mathlib proves that its two-variable theta series has a Fréchet
derivative in the pair `(z, τ)` whenever `im τ > 0`.  For an inverse
function theorem we need the slightly stronger fact that this derivative
is strict.  The first part of this file supplies the missing bridge: the
series of Fréchet derivatives converges locally uniformly, so its sum is
continuous, and the theta series is therefore `C¹`.

The second part transports this fact through the half-period formulas
defining `θ₁, …, θ₄`, and then through the quotient by `θ₁`.  At a point
where one normalized coordinate has nonzero `z`-derivative, the
block-triangular map

```
                    (τ, z) ↦ (τ, θⱼ(z,τ) / θ₁(z,τ))
```

has invertible strict derivative.  Mathlib's inverse-function theorem
then gives an honest local homeomorphism chart.
-/

namespace HGAS.Modular

open Complex Filter Real Set Topology

noncomputable section

/-- The open region in `ℂ × ℂ` on which the second entry is in the
complex upper half-plane. -/
def jacobiThetaJointDomain : Set (ℂ × ℂ) :=
  {p | 0 < im p.2}

theorem isOpen_jacobiThetaJointDomain :
    IsOpen jacobiThetaJointDomain := by
  exact
    (continuous_im.comp continuous_snd).isOpen_preimage
      (Set.Ioi 0) isOpen_Ioi

/-- The Fréchet derivative series of Mathlib's two-variable theta
function is continuous at every point of the upper-half-plane region.

This is the same normal-convergence estimate used in Mathlib's proof of
`hasFDerivAt_jacobiTheta₂`, now applied to the derivative series itself.
-/
theorem continuousAt_jacobiTheta₂_fderiv_joint
    (z τ : ℂ) (hτ : 0 < im τ) :
    ContinuousAt
      (fun p : ℂ × ℂ =>
        jacobiTheta₂_fderiv p.1 p.2)
      (z, τ) := by
  obtain ⟨T, hT, hτ'⟩ := exists_between hτ
  obtain ⟨S, hz⟩ := exists_gt |im z|
  let V : Set (ℂ × ℂ) :=
    {u | |im u| < S} ×ˢ {v | T < im v}
  have hVo : IsOpen V := by
    exact
      ((_root_.continuous_abs.comp continuous_im).isOpen_preimage
          (Set.Iio S) isOpen_Iio).prod
        (continuous_im.isOpen_preimage (Set.Ioi T) isOpen_Ioi)
  refine ContinuousOn.continuousAt ?_
    (hVo.mem_nhds ⟨hz, hτ'⟩)
  let u : ℤ → ℝ :=
    fun n =>
      3 * π * |n| ^ 2 *
        Real.exp (-π * (T * n ^ 2 - 2 * S * |n|))
  have hu : Summable u := by
    simp_rw [u, mul_assoc (3 * π)]
    exact
      (summable_pow_mul_jacobiTheta₂_term_bound
        S hT 2).mul_left (3 * π)
  refine continuousOn_tsum (fun n => ?_) hu
    (fun n p hp => ?_)
  · apply Continuous.continuousOn
    unfold jacobiTheta₂_term_fderiv
    fun_prop
  · exact
      (norm_jacobiTheta₂_term_fderiv_le
        n p.1 p.2).trans (by
          simp_rw [u, mul_assoc (3 * π)]
          refine mul_le_mul_of_nonneg_left ?_
            (mul_pos (by positivity : (0 : ℝ) < 3) pi_pos).le
          refine mul_le_mul_of_nonneg_left ?_
            (pow_nonneg (Int.cast_nonneg (abs_nonneg n)) 2)
          exact
            norm_jacobiTheta₂_term_le hT
              (le_of_lt hp.1) (le_of_lt hp.2) n)

/-- Mathlib's two-variable theta function is `C¹` jointly in `(z,τ)`
at every point with `im τ > 0`. -/
theorem contDiffAt_one_jacobiTheta₂_joint
    (z τ : ℂ) (hτ : 0 < im τ) :
    ContDiffAt ℂ 1
      (fun p : ℂ × ℂ =>
        jacobiTheta₂ p.1 p.2)
      (z, τ) := by
  rw [contDiffAt_one_iff]
  refine
    ⟨fun p : ℂ × ℂ =>
        jacobiTheta₂_fderiv p.1 p.2,
      jacobiThetaJointDomain,
      isOpen_jacobiThetaJointDomain.mem_nhds hτ,
      ?_, ?_⟩
  · intro p hp
    exact
      (continuousAt_jacobiTheta₂_fderiv_joint
        p.1 p.2 hp).continuousWithinAt
  · intro p hp
    exact hasFDerivAt_jacobiTheta₂ p.1 hp

/-- Strict joint differentiability of Mathlib's two-variable theta
function. -/
theorem hasStrictFDerivAt_jacobiTheta₂_joint
    (z τ : ℂ) (hτ : 0 < im τ) :
    HasStrictFDerivAt
      (fun p : ℂ × ℂ =>
        jacobiTheta₂ p.1 p.2)
      (jacobiTheta₂_fderiv z τ)
      (z, τ) := by
  exact
    (contDiffAt_one_jacobiTheta₂_joint z τ hτ).hasStrictFDerivAt'
      (hasFDerivAt_jacobiTheta₂ z hτ) one_ne_zero

/-- Joint `C¹` regularity of `θ₃`. -/
theorem contDiffAt_one_jacobiTheta3_joint
    (z τ : ℂ) (hτ : 0 < im τ) :
    ContDiffAt ℂ 1
      (fun p : ℂ × ℂ =>
        jacobiTheta3 p.1 p.2)
      (z, τ) := by
  simpa only [jacobiTheta3] using
    contDiffAt_one_jacobiTheta₂_joint z τ hτ

/-- Joint `C¹` regularity of `θ₄`. -/
theorem contDiffAt_one_jacobiTheta4_joint
    (z τ : ℂ) (hτ : 0 < im τ) :
    ContDiffAt ℂ 1
      (fun p : ℂ × ℂ =>
        jacobiTheta4 p.1 p.2)
      (z, τ) := by
  have haffine :
      ContDiffAt ℂ 1
        (fun p : ℂ × ℂ =>
          (p.1 + 1 / 2, p.2))
        (z, τ) := by
    fun_prop
  simpa only [jacobiTheta4, Function.comp_apply] using
    (contDiffAt_one_jacobiTheta₂_joint
      (z + 1 / 2) τ hτ).comp
        (z, τ) haffine

/-- Joint `C¹` regularity of `θ₂`. -/
theorem contDiffAt_one_jacobiTheta2_joint
    (z τ : ℂ) (hτ : 0 < im τ) :
    ContDiffAt ℂ 1
      (fun p : ℂ × ℂ =>
        jacobiTheta2 p.1 p.2)
      (z, τ) := by
  have haffine :
      ContDiffAt ℂ 1
        (fun p : ℂ × ℂ =>
          (p.1 + p.2 / 2, p.2))
        (z, τ) := by
    fun_prop
  have htheta :
      ContDiffAt ℂ 1
        (fun p : ℂ × ℂ =>
          jacobiTheta₂
            (p.1 + p.2 / 2) p.2)
        (z, τ) := by
    simpa only [Function.comp_apply] using
      (contDiffAt_one_jacobiTheta₂_joint
        (z + τ / 2) τ hτ).comp
          (z, τ) haffine
  have hexponential :
      ContDiffAt ℂ 1
        (fun p : ℂ × ℂ =>
          cexp (π * I * (p.2 / 4 + p.1)))
        (z, τ) := by
    fun_prop
  simpa only [jacobiTheta2] using
    hexponential.mul htheta

/-- Joint `C¹` regularity of `θ₁`. -/
theorem contDiffAt_one_jacobiTheta1_joint
    (z τ : ℂ) (hτ : 0 < im τ) :
    ContDiffAt ℂ 1
      (fun p : ℂ × ℂ =>
        jacobiTheta1 p.1 p.2)
      (z, τ) := by
  have haffine :
      ContDiffAt ℂ 1
        (fun p : ℂ × ℂ =>
          (p.1 + 1 / 2, p.2))
        (z, τ) := by
    fun_prop
  have hshift :
      ContDiffAt ℂ 1
        (fun p : ℂ × ℂ =>
          jacobiTheta2 (p.1 + 1 / 2) p.2)
        (z, τ) := by
    simpa only [Function.comp_apply] using
      (contDiffAt_one_jacobiTheta2_joint
        (z + 1 / 2) τ hτ).comp
          (z, τ) haffine
  simpa only [jacobiTheta1] using hshift.neg

/-- Every component of the four-coordinate theta vector is jointly
`C¹` in `(z,τ)` on `im τ > 0`. -/
theorem contDiffAt_one_jacobiThetaVector_component_joint
    (j : Fin 4) (z τ : ℂ) (hτ : 0 < im τ) :
    ContDiffAt ℂ 1
      (fun p : ℂ × ℂ =>
        jacobiThetaVector p.1 p.2 j)
      (z, τ) := by
  fin_cases j
  · simpa only [jacobiThetaVector,
      Matrix.cons_val_zero] using
      contDiffAt_one_jacobiTheta1_joint z τ hτ
  · simpa only [jacobiThetaVector,
      Matrix.cons_val_one, Matrix.cons_val_zero] using
      contDiffAt_one_jacobiTheta2_joint z τ hτ
  · simpa only [jacobiThetaVector,
      Matrix.cons_val_one, Matrix.cons_val_zero] using
      contDiffAt_one_jacobiTheta3_joint z τ hτ
  · simpa only [jacobiThetaVector,
      Matrix.cons_val_one, Matrix.cons_val_zero] using
      contDiffAt_one_jacobiTheta4_joint z τ hτ

/-- Ambient extension of one normalized theta coordinate.  The argument
order is `(τ,z)`, matching the block-triangular map used below. -/
def jacobiThetaReciprocalCoordinateAmbient
    (k : Fin 3) (p : ℂ × ℂ) : ℂ :=
  jacobiThetaVector p.2 p.1 k.succ /
    jacobiThetaVector p.2 p.1 0

@[simp]
theorem jacobiThetaReciprocalCoordinateAmbient_upperHalfPlane
    (k : Fin 3) (τ : UpperHalfPlane) (z : ℂ) :
    jacobiThetaReciprocalCoordinateAmbient k ((τ : ℂ), z) =
      jacobiThetaReciprocalCoordinates τ z k :=
  rfl

/-- A normalized theta coordinate is jointly `C¹` wherever `θ₁`
does not vanish. -/
theorem contDiffAt_one_jacobiThetaReciprocalCoordinateAmbient
    (k : Fin 3) (τ z : ℂ)
    (hτ : 0 < im τ)
    (h1 : jacobiTheta1 z τ ≠ 0) :
    ContDiffAt ℂ 1
      (jacobiThetaReciprocalCoordinateAmbient k)
      (τ, z) := by
  have hswap :
      ContDiffAt ℂ 1
        (fun p : ℂ × ℂ => (p.2, p.1))
        (τ, z) := by
    fun_prop
  have hnum :
      ContDiffAt ℂ 1
        (fun p : ℂ × ℂ =>
          jacobiThetaVector p.2 p.1 k.succ)
        (τ, z) := by
    simpa only [Function.comp_apply] using
      (contDiffAt_one_jacobiThetaVector_component_joint
        k.succ z τ hτ).comp (τ, z) hswap
  have hden :
      ContDiffAt ℂ 1
        (fun p : ℂ × ℂ =>
          jacobiThetaVector p.2 p.1 0)
        (τ, z) := by
    simpa only [Function.comp_apply] using
      (contDiffAt_one_jacobiThetaVector_component_joint
        0 z τ hτ).comp (τ, z) hswap
  exact hnum.div hden h1

/-- A selected normalized theta coordinate with nonzero vertical
derivative supplies a local homeomorphism in the joint variables.

The derivative of the displayed map is block triangular.  Its
lower-right entry is identified with `d` by restricting the joint
Fréchet derivative to the vertical complex line and invoking uniqueness
of the one-variable derivative.
-/
theorem exists_jacobiThetaReciprocalCoordinateAmbient_localHomeomorph
    (k : Fin 3) (τ : UpperHalfPlane) (z d : ℂ)
    (h1 : jacobiTheta1 z (τ : ℂ) ≠ 0)
    (hd : d ≠ 0)
    (hderiv :
      HasDerivAt
        (fun w =>
          jacobiThetaReciprocalCoordinates τ w k)
        d z) :
    ∃ e : OpenPartialHomeomorph (ℂ × ℂ) (ℂ × ℂ),
      ((τ : ℂ), z) ∈ e.source ∧
        (e : (ℂ × ℂ) → (ℂ × ℂ)) =
          fun q =>
            (q.1,
              jacobiThetaReciprocalCoordinateAmbient k q) := by
  let r : ℂ × ℂ → ℂ :=
    jacobiThetaReciprocalCoordinateAmbient k
  let p : ℂ × ℂ := ((τ : ℂ), z)
  let D : (ℂ × ℂ) →L[ℂ] ℂ :=
    fderiv ℂ r p
  have hrC1 :
      ContDiffAt ℂ 1 r p := by
    simpa only [r, p] using
      contDiffAt_one_jacobiThetaReciprocalCoordinateAmbient
        k (τ : ℂ) z τ.im_pos h1
  have hrD :
      HasFDerivAt r D p := by
    exact hrC1.differentiableAt_one.hasFDerivAt
  have hrStrict :
      HasStrictFDerivAt r D p := by
    exact hrC1.hasStrictFDerivAt' hrD one_ne_zero
  have hvertical :
      HasDerivAt
        (fun w => r ((τ : ℂ), w))
        (D (0, 1)) z := by
    simpa only [p, Prod.fst_zero, Prod.snd_zero,
      Prod.fst_one, Prod.snd_one,
      ContinuousLinearMap.inr_apply,
      ContinuousLinearMap.one_apply] using
      (hrD.comp z
        (hasFDerivAt_prodMk_right (τ : ℂ) z)).hasDerivAt
  have hderiv' :
      HasDerivAt
        (fun w => r ((τ : ℂ), w))
        d z := by
    simpa only [r,
      jacobiThetaReciprocalCoordinateAmbient_upperHalfPlane] using
      hderiv
  have hDvalue :
      D (0, 1) = d :=
    hvertical.unique hderiv'
  have hD :
      D (0, 1) ≠ 0 := by
    rw [hDvalue]
    exact hd
  let L : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
    HGAS.Topology.parameterizedComplexCoordinateDerivative D
  have hjoint :
      HasStrictFDerivAt
        (fun q : ℂ × ℂ => (q.1, r q))
        L p := by
    exact hasStrictFDerivAt_fst.prodMk hrStrict
  let E : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) :=
    HGAS.Topology.parameterizedComplexCoordinateDerivativeEquiv
      D hD
  have hjointE :
      HasStrictFDerivAt
        (fun q : ℂ × ℂ => (q.1, r q))
        (E : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) p := by
    simpa only [E, L,
      ContinuousLinearEquiv.coe_ofBijective] using hjoint
  let e : OpenPartialHomeomorph (ℂ × ℂ) (ℂ × ℂ) :=
    hjointE.toOpenPartialHomeomorph
      (fun q : ℂ × ℂ => (q.1, r q))
  exact
    ⟨e, hjointE.mem_toOpenPartialHomeomorph_source,
      by
        simpa only [e, r] using
          hjointE.toOpenPartialHomeomorph_coe⟩

/-- At every reciprocal-chart point, at least one normalized coordinate
extends to a joint local homeomorphism `(τ,z) ↦ (τ,rₖ(τ,z))`. -/
theorem exists_jacobiThetaReciprocalCoordinateAmbient_localHomeomorph_of_thetaOne_ne_zero
    (τ : UpperHalfPlane) (z : ℂ)
    (h1 : jacobiTheta1 z (τ : ℂ) ≠ 0) :
    ∃ (k : Fin 3)
        (e : OpenPartialHomeomorph (ℂ × ℂ) (ℂ × ℂ)),
      ((τ : ℂ), z) ∈ e.source ∧
        (e : (ℂ × ℂ) → (ℂ × ℂ)) =
          fun q =>
            (q.1,
              jacobiThetaReciprocalCoordinateAmbient k q) := by
  obtain ⟨k, d, hd, hderiv⟩ :=
    exists_jacobiThetaReciprocalCoordinate_hasDerivAt_ne_zero
      τ z h1
  obtain ⟨e, hp, he⟩ :=
    exists_jacobiThetaReciprocalCoordinateAmbient_localHomeomorph
      k τ z d h1 hd hderiv
  exact ⟨k, e, hp, he⟩

end

end HGAS.Modular
