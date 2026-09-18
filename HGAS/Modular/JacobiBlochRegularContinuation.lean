import HGAS.Modular.JacobiBlochSimultaneousPointwise
import HGAS.Modular.JacobiThetaPrimeContinuity
import HGAS.Modular.JacobiTrajectoryUniqueness
import Mathlib.Topology.Connected.Clopen

/-!
# Continuation of the reciprocal Jacobi--Bloch formula

The explicit theta formula contains the reciprocal `θ₁⁻¹`, so its ODE
identity is initially valid only while `θ₁ ≠ 0`.  It would be circular to
assume this for all time.

This module supplies the missing continuation argument.  We compare only
the first nine Jacobi coordinates, which contain no reciprocal and remain
continuous even at a zero of `θ₁`.  Their agreement set with a complete
polynomial trajectory is:

* closed, by continuity;
* open, by local `C¹` ODE uniqueness on the reciprocal chart; and
* nonempty, by the prescribed initial data.

The real line is connected, so the agreement set is all of `ℝ`.
The actual trajectory satisfies `U T₁ = 1`, hence `T₁` never vanishes.
Since the Bloch scale never vanishes either, agreement of the `T₁`
coordinate forces `θ₁ ≠ 0` at every time.  The reciprocal coordinates
then agree as well.

This is the precise replacement for the informal phrase “continue the
theta formula by ODE uniqueness.”
-/

namespace HGAS.Modular

open Complex Real
open Filter Set Topology
open UpperHalfPlane hiding I
open scoped Topology

noncomputable section

/-- The nine Jacobi coordinates which remain regular before the
reciprocal coordinate `U` is introduced. -/
abbrev JacobiCoreDimension : ℕ := 9

/-- Projection of a Jacobi state to its reciprocal-free core. -/
def jacobiCorePoint
    (z : JacobiState ℂ) :
    Fin JacobiCoreDimension → ℂ :=
  ![z.p2, z.p3, z.p4, z.H, z.T1, z.T2, z.T3, z.T4, z.Delta]

/-- Equality of the core together with the reciprocal equations recovers
equality of the complete Jacobi state. -/
theorem JacobiState.eq_of_core_eq_of_reciprocal
    {z w : JacobiState ℂ}
    (hcore : jacobiCorePoint z = jacobiCorePoint w)
    (hz : z.U * z.T1 = 1)
    (hw : w.U * w.T1 = 1) :
    z = w := by
  have hp2 := congrFun hcore (0 : Fin JacobiCoreDimension)
  have hp3 := congrFun hcore (1 : Fin JacobiCoreDimension)
  have hp4 := congrFun hcore (2 : Fin JacobiCoreDimension)
  have hH := congrFun hcore (3 : Fin JacobiCoreDimension)
  have hT1 := congrFun hcore (4 : Fin JacobiCoreDimension)
  have hT2 := congrFun hcore (5 : Fin JacobiCoreDimension)
  have hT3 := congrFun hcore (6 : Fin JacobiCoreDimension)
  have hT4 := congrFun hcore (7 : Fin JacobiCoreDimension)
  have hDelta := congrFun hcore (8 : Fin JacobiCoreDimension)
  change z.p2 = w.p2 at hp2
  change z.p3 = w.p3 at hp3
  change z.p4 = w.p4 at hp4
  change z.H = w.H at hH
  change z.T1 = w.T1 at hT1
  change z.T2 = w.T2 at hT2
  change z.T3 = w.T3 at hT3
  change z.T4 = w.T4 at hT4
  change z.Delta = w.Delta at hDelta
  have hzT1 : z.T1 ≠ 0 :=
    right_ne_zero_of_mul_eq_one hz
  have hwT1 : w.T1 ≠ 0 :=
    right_ne_zero_of_mul_eq_one hw
  have hzU : z.U = z.T1⁻¹ :=
    (mul_eq_one_iff_eq_inv₀ hzT1).mp hz
  have hwU : w.U = w.T1⁻¹ :=
    (mul_eq_one_iff_eq_inv₀ hwT1).mp hw
  ext
  · exact hp2
  · exact hp3
  · exact hp4
  · exact hH
  · exact hT1
  · exact hT2
  · exact hT3
  · exact hT4
  · exact hDelta
  · rw [hzU, hwU, hT1]

/-- The core of any Jacobi trajectory is continuous. -/
theorem IsScaledJacobiTrajectory.continuous_corePoint
    {κZ κPhi : ℂ} {z : ℝ → JacobiState ℂ}
    (hz : IsScaledJacobiTrajectory κZ κPhi z) :
    Continuous (fun t ↦ jacobiCorePoint (z t)) := by
  apply continuous_pi
  intro i
  fin_cases i
  · simpa only [jacobiCorePoint] using hz.continuous_p2
  · simpa only [jacobiCorePoint] using hz.continuous_p3
  · simpa only [jacobiCorePoint] using hz.continuous_p4
  · simpa only [jacobiCorePoint] using hz.continuous_H
  · simpa only [jacobiCorePoint] using hz.continuous_T1
  · simpa only [jacobiCorePoint] using hz.continuous_T2
  · simpa only [jacobiCorePoint] using hz.continuous_T3
  · simpa only [jacobiCorePoint] using hz.continuous_T4
  · simpa only [jacobiCorePoint] using hz.continuous_Delta

namespace AffineBlochParameters

/-- The upper-half-plane affine modulus path is continuous. -/
theorem continuous_tau
    (p : AffineBlochParameters) :
    Continuous p.tau := by
  rw [continuous_induced_rng]
  exact
    continuous_iff_continuousAt.mpr
      fun t ↦ (p.hasDerivAt_tauComplex t).continuousAt

/-- The affine elliptic argument is continuous. -/
theorem continuous_xi
    (p : AffineBlochParameters) :
    Continuous p.xi :=
  continuous_iff_continuousAt.mpr
    fun t ↦ (p.hasDerivAt_xi t).continuousAt

/-- The theta vector along the affine parameters is continuous, including
at possible zeros of its first component. -/
theorem continuous_jacobiThetaVector_comp
    (p : AffineBlochParameters) :
    Continuous
      (fun t ↦
        jacobiThetaVector (p.xi t) (p.tau t : ℂ)) := by
  have hpair :
      Continuous (fun t ↦ (p.xi t, p.tau t)) :=
    p.continuous_xi.prodMk p.continuous_tau
  simpa only [Function.comp_apply] using
    continuous_jacobiThetaVector_upperHalfPlane.comp hpair

/-- The first differentiated theta coordinate along the affine parameters
is continuous. -/
theorem continuous_jacobiTheta1Prime_comp
    (p : AffineBlochParameters) :
    Continuous
      (fun t ↦
        jacobiTheta1Prime (p.xi t) (p.tau t : ℂ)) := by
  have hpair :
      Continuous (fun t ↦ (p.xi t, p.tau t)) :=
    p.continuous_xi.prodMk p.continuous_tau
  simpa only [Function.comp_apply] using
    continuous_jacobiTheta1Prime_upperHalfPlane.comp hpair

set_option linter.flexible false in
/-- The reciprocal-free core of the affine Bloch formula is continuous
without any regular-chart hypothesis. -/
theorem continuous_jacobiBlochCorePoint
    (p : AffineBlochParameters) :
    Continuous
      (fun t ↦ jacobiCorePoint (p.jacobiBlochPath t)) := by
  have hscale :
      Continuous p.commonScale :=
    continuous_iff_continuousAt.mpr
      fun t ↦ (p.commonScale_hasDerivAt t).continuousAt
  have htheta :=
    p.continuous_jacobiThetaVector_comp
  have hprime :=
    p.continuous_jacobiTheta1Prime_comp
  have hp2 :=
    canonicalUnaryRoots_p2_mdifferentiable.continuous.comp
      p.continuous_tau
  have hp3 :=
    canonicalUnaryRoots_p3_mdifferentiable.continuous.comp
      p.continuous_tau
  have hp4 :=
    canonicalUnaryRoots_p4_mdifferentiable.continuous.comp
      p.continuous_tau
  have hH :=
    canonicalUnaryRoots_H_mdifferentiable.continuous.comp
      p.continuous_tau
  have htheta1 :=
    (continuous_apply (0 : Fin 4)).comp htheta
  have htheta2 :=
    (continuous_apply (1 : Fin 4)).comp htheta
  have htheta3 :=
    (continuous_apply (2 : Fin 4)).comp htheta
  have htheta4 :=
    (continuous_apply (3 : Fin 4)).comp htheta
  apply continuous_pi
  intro i
  fin_cases i
  · simpa only [jacobiCorePoint, jacobiBlochPath,
      jacobiBlochGaugePath, JacobiState.blochGauge,
      canonicalJacobiPath, canonicalJacobiThetaMovingPath,
      canonicalJacobiThetaState] using hp2
  · simpa only [jacobiCorePoint, jacobiBlochPath,
      jacobiBlochGaugePath, JacobiState.blochGauge,
      canonicalJacobiPath, canonicalJacobiThetaMovingPath,
      canonicalJacobiThetaState] using hp3
  · simpa only [jacobiCorePoint, jacobiBlochPath,
      jacobiBlochGaugePath, JacobiState.blochGauge,
      canonicalJacobiPath, canonicalJacobiThetaMovingPath,
      canonicalJacobiThetaState] using hp4
  · simpa only [jacobiCorePoint, jacobiBlochPath,
      jacobiBlochGaugePath, JacobiState.blochGauge,
      canonicalJacobiPath, canonicalJacobiThetaMovingPath,
      canonicalJacobiThetaState] using hH
  · simpa only [jacobiCorePoint, jacobiBlochPath,
      jacobiBlochGaugePath, JacobiState.blochGauge,
      canonicalJacobiPath, canonicalJacobiThetaMovingPath,
      canonicalJacobiThetaState, jacobiThetaVector,
      Matrix.cons_val_zero] using hscale.mul htheta1
  · simpa only [jacobiCorePoint, jacobiBlochPath,
      jacobiBlochGaugePath, JacobiState.blochGauge,
      canonicalJacobiPath, canonicalJacobiThetaMovingPath,
      canonicalJacobiThetaState, jacobiThetaVector,
      Matrix.cons_val_one, Matrix.cons_val_zero] using
      hscale.mul htheta2
  · simpa only [jacobiCorePoint, jacobiBlochPath,
      jacobiBlochGaugePath, JacobiState.blochGauge,
      canonicalJacobiPath, canonicalJacobiThetaMovingPath,
      canonicalJacobiThetaState, jacobiThetaVector,
      Matrix.cons_val_one, Matrix.cons_val_zero] using
      hscale.mul htheta3
  · simpa only [jacobiCorePoint, jacobiBlochPath,
      jacobiBlochGaugePath, JacobiState.blochGauge,
      canonicalJacobiPath, canonicalJacobiThetaMovingPath,
      canonicalJacobiThetaState, jacobiThetaVector,
      Matrix.cons_val_one, Matrix.cons_val_zero] using
      hscale.mul htheta4
  · have hdelta :=
      let hslope :
          Continuous
            (fun _ : ℝ ↦ p.jacobiSlope) :=
        continuous_const
      hscale.mul
        ((hprime.div_const π).add
          (hslope.mul htheta1))
    simpa only [jacobiCorePoint, jacobiBlochPath,
      jacobiBlochGaugePath, JacobiState.blochGauge,
      canonicalJacobiPath, canonicalJacobiThetaMovingPath,
      canonicalJacobiThetaState, jacobiThetaVector,
      Matrix.cons_val_zero] using hdelta

/-- The first theta coordinate along the affine parameters is continuous. -/
theorem continuous_jacobiTheta1_comp
    (p : AffineBlochParameters) :
    Continuous
      (fun t ↦
        jacobiTheta1 (p.xi t) (p.tau t : ℂ)) := by
  simpa only [jacobiThetaVector, Matrix.cons_val_zero] using
    (continuous_apply (0 : Fin 4)).comp
      p.continuous_jacobiThetaVector_comp

/-- Agreement of the core forces regularity because the complete
polynomial trajectory remains on the reciprocal locus. -/
theorem regular_of_core_eq
    (p : AffineBlochParameters)
    {z : ℝ → JacobiState ℂ}
    {t : ℝ}
    (hcore :
      jacobiCorePoint (z t) =
        jacobiCorePoint (p.jacobiBlochPath t))
    (hreciprocal : (z t).U * (z t).T1 = 1) :
    jacobiTheta1 (p.xi t) (p.tau t : ℂ) ≠ 0 := by
  have hT1 :=
    congrFun hcore (4 : Fin JacobiCoreDimension)
  change
    (z t).T1 = (p.jacobiBlochPath t).T1 at hT1
  have hzT1 : (z t).T1 ≠ 0 :=
    right_ne_zero_of_mul_eq_one hreciprocal
  intro htheta
  change
    jacobiTheta1 (p.xi t) (p.tauComplex t) = 0
      at htheta
  apply hzT1
  rw [hT1]
  change
    p.commonScale t *
      jacobiTheta1 (p.xi t) (p.tauComplex t) = 0
  rw [htheta, mul_zero]

/-- On a regular affine Bloch point, the reciprocal equation holds
exactly. -/
theorem jacobiBlochPath_reciprocal
    (p : AffineBlochParameters)
    (hc0 : p.c0 ≠ 0)
    {t : ℝ}
    (hregular :
      jacobiTheta1 (p.xi t) (p.tau t : ℂ) ≠ 0) :
    (p.jacobiBlochPath t).U *
        (p.jacobiBlochPath t).T1 = 1 := by
  have hscale := p.commonScale_ne_zero hc0 t
  change
    jacobiTheta1 (p.xi t) (p.tauComplex t) ≠ 0
      at hregular
  simp only [jacobiBlochPath, jacobiBlochGaugePath,
    JacobiState.blochGauge, canonicalJacobiPath,
    canonicalJacobiThetaMovingPath,
    canonicalJacobiThetaState]
  field_simp [hscale, hregular]

/-- Core agreement on the reciprocal locus is full state agreement. -/
theorem state_eq_of_core_eq
    (p : AffineBlochParameters)
    {z : ℝ → JacobiState ℂ}
    (hc0 : p.c0 ≠ 0)
    {t : ℝ}
    (hcore :
      jacobiCorePoint (z t) =
        jacobiCorePoint (p.jacobiBlochPath t))
    (hreciprocal : (z t).U * (z t).T1 = 1) :
    z t = p.jacobiBlochPath t := by
  have hregular :=
    p.regular_of_core_eq hcore hreciprocal
  exact
    JacobiState.eq_of_core_eq_of_reciprocal
      hcore hreciprocal
      (p.jacobiBlochPath_reciprocal hc0 hregular)

/-- **Global reciprocal-chart continuation.**

If a complete polynomial Jacobi trajectory agrees in its nine regular
coordinates with an affine Bloch formula at one time, and stays on
`U*T₁=1`, then the theta formula is regular and equal to the trajectory
for every real time. -/
theorem regular_and_eq_jacobiBlochPath_of_core_eq_at
    (p : AffineBlochParameters)
    {z : ℝ → JacobiState ℂ}
    (hz :
      IsScaledJacobiTrajectory
        ((π : ℂ) * (p.nu : ℂ))
        ((π : ℂ) * I * (p.kappa : ℂ)) z)
    (hc0 : p.c0 ≠ 0)
    (hreciprocal :
      ∀ t, (z t).U * (z t).T1 = 1)
    {t₀ : ℝ}
    (hinitial :
      jacobiCorePoint (z t₀) =
        jacobiCorePoint (p.jacobiBlochPath t₀)) :
    (∀ t,
      jacobiTheta1 (p.xi t) (p.tau t : ℂ) ≠ 0) ∧
      z = p.jacobiBlochPath := by
  let agreement : Set ℝ :=
    {t |
      jacobiCorePoint (z t) =
        jacobiCorePoint (p.jacobiBlochPath t)}
  have hagreement_closed : IsClosed agreement := by
    exact isClosed_eq hz.continuous_corePoint
      p.continuous_jacobiBlochCorePoint
  have hagreement_open : IsOpen agreement := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    have hregular :
        jacobiTheta1 (p.xi t) (p.tau t : ℂ) ≠ 0 :=
      p.regular_of_core_eq ht (hreciprocal t)
    have hregularEventually :
        ∀ᶠ s in nhds t,
          jacobiTheta1 (p.xi s) (p.tau s : ℂ) ≠ 0 :=
      p.continuous_jacobiTheta1_comp.continuousAt.eventually
        (isOpen_compl_singleton.mem_nhds hregular)
    have hstate :
        z t = p.jacobiBlochPath t :=
      p.state_eq_of_core_eq hc0 ht (hreciprocal t)
    have hleft :
        ∀ᶠ s in nhds t,
          HasDerivAt
            (fun u ↦ JacobiPolynomialCode.point (z u))
            (jacobiCoordinateVectorField
              ((π : ℂ) * (p.nu : ℂ))
              ((π : ℂ) * I * (p.kappa : ℂ))
              (JacobiPolynomialCode.point (z s))) s :=
      Filter.Eventually.of_forall
        fun s ↦ hz.point_hasDerivAt s
    have hright :
        ∀ᶠ s in nhds t,
          HasDerivAt
            (fun u ↦
              JacobiPolynomialCode.point
                (p.jacobiBlochPath u))
            (jacobiCoordinateVectorField
              ((π : ℂ) * (p.nu : ℂ))
              ((π : ℂ) * I * (p.kappa : ℂ))
              (JacobiPolynomialCode.point
                (p.jacobiBlochPath s))) s := by
      filter_upwards [hregularEventually] with s hs
      exact
        (p.jacobiBlochPath_isScaledAt hc0 hs).point_hasDerivAt
    have hpointEventually :
        (fun s ↦ JacobiPolynomialCode.point (z s)) =ᶠ[nhds t]
          (fun s ↦
            JacobiPolynomialCode.point
              (p.jacobiBlochPath s)) := by
      apply
        HGAS.Analysis.autonomousC1_ode_solution_eventuallyEq
          (contDiff_jacobiCoordinateVectorField
            ((π : ℂ) * (p.nu : ℂ))
            ((π : ℂ) * I * (p.kappa : ℂ)))
          hleft hright
      · exact (hz.point_hasDerivAt t).continuousAt
      · exact
          ((p.jacobiBlochPath_isScaledAt
            hc0 hregular).point_hasDerivAt).continuousAt
      · exact congrArg JacobiPolynomialCode.point hstate
    filter_upwards [hpointEventually] with s hs
    have hstateCore :=
      congrArg (fun q ↦
        jacobiCorePoint (JacobiPolynomialCode.state q)) hs
    simpa using hstateCore
  have hagreement_clopen : IsClopen agreement :=
    ⟨hagreement_closed, hagreement_open⟩
  have hagreement_nonempty : agreement.Nonempty :=
    ⟨t₀, hinitial⟩
  have hagreement_univ :
      agreement = Set.univ :=
    hagreement_clopen.eq_univ hagreement_nonempty
  have hcore_all :
      ∀ t,
        jacobiCorePoint (z t) =
          jacobiCorePoint (p.jacobiBlochPath t) := by
    intro t
    have ht : t ∈ agreement := by
      rw [hagreement_univ]
      exact Set.mem_univ t
    exact ht
  have hregular_all :
      ∀ t,
        jacobiTheta1 (p.xi t) (p.tau t : ℂ) ≠ 0 :=
    fun t ↦
      p.regular_of_core_eq
        (hcore_all t) (hreciprocal t)
  refine ⟨hregular_all, ?_⟩
  funext t
  exact
    p.state_eq_of_core_eq hc0
      (hcore_all t) (hreciprocal t)

end AffineBlochParameters

end

end HGAS.Modular
