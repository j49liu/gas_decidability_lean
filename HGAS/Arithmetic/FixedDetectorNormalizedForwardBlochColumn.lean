import HGAS.Arithmetic.CorrectedFixedDetectorOrdinaryTimeMomentSeries
import HGAS.Arithmetic.FixedDetectorForwardSubtrajectoryCrosswalk
import HGAS.Dynamics.ForwardRecurrenceEventualEquality
import HGAS.Lyapunov.CheckedRationalCertificateSoundness
import HGAS.Modular.JacobiBlochForwardRegularContinuation
import Mathlib.Tactic

/-!
# A normalized forward detector column determines its Bloch path

This file is deliberately independent of any particular sum-of-squares
validity compiler.  It starts with an arbitrary forward trajectory of the
literal fixed-detector field and records, explicitly, the normalization
data which a corrected validity theorem must supply.

The initial data are stronger than a merely twisted theta seed: the
reciprocal-free Jacobi core itself is aligned.  This distinction is
essential.  A projective theta identity with diagonal coefficient twists
does not, by itself, identify the polynomial Jacobi state.

From these data we derive, rather than assume, on the whole physical ray:

* equality of the controller family with the locked clock path;
* constancy of the two Jacobi readouts;
* regularity and equality of the Jacobi state with the affine Bloch path;
* equality of the detector gauge with the selected fourth-root gauge; and
* the gauged-output identity used by the moment-series theorems.

Only forward ODE uniqueness is used.  No equation at negative physical
time is needed.
-/

namespace HGAS

open Set
open Modular
open Clocks
open Clocks.ControllerPhaseProductCharacterCode

noncomputable section

namespace FixedDetectorNormalizedForwardBlochColumn

open FixedDetectorForwardSubtrajectoryCrosswalk
open FixedDetectorForwardTrajectoryReverseCrosswalk
open FixedDetectorOrdinaryTimeBlochCrosswalk
open FixedDetectorReverseTrajectoryCrosswalk

variable {eqs vars : ℕ}

/-- Exact normalized seed data for one detector column.

The phase normalization is represented by the type `Circle`, so the
explicit phase path lies on the unit circle by construction.  The
controller lock and the initial controller equality rule out replacing
the intended clocks by an unrelated solution.  The reciprocal identity
and full core alignment are precisely what the Jacobi continuation
argument consumes. -/
structure NormalizedSeed
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (x :
      ℝ →
        Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (x₀ :
      Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (controller :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → Circle)
    (j : Fin vars)
    (p : AffineBlochParameters)
    (d : ℂ) : Prop where
  structured :
    IsForwardStructuredTrajectory parameters I x x₀
  controller_lock :
    ∀ i,
      Controller.IsControllerEquilibrium
        (RationalCode.decode (parameters i) : ℝ)
        (controller i)
  controllers_zero :
    (recoveredState x 0).base.base.source.controllers =
      CanonicalFixedDetectorTrajectory.clockPath
        parameters controller phase₀ 0
  reciprocal :
    ∀ t, 0 ≤ t →
      ((recoveredState x t).base.base.source.linked j).jacobi.U *
          ((recoveredState x t).base.base.source.linked j).jacobi.T1 =
        1
  jacobi_core_zero :
    jacobiCorePoint
        ((recoveredState x 0).base.base.source.linked j).jacobi =
      jacobiCorePoint (p.jacobiBlochPath 0)
  gauge_zero :
    (recoveredState x 0).base.base.gauge j =
      p.fourthRootGauge d 0
  clocks :
    MatchesDetectorClocksRealPi p
      (CanonicalFixedDetectorTrajectory.omegaFrequency
        parameters controller j)
      (CanonicalFixedDetectorTrajectory.numberFrequency
        parameters I controller j)
  c0_ne_zero : p.c0 ≠ 0

/-- The actual controller coordinates form a forward trajectory of the
standalone product-controller field. -/
theorem actualControllers_isForwardTrajectory
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (x :
      ℝ →
        Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (x₀ :
      Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (h : IsForwardStructuredTrajectory parameters I x x₀) :
    IsForwardTrajectory
      (PolynomialFieldCode.realize
        (ControllerPhaseProductPolynomialCode.fieldCode parameters))
      (fun t =>
        ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint
          (recoveredState x t).base.base.source)
      (ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint
        (recoveredState x 0).base.base.source) := by
  refine ⟨rfl, ?_⟩
  intro t ht
  exact
    (structuredWithinAt_Ici
      parameters I x x₀ h t ht).controllers

/-- Forward uniqueness locks the actual controller family to the explicit
clock path from one normalized initial state. -/
theorem controllers_eqOn_Ici
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (x :
      ℝ →
        Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (x₀ :
      Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (controller :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → Circle)
    (j : Fin vars)
    (p : AffineBlochParameters)
    (d : ℂ)
    (h :
      NormalizedSeed
        parameters I x x₀ controller phase₀ j p d) :
    ∀ t, 0 ≤ t →
      (recoveredState x t).base.base.source.controllers =
        CanonicalFixedDetectorTrajectory.clockPath
          parameters controller phase₀ t := by
  let F :=
    PolynomialFieldCode.realize
      (ControllerPhaseProductPolynomialCode.fieldCode parameters)
  let actual : ℝ →
      Fin (ControllerPhaseProductPolynomialCode.dimension
        (FixedDetectorPolynomialCode.clockCount eqs vars)) → ℝ :=
    fun t =>
      ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint
        (recoveredState x t).base.base.source
  let explicit : ℝ →
      Fin (ControllerPhaseProductPolynomialCode.dimension
        (FixedDetectorPolynomialCode.clockCount eqs vars)) → ℝ :=
    fun t =>
      ControllerPhaseProductPolynomialCode.point
        (CanonicalFixedDetectorTrajectory.clockPath
          parameters controller phase₀ t)
  have hactual :
      IsForwardTrajectory F actual (actual 0) := by
    exact
      actualControllers_isForwardTrajectory
        parameters I x x₀ h.structured
  have hexplicit :
      IsForwardTrajectory F explicit (actual 0) := by
    refine ⟨?_, ?_⟩
    · exact congrArg
        ControllerPhaseProductPolynomialCode.point
        h.controllers_zero.symm
    · intro t ht
      exact
        (LockedControllerPhaseTrajectory.point_stateFamily_isIntegralCurve
          parameters controller phase₀ h.controller_lock t).hasDerivWithinAt
  have heq :
      EqOn actual explicit (Ici (0 : ℝ)) :=
    hactual.eqOn_Ici_of_contDiff
      (contDiff_polynomialFieldCode_realize
        (ControllerPhaseProductPolynomialCode.fieldCode parameters))
      hexplicit
  intro t ht
  have hpoint := heq ht
  have hstate :=
    congrArg ControllerPhaseProductPolynomialCode.state hpoint
  simpa only [actual, explicit,
    ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint,
    ControllerPhaseProductPolynomialCode.state_point] using hstate

/-- Controller locking turns the dynamic elliptic readout into the
constant detector value `(ω+N)/2`. -/
theorem kappaZ_eqOn_Ici
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (x :
      ℝ →
        Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (x₀ :
      Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (controller :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → Circle)
    (j : Fin vars)
    (p : AffineBlochParameters)
    (d : ℂ)
    (h :
      NormalizedSeed
        parameters I x x₀ controller phase₀ j p d) :
    ∀ t, 0 ≤ t →
      ControllerProductLinkedJacobiFamilyPolynomialCode.kappaZ
          (fun a i =>
            (RationalCode.decode
              (DetectorCharacterCode.omegaWeights
                (eqs := eqs) a i) : ℝ))
          (fun a i =>
            (RationalCode.decode
              (DetectorCharacterCode.numberWeights I a i) : ℝ))
          (fun i => (RationalCode.decode (parameters i) : ℝ))
          (recoveredState x t).base.base.source j =
        ((((CanonicalFixedDetectorTrajectory.omegaFrequency
              parameters controller j +
            CanonicalFixedDetectorTrajectory.numberFrequency
              parameters I controller j) / 2 : ℝ) : ℂ)) := by
  intro t ht
  unfold ControllerProductLinkedJacobiFamilyPolynomialCode.kappaZ
    ControllerProductLinkedJacobiFamilyPolynomialCode.omega
    ControllerProductLinkedJacobiFamilyPolynomialCode.number
    ControllerPhaseProductLinearFrequencyCode.value
  rw [controllers_eqOn_Ici
    parameters I x x₀ controller phase₀ j p d h t ht]
  simp only [CanonicalFixedDetectorTrajectory.clockPath,
    LockedControllerPhaseTrajectory.stateFamily_controller]
  rfl

/-- Controller locking turns the dynamic modular readout into the
constant detector value `iω`. -/
theorem kappaPhi_eqOn_Ici
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (x :
      ℝ →
        Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (x₀ :
      Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (controller :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → Circle)
    (j : Fin vars)
    (p : AffineBlochParameters)
    (d : ℂ)
    (h :
      NormalizedSeed
        parameters I x x₀ controller phase₀ j p d) :
    ∀ t, 0 ≤ t →
      ControllerProductLinkedJacobiFamilyPolynomialCode.kappaPhi
          (fun a i =>
            (RationalCode.decode
              (DetectorCharacterCode.omegaWeights
                (eqs := eqs) a i) : ℝ))
          (fun i => (RationalCode.decode (parameters i) : ℝ))
          (recoveredState x t).base.base.source j =
        Complex.I *
          CanonicalFixedDetectorTrajectory.omegaFrequency
            parameters controller j := by
  intro t ht
  unfold ControllerProductLinkedJacobiFamilyPolynomialCode.kappaPhi
    ControllerProductLinkedJacobiFamilyPolynomialCode.omega
    ControllerPhaseProductLinearFrequencyCode.value
  rw [controllers_eqOn_Ici
    parameters I x x₀ controller phase₀ j p d h t ht]
  simp only [CanonicalFixedDetectorTrajectory.clockPath,
    LockedControllerPhaseTrajectory.stateFamily_controller]
  rfl

/-- The clock matching equations identify the detector's elliptic
coefficient with the affine Bloch coefficient. -/
theorem clocks_jacobiKappaZ_eq
    {p : AffineBlochParameters} {ω N : ℝ}
    (h : MatchesDetectorClocksRealPi p ω N) :
    ((((ω + N) / 2 : ℝ) : ℂ)) =
      (Real.pi : ℂ) * (p.nu : ℂ) := by
  rw [h.nu_eq]
  push_cast
  field_simp [Real.pi_ne_zero]

/-- The clock matching equations identify the detector's modular
coefficient with the affine Bloch coefficient. -/
theorem clocks_jacobiKappaPhi_eq
    {p : AffineBlochParameters} {ω N : ℝ}
    (h : MatchesDetectorClocksRealPi p ω N) :
    Complex.I * (ω : ℂ) =
      (Real.pi : ℂ) * Complex.I * (p.kappa : ℂ) := by
  rw [h.kappa_eq]
  push_cast
  field_simp [Real.pi_ne_zero]

/-- After controller locking and clock matching, the selected actual
Jacobi block is a forward trajectory of the constant-coefficient Jacobi
field used by the affine Bloch formula. -/
theorem actualJacobi_isForwardTrajectory
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (x :
      ℝ →
        Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (x₀ :
      Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (controller :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → Circle)
    (j : Fin vars)
    (p : AffineBlochParameters)
    (d : ℂ)
    (h :
      NormalizedSeed
        parameters I x x₀ controller phase₀ j p d) :
    IsForwardTrajectory
      (jacobiCoordinateVectorField
        ((Real.pi : ℂ) * (p.nu : ℂ))
        ((Real.pi : ℂ) * Complex.I * (p.kappa : ℂ)))
      (fun t =>
        JacobiPolynomialCode.point
          ((recoveredState x t).base.base.source.linked j).jacobi)
      (JacobiPolynomialCode.point
        ((recoveredState x 0).base.base.source.linked j).jacobi) := by
  refine ⟨rfl, ?_⟩
  intro t ht
  rw [hasDerivWithinAt_pi]
  intro i
  have hi :=
    linkedPoint_hasDerivWithinAt_Ici
      parameters I x x₀ h.structured j
      (LinkedJacobiPolynomialCode.jacobiEmbedding i) t ht
  have hkZ :=
    kappaZ_eqOn_Ici
      parameters I x x₀ controller phase₀ j p d h t ht
  have hkPhi :=
    kappaPhi_eqOn_Ici
      parameters I x x₀ controller phase₀ j p d h t ht
  have hZmatch :=
    clocks_jacobiKappaZ_eq h.clocks
  have hPhimatch :=
    clocks_jacobiKappaPhi_eq h.clocks
  simpa [LinkedJacobiPolynomialCode.point,
    LinkedJacobiPolynomialCode.jacobiEmbedding,
    ComplexPolynomialBlockCode.point_rightEmbedding,
    ControllerProductLinkedJacobiFamilyPolynomialCode.vectorField,
    hkZ, hkPhi, hZmatch, hPhimatch,
    LinkedJacobiState.combinedVectorField,
    jacobiCoordinateVectorField,
    JacobiPolynomialCode.state_point] using hi

/-- The normalized seed and the positive-time ODE force global
reciprocal-chart regularity and exact Bloch equality on the physical
time ray. -/
theorem jacobi_regular_and_eqOn_Ici
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (x :
      ℝ →
        Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (x₀ :
      Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (controller :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → Circle)
    (j : Fin vars)
    (p : AffineBlochParameters)
    (d : ℂ)
    (h :
      NormalizedSeed
        parameters I x x₀ controller phase₀ j p d) :
    (∀ t, 0 ≤ t →
      jacobiTheta1 (p.xi t) (p.tau t : ℂ) ≠ 0) ∧
      ∀ t, 0 ≤ t →
        ((recoveredState x t).base.base.source.linked j).jacobi =
          p.jacobiBlochPath t := by
  apply
    p.regular_and_eqOn_Ici_jacobiBlochPath_of_core_eq_zero
      (actualJacobi_isForwardTrajectory
        parameters I x x₀ controller phase₀ j p d h)
      h.c0_ne_zero h.reciprocal h.jacobi_core_zero

/-- The actual private modular readout is the constant `ω` selected by
the locked controller family. -/
theorem omega_eqOn_Ici
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (x :
      ℝ →
        Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (x₀ :
      Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (controller :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → Circle)
    (j : Fin vars)
    (p : AffineBlochParameters)
    (d : ℂ)
    (h :
      NormalizedSeed
        parameters I x x₀ controller phase₀ j p d) :
    ∀ t, 0 ≤ t →
      ControllerProductLinkedJacobiFamilyPolynomialCode.omega
          (fun a i =>
            (RationalCode.decode
              (DetectorCharacterCode.omegaWeights
                (eqs := eqs) a i) : ℝ))
          (fun i => (RationalCode.decode (parameters i) : ℝ))
          (recoveredState x t).base.base.source j =
        CanonicalFixedDetectorTrajectory.omegaFrequency
          parameters controller j := by
  intro t ht
  unfold ControllerProductLinkedJacobiFamilyPolynomialCode.omega
    ControllerPhaseProductLinearFrequencyCode.value
  rw [controllers_eqOn_Ici
    parameters I x x₀ controller phase₀ j p d h t ht]
  simp only [CanonicalFixedDetectorTrajectory.clockPath,
    LockedControllerPhaseTrajectory.stateFamily_controller]
  rfl

/-- The actual arithmetic linear readout is the constant `N` selected by
the locked controller family. -/
theorem number_eqOn_Ici
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (x :
      ℝ →
        Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (x₀ :
      Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (controller :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → Circle)
    (j : Fin vars)
    (p : AffineBlochParameters)
    (d : ℂ)
    (h :
      NormalizedSeed
        parameters I x x₀ controller phase₀ j p d) :
    ∀ t, 0 ≤ t →
      ControllerProductLinkedJacobiFamilyPolynomialCode.number
          (fun a i =>
            (RationalCode.decode
              (DetectorCharacterCode.numberWeights I a i) : ℝ))
          (fun i => (RationalCode.decode (parameters i) : ℝ))
          (recoveredState x t).base.base.source j =
        CanonicalFixedDetectorTrajectory.numberFrequency
          parameters I controller j := by
  intro t ht
  unfold ControllerProductLinkedJacobiFamilyPolynomialCode.number
    ControllerPhaseProductLinearFrequencyCode.value
  rw [controllers_eqOn_Ici
    parameters I x x₀ controller phase₀ j p d h t ht]
  simp only [CanonicalFixedDetectorTrajectory.clockPath,
    LockedControllerPhaseTrajectory.stateFamily_controller]
  rfl

/-- The affine fourth-root gauge frequency is exactly the detector gauge
frequency `(ω+2N)/4`. -/
theorem clocks_fourthRootGaugeFrequency_eq
    {p : AffineBlochParameters} {ω N : ℝ}
    (h : MatchesDetectorClocksRealPi p ω N) :
    p.fourthRootGaugeFrequency = (ω + 2 * N) / 4 := by
  rw [AffineBlochParameters.fourthRootGaugeFrequency,
    h.nu_eq, h.kappa_eq]
  field_simp [Real.pi_ne_zero]
  ring

/-- A selected affine fourth-root gauge solves its scalar constant
frequency ODE at every real time. -/
theorem fourthRootGauge_hasDerivAt
    (p : AffineBlochParameters) (d : ℂ) (t : ℝ) :
    HasDerivAt
      (p.fourthRootGauge d)
      (((p.fourthRootGaugeFrequency : ℂ) * Complex.I) *
        p.fourthRootGauge d t) t := by
  let ω : ℝ := p.fourthRootGaugeFrequency
  let f : ℝ → ℂ := p.fourthRootGauge d
  have hf :
      f =
        fun s =>
          f 0 *
            HGAS.Analysis.realFrequencyExponential ω s := by
    funext s
    exact p.fourthRootGauge_eq_zero_mul_frequency d s
  have hcast :
      HasDerivAt (fun u : ℝ => (u : ℂ)) 1 t :=
    (hasDerivAt_id t).ofReal_comp
  have hlinear :
      HasDerivAt
        (fun u : ℝ => ((ω : ℂ) * Complex.I) * (u : ℂ))
        ((ω : ℂ) * Complex.I) t := by
    convert hcast.const_mul ((ω : ℂ) * Complex.I) using 1
    all_goals ring
  have hexponential :
      HasDerivAt
        (HGAS.Analysis.realFrequencyExponential ω)
        (((ω : ℂ) * Complex.I) *
          HGAS.Analysis.realFrequencyExponential ω t) t := by
    convert hlinear.cexp using 1
    all_goals
      unfold HGAS.Analysis.realFrequencyExponential
    all_goals ring
  have hscaled := hexponential.const_mul (f 0)
  change
    HasDerivAt f
      (((ω : ℂ) * Complex.I) * f t) t
  rw [hf]
  convert hscaled using 1
  · simp only [f, ω]
    ring

/-- The detector gauge coordinate is a forward trajectory of the same
constant-frequency scalar ODE as the selected affine gauge. -/
theorem actualGauge_isForwardTrajectory
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (x :
      ℝ →
        Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (x₀ :
      Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (controller :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → Circle)
    (j : Fin vars)
    (p : AffineBlochParameters)
    (d : ℂ)
    (h :
      NormalizedSeed
        parameters I x x₀ controller phase₀ j p d) :
    IsForwardTrajectory
      (fun G =>
        Complex.I * (p.fourthRootGaugeFrequency : ℂ) * G)
      (fun t => (recoveredState x t).base.base.gauge j)
      ((recoveredState x 0).base.base.gauge j) := by
  refine ⟨rfl, ?_⟩
  intro t ht
  have hg :=
    (structuredWithinAt_Ici
      parameters I x x₀ h.structured t ht).gauge j
  rw [DetectorJacobiGaugeData.detectorGaugeVelocity_eq] at hg
  have hω :=
    omega_eqOn_Ici
      parameters I x x₀ controller phase₀ j p d h t ht
  have hN :=
    number_eqOn_Ici
      parameters I x x₀ controller phase₀ j p d h t ht
  have hfrequency :=
    clocks_fourthRootGaugeFrequency_eq h.clocks
  simpa only [hω, hN, hfrequency] using hg

/-- Forward uniqueness forces equality of the actual detector gauge and
the selected affine fourth-root gauge. -/
theorem gauge_eqOn_Ici
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (x :
      ℝ →
        Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (x₀ :
      Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (controller :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → Circle)
    (j : Fin vars)
    (p : AffineBlochParameters)
    (d : ℂ)
    (h :
      NormalizedSeed
        parameters I x x₀ controller phase₀ j p d) :
    ∀ t, 0 ≤ t →
      (recoveredState x t).base.base.gauge j =
        p.fourthRootGauge d t := by
  let F : ℂ → ℂ :=
    fun G => Complex.I * (p.fourthRootGaugeFrequency : ℂ) * G
  let actual : ℝ → ℂ :=
    fun t => (recoveredState x t).base.base.gauge j
  let explicit : ℝ → ℂ :=
    p.fourthRootGauge d
  have hactual :
      IsForwardTrajectory F actual (actual 0) :=
    actualGauge_isForwardTrajectory
      parameters I x x₀ controller phase₀ j p d h
  have hexplicit :
      IsForwardTrajectory F explicit (actual 0) := by
    refine ⟨h.gauge_zero.symm, ?_⟩
    intro t _ht
    have ht := fourthRootGauge_hasDerivAt p d t
    convert ht.hasDerivWithinAt using 1
    all_goals
      simp only [F, explicit]
    all_goals ring
  have heq :
      EqOn actual explicit (Ici (0 : ℝ)) :=
    hactual.eqOn_Ici_of_contDiff (by
      dsimp only [F]
      fun_prop) hexplicit
  intro t ht
  exact heq ht

/-- The two independently continued equalities give the exact gauged
theta output needed by every moment row. -/
theorem output_eqOn_Ici
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (x :
      ℝ →
        Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (x₀ :
      Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (controller :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → Circle)
    (j : Fin vars)
    (p : AffineBlochParameters)
    (d : ℂ)
    (h :
      NormalizedSeed
        parameters I x x₀ controller phase₀ j p d) :
    ∀ t, 0 ≤ t →
      (recoveredState x t).base.base.gauge j *
          ((recoveredState x t).base.base.source.linked j).jacobi.T1 =
        p.fourthRootGauge d t *
          (p.jacobiBlochPath t).T1 := by
  intro t ht
  rw [gauge_eqOn_Ici
    parameters I x x₀ controller phase₀ j p d h t ht]
  rw [(jacobi_regular_and_eqOn_Ici
    parameters I x x₀ controller phase₀ j p d h).2 t ht]

/-- Pointwise packaging of the derived controller and output equalities
in the interface expected by the ordinary-time moment theorems. -/
theorem matchesCompiledGaugedBlochPhaseAt
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (x :
      ℝ →
        Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (x₀ :
      Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (controller :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → Circle)
    (j : Fin vars)
    (p : AffineBlochParameters)
    (d : ℂ)
    (h :
      NormalizedSeed
        parameters I x x₀ controller phase₀ j p d) :
    ∀ t, 0 ≤ t →
      MatchesCompiledGaugedBlochPhaseAt
        parameters controller phase₀ j p d t
        (recoveredState x t) := by
  intro t ht
  exact
    ⟨controllers_eqOn_Ici
        parameters I x x₀ controller phase₀ j p d h t ht,
      output_eqOn_Ici
        parameters I x x₀ controller phase₀ j p d h t ht⟩

end FixedDetectorNormalizedForwardBlochColumn

end

end HGAS
