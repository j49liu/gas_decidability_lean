import HGAS.Arithmetic.FixedDetectorNormalizedForwardClassifiedSeries
import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorCanonicalRootSeed
import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorColumnCharacters
import HGAS.Modular.JacobiBlochSelectedContinuationNonzero
import Mathlib.Tactic

/-!
# Physical-time classified Bloch seeds for selected detector columns

The closed-horocycle argument naturally standardizes a detector column
by the signed time factor `π / ωⱼ`.  At time zero this rescaling changes
no state.  Consequently its canonical root seed can be continued
directly in the original physical time, whose two Jacobi clocks are

```text
  π νⱼ = (ωⱼ + Nⱼ) / 2,       π i κⱼ = i ωⱼ,
  νⱼ = (ωⱼ + Nⱼ) / (2π),      κⱼ = ωⱼ / π.
```

This file carries out that direct continuation and retains the
nonvanishing affine scale `c0`.  It then chooses:

* the actual controller equilibrium at physical time zero;
* the actual unit-circle phase of every clock;
* the unique free fourth-root-gauge constant matching the detector
  gauge at time zero.

These choices package every selected physical column as the
`ClassifiedSeed` consumed by the three corrected Jacobi moment-series
theorems.  The construction is kept separate from those series so the
physical-time Bloch bridge is reusable.
-/

namespace
  HGAS.NormalizedCorrectedFixedDetectorPhysicalClassifiedSeed

open HGAS
open HGAS.Clocks
open HGAS.Modular
open UpperHalfPlane hiding I
open CompactAccumulatorPipelineCode.AllAffineCompactSourceChart
open NormalizedCorrectedFixedDetectorTwoSidedValidityOrbit
open NormalizedCorrectedFixedDetectorBidirectionalValidityOrbit
open NormalizedCorrectedFixedDetectorTwoSidedStructuredOrbit
open NormalizedCorrectedFixedDetectorTwoSidedControllerLocking
open NormalizedCorrectedFixedDetectorColumnTrajectory
open NormalizedCorrectedFixedDetectorColumnRecurrence
open NormalizedCorrectedFixedDetectorColumnCharacters
open NormalizedCorrectedFixedDetectorFiniteClosedBranchSelection
open NormalizedCorrectedFixedDetectorCanonicalRootSeed
open FixedDetectorOrdinaryTimeBlochCrosswalk
open FixedDetectorNormalizedForwardBlochColumn
open FixedDetectorNormalizedForwardClassifiedSeries
open
  NormalizedCorrectedFixedDetectorTwoSidedStructuredOrbit.SelectedTwoSidedValidityOrbit
open
  NormalizedCorrectedFixedDetectorTwoSidedControllerLocking.SelectedTwoSidedValidityOrbit
open
  NormalizedCorrectedFixedDetectorColumnTrajectory.SelectedTwoSidedValidityOrbit
open
  NormalizedCorrectedFixedDetectorColumnRecurrence.SelectedTwoSidedValidityOrbit
open
  NormalizedCorrectedFixedDetectorColumnCharacters.SelectedBidirectionalValidityOrbit
open
  NormalizedCorrectedFixedDetectorCanonicalRootSeed.SelectedBidirectionalValidityOrbit

noncomputable section

variable {eqs vars : ℕ}
variable
  {u :
    NormalizedCorrectedFixedDetectorCompactSourceCode.CompilerInput
      eqs vars}

/-- Ordinary-time elliptic speed of a selected detector column. -/
def physicalColumnNu
    (O : SelectedTwoSidedValidityOrbit u)
    (j : Fin vars) : ℝ :=
  (columnOmega O j + columnNumber O j) /
    (2 * Real.pi)

/-- Ordinary-time modular speed of a selected detector column. -/
def physicalColumnKappa
    (O : SelectedTwoSidedValidityOrbit u)
    (j : Fin vars) : ℝ :=
  columnOmega O j / Real.pi

namespace SelectedTwoSidedValidityOrbit

variable (O : SelectedTwoSidedValidityOrbit u)

/-- The literal physical detector clocks have the affine Bloch
`(πν, πiκ)` form. -/
theorem physicalLinkedColumn_isPiScaledTrajectory
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (hp :
      ∀ i,
        (1 : ℝ) <
          (RationalCode.decode
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
              u i) : ℝ))
    (j : Fin vars) :
    IsScaledLinkedJacobiTrajectory
      ((Real.pi : ℂ) * (physicalColumnNu O j : ℂ))
      ((Real.pi : ℂ) * Complex.I *
        (physicalColumnKappa O j : ℂ))
      (linkedColumn O j) := by
  have h :=
    linkedColumn_isScaledTrajectory O hscale hp j
  have hZ :
      columnKappaZ O j =
        (Real.pi : ℂ) * (physicalColumnNu O j : ℂ) := by
    unfold columnKappaZ physicalColumnNu
    push_cast
    field_simp [Real.pi_ne_zero]
  have hPhi :
      columnKappaPhi O j =
        (Real.pi : ℂ) * Complex.I *
          (physicalColumnKappa O j : ℂ) := by
    unfold columnKappaPhi physicalColumnKappa
    push_cast
    field_simp [Real.pi_ne_zero]
  rwa [hZ, hPhi] at h

/-- Recurrence of the full linked block projects to recurrence of its
ten-coordinate Jacobi block. -/
theorem physicalJacobiColumn_forwardRecurrentAt
    (j : Fin vars) :
    ForwardRecurrentAt
      (fun t ↦
        JacobiPolynomialCode.point
          (linkedColumn O j t).jacobi) 0 := by
  let projectJacobi :
      (Fin LinkedJacobiPolynomialCode.dimension → ℂ) →
        (Fin JacobiPolynomialCode.dimension → ℂ) :=
    fun z ↦ z ∘ LinkedJacobiPolynomialCode.jacobiEmbedding
  have hproject : Continuous projectJacobi := by
    apply continuous_pi
    intro i
    exact continuous_apply _
  have h :=
    (linkedColumn_forwardRecurrentAt O j).map hproject
  have hpoint :
      (fun t ↦
        projectJacobi
          (LinkedJacobiPolynomialCode.point
            (linkedColumn O j t))) =
        (fun t ↦
          JacobiPolynomialCode.point
            (linkedColumn O j t).jacobi) := by
    funext t i
    simp only [
      projectJacobi,
      LinkedJacobiPolynomialCode.point,
      Function.comp_apply,
      LinkedJacobiPolynomialCode.jacobiEmbedding,
      ComplexPolynomialBlockCode.point_rightEmbedding]
  rw [hpoint] at h
  exact h

end SelectedTwoSidedValidityOrbit

open
  HGAS.NormalizedCorrectedFixedDetectorPhysicalClassifiedSeed.SelectedTwoSidedValidityOrbit

namespace SelectedBidirectionalValidityOrbit

variable (O : SelectedBidirectionalValidityOrbit u)

private abbrev B :
    SelectedTwoSidedValidityOrbit u :=
  O.toSelectedTwoSidedValidityOrbit

/-- Unit-circle initial phases read from the selected physical clock
point. -/
def physicalInitialPhase
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ)) :
    Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → Circle :=
  HGAS.Clocks.LockedControllerPhaseCompleteCurve.initialPhase
    (clockPoint (B O))
    (fun i ↦
      (clockPoint_onClockCircles (B O) hscale 0 i).2)

/-- **Physical-time affine Bloch classification.**

The canonical standardized root seed is used only at time zero.  The
continuation itself is applied to the unscaled physical Jacobi ODE, so
the returned parameters already have the ordinary detector speeds. -/
theorem physicalJacobiColumn_exists_affineBlochParameters
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (hp :
      ∀ i,
        (1 : ℝ) <
          (RationalCode.decode
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
              u i) : ℝ))
    (j : Fin vars) :
    ∃ (τ : ℍ) (p : AffineBlochParameters),
      p.nu = physicalColumnNu (B O) j ∧
      p.kappa = physicalColumnKappa (B O) j ∧
      p.tau 0 = τ ∧
      p.w 0 = 0 ∧
      p.c0 ≠ 0 ∧
      (∀ t,
        jacobiTheta1 (p.xi t) (p.tau t : ℂ) ≠ 0) ∧
      (fun t ↦ (linkedColumn (B O) j t).jacobi) =
        p.jacobiBlochPath := by
  let z : ℝ → JacobiState ℂ :=
    fun t ↦ (linkedColumn (B O) j t).jacobi
  have hzLinked :=
    physicalLinkedColumn_isPiScaledTrajectory
      (B O) hscale hp j
  have hz :
      IsScaledJacobiTrajectory
        ((Real.pi : ℂ) *
          (physicalColumnNu (B O) j : ℂ))
        ((Real.pi : ℂ) * Complex.I *
          (physicalColumnKappa (B O) j : ℂ))
        z := by
    simpa only [z] using hzLinked.jacobi
  obtain ⟨τ, hp2, hp3, hp4, hH⟩ :=
    standardizedLinkedColumn_exists_canonicalRootSeed
      O hscale hp j
  have hp2' :
      (z 0).p2 = (canonicalUnaryRoots τ).p2 := by
    simpa only [z, standardizedLinkedColumn, mul_zero] using hp2
  have hp3' :
      (z 0).p3 = (canonicalUnaryRoots τ).p3 := by
    simpa only [z, standardizedLinkedColumn, mul_zero] using hp3
  have hp4' :
      (z 0).p4 = (canonicalUnaryRoots τ).p4 := by
    simpa only [z, standardizedLinkedColumn, mul_zero] using hp4
  have hH' :
      (z 0).H = (canonicalUnaryRoots τ).H := by
    simpa only [z, standardizedLinkedColumn, mul_zero] using hH
  have hR1 :
      JacobiState.residualR1 (z 0) = 0 := by
    simpa only [linkedJacobiResidual, z] using
      linkedColumn_residual_zero
        (B O) hscale j 0 .thetaQuadricOne
  have hR2 :
      JacobiState.residualR2 (z 0) = 0 := by
    simpa only [linkedJacobiResidual, z] using
      linkedColumn_residual_zero
        (B O) hscale j 0 .thetaQuadricTwo
  have hreciprocal :
      ∀ t, (z t).U * (z t).T1 = 1 := by
    intro t
    have h :=
      linkedColumn_residual_zero
        (B O) hscale j t .reciprocalChart
    change JacobiState.residualRU (z t) = 0 at h
    exact sub_eq_zero.mp h
  obtain
      ⟨p, hpnu, hpkappa, hptau, hpw, hc0,
        hpregular, hpath⟩ :=
    exists_affineBlochParameters_with_c0_ne_zero_eq_of_canonical_residual_at
      τ 0
      (physicalColumnNu (B O) j)
      (physicalColumnKappa (B O) j)
      0 hz hp2' hp3' hp4' hH' hR1 hR2 hreciprocal
  exact
    ⟨τ, p, hpnu, hpkappa, hptau, hpw, hc0,
      hpregular, hpath⟩

/-- **Selected physical columns supply classified moment-series seeds.**

The existentially selected gauge constant and initial phase have no
mathematical ambiguity: each is given by an explicit formula from the
actual detector state at physical time zero. -/
theorem physicalColumn_exists_classifiedSeed
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (hp :
      ∀ i,
        (1 : ℝ) <
          (RationalCode.decode
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
              u i) : ℝ))
    (j : Fin vars) :
    ∃ (τ : ℍ) (p : AffineBlochParameters) (d : ℂ)
        (phase₀ :
          Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
            Circle),
      p.tau 0 = τ ∧
      p.w 0 = 0 ∧
      p.c0 ≠ 0 ∧
      ClassifiedSeed
        (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
        (B O).physicalPoint
        (affinePoint O.point)
        (initialController (B O))
        phase₀ j p d 0 := by
  obtain
      ⟨τ, p, hpnu, hpkappa, hptau, hpw, hc0,
        _hpregular, hpath⟩ :=
    physicalJacobiColumn_exists_affineBlochParameters
      O hscale hp j
  let phase₀ := physicalInitialPhase O hscale
  let gaugeValue : ℂ :=
    ((FixedDetectorReverseTrajectoryCrosswalk.recoveredState
      (B O).physicalPoint 0).base.base.gauge j : ℂ)
  let d : ℂ :=
    gaugeConstantForValue p gaugeValue 0
  have hcontrollers :
      (FixedDetectorReverseTrajectoryCrosswalk.recoveredState
          (B O).physicalPoint 0).base.base.source.controllers =
        CanonicalFixedDetectorTrajectory.clockPath
          (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
          (initialController (B O)) phase₀ 0 := by
    have hlocked :=
      clockState_eq_lockedStateFamily O hscale hp 0
    have hrecovered :=
      clockState_eq_recoveredControllers O 0
    have hinitialController :
        HGAS.Clocks.LockedControllerPhaseCompleteCurve.initialController
            (clockPoint (B O)) =
          initialController (B O) := by
      funext i
      simp only [
        HGAS.Clocks.LockedControllerPhaseCompleteCurve.initialController,
        clockPoint,
        ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint,
        ControllerPhaseProductPolynomialCode.state_point,
        initialController]
    calc
      (FixedDetectorReverseTrajectoryCrosswalk.recoveredState
          (B O).physicalPoint 0).base.base.source.controllers =
          ControllerPhaseProductPolynomialCode.state
            (clockPoint (B O) 0) := by
        simpa only using hrecovered.symm
      _ =
          HGAS.Clocks.LockedControllerPhaseTrajectory.stateFamily
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
            (HGAS.Clocks.LockedControllerPhaseCompleteCurve.initialController
              (clockPoint (B O)))
            (HGAS.Clocks.LockedControllerPhaseCompleteCurve.initialPhase
              (clockPoint (B O))
              (fun i ↦
                (clockPoint_onClockCircles
                  (B O) hscale 0 i).2))
            0 := by
        simpa only using hlocked
      _ =
          CanonicalFixedDetectorTrajectory.clockPath
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
            (initialController (B O)) phase₀ 0 := by
        rw [hinitialController]
        rfl
  have hreciprocal :
      ∀ t, 0 ≤ t →
        ((FixedDetectorReverseTrajectoryCrosswalk.recoveredState
            (B O).physicalPoint t).base.base.source.linked j).jacobi.U *
          ((FixedDetectorReverseTrajectoryCrosswalk.recoveredState
            (B O).physicalPoint t).base.base.source.linked j).jacobi.T1 =
        1 := by
    intro t _ht
    have h :=
      linkedColumn_residual_zero
        (B O) hscale j t .reciprocalChart
    change
      JacobiState.residualRU
        ((FixedDetectorReverseTrajectoryCrosswalk.recoveredState
          (B O).physicalPoint t).base.base.source.linked j).jacobi =
        0 at h
    exact sub_eq_zero.mp h
  have hcore :
      jacobiCorePoint
          ((FixedDetectorReverseTrajectoryCrosswalk.recoveredState
            (B O).physicalPoint 0).base.base.source.linked j).jacobi =
        jacobiCorePoint (p.jacobiBlochPath 0) := by
    exact congrArg jacobiCorePoint (congrFun hpath 0)
  have hgauge :
      (FixedDetectorReverseTrajectoryCrosswalk.recoveredState
          (B O).physicalPoint 0).base.base.gauge j =
        p.fourthRootGauge d 0 := by
    exact
      (fourthRootGauge_gaugeConstantForValue
        p gaugeValue 0).symm
  have hclocks :
      MatchesDetectorClocksRealPi p
        (CanonicalFixedDetectorTrajectory.omegaFrequency
          (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
          (initialController (B O)) j)
        (CanonicalFixedDetectorTrajectory.numberFrequency
          (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
          (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
          (initialController (B O)) j) := by
    exact ⟨hpkappa, hpnu⟩
  refine
    ⟨τ, p, d, phase₀, hptau, hpw, hc0, ?_⟩
  refine {
    normalized := {
      structured :=
        physicalPoint_isForwardStructuredTrajectory (B O)
      controller_lock := ?_
      controllers_zero := hcontrollers
      reciprocal := hreciprocal
      jacobi_core_zero := hcore
      gauge_zero := hgauge
      clocks := hclocks
      c0_ne_zero := hc0
    }
    recurrenceTime_nonnegative := le_rfl
    recurrent :=
      physicalJacobiColumn_forwardRecurrentAt (B O) j
    omega_ne_zero :=
      columnOmega_ne_zero (B O) hscale hp j
  }
  intro i
  simpa only [initialController] using
    controller_equilibrium_at_zero (B O) hscale hp i

end SelectedBidirectionalValidityOrbit

end

end
  HGAS.NormalizedCorrectedFixedDetectorPhysicalClassifiedSeed
