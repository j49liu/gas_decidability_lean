import HGAS.Arithmetic.FixedDetectorJacobiMomentSeries
import HGAS.Arithmetic.FixedDetectorSelectorCharacterFrequency
import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorColumnStandardization
import HGAS.Clocks.LockedControllerPhaseCompleteCurve
import HGAS.Modular.HorizontalThetaFirstMoment
import Mathlib.Tactic

/-!
# Exact selector characters on a standardized detector column

The selected detector orbit need not start with all phase clocks equal to
one.  The only legitimate conclusion is therefore a constant unit phase
times the expected exponential.

This file derives that conclusion from the complete controller--phase ODE,
rather than assuming a canonical initial phase.  Before standardization,
the first and root-half characters have frequencies `-ω_j` and
`-ω_j/2`.  After the literal time change `a_j = π/ω_j`, they become

```text
                 η₁ exp(-π i t),
                 η₂ exp(-π i t / 2),
```

where both constants have norm one.
-/

namespace HGAS.NormalizedCorrectedFixedDetectorColumnCharacters

open HGAS
open HGAS.Clocks
open HGAS.Modular
open Clocks.ControllerPhaseProductCharacterCode
open NormalizedCorrectedFixedDetectorTwoSidedValidityOrbit
open NormalizedCorrectedFixedDetectorBidirectionalValidityOrbit
open NormalizedCorrectedFixedDetectorTwoSidedControllerLocking
open NormalizedCorrectedFixedDetectorTwoSidedCompleteControllerLocking
open NormalizedCorrectedFixedDetectorColumnTrajectory
open NormalizedCorrectedFixedDetectorColumnStandardization
open NormalizedCorrectedFixedDetectorTwoSidedValidityOrbit.SelectedTwoSidedValidityOrbit
open
  NormalizedCorrectedFixedDetectorTwoSidedControllerLocking.SelectedTwoSidedValidityOrbit
open
  NormalizedCorrectedFixedDetectorTwoSidedCompleteControllerLocking.SelectedTwoSidedValidityOrbit
open NormalizedCorrectedFixedDetectorColumnTrajectory.SelectedTwoSidedValidityOrbit
open NormalizedCorrectedFixedDetectorColumnStandardization.SelectedTwoSidedValidityOrbit
open
  NormalizedCorrectedFixedDetectorBidirectionalValidityOrbit.SelectedBidirectionalValidityOrbit

noncomputable section

variable {eqs vars : ℕ}
variable
  {u :
    NormalizedCorrectedFixedDetectorCompactSourceCode.CompilerInput
      eqs vars}

/-- Standard negative half-harmonic character used by the `p₂` selector. -/
def standardRootHalfCharacter (t : ℝ) : ℂ :=
  HGAS.Analysis.realFrequencyExponential (-Real.pi / 2) t

namespace SelectedBidirectionalValidityOrbit

variable (O : SelectedBidirectionalValidityOrbit u)

private abbrev B :=
  O.toSelectedTwoSidedValidityOrbit

/-- Reading the structured state of the raw clock point recovers the
controller family in the detector state. -/
theorem clockState_eq_recoveredControllers
    (t : ℝ) :
    ControllerPhaseProductPolynomialCode.state
        (clockPoint (B O) t) =
      (FixedDetectorReverseTrajectoryCrosswalk.recoveredState
        (B O).physicalPoint t).base.base.source.controllers := by
  simp [clockPoint,
    ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint]

/-- The selected complete clock curve is exactly the explicit locked
phase-rotation curve through its actual initial phase point. -/
theorem clockState_eq_lockedStateFamily
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
    (t : ℝ) :
    ControllerPhaseProductPolynomialCode.state
        (clockPoint (B O) t) =
      LockedControllerPhaseTrajectory.stateFamily
        (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
        (HGAS.Clocks.LockedControllerPhaseCompleteCurve.initialController
          (clockPoint (B O)))
        (HGAS.Clocks.LockedControllerPhaseCompleteCurve.initialPhase
          (clockPoint (B O))
          (fun i ↦
            (clockPoint_onClockCircles (B O) hscale 0 i).2))
        t := by
  exact
    HGAS.Clocks.LockedControllerPhaseCompleteCurve.state_curve_eq_stateFamily
      (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
      (clockPoint (B O))
      (clockPoint_isIntegralCurve (B O))
      (fun i ↦
        (clockPoint_onClockCircles (B O) hscale 0 i).2)
      (by
        intro i
        simpa [
          HGAS.Clocks.LockedControllerPhaseCompleteCurve.initialController,
          clockState_eq_recoveredControllers O 0,
          initialController] using
          controller_equilibrium_at_zero (B O) hscale hp i)
      t

/-- Closed formula for every integral character along the actual physical
detector clock curve. -/
theorem characterValue_physical_eq_initial_mul_exponential
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
    (exponents :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → ℤ)
    (t : ℝ) :
    characterValue exponents
        (FixedDetectorReverseTrajectoryCrosswalk.recoveredState
          (B O).physicalPoint t).base.base.source.controllers =
      characterValue exponents
        (FixedDetectorReverseTrajectoryCrosswalk.recoveredState
          (B O).physicalPoint 0).base.base.source.controllers *
        HGAS.Analysis.realFrequencyExponential
          (LockedControllerPhaseTrajectory.characterFrequency
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
            (initialController (B O)) exponents) t := by
  let hphase :
      ∀ i,
        Controller.phaseRadiusSq
          (ControllerPhaseProductPolynomialCode.state
            (clockPoint (B O) 0) i).phase = 1 :=
    fun i ↦ (clockPoint_onClockCircles (B O) hscale 0 i).2
  rw [← clockState_eq_recoveredControllers O t]
  rw [clockState_eq_lockedStateFamily O hscale hp t]
  rw [
    LockedControllerPhaseTrajectory.characterValue_stateFamily_eq_initial_mul_exponential]
  rw [
    HGAS.Clocks.LockedControllerPhaseCompleteCurve.stateFamily_initial_eq
        (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
        (clockPoint (B O)) hphase]
  rw [clockState_eq_recoveredControllers O 0]
  congr 3
  funext i
  simp [
    HGAS.Clocks.LockedControllerPhaseCompleteCurve.initialController,
    clockState_eq_recoveredControllers O 0,
    initialController]

/-- Initial phase of the first-harmonic character. -/
def unaryFirstInitialPhase (j : Fin vars) : ℂ :=
  characterValue
    (FixedDetectorMomentCode.unaryFirstHarmonicExponent j)
    (FixedDetectorReverseTrajectoryCrosswalk.recoveredState
      (B O).physicalPoint 0).base.base.source.controllers

/-- Initial phase of the root-half character. -/
def rootHalfInitialPhase (j : Fin vars) : ℂ :=
  characterValue
    (FixedDetectorMomentCode.rootHalfExponent j)
    (FixedDetectorReverseTrajectoryCrosswalk.recoveredState
      (B O).physicalPoint 0).base.base.source.controllers

/-- The first-harmonic initial factor has norm one. -/
theorem norm_unaryFirstInitialPhase
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (j : Fin vars) :
    ‖unaryFirstInitialPhase O j‖ = 1 := by
  apply norm_characterValue_eq_one
  intro i
  have h :=
    (clockPoint_onClockCircles (B O) hscale 0 i).2
  simpa [clockState_eq_recoveredControllers O 0] using
    NormalizedCorrectedFixedDetectorNormalizationConsequences.norm_phaseValue_eq_one_of_radiusSq
        (ControllerPhaseProductPolynomialCode.state
          (clockPoint (B O) 0)) i h

/-- The root-half initial factor has norm one. -/
theorem norm_rootHalfInitialPhase
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (j : Fin vars) :
    ‖rootHalfInitialPhase O j‖ = 1 := by
  apply norm_characterValue_eq_one
  intro i
  have h :=
    (clockPoint_onClockCircles (B O) hscale 0 i).2
  simpa [clockState_eq_recoveredControllers O 0] using
    NormalizedCorrectedFixedDetectorNormalizationConsequences.norm_phaseValue_eq_one_of_radiusSq
        (ControllerPhaseProductPolynomialCode.state
          (clockPoint (B O) 0)) i h

/-- At standardized time, the first-harmonic character is its initial
unit phase times `exp(-πit)`. -/
theorem unaryFirstCharacter_standardized
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
    (j : Fin vars)
    (t : ℝ) :
    characterValue
        (FixedDetectorMomentCode.unaryFirstHarmonicExponent j)
        (FixedDetectorReverseTrajectoryCrosswalk.recoveredState
          (B O).physicalPoint
          (columnStandardScale (B O) j * t)).base.base.source.controllers =
      unaryFirstInitialPhase O j *
        standardUnaryFirstCharacter t := by
  rw [
    characterValue_physical_eq_initial_mul_exponential
      O hscale hp _ _]
  rw [
    HGAS.FixedDetectorSelectorCharacterFrequency.characterFrequency_unaryFirstHarmonicExponent]
  change
    unaryFirstInitialPhase O j *
        HGAS.Analysis.realFrequencyExponential
          (-columnOmega (B O) j)
          (columnStandardScale (B O) j * t) =
      unaryFirstInitialPhase O j * standardUnaryFirstCharacter t
  unfold standardUnaryFirstCharacter
  congr 1
  unfold HGAS.Analysis.realFrequencyExponential
  congr 1
  have hnormal :=
    columnStandardScale_mul_omega (B O) hscale hp j
  calc
    (((-columnOmega (B O) j : ℝ) : ℂ) * Complex.I) *
          ((columnStandardScale (B O) j * t : ℝ) : ℂ) =
        (-((columnStandardScale (B O) j *
            columnOmega (B O) j) : ℝ) : ℂ) *
          Complex.I * (t : ℂ) := by
            push_cast
            ring
    _ = (((-Real.pi : ℝ) : ℂ) * Complex.I * (t : ℂ)) := by
      rw [hnormal]
      push_cast
      rfl

/-- At standardized time, the root-half character is its initial unit
phase times `exp(-πit/2)`. -/
theorem rootHalfCharacter_standardized
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
    (j : Fin vars)
    (t : ℝ) :
    characterValue
        (FixedDetectorMomentCode.rootHalfExponent j)
        (FixedDetectorReverseTrajectoryCrosswalk.recoveredState
          (B O).physicalPoint
          (columnStandardScale (B O) j * t)).base.base.source.controllers =
      rootHalfInitialPhase O j *
        standardRootHalfCharacter t := by
  rw [
    characterValue_physical_eq_initial_mul_exponential
      O hscale hp _ _]
  rw [
    HGAS.FixedDetectorSelectorCharacterFrequency.characterFrequency_rootHalfExponent]
  change
    rootHalfInitialPhase O j *
        HGAS.Analysis.realFrequencyExponential
          (-columnOmega (B O) j / 2)
          (columnStandardScale (B O) j * t) =
      rootHalfInitialPhase O j * standardRootHalfCharacter t
  unfold standardRootHalfCharacter
  congr 1
  unfold HGAS.Analysis.realFrequencyExponential
  congr 1
  have hnormal :=
    columnStandardScale_mul_omega (B O) hscale hp j
  calc
    (((-columnOmega (B O) j / 2 : ℝ) : ℂ) * Complex.I) *
          ((columnStandardScale (B O) j * t : ℝ) : ℂ) =
        ((-((columnStandardScale (B O) j *
            columnOmega (B O) j) : ℝ) / 2 : ℝ) : ℂ) *
          Complex.I * (t : ℂ) := by
            push_cast
            ring
    _ = (((-Real.pi / 2 : ℝ) : ℂ)) *
          Complex.I * (t : ℂ) := by
      rw [hnormal]

end SelectedBidirectionalValidityOrbit

end

end HGAS.NormalizedCorrectedFixedDetectorColumnCharacters
