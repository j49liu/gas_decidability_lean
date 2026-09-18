import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorColumnCharacters
import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorTwoSidedStructuredOrbit
import HGAS.Clocks.ControllerPhaseProductTorusObservation
import Mathlib.Tactic

/-!
# The actual torus phase of a selected normalized detector orbit

The compact-source argument selects a physical detector orbit whose clock
phases need not start at one.  Nevertheless, the repaired validity
coordinate forces every real phase pair `(c,d)` to satisfy

```text
                             c² + d² = 1.
```

Thus every stored pair determines an honest point of the multiplicative
unit circle, and hence a point of the additive torus `ℝ/ℤ`.  This file
defines that *actual* phase directly from the selected physical state.

The polynomial compiler stores fourth roots of the arithmetic clocks.
Accordingly, the detector phase is four times the fundamental additive
phase, after reindexing `Fin (vars + eqs)` as
`Fin vars ⊕ Fin eqs`.  The main theorem proves pointwise that every
arithmetic Fourier character at this detector phase is literally the
corresponding compiled signed-power character.  No canonical initial
phase and no Jacobi classification is used.
-/

namespace
  HGAS.NormalizedCorrectedFixedDetectorSelectedPhysicalPhase

open HGAS
open HGAS.Clocks
open Clocks.ControllerPhaseProductCharacterCode
open NormalizedCorrectedFixedDetectorTwoSidedValidityOrbit
open NormalizedCorrectedFixedDetectorBidirectionalValidityOrbit
open NormalizedCorrectedFixedDetectorTwoSidedStructuredOrbit
open
  NormalizedCorrectedFixedDetectorTwoSidedStructuredOrbit.SelectedTwoSidedValidityOrbit

noncomputable section

variable {eqs vars : ℕ}
variable
  {u :
    NormalizedCorrectedFixedDetectorCompactSourceCode.CompilerInput
      eqs vars}

namespace SelectedBidirectionalValidityOrbit

variable (O : SelectedBidirectionalValidityOrbit u)

private abbrev B : SelectedTwoSidedValidityOrbit u :=
  O.toSelectedTwoSidedValidityOrbit

/-- The structured controller family read from the selected physical
detector state. -/
def physicalControllers (t : ℝ) :
    ControllerPhaseProductPolynomialCode.StateFamily
      (FixedDetectorPolynomialCode.clockCount eqs vars) ℝ :=
  (FixedDetectorReverseTrajectoryCrosswalk.recoveredState
    (B O).physicalPoint t).base.base.source.controllers

/-- Every physical clock phase lies on its unit circle. -/
theorem physicalControllers_phaseRadiusSq
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (t : ℝ) (i : Fin (FixedDetectorPolynomialCode.clockCount eqs vars)) :
    Controller.phaseRadiusSq
        ((physicalControllers O t i).phase) = 1 := by
  exact (clockRadii_one_physicalTime (B O) hscale t).2 i

/-- Norm-one form of the same physical phase-circle statement. -/
theorem physicalControllers_onPhaseCircles
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (t : ℝ) :
    OnPhaseCircles (physicalControllers O t) := by
  intro i
  exact
    NormalizedCorrectedFixedDetectorNormalizationConsequences.norm_phaseValue_eq_one_of_radiusSq
      (physicalControllers O t) i
      (physicalControllers_phaseRadiusSq O hscale t i)

/-- The actual fundamental additive-torus phase, obtained directly from
the real unit-circle coordinates stored in the physical state. -/
def physicalFundamentalPhase
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (t : ℝ) :
    UnitAddTorus (Fin (FixedDetectorPolynomialCode.clockCount eqs vars)) :=
  ControllerPhaseProductTorusObservation.phase
    (physicalControllers O)
    (fun s i ↦ physicalControllers_phaseRadiusSq O hscale s i)
    t

/-- The arithmetic detector phase.  Its coordinate at `phase` is four
times the actual fundamental clock angle indexed by
`finSumFinEquiv phase`. -/
def physicalDetectorPhase
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (t : ℝ) :
    UnitAddTorus (DetectorPhase eqs vars) :=
  fun phase ↦
    (4 : ℤ) •
      physicalFundamentalPhase O hscale t (finSumFinEquiv phase)

/-- Flattening an arithmetic character is exactly evaluation on four
times the reindexed fundamental phase. -/
theorem mFourier_physicalDetectorPhase_eq_fundamental
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (a : DetectorPhase eqs vars → ℤ)
    (t : ℝ) :
    UnitAddTorus.mFourier a
        (physicalDetectorPhase O hscale t) =
      UnitAddTorus.mFourier
        (DetectorCharacterCode.flattenCharacter a)
        (physicalFundamentalPhase O hscale t) := by
  classical
  unfold UnitAddTorus.mFourier physicalDetectorPhase
    DetectorCharacterCode.flattenCharacter
  simp only [ContinuousMap.coe_mk]
  rw [← finSumFinEquiv.prod_comp]
  apply Finset.prod_congr rfl
  intro i _
  rw [fourier_apply, fourier_apply]
  rw [mul_zsmul]
  simp only [finSumFinEquiv.symm_apply_apply, smul_smul]
  rw [mul_comm]

/-- **Actual-phase character crosswalk.**  Every detector-torus Fourier
character is the literal compiled Laurent character evaluated on the
selected physical clocks. -/
theorem mFourier_physicalDetectorPhase
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (a : DetectorPhase eqs vars → ℤ)
    (t : ℝ) :
    UnitAddTorus.mFourier a
        (physicalDetectorPhase O hscale t) =
      characterValue
        (DetectorCharacterCode.flattenCharacter a)
        (physicalControllers O t) := by
  rw [mFourier_physicalDetectorPhase_eq_fundamental O hscale a t]
  exact
    ControllerPhaseProductTorusObservation.mFourier_phase
      (physicalControllers O)
      (fun s i ↦ physicalControllers_phaseRadiusSq O hscale s i)
      t
      (DetectorCharacterCode.flattenCharacter a)

/-- The selected Poisson argument character is the corresponding torus
Fourier character at the actual detector phase. -/
theorem poissonCharacterValue_eq_mFourier
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (j : Fin vars) (t : ℝ) :
    DetectorPoissonReciprocalCode.poissonCharacterValue
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
        ((B O).physicalState t).base j =
      UnitAddTorus.mFourier
        (DetectorCharacterCode.poissonArgumentCharacter
          (NormalizedCorrectedFixedDetectorCompactSourceCode.system u) j)
        (physicalDetectorPhase O hscale t) := by
  symm
  rw [mFourier_physicalDetectorPhase O hscale]
  rfl

end SelectedBidirectionalValidityOrbit

end

end HGAS.NormalizedCorrectedFixedDetectorSelectedPhysicalPhase
