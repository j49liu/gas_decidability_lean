import HGAS.Arithmetic.CanonicalDetectorThetaQuadraticGeometric
import HGAS.Arithmetic.NormalizedCorrectedEffectiveColumnFrequencyIrrational
import HGAS.Arithmetic.NormalizedCorrectedEffectiveSelectedDetectorAverage
import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorPhysicalClassifiedSeed
import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorThreeMomentTargetOutput
import Mathlib.Tactic

/-!
# Canonical theta outputs on the effective selected detector orbit

This file closes the three-moment identification for DQL systems in
which every variable has a nonzero linear column.

For each detector column we:

1. select its physical affine Bloch classification;
2. freeze the canonical Gaussian theta coefficients at the actual
   initial detector phase;
3. use prime-radical nonresonance to prove the linear/private clock ratio
   irrational;
4. apply the abstract three-moment target theorem; and
5. unfold the target quadratic series along the actual torus
   translation.

The result is exactly the named `HasCanonicalThetaOutputs` interface
consumed by the effective detector-average contradiction.  General DQL
systems enter this theorem only after the solvability-preserving
nonzero-linear-column augmentation.
-/

noncomputable section

namespace HGAS.NormalizedCorrectedEffectiveCanonicalThetaOutputs

open HGAS
open HGAS.Clocks
open HGAS.Modular
open DQLNonzeroLinearAugmentation
open CanonicalDetectorThetaQuadraticGeometric
open NormalizedCorrectedEffectiveCompilerInput
open NormalizedCorrectedEffectiveColumnFrequencyIrrational
open NormalizedCorrectedEffectiveSelectedDetectorAverage
open NormalizedCorrectedFixedDetectorBidirectionalValidityOrbit
open NormalizedCorrectedFixedDetectorColumnTrajectory
open NormalizedCorrectedFixedDetectorPhysicalClassifiedSeed
open NormalizedCorrectedFixedDetectorSelectedFactorization
open NormalizedCorrectedFixedDetectorSelectedPhysicalPhase
open NormalizedCorrectedFixedDetectorThreeMomentTargetOutput
open NormalizedCorrectedFixedDetectorTwoSidedStructuredOrbit
open NormalizedCorrectedFixedDetectorTwoSidedValidityOrbit
open
  NormalizedCorrectedFixedDetectorPhysicalClassifiedSeed.SelectedBidirectionalValidityOrbit
open
  NormalizedCorrectedFixedDetectorThreeMomentTargetOutput.SelectedTwoSidedValidityOrbit
open
  NormalizedCorrectedFixedDetectorSelectedFactorization.SelectedBidirectionalValidityOrbit
open
  NormalizedCorrectedFixedDetectorSelectedPhysicalPhase.SelectedBidirectionalValidityOrbit
open
  NormalizedCorrectedFixedDetectorTwoSidedStructuredOrbit.SelectedTwoSidedValidityOrbit

variable {eqs vars : ℕ}
variable (D : DQLSystem eqs vars)

private abbrev u :=
  NormalizedCorrectedEffectiveCompilerInput.compilerInput D

variable
  (O : SelectedBidirectionalValidityOrbit (u D))

private abbrev B :=
  O.toSelectedTwoSidedValidityOrbit

/-- Pairing the private detector character with the physical frequency in
turns recovers the literal private angular frequency of the classified
column. -/
theorem privateAngularFrequency_physicalDetectorTurnsFrequency
    (j : Fin vars) :
    privateAngularFrequency j (physicalDetectorTurnsFrequency O) =
      CanonicalFixedDetectorTrajectory.omegaFrequency
        (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters (u D))
        (SelectedTwoSidedValidityOrbit.initialController (B D O)) j := by
  symm
  rw [CanonicalFixedDetectorFourierCrosswalk.omegaFrequency_eq_characterFrequency]
  exact
    characterFrequency_eq_two_pi_mul_physicalPairing
      D O (DetectorCharacterCode.privateCharacter j)

/-- The analogous pairing for the linear column recovers the literal
elliptic-number angular frequency. -/
theorem linearAngularFrequency_physicalDetectorTurnsFrequency
    (j : Fin vars) :
    linearAngularFrequency D j (physicalDetectorTurnsFrequency O) =
      CanonicalFixedDetectorTrajectory.numberFrequency
        (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters (u D))
        D
        (SelectedTwoSidedValidityOrbit.initialController (B D O)) j := by
  symm
  rw [CanonicalFixedDetectorFourierCrosswalk.numberFrequency_eq_characterFrequency]
  exact
    characterFrequency_eq_two_pi_mul_physicalPairing
      D O (DetectorCharacterCode.linearCharacter D j)

/-- **Canonical theta-output endpoint for nonzero linear columns.** -/
theorem hasCanonicalThetaOutputs
    (hcolumns : HasNonzeroLinearColumn D) :
    HasCanonicalThetaOutputs D O := by
  intro t ht j
  let hscale :=
    NormalizedCorrectedEffectiveCompilerInput.compilerInput_accumulatorScale_pos
      D
  let hp :=
    NormalizedCorrectedEffectiveCompilerInput.controllerParameters_gt_one
      eqs vars
  obtain ⟨τ, p, d, phase₀, hτ, hw, hc0, hseed⟩ :=
    physicalColumn_exists_classifiedSeed O hscale hp j
  let target : ℤ → ℂ :=
    fixedPhaseThetaCoefficient (1 / 256 : ℝ) D j
      (physicalDetectorPhase O hscale 0)
  have hTarget : IsQuadraticGeometric target := by
    exact
      canonicalFixedPhaseThetaCoefficient_isQuadraticGeometric
        D j (physicalDetectorPhase O hscale 0)
  have hlinear :
      DetectorCharacterCode.linearCharacter D j ≠ 0 :=
    linearCharacter_ne_zero_of_hasNonzeroLinearColumn D hcolumns j
  have hratio :
      Irrational
        (CanonicalFixedDetectorTrajectory.numberFrequency
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters (u D))
            D (SelectedTwoSidedValidityOrbit.initialController (B D O)) j /
          CanonicalFixedDetectorTrajectory.omegaFrequency
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters (u D))
            (SelectedTwoSidedValidityOrbit.initialController (B D O)) j) := by
    exact
      numberFrequency_div_omegaFrequency_irrational
        D O hcolumns j
  have hcontrollers :
      physicalControllers O 0 =
        CanonicalFixedDetectorTrajectory.clockPath
          (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters (u D))
          (SelectedTwoSidedValidityOrbit.initialController (B D O))
          phase₀ 0 := by
    simpa only [physicalControllers] using
      hseed.normalized.controllers_zero
  have hplusTarget :
      ControllerPhaseProductCharacterCode.characterValue
            (FixedDetectorMomentCode.jacobiPlusExponent D j)
            (CanonicalFixedDetectorTrajectory.clockPath
              (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
                (u D))
              (SelectedTwoSidedValidityOrbit.initialController (B D O))
              phase₀ 0) *
          target 1 =
        (1 / 256 : ℂ) := by
    rw [← hcontrollers]
    change
      ControllerPhaseProductCharacterCode.characterValue
            (FixedDetectorMomentCode.jacobiPlusExponent D j)
            (physicalControllers O 0) *
          fixedPhaseThetaCoefficient (1 / 256 : ℝ) D j
            (physicalDetectorPhase O hscale 0) 1 =
        (1 / 256 : ℂ)
    convert
      characterValue_jacobiPlusExponent_mul_physicalThetaCoefficient_one
        O hscale (1 / 256 : ℝ) D j using 1
    all_goals norm_num
  have hminusTarget :
      ControllerPhaseProductCharacterCode.characterValue
            (FixedDetectorMomentCode.jacobiMinusExponent D j)
            (CanonicalFixedDetectorTrajectory.clockPath
              (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
                (u D))
              (SelectedTwoSidedValidityOrbit.initialController (B D O))
              phase₀ 0) *
          target (-1) =
        (1 / 256 : ℂ) := by
    rw [← hcontrollers]
    change
      ControllerPhaseProductCharacterCode.characterValue
            (FixedDetectorMomentCode.jacobiMinusExponent D j)
            (physicalControllers O 0) *
          fixedPhaseThetaCoefficient (1 / 256 : ℝ) D j
            (physicalDetectorPhase O hscale 0) (-1) =
        (1 / 256 : ℂ)
    convert
      characterValue_jacobiMinusExponent_mul_physicalThetaCoefficient_neg_one
        O hscale (1 / 256 : ℝ) D j using 1
    all_goals norm_num
  have houtput :=
    gaugedOutput_eq_targetSeries
        (B D O) hscale
        (SelectedTwoSidedValidityOrbit.initialController (B D O))
        phase₀
        (CompactAccumulatorPipelineCode.AllAffineCompactSourceChart.affinePoint
          O.point)
        j p d 0 hseed target hTarget hlinear hratio
        hplusTarget hminusTarget t ht
  have hprivate :
      privateAngularFrequency j (physicalDetectorTurnsFrequency O) ≠ 0 := by
    rw [privateAngularFrequency_physicalDetectorTurnsFrequency D O j]
    exact hseed.omega_ne_zero
  have htargetSeries :=
    quadraticMomentSeries_fixedPhaseThetaCoefficient_eq_thetaSum
      (1 / 256 : ℝ) D j
      (physicalDetectorTurnsFrequency O)
      (physicalDetectorPhase O hscale 0)
      hprivate t
  rw [privateAngularFrequency_physicalDetectorTurnsFrequency D O j,
    linearAngularFrequency_physicalDetectorTurnsFrequency D O j] at htargetSeries
  rw [← physicalDetectorPhase_eq_translation O hscale hp t] at htargetSeries
  simpa only [recoveredState_physicalPoint, target] using
    houtput.trans htargetSeries

end HGAS.NormalizedCorrectedEffectiveCanonicalThetaOutputs
