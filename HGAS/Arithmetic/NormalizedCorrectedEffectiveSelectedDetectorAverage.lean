import HGAS.Analysis.CesaroMeanAtLinearity
import HGAS.Arithmetic.DetectorFourierCesaroArbitraryHorizon
import HGAS.Arithmetic.NormalizedCorrectedEffectiveSelectedDetectorPhase
import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorSelectedFactorization
import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorTwoSidedPhysicalMomentAverages
import Mathlib.Tactic

/-!
# The selected effective detector has a nonzero physical mean

This module composes four independent ingredients:

1. the actual detector phase is a nonresonant prime-radical torus
   translation through its selected initial phase;
2. the literal detector is a fixed nonzero twist times the expanded
   theta--Poisson detector, once its Jacobi theta outputs are identified;
3. arbitrary-horizon Cesàro averages of that Fourier detector converge to
   its Haar constant term; and
4. the Haar constant term is nonzero for a solvable DQL system.

The conclusion is stated first under the one remaining pointwise theta
identity.  A later module discharges that identity using the three
corrected Jacobi moments.
-/

noncomputable section

open Filter MeasureTheory Topology

namespace HGAS.NormalizedCorrectedEffectiveSelectedDetectorAverage

open HGAS
open NormalizedCorrectedFixedDetectorBidirectionalValidityOrbit
open NormalizedCorrectedFixedDetectorSelectedPhysicalPhase
open NormalizedCorrectedFixedDetectorSelectedFactorization
open NormalizedCorrectedEffectiveSelectedDetectorPhase
open NormalizedCorrectedFixedDetectorTwoSidedPhysicalMomentAverages
open
  NormalizedCorrectedFixedDetectorSelectedPhysicalPhase.SelectedBidirectionalValidityOrbit
open
  NormalizedCorrectedFixedDetectorSelectedFactorization.SelectedBidirectionalValidityOrbit
open
  NormalizedCorrectedEffectiveSelectedDetectorPhase.SelectedBidirectionalValidityOrbit

local instance : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs
    (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs
    (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {eqs vars : ℕ}
variable (D : DQLSystem eqs vars)

private abbrev u :
    NormalizedCorrectedFixedDetectorCompactSourceCode.CompilerInput
      eqs vars :=
  NormalizedCorrectedEffectiveCompilerInput.compilerInput D

private abbrev B
    (O : SelectedBidirectionalValidityOrbit (u D)) :=
  O.toSelectedTwoSidedValidityOrbit

/-- Pointwise theta-output identity required by the factorized detector
crosswalk.  It is intentionally a named proposition so the analytic
average theorem and the Jacobi rigidity theorem meet at a small,
auditable interface. -/
def HasCanonicalThetaOutputs
    (O : SelectedBidirectionalValidityOrbit (u D)) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    ∀ j : Fin vars,
      ((B D O).physicalState t).base.base.gauge j *
          (((B D O).physicalState t).base.base.source.linked j).jacobi.T1 =
        ∑' n : ℤ,
          DetectorFactorizedFourier.thetaTerm
            (1 / 256 : ℝ) D j n
            (physicalDetectorPhase O
              (NormalizedCorrectedEffectiveCompilerInput.compilerInput_accumulatorScale_pos
                D) t)

/-- Under the canonical theta-output identity, the literal selected
detector average converges to the fixed RHS twist times the Haar detector
integral. -/
theorem detectorComplexAverage_tendsto_twistedIntegral
    (O : SelectedBidirectionalValidityOrbit (u D))
    (htheta : HasCanonicalThetaOutputs D O) :
    Tendsto
      (fun q ↦
        Analysis.cesaroMeanAt
          (fun t ↦
            NormalizedCorrectedFixedDetectorDriftCode.detectorValue
              ((B D O).physicalState t))
          (physicalHorizon (B D O) q))
      atTop
      (𝓝
        (physicalRHSTwist O
            (NormalizedCorrectedEffectiveCompilerInput.compilerInput_accumulatorScale_pos
              D) *
          ∫ phase : UnitAddTorus (DetectorPhase eqs vars),
            expandedDetector (1 / 256 : ℝ) (1 / 2 : ℝ)
              D phase)) := by
  let hscale :=
    NormalizedCorrectedEffectiveCompilerInput.compilerInput_accumulatorScale_pos
      D
  let hp :=
    NormalizedCorrectedEffectiveCompilerInput.controllerParameters_gt_one
      eqs vars
  let phase₀ :=
    physicalDetectorPhase O hscale 0
  let frequency :=
    physicalDetectorTurnsFrequency O
  have htorus :=
    cesaroMeanAt_expandedDetector_translation_tendsto_integral
      (by norm_num : (0 : ℝ) ≤ 1 / 256)
      (by norm_num : (1 / 256 : ℝ) < 1)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
      D frequency
      (physicalDetectorTurnsFrequency_hasNoCharacter D O)
      phase₀
      (physicalHorizon_tendsto_atTop (B D O))
  have hphase :
      (fun t ↦
        expandedDetector (1 / 256 : ℝ) (1 / 2 : ℝ) D
          (Clocks.RadicalClock.torusTranslationFlow
            frequency t phase₀)) =
        (fun t ↦
          expandedDetector (1 / 256 : ℝ) (1 / 2 : ℝ) D
            (physicalDetectorPhase O hscale t)) := by
    funext t
    rw [physicalDetectorPhase_eq_translation O hscale hp t]
  rw [hphase] at htorus
  have htwisted :=
    Analysis.tendsto_cesaroMeanAt_const_mul
      (physicalRHSTwist O hscale)
      (∫ phase : UnitAddTorus (DetectorPhase eqs vars),
        expandedDetector (1 / 256 : ℝ) (1 / 2 : ℝ) D phase)
      (fun t ↦
        expandedDetector (1 / 256 : ℝ) (1 / 2 : ℝ) D
          (physicalDetectorPhase O hscale t))
      htorus
  apply htwisted.congr'
  exact
    (Analysis.eventually_cesaroMeanAt_eq_of_eqOn_nonnegative
      (physicalHorizon_tendsto_atTop (B D O))
      (fun t ht ↦
        detectorValue_eq_twist_mul_expandedDetector
          O hscale hp t ht (htheta t ht))).symm

/-- In a solvable instance the limiting twisted Haar constant is
nonzero. -/
theorem twistedIntegral_ne_zero_of_solvable
    (O : SelectedBidirectionalValidityOrbit (u D))
    (hsolvable : D.Solvable) :
    physicalRHSTwist O
          (NormalizedCorrectedEffectiveCompilerInput.compilerInput_accumulatorScale_pos
            D) *
        (∫ phase : UnitAddTorus (DetectorPhase eqs vars),
          expandedDetector (1 / 256 : ℝ) (1 / 2 : ℝ) D phase) ≠
      0 := by
  apply mul_ne_zero
  · exact
      physicalRHSTwist_ne_zero O
        (NormalizedCorrectedEffectiveCompilerInput.compilerInput_accumulatorScale_pos
          D)
  · exact
      integral_expandedDetector_ne_zero_of_solvable
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        D hsolvable

/-- **Selected-orbit contradiction.**  A solvable instance cannot have
both zero compiled detector drift average and canonical theta outputs.
The former is automatic for every selected validity orbit; hence the
three-moment theta theorem will make this conclusion unconditional. -/
theorem false_of_solvable_and_canonicalThetaOutputs
    (O : SelectedBidirectionalValidityOrbit (u D))
    (hsolvable : D.Solvable)
    (htheta : HasCanonicalThetaOutputs D O) :
    False := by
  have hnonzero :=
    twistedIntegral_ne_zero_of_solvable D O hsolvable
  have hlimit :=
    detectorComplexAverage_tendsto_twistedIntegral D O htheta
  have hzero :=
    detectorComplexAverage_tendsto_zero
      (B D O)
      (NormalizedCorrectedEffectiveCompilerInput.compilerInput_accumulatorScale_pos
        D).ne'
  exact hnonzero (tendsto_nhds_unique hlimit hzero)

end HGAS.NormalizedCorrectedEffectiveSelectedDetectorAverage
