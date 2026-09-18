import HGAS.Arithmetic.NormalizedCorrectedEffectiveSelectedDetectorAverage
import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorBidirectionalValidityOrbit
import Mathlib.Tactic

/-!
# From canonical theta outputs to the yes-instance nonzero-mean field

If every conditional drift coordinate vanished, the compact recurrence
selection theorem would produce a bidirectionally recurrent validity
orbit.  Canonical theta outputs on that orbit contradict the solvable
detector mean theorem.  This module records that short logical passage in
the exact types used by the compact-accumulator gap certificate.
-/

noncomputable section

open Function MeasureTheory Set

namespace HGAS.NormalizedCorrectedEffectiveNonzeroMeanFromTheta

open HGAS
open CompactAccumulatorPipelineCode
open
  CompactAccumulatorPipelineCode.AllAffineCompactSourceChart
open NormalizedCorrectedFixedDetectorTwoSidedValidityOrbit
open NormalizedCorrectedFixedDetectorBidirectionalValidityOrbit
open NormalizedCorrectedEffectiveSelectedDetectorAverage

variable {eqs vars : ℕ}
variable (D : DQLSystem eqs vars)

private abbrev u :
    NormalizedCorrectedFixedDetectorCompactSourceCode.CompilerInput
      eqs vars :=
  NormalizedCorrectedEffectiveCompilerInput.compilerInput D

/-- Positive mass of the common finite central chart. -/
def HasPositiveFiniteInterior
    (μ :
      Dynamics.InvariantProbabilityMeasure
        (compactFlow (u D))) : Prop :=
  (μ.measure :
      Measure
        (AllAffineCompactSourceChart.SourceSpace
          (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDimension
            eqs vars)
          (NormalizedCorrectedFixedDetectorCompactSourceCode.driftDimension
            vars)))
      (sourceFiniteInteriorSet
        (m :=
          NormalizedCorrectedFixedDetectorCompactSourceCode.driftDimension
            vars)
        (layout
          (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDimension
            eqs vars))) ≠ 0

/-- Every conditional base drift coordinate has zero integral. -/
def ConditionalBaseDriftZero
    (μ :
      Dynamics.InvariantProbabilityMeasure
        (compactFlow (u D)))
    (hpos : HasPositiveFiniteInterior D μ) : Prop :=
  ∀ i :
      Fin
        (NormalizedCorrectedFixedDetectorCompactSourceCode.driftDimension
          vars),
    (∫ b,
      baseDriftBCF
        (layout
          (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDimension
            eqs vars))
        (2 * speedExponent D)
        (NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          (u D))
        (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode D)
        b i
      ∂((conditionalBaseProbability
          (layout
            (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDimension
              eqs vars))
          (speedExponent D)
          (2 * speedExponent D)
          (NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
            (u D))
          (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
              (u D))
            D)
          (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode_termsDegreeLE
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
              (u D))
            D)
          (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode D)
          (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode_termsDegreeLE
            D)
          (NormalizedCorrectedFixedDetectorCompactSourceCode.rewardMargin
            (u D))
          (NormalizedCorrectedFixedDetectorCompactSourceCode.baseCompactTangency
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
              (u D))
            D)
          μ hpos).measure :
        Measure
          (BaseSpace
            (layout
              (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDimension
                eqs vars))))) = 0

/-- A solvable instance with canonical theta outputs cannot have all
conditional drift means zero. -/
theorem not_conditionalBaseDriftZero_of_solvable
    (hcanonical :
      ∀ O :
          SelectedBidirectionalValidityOrbit (u D),
        HasCanonicalThetaOutputs D O)
    (hsolvable : D.Solvable)
    (μ :
      Dynamics.InvariantProbabilityMeasure
        (compactFlow (u D)))
    (hμ :
      Dynamics.IsErgodicInvariantProbability
        (compactFlow (u D)) μ.measure)
    (hpos : HasPositiveFiniteInterior D μ) :
    ¬ConditionalBaseDriftZero D μ hpos := by
  intro hzero
  obtain ⟨O⟩ :=
    exists_selectedBidirectionalValidityOrbit_of_conditionalBase_zero
      (u D) μ hμ hpos hzero
      (NormalizedCorrectedEffectiveCompilerInput.compilerInput_accumulatorScale_pos
        D).le
  exact
    false_of_solvable_and_canonicalThetaOutputs
      D O hsolvable (hcanonical O)

end HGAS.NormalizedCorrectedEffectiveNonzeroMeanFromTheta
