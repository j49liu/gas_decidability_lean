import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorTwoSidedValidityOrbit
import HGAS.Compiler.AllAffineConditionalBidirectionallyRecurrentGenericZeroOrbit
import Mathlib.Tactic

/-!
# A normalized detector orbit recurrent in both directions

The ordinary two-sided validity orbit carries a complete physical clock
but records compact recurrence only in the forward direction.  For a
signed private frequency this is insufficient: normalizing a negative
frequency reverses time.  We therefore refine the selected object with
an independent recurrence certificate for the reversed compact flow.

All established detector theorems remain reusable through the projection
`toSelectedTwoSidedValidityOrbit`.
-/

namespace HGAS.NormalizedCorrectedFixedDetectorBidirectionalValidityOrbit

open HGAS
open Filter Function MeasureTheory Set Topology
open scoped BoundedContinuousFunction

noncomputable section

open CompactAccumulatorPipelineCode
open CompactAccumulatorPipelineCode.AllAffineCompactSourceChart
open CompactAccumulatorPipelineCode.AllAffineCompactSourceClock
open CompactAccumulatorPipelineCode.AllAffineCompactSourceTwoSidedClock
open CompactAccumulatorPipelineCode.AllAffineCompactSourceDrift
open CompactAccumulatorPipelineCode.AllAffineConditionalGenericOrbit
open
  CompactAccumulatorPipelineCode.AllAffineConditionalBidirectionallyRecurrentGenericZeroOrbit
open NormalizedCorrectedFixedDetectorTwoSidedValidityOrbit

variable {eqs vars : ℕ}

/-- A complete normalized validity orbit with recurrence for both the
compact flow and its reversal. -/
structure SelectedBidirectionalValidityOrbit
    (u : NormalizedCorrectedFixedDetectorCompactSourceCode.CompilerInput eqs vars)
    extends SelectedTwoSidedValidityOrbit u where
  recurrent_reverse :
    ForwardRecurrentAt
      (fun t : ℝ ↦
        ((compactFlow u).restrict (finiteInvariant u)).reverse t point) 0

/-- Conditional zero drift means select a bidirectionally recurrent
normalized validity orbit. -/
theorem exists_selectedBidirectionalValidityOrbit_of_conditionalBase_zero
    (u : NormalizedCorrectedFixedDetectorCompactSourceCode.CompilerInput eqs vars)
    (μ : Dynamics.InvariantProbabilityMeasure (compactFlow u))
    (hμ :
      Dynamics.IsErgodicInvariantProbability
        (compactFlow u) μ.measure)
    (hpos :
      (μ.measure :
        Measure
          (AllAffineCompactSourceChart.SourceSpace
            (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDimension
              eqs vars)
            (NormalizedCorrectedFixedDetectorCompactSourceCode.driftDimension vars)))
        (sourceFiniteInteriorSet
          (m :=
            NormalizedCorrectedFixedDetectorCompactSourceCode.driftDimension vars)
          (layout
            (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDimension
              eqs vars))) ≠ 0)
    (hzero :
      ∀ i :
          Fin (NormalizedCorrectedFixedDetectorCompactSourceCode.driftDimension vars),
        (∫ b,
          baseDriftBCF
            (layout
              (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDimension
                eqs vars))
            (2 *
              speedExponent
                (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
            (NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale u)
            (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode
              (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
            b i
          ∂((conditionalBaseProbability
              (layout
                (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDimension
                  eqs vars))
              (speedExponent
                (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
              (2 *
                speedExponent
                  (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
              (NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale u)
              (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode
                (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
                (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
              (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode_termsDegreeLE
                (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
                (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
              (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode
                (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
              (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode_termsDegreeLE
                (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
              (NormalizedCorrectedFixedDetectorCompactSourceCode.rewardMargin u)
              (NormalizedCorrectedFixedDetectorCompactSourceCode.baseCompactTangency
                (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
                (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
              μ hpos).measure :
            Measure
              (BaseSpace
                (layout
                  (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDimension
                    eqs vars))))) = 0)
    (hscale :
      0 ≤
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale u).decode :
          ℝ)) :
    Nonempty (SelectedBidirectionalValidityOrbit u) := by
  obtain
      ⟨v, c, hclock, hc, hrec, hrecReverse, hvalid, hspeed,
        hspeedReverse, hdrift, hdriftReverse⟩ :=
    exists_birecurrentPhysicalPoint_zeroCoordinate_of_conditionalBase_zero
      (speedExponent
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
      (speedExponent
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
      (NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale u)
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode
        (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode_termsDegreeLE
        (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode_termsDegreeLE
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
      (NormalizedCorrectedFixedDetectorCompactSourceCode.rewardMargin u)
      μ hμ hpos hzero
      (NormalizedCorrectedFixedDetectorDriftCode.validityIndex vars)
      (finiteValidityDrift_nonneg u hscale)
  exact
    ⟨{
      point := v
      speedMean := c
      clock := hclock
      speedMean_pos := hc
      recurrent := hrec
      validityDrift_zero := hvalid
      speed_generic := hspeed
      speed_generic_reverse := hspeedReverse
      drift_generic := hdrift
      drift_generic_reverse := hdriftReverse
      recurrent_reverse := hrecReverse
    }⟩

namespace SelectedBidirectionalValidityOrbit

variable
  {u : NormalizedCorrectedFixedDetectorCompactSourceCode.CompilerInput eqs vars}
  (O : SelectedBidirectionalValidityOrbit u)

/-- The physical detector point inherited from the underlying selected
two-sided orbit. -/
abbrev physicalPoint :=
  O.toSelectedTwoSidedValidityOrbit.physicalPoint

end SelectedBidirectionalValidityOrbit

end

end HGAS.NormalizedCorrectedFixedDetectorBidirectionalValidityOrbit
