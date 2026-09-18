import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorFiniteClosedBranchSelection
import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorStandardizedUnitSpeedHaarExclusion
import HGAS.Modular.HorizontalUnaryClosedChart
import HGAS.Modular.RecurrentLiftExactFrameDifferentiable
import Mathlib.Tactic

/-!
# Automatic differentiable closed charts for selected detector columns

The recurrent exact-frame classification has two branches.

* A horizontal lift is already a closed horocycle around the infinity
  cusp.  Genericity forces its speed to be nonzero, and its canonical
  upper-triangular frame is periodic in `Γ(2) \ SL(2, ℝ)`.
* A nonhorizontal exact frame is periodic by the unit-speed
  Dani--Smillie/cusp contradiction.

Consequently every selected standardized detector column admits a
`ClosedUnaryHorocycleChart`.  This module retains differentiability of
the canonical-lambda lift and then feeds the chart directly into the
finite closed-cusp moment selector.
-/

namespace
  HGAS.NormalizedCorrectedFixedDetectorDifferentiableClosedChart

open HGAS
open HGAS.Modular
open UpperHalfPlane hiding I
open NormalizedCorrectedFixedDetectorTwoSidedValidityOrbit
open NormalizedCorrectedFixedDetectorBidirectionalValidityOrbit
open NormalizedCorrectedFixedDetectorColumnStandardization
open NormalizedCorrectedFixedDetectorFiniteClosedBranchSelection
open
  NormalizedCorrectedFixedDetectorColumnStandardization.SelectedTwoSidedValidityOrbit
open
  NormalizedCorrectedFixedDetectorColumnStandardization.SelectedBidirectionalValidityOrbit
open
  NormalizedCorrectedFixedDetectorFiniteClosedBranchSelection.SelectedBidirectionalValidityOrbit
open
  NormalizedFixedDetectorUnitSpeedHaarExclusion.SelectedBidirectionalValidityOrbit

noncomputable section

variable {eqs vars : ℕ}
variable
  {u :
    NormalizedCorrectedFixedDetectorCompactSourceCode.CompilerInput
      eqs vars}

namespace SelectedBidirectionalValidityOrbit

variable (O : SelectedBidirectionalValidityOrbit u)

private abbrev B :
    SelectedTwoSidedValidityOrbit u :=
  O.toSelectedTwoSidedValidityOrbit

/-- Every selected standardized detector column has a differentiable
canonical-lambda lift equipped with an actual closed unary horocycle
chart.  Both the horizontal and exact-frame branches are discharged
internally. -/
theorem standardizedUnaryColumn_exists_differentiable_closedChart
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
    ∃ T : ℝ → ℍ,
      Continuous T ∧
      (∀ t,
        UnaryModularState.lambdaCoordinate
            (standardizedUnaryColumn (B O) j t) =
          canonicalLambda (T t)) ∧
      (∀ t, ∃ w : ℂ,
        HasDerivAt (fun s : ℝ ↦ (T s : ℂ)) w t) ∧
      Nonempty
        (ClosedUnaryHorocycleChart
          (standardizedUnaryColumn (B O) j) T) := by
  have hz :
      IsScaledUnaryModularTrajectory
        modularIndependentVariableClock
        (standardizedUnaryColumn (B O) j) :=
    standardizedUnaryColumn_isScaledTrajectory
      (B O) hscale hp j
  have hgeneric :=
    standardizedUnaryColumn_generic O hscale hp j
  have hB :
      ∀ t,
        UnaryModularState.B
          (standardizedUnaryColumn (B O) j t) ≠ 0 :=
    hz.B_ne_zero hgeneric.2.2
  obtain
      ⟨T, hT, hlambda, hTdiff, hhorizontal | hexact⟩ :=
    recurrentGenericUnaryTrajectory_exists_differentiable_horizontal_or_exactFrame
      hz hgeneric.1 hgeneric.2.1 hgeneric.2.2
      (standardizedUnaryColumn_forwardRecurrentAt
        O hscale hp j)
  · obtain ⟨x, y, s, hy, hline⟩ := hhorizontal
    exact
      ⟨T, hT, hlambda, hTdiff,
        exists_closedUnaryHorocycleChart_of_horizontalLine
          hz hB hlambda x y s hy hline⟩
  · obtain ⟨g, σ, hσ, hframe⟩ := hexact
    have hperiodic :
        IsPeriodicHorocyclePoint 1
          (gammaTwoFrameQuotientMk g) :=
      periodic_of_standardizedExactFrameBranch
        O hscale hp j T hlambda g σ hσ hframe
    exact
      ⟨T, hT, hlambda, hTdiff,
        exists_closedUnaryHorocycleChart
          (standardizedUnaryColumn (B O) j)
          T g σ hσ hframe hperiodic⟩

/-- Full detector-facing composition: there is a differentiable closed
chart for the selected column, and the finite-cusp moment selector
applies to that same chart.

The returned `FiniteClosedCuspMeanSelection` contains the strict
conclusions that the cusp is infinity, the quartic amplitude is one, the
two coherent root scales are one, and the linked coordinates are the
canonical theta functions in the chart clock. -/
theorem standardizedUnaryColumn_exists_selectedFiniteClosedChart
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
    ∃ (T : ℝ → ℍ)
        (c :
          ClosedUnaryHorocycleChart
            (standardizedUnaryColumn (B O) j) T),
      Continuous T ∧
      (∀ t,
        UnaryModularState.lambdaCoordinate
            (standardizedUnaryColumn (B O) j t) =
          canonicalLambda (T t)) ∧
      (∀ t, ∃ w : ℂ,
        HasDerivAt (fun s : ℝ ↦ (T s : ℂ)) w t) ∧
      Nonempty
        (FiniteClosedCuspMeanSelection
          c.cuspLabel
          (standardizedLinkedColumn (B O) j)
          (closedChartX c)
          (closedChartHeight c)
          (closedChartSpeed c)
          (closedChartHeight_pos c)
          (closedChartAmplitude c)) := by
  obtain ⟨T, hT, hlambda, hTdiff, ⟨c⟩⟩ :=
    standardizedUnaryColumn_exists_differentiable_closedChart
      O hscale hp j
  refine ⟨T, c, hT, hlambda, hTdiff, ?_⟩
  exact
    standardizedFiniteClosedBranch_selection
      O hscale hp j T c hlambda hTdiff

/-- Data-valued version of the preceding endpoint.  It returns the
finite-cusp selection witness itself rather than only its nonemptiness,
so downstream code can use its normalized theta identities directly. -/
theorem standardizedUnaryColumn_exists_finiteClosedSelectionData
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
    ∃ (T : ℝ → ℍ)
        (c :
          ClosedUnaryHorocycleChart
            (standardizedUnaryColumn (B O) j) T)
        (selection :
          FiniteClosedCuspMeanSelection
            c.cuspLabel
            (standardizedLinkedColumn (B O) j)
            (closedChartX c)
            (closedChartHeight c)
            (closedChartSpeed c)
            (closedChartHeight_pos c)
            (closedChartAmplitude c)),
      Continuous T ∧
      (∀ t,
        UnaryModularState.lambdaCoordinate
            (standardizedUnaryColumn (B O) j t) =
          canonicalLambda (T t)) ∧
      (∀ t, ∃ w : ℂ,
        HasDerivAt (fun s : ℝ ↦ (T s : ℂ)) w t) ∧
      c.cuspLabel = .infinity ∧
      closedChartAmplitude c = 1 ∧
      selection.branches.yScale = 1 ∧
      selection.branches.p4Scale = 1 := by
  obtain
      ⟨T, c, hT, hlambda, hTdiff, ⟨selection⟩⟩ :=
    standardizedUnaryColumn_exists_selectedFiniteClosedChart
      O hscale hp j
  exact
    ⟨T, c, selection, hT, hlambda, hTdiff,
      selection.cusp_eq_infinity,
      selection.q_eq_one,
      selection.yScale_eq_one,
      selection.p4Scale_eq_one⟩

end SelectedBidirectionalValidityOrbit

end

end
  HGAS.NormalizedCorrectedFixedDetectorDifferentiableClosedChart
