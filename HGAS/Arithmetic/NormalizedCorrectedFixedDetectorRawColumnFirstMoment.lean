import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorRawColumnMeans
import Mathlib.Tactic

/-!
# The raw first-harmonic moment of a selected detector column

The corrected compiler stores the centered first selector

```text
  Y(t) χ₁(t) - 1/128.
```

Its complex physical Cesàro mean is zero along the common detector
horizons.  This module adds the constant back and exposes the exact raw
statement needed by the modular height selector:

```text
  Cesàro(Y χ₁) → 1/128.
```

The proof goes through the literal sparse polynomial semantics, so there
is no informal identification between a compiler coordinate and its
intended observable.
-/

namespace
  HGAS.NormalizedCorrectedFixedDetectorRawColumnFirstMoment

open HGAS
open Filter
open HGAS.Clocks.ControllerPhaseProductCharacterCode
open HGAS.Modular
open NormalizedCorrectedFixedDetectorTwoSidedValidityOrbit
open NormalizedCorrectedFixedDetectorColumnTrajectory
open NormalizedCorrectedFixedDetectorColumnGenericity
open NormalizedCorrectedFixedDetectorRawColumnMeans
open NormalizedCorrectedFixedDetectorTwoSidedPhysicalMomentAverages
open NormalizedCorrectedFixedDetectorTwoSidedValidityOrbit.SelectedTwoSidedValidityOrbit
open NormalizedCorrectedFixedDetectorColumnTrajectory.SelectedTwoSidedValidityOrbit
open NormalizedCorrectedFixedDetectorColumnGenericity.SelectedTwoSidedValidityOrbit
open
  NormalizedCorrectedFixedDetectorRawColumnMeans.SelectedTwoSidedValidityOrbit
open scoped Topology

noncomputable section

variable {eqs vars : ℕ}
variable
  {u :
    NormalizedCorrectedFixedDetectorCompactSourceCode.CompilerInput
      eqs vars}

namespace SelectedTwoSidedValidityOrbit

variable (O : SelectedTwoSidedValidityOrbit u)

/-- The uncentered first-harmonic observable in physical detector time. -/
def unaryFirstRawObservable
    (j : Fin vars) (t : ℝ) : ℂ :=
  (linkedColumn O j t).unary.Y *
    characterValue
      (FixedDetectorMomentCode.unaryFirstHarmonicExponent j)
      (FixedDetectorReverseTrajectoryCrosswalk.recoveredState
        O.physicalPoint t).base.base.source.controllers

/-- Literal semantic identification of local detector moment one. -/
theorem unaryFirst_momentValue
    (j : Fin vars) (t : ℝ) :
    CorrectedFixedDetectorMomentCode.momentValue
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
        (O.physicalState t)
        (columnMomentIndex j (1 : Fin 7)) =
      unaryFirstRawObservable O j t - (1 / 128 : ℂ) := by
  rw [momentValue_columnMomentIndex]
  simp [
    CorrectedFixedDetectorMomentCode.localMomentValue,
    unaryFirstRawObservable, linkedColumn, physicalState,
    FixedDetectorReverseTrajectoryCrosswalk.recoveredState]

/-- The raw first-harmonic observable is continuous. -/
theorem continuous_unaryFirstRawObservable
    (j : Fin vars) :
    Continuous (unaryFirstRawObservable O j) := by
  have hm :=
    continuous_momentValue_physical
      O (columnMomentIndex j (1 : Fin 7))
  have heq :
      unaryFirstRawObservable O j =
        fun t ↦
          CorrectedFixedDetectorMomentCode.momentValue
              (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
              (O.physicalState t)
              (columnMomentIndex j (1 : Fin 7)) +
            (1 / 128 : ℂ) := by
    funext t
    rw [unaryFirst_momentValue O j t]
    ring
  rw [heq]
  exact hm.add continuous_const

/-- The physical raw first-harmonic mean is exactly the compiler target
`1/128`. -/
theorem unaryFirstRawObservable_cesaroMean_tendsto
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (j : Fin vars) :
    Tendsto
      (fun n ↦
        HGAS.Analysis.cesaroMeanAt
          (unaryFirstRawObservable O j)
          (physicalHorizon O n))
      atTop (nhds (1 / 128 : ℂ)) := by
  have hcentered :
      Tendsto
        (fun n ↦
          HGAS.Analysis.cesaroMeanAt
            (fun t ↦
              unaryFirstRawObservable O j t -
                (1 / 128 : ℂ))
            (physicalHorizon O n))
        atTop (nhds 0) := by
    simpa only [unaryFirst_momentValue O j] using
      (momentComplexAverage_tendsto_zero
        O hscale.ne' (columnMomentIndex j (1 : Fin 7)))
  exact
    HGAS.Analysis.tendsto_cesaroMeanAt_of_sub_const_tendsto_zero
      (continuous_unaryFirstRawObservable O j)
      (1 / 128 : ℂ)
      (rawMeanPhysicalHorizon_tendsto O) hcentered

end SelectedTwoSidedValidityOrbit

end

end HGAS.NormalizedCorrectedFixedDetectorRawColumnFirstMoment
