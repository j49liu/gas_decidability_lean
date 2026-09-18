import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorColumnRecurrence
import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorTwoSidedPhysicalMomentAverages
import HGAS.Modular.RecurrentUnaryMomentGenericityArbitraryClock
import Mathlib.Tactic

/-!
# Corrected detector moments force every selected column to be generic

Three entries of the seven-moment detector vector are precisely the
elementary divisor-exclusion observables:

```
             Y - 1,       p₄ - 1,       p₂ χ - 1/4.
```

The common physical Cesàro limits already proved for the corrected drift
therefore exclude `A = 0`, `C = 0`, and `A + C = 0` in each linked
column.  This argument is made before normalizing the signed modular
clock.
-/

namespace HGAS.NormalizedCorrectedFixedDetectorColumnGenericity

open HGAS
open Filter Topology
open HGAS.Clocks.ControllerPhaseProductCharacterCode
open HGAS.Modular
open NormalizedCorrectedFixedDetectorTwoSidedValidityOrbit
open NormalizedCorrectedFixedDetectorColumnTrajectory
open NormalizedCorrectedFixedDetectorColumnRecurrence
open NormalizedCorrectedFixedDetectorTwoSidedPhysicalMomentAverages
open NormalizedCorrectedFixedDetectorTwoSidedValidityOrbit.SelectedTwoSidedValidityOrbit
open NormalizedCorrectedFixedDetectorColumnTrajectory.SelectedTwoSidedValidityOrbit
open NormalizedCorrectedFixedDetectorColumnRecurrence.SelectedTwoSidedValidityOrbit

noncomputable section

variable {eqs vars : ℕ}
variable
  {u :
    NormalizedCorrectedFixedDetectorCompactSourceCode.CompilerInput
      eqs vars}

namespace SelectedTwoSidedValidityOrbit

variable (O : SelectedTwoSidedValidityOrbit u)

/-- Flattened index of local moment kind `r` in detector column `j`. -/
def columnMomentIndex
    (j : Fin vars)
    (r : Fin CorrectedFixedDetectorMomentCode.localMomentCount) :
    Fin (CorrectedFixedDetectorMomentCode.momentCount vars) :=
  finProdFinEquiv (j, r)

/-- The phase character appearing in the corrected `p₂` root moment. -/
def rootHalfCharacter
    (j : Fin vars)
    (t : ℝ) : ℂ :=
  characterValue
    (FixedDetectorMomentCode.rootHalfExponent j)
    (FixedDetectorReverseTrajectoryCrosswalk.recoveredState
      O.physicalPoint t).base.base.source.controllers

theorem momentValue_columnMomentIndex
    (j : Fin vars)
    (r : Fin CorrectedFixedDetectorMomentCode.localMomentCount)
    (t : ℝ) :
    CorrectedFixedDetectorMomentCode.momentValue
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
        (O.physicalState t)
        (columnMomentIndex j r) =
      CorrectedFixedDetectorMomentCode.localMomentValue
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
        j (O.physicalState t) r := by
  simp [CorrectedFixedDetectorMomentCode.momentValue,
    columnMomentIndex]

theorem unaryMean_momentValue
    (j : Fin vars)
    (t : ℝ) :
    CorrectedFixedDetectorMomentCode.momentValue
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
        (O.physicalState t)
        (columnMomentIndex j (0 : Fin 7)) =
      unaryMeanObservable (linkedColumn O j) t := by
  rw [momentValue_columnMomentIndex]
  simp [CorrectedFixedDetectorMomentCode.localMomentValue,
    unaryMeanObservable, linkedColumn,
    physicalState,
    FixedDetectorReverseTrajectoryCrosswalk.recoveredState]

theorem rootP4_momentValue
    (j : Fin vars)
    (t : ℝ) :
    CorrectedFixedDetectorMomentCode.momentValue
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
        (O.physicalState t)
        (columnMomentIndex j (2 : Fin 7)) =
      rootP4MeanObservable (linkedColumn O j) t := by
  rw [momentValue_columnMomentIndex]
  simp [CorrectedFixedDetectorMomentCode.localMomentValue,
    rootP4MeanObservable, linkedColumn,
    physicalState,
    FixedDetectorReverseTrajectoryCrosswalk.recoveredState]

theorem rootP2_momentValue
    (j : Fin vars)
    (t : ℝ) :
    CorrectedFixedDetectorMomentCode.momentValue
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
        (O.physicalState t)
        (columnMomentIndex j (3 : Fin 7)) =
      rootP2MeanObservable
        (linkedColumn O j) (rootHalfCharacter O j) t := by
  rw [momentValue_columnMomentIndex]
  simp [CorrectedFixedDetectorMomentCode.localMomentValue,
    rootP2MeanObservable, rootHalfCharacter, linkedColumn,
    physicalState,
    FixedDetectorReverseTrajectoryCrosswalk.recoveredState]

/-- The three corrected moment limits force the generic unary locus at
physical time zero. -/
theorem linkedColumn_unary_generic
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
    (linkedColumn O j 0).unary.A ≠ 0 ∧
      (linkedColumn O j 0).unary.C ≠ 0 ∧
      UnaryModularState.B (linkedColumn O j 0).unary ≠ 0 := by
  let T := physicalHorizon O
  have htrajectory :=
    linkedColumn_isScaledTrajectory O hscale hp j
  have hT : Tendsto T atTop atTop := by
    simpa only [T, physicalHorizon] using
      O.physicalHorizon_tendsto_atTop
  apply
    recurrentUnary_generic_of_selectorMomentLimits_arbitraryClock
      htrajectory.unary
      (linkedColumn_residual_zero O hscale j)
      hT
      (rootHalfCharacter O j)
  · simpa only [T, unaryMean_momentValue O j] using
      momentComplexAverage_tendsto_zero
        O hscale.ne' (columnMomentIndex j (0 : Fin 7))
  · simpa only [T, rootP4_momentValue O j] using
      momentComplexAverage_tendsto_zero
        O hscale.ne' (columnMomentIndex j (2 : Fin 7))
  · simpa only [T, rootP2_momentValue O j] using
      momentComplexAverage_tendsto_zero
        O hscale.ne' (columnMomentIndex j (3 : Fin 7))

end SelectedTwoSidedValidityOrbit

end

end HGAS.NormalizedCorrectedFixedDetectorColumnGenericity
