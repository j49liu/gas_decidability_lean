import HGAS.Analysis.CesaroConstantTimeRescaling
import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorColumnGenericity
import Mathlib.Tactic

/-!
# Raw normalized means of a selected detector column

The compiler stores centered selector moments.  In column `j`, moment
zero is `Y-1` and moment two is `p₄-1`.  Their complex physical Cesàro
means vanish along the common physical horizons.  Adding the constants
back therefore gives the raw normalizations

```text
  Cesàro(Y)  → 1,       Cesàro(p₄) → 1.
```

These are precisely the two inputs used by the finite cusp selector.
-/

namespace HGAS.NormalizedCorrectedFixedDetectorRawColumnMeans

open HGAS
open Filter
open HGAS.Modular
open NormalizedCorrectedFixedDetectorTwoSidedValidityOrbit
open NormalizedCorrectedFixedDetectorColumnTrajectory
open NormalizedCorrectedFixedDetectorColumnGenericity
open NormalizedCorrectedFixedDetectorTwoSidedPhysicalMomentAverages
open NormalizedCorrectedFixedDetectorTwoSidedValidityOrbit.SelectedTwoSidedValidityOrbit
open NormalizedCorrectedFixedDetectorColumnTrajectory.SelectedTwoSidedValidityOrbit
open NormalizedCorrectedFixedDetectorColumnGenericity.SelectedTwoSidedValidityOrbit
open scoped Topology

noncomputable section

variable {eqs vars : ℕ}
variable
  {u :
    NormalizedCorrectedFixedDetectorCompactSourceCode.CompilerInput
      eqs vars}

namespace SelectedTwoSidedValidityOrbit

variable (O : SelectedTwoSidedValidityOrbit u)

set_option linter.style.longLine false in
/-- The common physical horizons used by the raw column means diverge. -/
theorem rawMeanPhysicalHorizon_tendsto :
    Tendsto (physicalHorizon O) atTop atTop :=
  _root_.HGAS.NormalizedCorrectedFixedDetectorTwoSidedPhysicalMomentAverages.physicalHorizon_tendsto_atTop O

/-- The raw unary root `Y` has physical Cesàro mean one. -/
theorem linkedColumn_Y_cesaroMean_tendsto_one
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
    Tendsto
      (fun n ↦
        HGAS.Analysis.cesaroMeanAt
          (fun t ↦ (linkedColumn O j t).unary.Y)
          (physicalHorizon O n))
      atTop (nhds 1) := by
  have hz :=
    linkedColumn_isScaledTrajectory O hscale hp j
  have hcentered :
      Tendsto
        (fun n ↦
          HGAS.Analysis.cesaroMeanAt
            (fun t ↦ (linkedColumn O j t).unary.Y - 1)
            (physicalHorizon O n))
        atTop (nhds 0) := by
    simpa only [
      unaryMean_momentValue O j,
      unaryMeanObservable] using
      (momentComplexAverage_tendsto_zero
        O hscale.ne' (columnMomentIndex j (0 : Fin 7)))
  exact
    HGAS.Analysis.tendsto_cesaroMeanAt_of_sub_const_tendsto_zero
      hz.unary.continuous_Y 1
      (rawMeanPhysicalHorizon_tendsto O) hcentered

/-- The raw coefficient root `p₄` has physical Cesàro mean one. -/
theorem linkedColumn_p4_cesaroMean_tendsto_one
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
    Tendsto
      (fun n ↦
        HGAS.Analysis.cesaroMeanAt
          (fun t ↦ (linkedColumn O j t).jacobi.p4)
          (physicalHorizon O n))
      atTop (nhds 1) := by
  have hz :=
    linkedColumn_isScaledTrajectory O hscale hp j
  have hcentered :
      Tendsto
        (fun n ↦
          HGAS.Analysis.cesaroMeanAt
            (fun t ↦ (linkedColumn O j t).jacobi.p4 - 1)
            (physicalHorizon O n))
        atTop (nhds 0) := by
    simpa only [
      rootP4_momentValue O j,
      rootP4MeanObservable] using
      (momentComplexAverage_tendsto_zero
        O hscale.ne' (columnMomentIndex j (2 : Fin 7)))
  exact
    HGAS.Analysis.tendsto_cesaroMeanAt_of_sub_const_tendsto_zero
      hz.jacobi.continuous_p4 1
      (rawMeanPhysicalHorizon_tendsto O) hcentered

end SelectedTwoSidedValidityOrbit

end

end HGAS.NormalizedCorrectedFixedDetectorRawColumnMeans
