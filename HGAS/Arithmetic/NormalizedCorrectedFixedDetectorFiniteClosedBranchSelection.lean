import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorColumnStandardization
import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorRawColumnMeans
import HGAS.Modular.ClosedUnaryHorocycleChartExactAmplitude
import HGAS.Modular.FiniteClosedCuspResampledMeanSelector
import Mathlib.Tactic

/-!
# The finite closed branch of a standardized detector column

This is the detector-facing endpoint of the finite-cusp calculation.
For a selected bidirectionally recurrent validity orbit and one detector
column, let

```text
  a = π / ω_j,
  z_std(t) = z_physical(a t).
```

The exact standardization may reverse time.  The detector moments remain
available in physical time, which is the resampling
`z_std(a⁻¹ t)=z_physical(t)`.  The resampled-mean selector therefore uses
the actual compiler moments without making any unsupported forward-to-
backward inference.

Given a finite closed horocycle chart for the standardized canonical
lambda lift, the theorem below proves:

* the chart cusp is infinity;
* the exact quartic amplitude is one;
* the coherent `Y` and `p₄` root scales are one; and
* in the chart clock, `Y=θ₃` and `p₄=θ₄²` pointwise.
-/

namespace
  HGAS.NormalizedCorrectedFixedDetectorFiniteClosedBranchSelection

open HGAS
open Filter
open HGAS.Modular
open UpperHalfPlane hiding I
open NormalizedCorrectedFixedDetectorTwoSidedValidityOrbit
open NormalizedCorrectedFixedDetectorBidirectionalValidityOrbit
open NormalizedCorrectedFixedDetectorColumnTrajectory
open NormalizedCorrectedFixedDetectorColumnRecurrence
open NormalizedCorrectedFixedDetectorColumnStandardization
open NormalizedCorrectedFixedDetectorRawColumnMeans
open NormalizedCorrectedFixedDetectorTwoSidedPhysicalMomentAverages
open NormalizedCorrectedFixedDetectorTwoSidedValidityOrbit.SelectedTwoSidedValidityOrbit
open NormalizedCorrectedFixedDetectorColumnTrajectory.SelectedTwoSidedValidityOrbit
open NormalizedCorrectedFixedDetectorColumnRecurrence.SelectedTwoSidedValidityOrbit
open NormalizedCorrectedFixedDetectorRawColumnMeans.SelectedTwoSidedValidityOrbit
open
  NormalizedCorrectedFixedDetectorColumnStandardization.SelectedTwoSidedValidityOrbit
open
  NormalizedCorrectedFixedDetectorColumnStandardization.SelectedBidirectionalValidityOrbit
open scoped Topology

noncomputable section

variable {eqs vars : ℕ}
variable
  {u :
    NormalizedCorrectedFixedDetectorCompactSourceCode.CompilerInput
      eqs vars}

/-! ## The full standardized linked column -/

/-- All fourteen linked coordinates in the same standardized clock used
by `standardizedUnaryColumn`. -/
def standardizedLinkedColumn
    (O : SelectedTwoSidedValidityOrbit u)
    (j : Fin vars) (t : ℝ) :
    LinkedJacobiState ℂ :=
  linkedColumn O j (columnStandardScale O j * t)

@[simp]
theorem standardizedLinkedColumn_unary
    (O : SelectedTwoSidedValidityOrbit u)
    (j : Fin vars) (t : ℝ) :
    (standardizedLinkedColumn O j t).unary =
      standardizedUnaryColumn O j t :=
  rfl

/-- The full linked trajectory rescales together with its two clocks. -/
theorem standardizedLinkedColumn_isScaledTrajectory
    (O : SelectedTwoSidedValidityOrbit u)
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
    IsScaledLinkedJacobiTrajectory
      (((columnStandardScale O j : ℝ) : ℂ) * columnKappaZ O j)
      (((columnStandardScale O j : ℝ) : ℂ) * columnKappaPhi O j)
      (standardizedLinkedColumn O j) := by
  simpa only [standardizedLinkedColumn] using
    (linkedColumn_isScaledTrajectory O hscale hp j).rescale
      (columnStandardScale O j)

/-- Inverse resampling of a standardized column is exactly the original
physical column. -/
theorem standardizedLinkedColumn_invScale
    (O : SelectedTwoSidedValidityOrbit u)
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
    (j : Fin vars) (t : ℝ) :
    standardizedLinkedColumn O j
        ((columnStandardScale O j)⁻¹ * t) =
      linkedColumn O j t := by
  have ha :
      columnStandardScale O j ≠ 0 :=
    columnStandardScale_ne_zero O hscale hp j
  unfold standardizedLinkedColumn
  rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]

/-! ## Compact names for the chart parameters -/

def closedChartX
    {z : ℝ → UnaryModularState ℂ}
    {T : ℝ → UpperHalfPlane}
    (c : ClosedUnaryHorocycleChart z T) : ℝ :=
  c.horizontalization.cuspNormalized.upperLeft *
    c.horizontalization.cuspNormalized.upperRight

def closedChartHeight
    {z : ℝ → UnaryModularState ℂ}
    {T : ℝ → UpperHalfPlane}
    (c : ClosedUnaryHorocycleChart z T) : ℝ :=
  c.horizontalization.cuspNormalized.upperLeft ^ 2

def closedChartSpeed
    {z : ℝ → UnaryModularState ℂ}
    {T : ℝ → UpperHalfPlane}
    (c : ClosedUnaryHorocycleChart z T) : ℝ :=
  closedChartHeight c * c.orbitSpeed

theorem closedChartHeight_pos
    {z : ℝ → UnaryModularState ℂ}
    {T : ℝ → UpperHalfPlane}
    (c : ClosedUnaryHorocycleChart z T) :
    0 < closedChartHeight c :=
  sq_pos_of_ne_zero
    c.horizontalization.cuspNormalized.upperLeft_ne_zero

theorem closedChartSpeed_ne_zero
    {z : ℝ → UnaryModularState ℂ}
    {T : ℝ → UpperHalfPlane}
    (c : ClosedUnaryHorocycleChart z T) :
    closedChartSpeed c ≠ 0 := by
  simpa only [closedChartSpeed, closedChartHeight] using
    c.horizontalSpeed_ne_zero

def closedChartAmplitude
    {z : ℝ → UnaryModularState ℂ}
    {T : ℝ → UpperHalfPlane}
    (c : ClosedUnaryHorocycleChart z T) : ℂ :=
  cuspQuarticAmplitude c.cuspLabel (closedChartSpeed c)

/-! ## Detector-facing endpoint -/

namespace SelectedBidirectionalValidityOrbit

variable (O : SelectedBidirectionalValidityOrbit u)

/-- A finite closed branch of an actual selected standardized detector
column is the normalized infinity branch.

All analytic mean hypotheses are discharged internally from the compiled
detector moments.  The only geometric inputs are the canonical-lambda
identity, differentiability of its lift, and the closed chart itself. -/
theorem standardizedFiniteClosedBranch_selection
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
    (T : ℝ → UpperHalfPlane)
    (c :
      ClosedUnaryHorocycleChart
        (standardizedUnaryColumn
          O.toSelectedTwoSidedValidityOrbit j) T)
    (hlambda :
      ∀ t,
        UnaryModularState.lambdaCoordinate
            (standardizedUnaryColumn
              O.toSelectedTwoSidedValidityOrbit j t) =
          canonicalLambda (T t))
    (hTdiff :
      ∀ t, ∃ v : ℂ,
        HasDerivAt (fun s : ℝ ↦ (T s : ℂ)) v t) :
    Nonempty
      (FiniteClosedCuspMeanSelection
        c.cuspLabel
        (standardizedLinkedColumn
          O.toSelectedTwoSidedValidityOrbit j)
        (closedChartX c)
        (closedChartHeight c)
        (closedChartSpeed c)
        (closedChartHeight_pos c)
        (closedChartAmplitude c)) := by
  let B := O.toSelectedTwoSidedValidityOrbit
  let z :=
    standardizedLinkedColumn B j
  let a :=
    columnStandardScale B j
  let b := a⁻¹
  let x := closedChartX c
  let y := closedChartHeight c
  let s := closedChartSpeed c
  let q := closedChartAmplitude c
  have ha : a ≠ 0 := by
    exact
      columnStandardScale_ne_zero B hscale hp j
  have hb : b ≠ 0 :=
    inv_ne_zero ha
  have hy : 0 < y :=
    closedChartHeight_pos c
  have hs : s ≠ 0 :=
    closedChartSpeed_ne_zero c
  have hz :
      IsScaledLinkedJacobiTrajectory
        (((a : ℝ) : ℂ) * columnKappaZ B j)
        (((a : ℝ) : ℂ) * columnKappaPhi B j) z := by
    simpa only [a, z] using
      standardizedLinkedColumn_isScaledTrajectory
        B hscale hp j
  have hzUnary :
      IsScaledUnaryModularTrajectory
        modularIndependentVariableClock
        (standardizedUnaryColumn B j) :=
    standardizedUnaryColumn_isScaledTrajectory
      B hscale hp j
  have hgeneric :=
    standardizedUnaryColumn_generic O hscale hp j
  have hB :
      ∀ t,
        UnaryModularState.B
          (standardizedUnaryColumn B j t) ≠ 0 := by
    intro t hzero
    exact hgeneric.2.2 (hzUnary.B_eq_zero hzero 0)
  have hamplitude :
      ∀ t,
        HasCuspQuarticAmplitude c.cuspLabel
          (z t).unary
          (horizontalLine x y s hy t) q := by
    intro t
    have h :=
      c.hasCuspQuarticAmplitude
        hzUnary hB hlambda hTdiff t
    rw [c.horizontalModulus_eq] at h
    simpa only [
      z, standardizedLinkedColumn_unary,
      x, y, s, q, closedChartX,
      closedChartHeight, closedChartSpeed,
      closedChartAmplitude] using h
  have hq : q ≠ 0 :=
    (hamplitude 0).1
  have hresidual :
      ∀ t (r : LinkedJacobiResidualIndex),
        linkedJacobiResidual r (z t) = 0 := by
    intro t r
    exact
      linkedColumn_residual_zero B hscale j (a * t) r
  have hT :
      Tendsto (physicalHorizon B) atTop atTop :=
    rawMeanPhysicalHorizon_tendsto B
  have hmeanY :
      Tendsto
        (fun n ↦
          HGAS.Analysis.cesaroMeanAt
            (fun t ↦ (z (b * t)).unary.Y)
            (physicalHorizon B n))
        atTop (nhds 1) := by
    simpa only [
      z, b, a,
      standardizedLinkedColumn_invScale
        B hscale hp j] using
      (linkedColumn_Y_cesaroMean_tendsto_one
        B hscale hp j)
  have hmeanP4 :
      Tendsto
        (fun n ↦
          HGAS.Analysis.cesaroMeanAt
            (fun t ↦ (z (b * t)).jacobi.p4)
            (physicalHorizon B n))
        atTop (nhds 1) := by
    simpa only [
      z, b, a,
      standardizedLinkedColumn_invScale
        B hscale hp j] using
      (linkedColumn_p4_cesaroMean_tendsto_one
        B hscale hp j)
  simpa only [B, z, x, y, s, q] using
    finiteClosedCuspMeanSelection_of_resampled_means
      c.cuspLabel z hz x y s hy hs q hq
      hamplitude hresidual b hb hT hmeanY hmeanP4

end SelectedBidirectionalValidityOrbit

end

end
  HGAS.NormalizedCorrectedFixedDetectorFiniteClosedBranchSelection
