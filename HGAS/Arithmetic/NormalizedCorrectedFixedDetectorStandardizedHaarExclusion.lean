import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorColumnStandardization
import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorUnaryInverseClockBound
import HGAS.Dynamics.PositiveIntegralClockRangeRescaling
import HGAS.Modular.GammaTwoPositiveMultipleH4SquareCompactTests
import HGAS.Modular.RealFrameHorocycleUnaryAmplitude
import Mathlib.Tactic

/-!
# Haar exclusion after exact signed detector-column standardization

Detector column `j` is put into the standard unary clock by the nonzero
time factor

```text
  aⱼ = π / ωⱼ.
```

The standardized trajectory at time `t` is the original physical
detector state at time `aⱼ t`.  Therefore its compactification clock is
not literally the original one:

* when `aⱼ > 0`, divide the original compact-time speed by `aⱼ`;
* when `aⱼ < 0`, first reverse the clock and then divide by `-aⱼ`.

In either case the reciprocal speed acquires the positive factor
`|aⱼ|`.  The compact-test theorem for positive multiples absorbs exactly
that factor.  The two sign-specific theorems below are combined in the
final endpoint, so no orientation assumption remains.
-/

namespace
  HGAS.NormalizedCorrectedFixedDetectorStandardizedHaarExclusion

open HGAS
open Filter Topology
open HGAS.Modular
open UpperHalfPlane hiding I
open CompactAccumulatorPipelineCode.AllAffineCompactSourceChart
open CompactAccumulatorPipelineCode.AllAffineCompactSourceTwoSidedClock
open CompactAccumulatorPipelineCode.AllAffineCompactSourceReverseRecurrence
open NormalizedCorrectedFixedDetectorTwoSidedValidityOrbit
open NormalizedCorrectedFixedDetectorBidirectionalValidityOrbit
open NormalizedCorrectedFixedDetectorColumnTrajectory
open NormalizedCorrectedFixedDetectorColumnStandardization
open
  NormalizedCorrectedFixedDetectorTwoSidedValidityOrbit.SelectedTwoSidedValidityOrbit
open
  NormalizedCorrectedFixedDetectorColumnStandardization.SelectedTwoSidedValidityOrbit
open
  NormalizedCorrectedFixedDetectorColumnStandardization.SelectedBidirectionalValidityOrbit

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

private abbrev K : ℕ :=
  speedExponent
    (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)

/-- The compactification exponent is positive: the fixed detector field
degree is at least nine. -/
private theorem one_le_K : 1 ≤ K (u := u) := by
  unfold K speedExponent
  unfold
    NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDegreeBound
    CorrectedFixedDetectorCompactSourceCode.sourceDegreeBound
    FixedDetectorPolynomialCode.fieldDegree
  omega

/-- The standardized unary `C` coordinate is literally the selected
physical-state coordinate at time `aⱼ t`. -/
theorem standardizedUnaryColumn_C_eq
    (j : Fin vars) (t : ℝ) :
    (standardizedUnaryColumn (B O) j t).C =
      ((((B O).physicalState
        (columnStandardScale (B O) j * t)).base.base.source.linked j).unary.C) := by
  rfl

/-- Positive standardization scale: the exact frame branch cannot be
Haar generic. -/
theorem
    not_haarGeneric_of_standardizedExactFrameBranch_of_scale_pos
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
    (T : ℝ → ℍ)
    (hlambda :
      ∀ t,
        UnaryModularState.lambdaCoordinate
            (standardizedUnaryColumn (B O) j t) =
          canonicalLambda (T t))
    (g : RealModularFrame) (σ : ℝ) (hσ : σ ≠ 0)
    (hframe :
      ∀ t,
        T t =
          realModularFrameBasePoint
            (g * upperUnipotent (σ * t)))
    (ha :
      0 < columnStandardScale (B O) j)
    (hgeneric :
      IsForwardGenericFor
        (scaledGammaTwoHorocycleFlow σ)
        gammaTwoFrameHaarProbability
        (gammaTwoFrameQuotientMk g)) :
    False := by
  let a : ℝ := columnStandardScale (B O) j
  let w : ℝ → ℝ :=
    twoSidedClockWeight (K (u := u))
      (affineCurve u (B O).point)
  let hclock :
      PositiveIntegralClock
        (rangeRescaledClockWeight a w) :=
    (B O).clock.rangeRescale (by simpa only [a] using ha)
  have hz :
      IsScaledUnaryModularTrajectory
        modularIndependentVariableClock
        (standardizedUnaryColumn (B O) j) :=
    SelectedTwoSidedValidityOrbit.standardizedUnaryColumn_isScaledTrajectory
      (B O) hscale hp j
  have hinitial :=
    standardizedUnaryColumn_generic O hscale hp j
  have hB :
      ∀ t,
        UnaryModularState.B
          (standardizedUnaryColumn (B O) j t) ≠ 0 :=
    hz.B_ne_zero hinitial.2.2
  have hmean :
      Tendsto
        (fun n : ℕ ↦
          (positiveIntegerHorizon n)⁻¹ *
            integralClock
              (rangeRescaledClockWeight a w)
              (positiveIntegerHorizon n))
        atTop (nhds (a⁻¹ * (B O).speedMean)) := by
    exact
      HGAS.Dynamics.positiveIntegerMean_rangeRescale
        (b := a) (by
          simpa only [a, w] using
            (B O).clock_positiveIntegerMean)
  have hmean_pos : 0 < a⁻¹ * (B O).speedMean :=
    mul_pos (inv_pos.mpr (by simpa only [a] using ha))
      (B O).speedMean_pos
  have horbit :
      ∀ t : ℝ,
        a *
            gammaTwoScaledH4SquareNormPower
              (horocycleSpeedNorm σ) (K (u := u))
              (scaledGammaTwoHorocycleFlow σ t
                (gammaTwoFrameQuotientMk g)) ≤
          HGAS.Dynamics.inverseClockReciprocal hclock t := by
    intro t
    have hexact :=
      gammaTwoScaledH4SquareNormPower_eq_unaryC_norm_pow
        hz hB hlambda g σ hframe (K (u := u)) t
    have hcoordinate :=
      (B O).unaryC_evenPower_le_inverseClockReciprocal
        j (a * t)
    calc
      a *
          gammaTwoScaledH4SquareNormPower
            (horocycleSpeedNorm σ) (K (u := u))
            (scaledGammaTwoHorocycleFlow σ t
              (gammaTwoFrameQuotientMk g)) =
        a *
          ‖(standardizedUnaryColumn (B O) j t).C‖ ^
            (2 * K (u := u)) := by rw [hexact]
      _ =
        a *
          ‖((((B O).physicalState
              (a * t)).base.base.source.linked j).unary.C)‖ ^
            (2 * K (u := u)) := by
          rw [standardizedUnaryColumn_C_eq O j t]
      _ ≤
        a *
          HGAS.Dynamics.inverseClockReciprocal
            (B O).clock (a * t) :=
          mul_le_mul_of_nonneg_left hcoordinate ha.le
      _ =
        HGAS.Dynamics.inverseClockReciprocal
          hclock t := by
          simpa only [hclock, a, w] using
            (HGAS.Dynamics.inverseClockReciprocal_rangeRescale
              (B O).clock ha t).symm
  exact
    not_gammaTwoHaarGeneric_of_positiveMeanClock_and_positiveMultiple_scaledH4Square_orbitBound
      (scaledGammaTwoHorocycleFlow σ)
      hgeneric hclock hmean_pos hmean
      (horocycleSpeedNorm σ)
      (horocycleSpeedNorm_ne_zero hσ)
      (K (u := u)) (one_le_K (u := u))
      a (by simpa only [a] using ha)
      horbit

/-- Negative standardization scale: reverse the complete clock, then the
same exact frame branch cannot be Haar generic. -/
theorem
    not_haarGeneric_of_standardizedExactFrameBranch_of_scale_neg
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
    (T : ℝ → ℍ)
    (hlambda :
      ∀ t,
        UnaryModularState.lambdaCoordinate
            (standardizedUnaryColumn (B O) j t) =
          canonicalLambda (T t))
    (g : RealModularFrame) (σ : ℝ) (hσ : σ ≠ 0)
    (hframe :
      ∀ t,
        T t =
          realModularFrameBasePoint
            (g * upperUnipotent (σ * t)))
    (ha :
      columnStandardScale (B O) j < 0)
    (hgeneric :
      IsForwardGenericFor
        (scaledGammaTwoHorocycleFlow σ)
        gammaTwoFrameHaarProbability
        (gammaTwoFrameQuotientMk g)) :
    False := by
  let a : ℝ := columnStandardScale (B O) j
  let b : ℝ := -a
  let w : ℝ → ℝ :=
    twoSidedClockWeight (K (u := u))
      (affineCurve u (B O).point)
  let hreverse :=
    reverseClock (B O).clock
  have hb : 0 < b := by
    simpa only [b, a] using neg_pos.mpr ha
  let hclock :
      PositiveIntegralClock
        (rangeRescaledClockWeight b
          (fun t ↦ w (-t))) :=
    hreverse.rangeRescale hb
  have hz :
      IsScaledUnaryModularTrajectory
        modularIndependentVariableClock
        (standardizedUnaryColumn (B O) j) :=
    SelectedTwoSidedValidityOrbit.standardizedUnaryColumn_isScaledTrajectory
      (B O) hscale hp j
  have hinitial :=
    standardizedUnaryColumn_generic O hscale hp j
  have hB :
      ∀ t,
        UnaryModularState.B
          (standardizedUnaryColumn (B O) j t) ≠ 0 :=
    hz.B_ne_zero hinitial.2.2
  have hmean :
      Tendsto
        (fun n : ℕ ↦
          (positiveIntegerHorizon n)⁻¹ *
            integralClock
              (rangeRescaledClockWeight b
                (fun t ↦ w (-t)))
              (positiveIntegerHorizon n))
        atTop (nhds (b⁻¹ * (B O).speedMean)) := by
    exact
      HGAS.Dynamics.positiveIntegerMean_rangeRescale
        (b := b) (by
          simpa only [w] using
            (B O).reverseClock_positiveIntegerMean)
  have hmean_pos : 0 < b⁻¹ * (B O).speedMean :=
    mul_pos (inv_pos.mpr hb) (B O).speedMean_pos
  have horbit :
      ∀ t : ℝ,
        b *
            gammaTwoScaledH4SquareNormPower
              (horocycleSpeedNorm σ) (K (u := u))
              (scaledGammaTwoHorocycleFlow σ t
                (gammaTwoFrameQuotientMk g)) ≤
          HGAS.Dynamics.inverseClockReciprocal hclock t := by
    intro t
    have hexact :=
      gammaTwoScaledH4SquareNormPower_eq_unaryC_norm_pow
        hz hB hlambda g σ hframe (K (u := u)) t
    have hcoordinate :=
      (B O).unaryC_evenPower_le_inverseClockReciprocal
        j (a * t)
    have hat : a * t = -(b * t) := by
      simp only [a, b]
      ring
    calc
      b *
          gammaTwoScaledH4SquareNormPower
            (horocycleSpeedNorm σ) (K (u := u))
            (scaledGammaTwoHorocycleFlow σ t
              (gammaTwoFrameQuotientMk g)) =
        b *
          ‖(standardizedUnaryColumn (B O) j t).C‖ ^
            (2 * K (u := u)) := by rw [hexact]
      _ =
        b *
          ‖((((B O).physicalState
              (a * t)).base.base.source.linked j).unary.C)‖ ^
            (2 * K (u := u)) := by
          rw [standardizedUnaryColumn_C_eq O j t]
      _ ≤
        b *
          HGAS.Dynamics.inverseClockReciprocal
            (B O).clock (a * t) :=
          mul_le_mul_of_nonneg_left hcoordinate hb.le
      _ =
        b *
          HGAS.Dynamics.inverseClockReciprocal
            hreverse (b * t) := by
          rw [(B O).inverseClockReciprocal_reverseClock]
          rw [hat]
      _ =
        HGAS.Dynamics.inverseClockReciprocal
          hclock t := by
          simpa only [hclock, hreverse, b, w] using
            (HGAS.Dynamics.inverseClockReciprocal_rangeRescale
              hreverse hb t).symm
  exact
    not_gammaTwoHaarGeneric_of_positiveMeanClock_and_positiveMultiple_scaledH4Square_orbitBound
      (scaledGammaTwoHorocycleFlow σ)
      hgeneric hclock hmean_pos hmean
      (horocycleSpeedNorm σ)
      (horocycleSpeedNorm_ne_zero hσ)
      (K (u := u)) (one_le_K (u := u))
      b hb horbit

/-- Orientation-free endpoint for an exact frame lift of a standardized
selected detector column. -/
theorem not_haarGeneric_of_standardizedExactFrameBranch
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
    (T : ℝ → ℍ)
    (hlambda :
      ∀ t,
        UnaryModularState.lambdaCoordinate
            (standardizedUnaryColumn (B O) j t) =
          canonicalLambda (T t))
    (g : RealModularFrame) (σ : ℝ) (hσ : σ ≠ 0)
    (hframe :
      ∀ t,
        T t =
          realModularFrameBasePoint
            (g * upperUnipotent (σ * t)))
    (hgeneric :
      IsForwardGenericFor
        (scaledGammaTwoHorocycleFlow σ)
        gammaTwoFrameHaarProbability
        (gammaTwoFrameQuotientMk g)) :
    False := by
  have ha0 :
      columnStandardScale (B O) j ≠ 0 :=
    SelectedTwoSidedValidityOrbit.columnStandardScale_ne_zero
      (B O) hscale hp j
  rcases lt_or_gt_of_ne ha0 with ha | ha
  · exact
      not_haarGeneric_of_standardizedExactFrameBranch_of_scale_neg
        O hscale hp j T hlambda g σ hσ hframe ha hgeneric
  · exact
      not_haarGeneric_of_standardizedExactFrameBranch_of_scale_pos
        O hscale hp j T hlambda g σ hσ hframe ha hgeneric

end SelectedBidirectionalValidityOrbit

end

end HGAS.NormalizedCorrectedFixedDetectorStandardizedHaarExclusion
