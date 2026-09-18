import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorStandardizedHaarExclusion
import HGAS.Modular.GammaTwoOffPeriodicUnique
import Mathlib.Tactic

/-!
# Unit-speed exclusion for an arbitrary signed exact frame

Exact frame reconstruction returns

```text
T(t) = basePoint(g * upperUnipotent(σ t)),   σ ≠ 0,
```

while the unconditional pointwise Dani--Smillie theorem is exposed for
the positive unit-speed flow.  There is no need to prove a separate
time-reversal theorem for generic points.  Instead, evaluate the detector
identity at standardized time `σ⁻¹ t`.  The quotient point is then
literally

```text
gammaTwoHorocycleFlow t (quotientMk g).
```

The corresponding physical time factor is

```text
c = columnStandardScale * σ⁻¹.
```

If `c > 0`, range-rescale the original complete clock.  If `c < 0`,
reverse that clock first and range-rescale by `-c`.  Bidirectional
validity supplies the same positive mean in both orientations.

This simple reparametrization closes the signed-speed interface mismatch
without transporting one-sided genericity through a negative time
change.
-/

namespace
  HGAS.NormalizedFixedDetectorUnitSpeedHaarExclusion

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
open
  NormalizedCorrectedFixedDetectorStandardizedHaarExclusion.SelectedBidirectionalValidityOrbit

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

private theorem one_le_K : 1 ≤ K (u := u) := by
  unfold K speedExponent
  unfold
    NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDegreeBound
    CorrectedFixedDetectorCompactSourceCode.sourceDegreeBound
    FixedDetectorPolynomialCode.fieldDegree
  omega

/-- Reparametrizing an arbitrary nonzero exact frame by inverse speed
excludes Haar genericity for the positive unit-speed horocycle flow. -/
theorem
    not_unitSpeedHaarGeneric_of_standardizedExactFrameBranch
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
        gammaTwoHorocycleFlow
        gammaTwoFrameHaarProbability
        (gammaTwoFrameQuotientMk g)) :
    False := by
  let a : ℝ := columnStandardScale (B O) j
  let r : ℝ := σ⁻¹
  let c : ℝ := a * r
  let w : ℝ → ℝ :=
    twoSidedClockWeight (K (u := u))
      (affineCurve u (B O).point)
  have ha0 : a ≠ 0 := by
    simpa only [a] using
      columnStandardScale_ne_zero (B O) hscale hp j
  have hr0 : r ≠ 0 := by
    simpa only [r] using inv_ne_zero hσ
  have hc0 : c ≠ 0 := by
    exact mul_ne_zero ha0 hr0
  have hz :
      IsScaledUnaryModularTrajectory
        modularIndependentVariableClock
        (standardizedUnaryColumn (B O) j) :=
    standardizedUnaryColumn_isScaledTrajectory
      (B O) hscale hp j
  have hinitial :=
    standardizedUnaryColumn_generic O hscale hp j
  have hB :
      ∀ t,
        UnaryModularState.B
          (standardizedUnaryColumn (B O) j t) ≠ 0 :=
    hz.B_ne_zero hinitial.2.2
  have hflow :
      ∀ t : ℝ,
        scaledGammaTwoHorocycleFlow σ (r * t)
            (gammaTwoFrameQuotientMk g) =
          gammaTwoHorocycleFlow t
            (gammaTwoFrameQuotientMk g) := by
    intro t
    change
      gammaTwoHorocycleFlow (σ * (r * t))
          (gammaTwoFrameQuotientMk g) =
        gammaTwoHorocycleFlow t
          (gammaTwoFrameQuotientMk g)
    congr 1
    dsimp only [r]
    field_simp
  have hexact :
      ∀ t : ℝ,
        gammaTwoScaledH4SquareNormPower
            (horocycleSpeedNorm σ) (K (u := u))
            (gammaTwoHorocycleFlow t
              (gammaTwoFrameQuotientMk g)) =
          ‖(standardizedUnaryColumn
              (B O) j (r * t)).C‖ ^
            (2 * K (u := u)) := by
    intro t
    have h :=
      gammaTwoScaledH4SquareNormPower_eq_unaryC_norm_pow
        hz hB hlambda g σ hframe
        (K (u := u)) (r * t)
    rwa [hflow t] at h
  have hphysicalTime :
      ∀ t : ℝ, a * (r * t) = c * t := by
    intro t
    simp only [c]
    ring
  rcases lt_or_gt_of_ne hc0 with hcneg | hcpos
  · let b : ℝ := -c
    let hreverse :=
      reverseClock (B O).clock
    have hb : 0 < b := by
      simpa only [b] using neg_pos.mpr hcneg
    let hclock :
        PositiveIntegralClock
          (rangeRescaledClockWeight b
            (fun t ↦ w (-t))) :=
      hreverse.rangeRescale hb
    have hmean :
        Tendsto
          (fun n : ℕ ↦
            (positiveIntegerHorizon n)⁻¹ *
              integralClock
                (rangeRescaledClockWeight b
                  (fun t ↦ w (-t)))
                (positiveIntegerHorizon n))
          atTop
          (nhds (b⁻¹ * (B O).speedMean)) := by
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
                (gammaTwoHorocycleFlow t
                  (gammaTwoFrameQuotientMk g)) ≤
            HGAS.Dynamics.inverseClockReciprocal hclock t := by
      intro t
      have hcoordinate :=
        (B O).unaryC_evenPower_le_inverseClockReciprocal
          j (c * t)
      have hct : c * t = -(b * t) := by
        simp only [b]
        ring
      calc
        b *
            gammaTwoScaledH4SquareNormPower
              (horocycleSpeedNorm σ) (K (u := u))
              (gammaTwoHorocycleFlow t
                (gammaTwoFrameQuotientMk g)) =
          b *
            ‖(standardizedUnaryColumn
                (B O) j (r * t)).C‖ ^
              (2 * K (u := u)) := by rw [hexact t]
        _ =
          b *
            ‖((((B O).physicalState
                (a * (r * t))).base.base.source.linked j).unary.C)‖ ^
              (2 * K (u := u)) := by
            rw [standardizedUnaryColumn_C_eq O j (r * t)]
        _ =
          b *
            ‖((((B O).physicalState
                (c * t)).base.base.source.linked j).unary.C)‖ ^
              (2 * K (u := u)) := by
            rw [hphysicalTime t]
        _ ≤
          b *
            HGAS.Dynamics.inverseClockReciprocal
              (B O).clock (c * t) :=
            mul_le_mul_of_nonneg_left hcoordinate hb.le
        _ =
          b *
            HGAS.Dynamics.inverseClockReciprocal
              hreverse (b * t) := by
            rw [(B O).inverseClockReciprocal_reverseClock]
            rw [hct]
        _ =
          HGAS.Dynamics.inverseClockReciprocal
            hclock t := by
            simpa only [hclock, hreverse, b, w] using
              (HGAS.Dynamics.inverseClockReciprocal_rangeRescale
                hreverse hb t).symm
    exact
      not_gammaTwoHaarGeneric_of_positiveMeanClock_and_positiveMultiple_scaledH4Square_orbitBound
        gammaTwoHorocycleFlow
        hgeneric hclock hmean_pos hmean
        (horocycleSpeedNorm σ)
        (horocycleSpeedNorm_ne_zero hσ)
        (K (u := u)) (one_le_K (u := u))
        b hb horbit
  · let hclock :
        PositiveIntegralClock
          (rangeRescaledClockWeight c w) :=
      (B O).clock.rangeRescale hcpos
    have hmean :
        Tendsto
          (fun n : ℕ ↦
            (positiveIntegerHorizon n)⁻¹ *
              integralClock
                (rangeRescaledClockWeight c w)
                (positiveIntegerHorizon n))
          atTop
          (nhds (c⁻¹ * (B O).speedMean)) := by
      exact
        HGAS.Dynamics.positiveIntegerMean_rangeRescale
          (b := c) (by
            simpa only [w] using
              (B O).clock_positiveIntegerMean)
    have hmean_pos : 0 < c⁻¹ * (B O).speedMean :=
      mul_pos (inv_pos.mpr hcpos) (B O).speedMean_pos
    have horbit :
        ∀ t : ℝ,
          c *
              gammaTwoScaledH4SquareNormPower
                (horocycleSpeedNorm σ) (K (u := u))
                (gammaTwoHorocycleFlow t
                  (gammaTwoFrameQuotientMk g)) ≤
            HGAS.Dynamics.inverseClockReciprocal hclock t := by
      intro t
      have hcoordinate :=
        (B O).unaryC_evenPower_le_inverseClockReciprocal
          j (c * t)
      calc
        c *
            gammaTwoScaledH4SquareNormPower
              (horocycleSpeedNorm σ) (K (u := u))
              (gammaTwoHorocycleFlow t
                (gammaTwoFrameQuotientMk g)) =
          c *
            ‖(standardizedUnaryColumn
                (B O) j (r * t)).C‖ ^
              (2 * K (u := u)) := by rw [hexact t]
        _ =
          c *
            ‖((((B O).physicalState
                (a * (r * t))).base.base.source.linked j).unary.C)‖ ^
              (2 * K (u := u)) := by
            rw [standardizedUnaryColumn_C_eq O j (r * t)]
        _ =
          c *
            ‖((((B O).physicalState
                (c * t)).base.base.source.linked j).unary.C)‖ ^
              (2 * K (u := u)) := by
            rw [hphysicalTime t]
        _ ≤
          c *
            HGAS.Dynamics.inverseClockReciprocal
              (B O).clock (c * t) :=
            mul_le_mul_of_nonneg_left hcoordinate hcpos.le
        _ =
          HGAS.Dynamics.inverseClockReciprocal
            hclock t := by
            simpa only [hclock, c, w] using
              (HGAS.Dynamics.inverseClockReciprocal_rangeRescale
                (B O).clock hcpos t).symm
    exact
      not_gammaTwoHaarGeneric_of_positiveMeanClock_and_positiveMultiple_scaledH4Square_orbitBound
        gammaTwoHorocycleFlow
        hgeneric hclock hmean_pos hmean
        (horocycleSpeedNorm σ)
        (horocycleSpeedNorm_ne_zero hσ)
        (K (u := u)) (one_le_K (u := u))
        c hcpos horbit

/-- The arbitrary signed exact-frame branch of a standardized selected
detector column is periodic.  This is the direct unconditional
Dani--Smillie composition. -/
theorem periodic_of_standardizedExactFrameBranch
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
            (g * upperUnipotent (σ * t))) :
    IsPeriodicHorocyclePoint 1
      (gammaTwoFrameQuotientMk g) := by
  by_contra hnonperiodic
  have hgeneric :
      IsForwardGenericFor
        gammaTwoHorocycleFlow
        gammaTwoFrameHaarProbability
        (gammaTwoFrameQuotientMk g) :=
    gammaTwoPointwiseHorocycleEquidistribution_unconditional
      gammaTwoFrameHaarProbability
      gammaTwoFrameHaarProbability_rightInvariant
      (gammaTwoFrameQuotientMk g)
      hnonperiodic
  exact
    not_unitSpeedHaarGeneric_of_standardizedExactFrameBranch
      O hscale hp j T hlambda g σ hσ hframe hgeneric

/-- The same exact branch is periodic for its reconstructed signed speed.
This is equivalent to the unit-speed conclusion because `σ ≠ 0`. -/
theorem scaledPeriodic_of_standardizedExactFrameBranch
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
            (g * upperUnipotent (σ * t))) :
    IsPeriodicHorocyclePoint σ
      (gammaTwoFrameQuotientMk g) := by
  apply
    (isPeriodicHorocyclePoint_iff_of_ne_zero hσ
      (gammaTwoFrameQuotientMk g)).mpr
  exact
    periodic_of_standardizedExactFrameBranch
      O hscale hp j T hlambda g σ hσ hframe

end SelectedBidirectionalValidityOrbit

end

end
  HGAS.NormalizedFixedDetectorUnitSpeedHaarExclusion
