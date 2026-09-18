import HGAS.Dynamics.ErgodicInvariantProbability
import HGAS.Modular.TwoControllerLinkedJacobiMixedClockDynamics
import Mathlib.Tactic

/-!
# The zero-speed equator of the faithful mixed clock factor

The common clock speed in the mixed compactification is `w^8`.  The set
where it vanishes is therefore exactly the unique affine equator `w=0`.
This file proves directly from the emitted polynomial equation that the
equator is invariant under the canonical compact base flow.

Consequently an ergodic invariant probability satisfies a sharp
dichotomy:

* it is supported on the zero-speed equator; or
* the clock speed is nonzero almost everywhere.

If the speed has nonzero integral, only the second alternative is
possible.  This is the precise measure-theoretic fact needed to recover
almost-everywhere information from the normalized clock-density measure.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BoundedContinuousFunction ENNReal NNReal

namespace HGAS.Modular.TwoControllerLinkedJacobiMixedClockEquator

open HGAS
open TwoControllerLinkedJacobiMixedCompactSourceCode
open TwoControllerLinkedJacobiMixedClockDynamics

abbrev BaseSpace :=
  TwoControllerLinkedJacobiMixedClockProjection.BaseSpace

/-- Evaluation of the cleared affine-block dot polynomial on the compact
base. -/
def baseAffineDotValue
    (pΩ pN : RationalCode)
    (y : BaseSpace) : ℝ :=
  ratMvPolynomialEval
    (PolynomialCode.decode
      (MixedCentralPolynomialCode.affineBlockDotCode
        layout clearingExponent (sourceFieldCode pΩ pN)
        (0 : Fin affineBlockCount))) y.1

theorem continuous_baseAffineDotValue
    (pΩ pN : RationalCode) :
    Continuous (baseAffineDotValue pΩ pN) :=
  (contDiff_ratMvPolynomialEval
    (PolynomialCode.decode
      (MixedCentralPolynomialCode.affineBlockDotCode
        layout clearingExponent (sourceFieldCode pΩ pN)
        (0 : Fin affineBlockCount)))).continuous.comp
    (continuous_subtype_val :
      Continuous (fun y : BaseSpace ↦ y.1))

/-- The unique affine chart coordinate. -/
def chartWeight (y : BaseSpace) : ℝ :=
  affineWeights y (0 : Fin affineBlockCount)

theorem continuous_chartWeight :
    Continuous chartWeight :=
  (continuous_apply (0 : Fin affineBlockCount)).comp
    continuous_affineWeights

/-- The literal base-field chart equation factors as
`w' = (-w D) w`. -/
theorem realize_baseFieldCode_chartWeight
    (pΩ pN : RationalCode)
    (y : BaseSpace) :
    PolynomialFieldCode.realize
        (CompactAccumulatorPipelineCode.baseFieldCode
          layout clearingExponent (sourceFieldCode pΩ pN))
        y.1
        (MixedCentralPolynomialCode.wIndex
          (n := sourceDimension)
          (0 : Fin affineBlockCount)) =
      (-chartWeight y * baseAffineDotValue pΩ pN y) *
        chartWeight y := by
  rw [PolynomialFieldCode.realize_apply,
    CompactAccumulatorPipelineCode.baseFieldCode]
  simp only [MixedCentralPolynomialCode.fieldCode,
    MixedCentralPolynomialCode.finSumFinEquiv_symm_wIndex,
    MixedCentralPolynomialCode.wFieldCode,
    PolynomialCode.decode_neg_code,
    PolynomialCode.decode_mul_code,
    PolynomialCode.decode_pow_code,
    PolynomialCode.decode_varCode,
    map_neg, map_mul, map_pow, MvPolynomial.eval₂Hom_X',
    baseAffineDotValue, ratMvPolynomialEval_eq_eval₂Hom,
    chartWeight, affineWeights]
  ring

/-- The zero-speed equator. -/
def clockEquator : Set BaseSpace :=
  {y | clockSlowdown y = 0}

theorem clockEquator_eq_chartWeight_zero :
    clockEquator = {y : BaseSpace | chartWeight y = 0} := by
  ext y
  simp only [clockEquator, Set.mem_setOf_eq,
    clockSlowdown_eq_zero_iff, chartWeight, affineWeights]

theorem isClosed_clockEquator :
    IsClosed clockEquator := by
  rw [clockEquator_eq_chartWeight_zero]
  exact isClosed_eq continuous_chartWeight continuous_const

theorem measurableSet_clockEquator :
    MeasurableSet clockEquator :=
  isClosed_clockEquator.measurableSet

/-- The zero-speed equator is invariant under the canonical mixed base
flow. -/
theorem isInvariant_clockEquator
    (pΩ pN : RationalCode) :
    IsInvariant (mixedBaseFlow pΩ pN) clockEquator := by
  intro t y hy
  let r : ℝ → ℝ :=
    fun s ↦ chartWeight (mixedBaseFlow pΩ pN s y)
  let a : ℝ → ℝ :=
    fun s ↦
      -chartWeight (mixedBaseFlow pΩ pN s y) *
        baseAffineDotValue pΩ pN (mixedBaseFlow pΩ pN s y)
  have htrajectory :
      Continuous (fun s : ℝ ↦ mixedBaseFlow pΩ pN s y) :=
    (mixedBaseFlow pΩ pN).continuous
      continuous_id continuous_const
  have ha : Continuous a := by
    exact
      ((continuous_chartWeight.comp htrajectory).neg.mul
        (continuous_baseAffineDotValue pΩ pN |>.comp htrajectory))
  have hcurve :=
    CompactAccumulatorPipelineCode.baseFlow_integralCurve
      layout 9 clearingExponent (sourceFieldCode pΩ pN)
      (sourceFieldCode_termsDegreeLE pΩ pN)
      (baseCompactTangency pΩ pN) y
  have hr : ∀ s, HasDerivAt r (a s * r s) s := by
    intro s
    have hcoord :=
      (hasDerivAt_pi.mp (hcurve s))
        (MixedCentralPolynomialCode.wIndex
          (n := sourceDimension)
          (0 : Fin affineBlockCount))
    change
      HasDerivAt r
        (PolynomialFieldCode.realize
          (CompactAccumulatorPipelineCode.baseFieldCode
            layout clearingExponent (sourceFieldCode pΩ pN))
          (mixedBaseFlow pΩ pN s y).1
          (MixedCentralPolynomialCode.wIndex
            (n := sourceDimension)
            (0 : Fin affineBlockCount)))
        s at hcoord
    rw [realize_baseFieldCode_chartWeight] at hcoord
    simpa only [a, r] using hcoord
  have hr0 : r 0 = 0 := by
    rw [show r 0 = chartWeight y by
      simp [r, Flow.map_zero_apply]]
    rw [clockEquator_eq_chartWeight_zero] at hy
    exact hy
  have hzero :=
    real_eq_zero_of_hasDerivAt_eq_mul a r ha hr hr0
  rw [clockEquator_eq_chartWeight_zero]
  exact congrFun hzero t

/-- Ergodicity gives the exact alternative: full mass on the zero-speed
equator, or nonzero speed almost everywhere. -/
theorem equator_full_or_speed_ae_ne_zero
    (pΩ pN : RationalCode)
    (η : ProbabilityMeasure BaseSpace)
    (hη :
      HGAS.Dynamics.IsErgodicInvariantProbability
        (mixedBaseFlow pΩ pN) η) :
    (η : Measure BaseSpace) clockEquator = 1 ∨
      ∀ᵐ y ∂(η : Measure BaseSpace), clockSlowdown y ≠ 0 := by
  rcases hη.zero_or_one_of_isInvariant
      measurableSet_clockEquator
      (isInvariant_clockEquator pΩ pN) with
    hzero | hone
  · right
    have hnot :
        ∀ᵐ y ∂(η : Measure BaseSpace), y ∉ clockEquator := by
      rw [ae_iff]
      simpa only [not_not] using hzero
    filter_upwards [hnot] with y hy
    simpa only [clockEquator, Set.mem_compl_iff,
      Set.mem_setOf_eq] using hy
  · exact Or.inl hone

/-- A nonzero total clock mass rules out the equatorial alternative. -/
theorem clockSlowdown_ae_ne_zero_of_mass_ne_zero
    (pΩ pN : RationalCode)
    (η : ProbabilityMeasure BaseSpace)
    (hη :
      HGAS.Dynamics.IsErgodicInvariantProbability
        (mixedBaseFlow pΩ pN) η)
    (a : ℝ≥0) (ha : a ≠ 0)
    (hmass :
      ∫⁻ y, (clockSlowdownBCF y : ENNReal)
          ∂(η : Measure BaseSpace) =
        (a : ENNReal)) :
    ∀ᵐ y ∂(η : Measure BaseSpace), clockSlowdown y ≠ 0 := by
  rcases equator_full_or_speed_ae_ne_zero pΩ pN η hη with
    hequator | hpositive
  · exfalso
    have hae :
        ∀ᵐ y ∂(η : Measure BaseSpace), y ∈ clockEquator := by
      apply (ae_mem_iff_measure_eq
        measurableSet_clockEquator.nullMeasurableSet).2
      simpa only [measure_univ] using hequator
    have hzero :
        ∀ᵐ y ∂(η : Measure BaseSpace),
          (clockSlowdownBCF y : ENNReal) = 0 := by
      filter_upwards [hae] with y hy
      rw [ENNReal.coe_eq_zero, clockSlowdownBCF_apply]
      apply NNReal.eq
      simpa only [clockSlowdownNNReal_coe, NNReal.coe_zero,
        clockEquator, Set.mem_setOf_eq] using hy
    have hintegral :
        (∫⁻ y, (clockSlowdownBCF y : ENNReal)
            ∂(η : Measure BaseSpace)) = 0 := by
      rw [lintegral_congr_ae hzero]
      simp
    rw [hintegral] at hmass
    have hazero : a = 0 := by
      exact_mod_cast hmass.symm
    exact ha hazero
  · exact hpositive

end HGAS.Modular.TwoControllerLinkedJacobiMixedClockEquator
