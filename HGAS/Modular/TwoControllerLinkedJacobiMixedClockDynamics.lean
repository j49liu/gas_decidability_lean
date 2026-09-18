import HGAS.Compiler.CompactAccumulatorPipelineFactor
import HGAS.Dynamics.InvariantMeasureTimeChangedFactor
import HGAS.Modular.TwoControllerLinkedJacobiMixedClockProjection
import Mathlib.Tactic

/-!
# The exact clock time change in the faithful mixed compactification

The mixed compactification leaves the four controller and phase circles
geometrically unchanged, but denominator clearing multiplies their vector
field by one common scalar.  In the present one-affine-block construction
that scalar is

```
                         f(y) = w(y)^8.
```

Thus the clock observation is not a same-time factor of the compact base
flow.  It is an exact orbit factor with the state-dependent time change
`dτ/dt = f(y(t))`.  This file proves that statement first at the level of
literal compiled polynomial coordinates and then as an orbitwise
derivative theorem for the canonical compact base flow.

The linear coordinate projection and the finite-product clock comparison
are kept separate.  Those lemmas can be reused by other mixed
compactifications whose already-compact blocks carry autonomous
polynomial subsystems.
-/

noncomputable section

namespace HGAS.Modular.TwoControllerLinkedJacobiMixedClockDynamics

open HGAS
open TwoControllerLinkedJacobiMixedCompactSourceCode
open scoped BoundedContinuousFunction NNReal

namespace Projection

abbrev BaseSpace :=
  TwoControllerLinkedJacobiMixedClockProjection.BaseSpace

end Projection

/-- The chart weights of the newly compactified affine blocks.  There is
exactly one such block in the faithful linked-Jacobi construction. -/
def affineWeights
    (y : Projection.BaseSpace) :
    Fin affineBlockCount → ℝ :=
  fun b ↦
    y.1 (MixedCentralPolynomialCode.wIndex
      (n := sourceDimension) b)

/-- The common denominator-clearing speed seen by every inherited clock
coordinate. -/
def clockSlowdown (y : Projection.BaseSpace) : ℝ :=
  MixedCentralPolynomialCode.slowdown
    clearingExponent (affineWeights y)

/-- In the one-block construction the abstract product defining the
slowdown is literally the eighth power of its unique chart coordinate. -/
theorem clockSlowdown_eq_weight_pow
    (y : Projection.BaseSpace) :
    clockSlowdown y =
      y.1 (MixedCentralPolynomialCode.wIndex
        (n := sourceDimension) (0 : Fin affineBlockCount)) ^ 8 := by
  simp [clockSlowdown, affineWeights,
    MixedCentralPolynomialCode.slowdown,
    clearingExponent, affineBlockCount]

theorem clockSlowdown_nonneg
    (y : Projection.BaseSpace) :
    0 ≤ clockSlowdown y := by
  rw [clockSlowdown_eq_weight_pow]
  positivity

theorem clockSlowdown_eq_zero_iff
    (y : Projection.BaseSpace) :
    clockSlowdown y = 0 ↔
      y.1 (MixedCentralPolynomialCode.wIndex
        (n := sourceDimension) (0 : Fin affineBlockCount)) = 0 := by
  rw [clockSlowdown_eq_weight_pow, pow_eq_zero_iff]
  norm_num

theorem continuous_affineWeights :
    Continuous affineWeights := by
  apply continuous_pi
  intro b
  exact
    (continuous_apply
      (MixedCentralPolynomialCode.wIndex
        (n := sourceDimension) b)).comp
      continuous_subtype_val

theorem continuous_clockSlowdown :
    Continuous clockSlowdown := by
  rw [show clockSlowdown =
      fun y ↦
        y.1 (MixedCentralPolynomialCode.wIndex
          (n := sourceDimension)
          (0 : Fin affineBlockCount)) ^ 8 by
    funext y
    exact clockSlowdown_eq_weight_pow y]
  exact
    (((continuous_apply
      (MixedCentralPolynomialCode.wIndex
        (n := sourceDimension)
        (0 : Fin affineBlockCount))).comp
      continuous_subtype_val).pow 8)

/-- Package the nonnegative clock speed as an `ℝ≥0`-valued continuous
function, as required by invariant-measure time-change statements. -/
def clockSlowdownNNReal
    (y : Projection.BaseSpace) : ℝ≥0 :=
  ⟨clockSlowdown y, clockSlowdown_nonneg y⟩

@[simp]
theorem clockSlowdownNNReal_coe
    (y : Projection.BaseSpace) :
    (clockSlowdownNNReal y : ℝ) = clockSlowdown y :=
  rfl

theorem continuous_clockSlowdownNNReal :
    Continuous clockSlowdownNNReal :=
  continuous_clockSlowdown.subtype_mk _

/-- The clock speed as a bounded continuous function on the compact
mixed base. -/
def clockSlowdownBCF :
    Projection.BaseSpace →ᵇ ℝ≥0 :=
  BoundedContinuousFunction.mkOfCompact
    ⟨clockSlowdownNNReal, continuous_clockSlowdownNNReal⟩

@[simp]
theorem clockSlowdownBCF_apply
    (y : Projection.BaseSpace) :
    clockSlowdownBCF y = clockSlowdownNNReal y :=
  rfl

/-- Every one of the eight controller coordinates belongs to one of the
four already-compact circle blocks. -/
theorem layout_controllersEmbedding
    (i :
      Fin
        TwoControllerLinkedJacobiPolynomialCode.controllerPairDimension) :
    layout
        (TwoControllerLinkedJacobiPolynomialCode.controllersEmbedding i) =
      Sum.inr (controllerCompactBlock i) := by
  simp [layout, RightAffineLeftCompactLayout.layout,
    TwoControllerLinkedJacobiPolynomialCode.controllersEmbedding]

/-! ## The original controller pair is the canonical two-clock field -/

/-- Evaluating the thirty-six-dimensional source field in a controller
coordinate only sees the eight-dimensional controller-pair field. -/
theorem realize_sourceFieldCode_controllersEmbedding
    (pΩ pN : RationalCode)
    (x : Fin sourceDimension → ℝ)
    (i :
      Fin
        TwoControllerLinkedJacobiPolynomialCode.controllerPairDimension) :
    PolynomialFieldCode.realize (sourceFieldCode pΩ pN) x
        (TwoControllerLinkedJacobiPolynomialCode.controllersEmbedding i) =
      PolynomialFieldCode.realize
        (TwoControllerLinkedJacobiPolynomialCode.controllerPairFieldCode
          pΩ pN)
        (x ∘
          TwoControllerLinkedJacobiPolynomialCode.controllersEmbedding)
        i := by
  rw [PolynomialFieldCode.realize_apply, sourceFieldCode,
    TwoControllerLinkedJacobiPolynomialCode.fieldCode_controllersEmbedding,
    PolynomialBlockCode.left,
    PolynomialCode.eval₂Hom_decode_injectVariables]
  rfl

private theorem realize_controllerPairFieldCode_omega
    (pΩ pN : RationalCode)
    (x : Fin sourceDimension → ℝ)
    (q : Fin HGAS.Clocks.ControllerPolynomialCode.dimension) :
    PolynomialFieldCode.realize
        (TwoControllerLinkedJacobiPolynomialCode.controllerPairFieldCode
          pΩ pN)
        (x ∘
          TwoControllerLinkedJacobiPolynomialCode.controllersEmbedding)
        (TwoControllerLinkedJacobiPolynomialCode.omegaControllerEmbedding
          q) =
      PolynomialFieldCode.realize
        (HGAS.Clocks.ControllerPhaseProductPolynomialCode.fieldCode
          (![pΩ, pN] : Fin 2 → RationalCode))
        (fun i ↦
          x
            (TwoControllerLinkedJacobiPolynomialCode.controllersEmbedding
              i))
        (TwoControllerLinkedJacobiPolynomialCode.omegaControllerEmbedding
          q) := by
  rw [PolynomialFieldCode.realize_apply,
    TwoControllerLinkedJacobiPolynomialCode.controllerPairFieldCode]
  simp only [
    TwoControllerLinkedJacobiPolynomialCode.omegaControllerEmbedding]
  rw [PolynomialBlockCode.field_leftEmbedding,
    PolynomialBlockCode.left,
    PolynomialCode.eval₂Hom_decode_injectVariables]
  have hi :
      PolynomialBlockCode.leftEmbedding
          (p := HGAS.Clocks.ControllerPolynomialCode.dimension) q =
        HGAS.Clocks.ControllerPhaseProductPolynomialCode.blockEmbedding
          (0 : Fin 2) q := by
    simpa [
      TwoControllerLinkedJacobiPolynomialCode.omegaControllerEmbedding]
      using
        (TwoControllerLinkedJacobiMixedClockProjection.productBlockEmbedding_zero
          q).symm
  rw [hi,
    HGAS.Clocks.ControllerPhaseProductPolynomialCode.realize_fieldCode_blockEmbedding]
  congr 2

private theorem realize_controllerPairFieldCode_number
    (pΩ pN : RationalCode)
    (x : Fin sourceDimension → ℝ)
    (q : Fin HGAS.Clocks.ControllerPolynomialCode.dimension) :
    PolynomialFieldCode.realize
        (TwoControllerLinkedJacobiPolynomialCode.controllerPairFieldCode
          pΩ pN)
        (x ∘
          TwoControllerLinkedJacobiPolynomialCode.controllersEmbedding)
        (TwoControllerLinkedJacobiPolynomialCode.numberControllerEmbedding
          q) =
      PolynomialFieldCode.realize
        (HGAS.Clocks.ControllerPhaseProductPolynomialCode.fieldCode
          (![pΩ, pN] : Fin 2 → RationalCode))
        (fun i ↦
          x
            (TwoControllerLinkedJacobiPolynomialCode.controllersEmbedding
              i))
        (TwoControllerLinkedJacobiPolynomialCode.numberControllerEmbedding
          q) := by
  rw [PolynomialFieldCode.realize_apply,
    TwoControllerLinkedJacobiPolynomialCode.controllerPairFieldCode]
  simp only [
    TwoControllerLinkedJacobiPolynomialCode.numberControllerEmbedding]
  rw [PolynomialBlockCode.field_rightEmbedding,
    PolynomialBlockCode.right,
    PolynomialCode.eval₂Hom_decode_injectVariables]
  have hi :
      PolynomialBlockCode.rightEmbedding
          (m := HGAS.Clocks.ControllerPolynomialCode.dimension) q =
        HGAS.Clocks.ControllerPhaseProductPolynomialCode.blockEmbedding
          (1 : Fin 2) q := by
    simpa [
      TwoControllerLinkedJacobiPolynomialCode.numberControllerEmbedding]
      using
        (TwoControllerLinkedJacobiMixedClockProjection.productBlockEmbedding_one
          q).symm
  rw [hi,
    HGAS.Clocks.ControllerPhaseProductPolynomialCode.realize_fieldCode_blockEmbedding]
  congr 2
  funext i
  exact congrArg
    (fun u ↦
      x
        (TwoControllerLinkedJacobiPolynomialCode.controllersEmbedding u))
    (TwoControllerLinkedJacobiMixedClockProjection.productBlockEmbedding_one
      i).symm

/-- Coordinate-free eight-dimensional version of the preceding two block
computations. -/
theorem realize_controllerPairFieldCode_eq_clockField
    (pΩ pN : RationalCode)
    (x : Fin sourceDimension → ℝ)
    (i :
      Fin
        TwoControllerLinkedJacobiPolynomialCode.controllerPairDimension) :
    PolynomialFieldCode.realize
        (TwoControllerLinkedJacobiPolynomialCode.controllerPairFieldCode
          pΩ pN)
        (x ∘
          TwoControllerLinkedJacobiPolynomialCode.controllersEmbedding)
        i =
      PolynomialFieldCode.realize
        (HGAS.Clocks.ControllerPhaseProductPolynomialCode.fieldCode
          (![pΩ, pN] : Fin 2 → RationalCode))
        (fun q ↦
          x
            (TwoControllerLinkedJacobiPolynomialCode.controllersEmbedding
              q))
        i := by
  obtain ⟨q | q, rfl⟩ := finSumFinEquiv.surjective i
  · exact realize_controllerPairFieldCode_omega pΩ pN x q
  · exact realize_controllerPairFieldCode_number pΩ pN x q

/-- The controller part of the original linked-Jacobi source is exactly
the canonical finite-product two-clock compiler. -/
theorem realize_sourceFieldCode_eq_clockField
    (pΩ pN : RationalCode)
    (x : Fin sourceDimension → ℝ)
    (i :
      Fin
        TwoControllerLinkedJacobiPolynomialCode.controllerPairDimension) :
    PolynomialFieldCode.realize (sourceFieldCode pΩ pN) x
        (TwoControllerLinkedJacobiPolynomialCode.controllersEmbedding i) =
      PolynomialFieldCode.realize
        (HGAS.Clocks.ControllerPhaseProductPolynomialCode.fieldCode
          (![pΩ, pN] : Fin 2 → RationalCode))
        (fun q ↦
          x
            (TwoControllerLinkedJacobiPolynomialCode.controllersEmbedding
              q))
        i := by
  rw [realize_sourceFieldCode_controllersEmbedding]
  exact realize_controllerPairFieldCode_eq_clockField pΩ pN x i

/-! ## Literal mixed-base velocity -/

/-- Each compact-base clock coordinate has exactly the common slowed
source velocity.  This theorem is global: it remains valid at the affine
equator `w=0`. -/
theorem realize_baseFieldCode_clockCoordinate
    (pΩ pN : RationalCode)
    (y : Projection.BaseSpace)
    (i :
      Fin
        TwoControllerLinkedJacobiPolynomialCode.controllerPairDimension) :
    PolynomialFieldCode.realize
        (CompactAccumulatorPipelineCode.baseFieldCode
          layout clearingExponent (sourceFieldCode pΩ pN))
        y.1
        (MixedCentralPolynomialCode.xIndex
          (k := affineBlockCount)
          (TwoControllerLinkedJacobiPolynomialCode.controllersEmbedding
            i)) =
      clockSlowdown y *
        PolynomialFieldCode.realize (sourceFieldCode pΩ pN)
          (TwoControllerLinkedJacobiMixedClockProjection.oldPoint y)
          (TwoControllerLinkedJacobiPolynomialCode.controllersEmbedding
            i) := by
  let j :=
    TwoControllerLinkedJacobiPolynomialCode.controllersEmbedding i
  have hj :
      layout j = Sum.inr (controllerCompactBlock i) := by
    exact layout_controllersEmbedding i
  have hy :
      MixedCentralPolynomialCode.chartPoint
          (TwoControllerLinkedJacobiMixedClockProjection.oldPoint y)
          (affineWeights y) =
        y.1 :=
    MixedCentralPolynomialCode.chartPoint_decompose y.1
  rw [← hy]
  rw [PolynomialFieldCode.realize_apply,
    CompactAccumulatorPipelineCode.baseFieldCode]
  have hfield := congrFun
    (MixedCentralPolynomialCode.eval₂Hom_fieldCode_chartPoint
      layout clearingExponent (sourceFieldCode pΩ pN)
      (TwoControllerLinkedJacobiMixedClockProjection.oldPoint y)
      (affineWeights y))
    (MixedCentralPolynomialCode.xIndex
      (k := affineBlockCount) j)
  rw [hfield]
  simp only [MixedCentralPolynomialCode.mixedAmbientField,
    MixedCentralPolynomialCode.finSumFinEquiv_symm_xIndex]
  simp only [MixedCentralPolynomialCode.mixedXField, hj, one_mul]
  simp only [MixedCentralPolynomialCode.clearedSourceVelocity]
  rw [
    MixedCentralPolynomialCode.eval₂Hom_homogenize_chartPoint_of_termsAffineDegreeZero
        layout clearingExponent (sourceFieldCode pΩ pN j)
        (sourceFieldCode_termsAffineDegreeZero_of_compact
          pΩ pN j (controllerCompactBlock i) hj)
        (TwoControllerLinkedJacobiMixedClockProjection.oldPoint y)
        (affineWeights y)]
  rfl

/-- Vector form of the exact global time-change identity. -/
theorem clockVelocity_eq_slowdown_smul
    (pΩ pN : RationalCode)
    (y : Projection.BaseSpace) :
    (fun i ↦
      PolynomialFieldCode.realize
          (CompactAccumulatorPipelineCode.baseFieldCode
            layout clearingExponent (sourceFieldCode pΩ pN))
          y.1
          (MixedCentralPolynomialCode.xIndex
            (k := affineBlockCount)
            (TwoControllerLinkedJacobiPolynomialCode.controllersEmbedding
              i))) =
      clockSlowdown y •
        PolynomialFieldCode.realize
          (HGAS.Clocks.ControllerPhaseProductPolynomialCode.fieldCode
            (![pΩ, pN] : Fin 2 → RationalCode))
          (TwoControllerLinkedJacobiMixedClockProjection.clockRawPoint
            y) := by
  funext i
  rw [Pi.smul_apply, smul_eq_mul,
    realize_baseFieldCode_clockCoordinate,
    realize_sourceFieldCode_eq_clockField]
  rfl

/-! ## Orbitwise derivative theorem -/

/-- The eight-coordinate clock observation as a continuous linear map on
the ambient mixed-base coordinates. -/
def clockRawLinearMap :
    (Fin (sourceDimension + affineBlockCount) → ℝ) →L[ℝ]
      (Fin
          TwoControllerLinkedJacobiPolynomialCode.controllerPairDimension →
        ℝ) :=
  ContinuousLinearMap.pi fun i ↦
    ContinuousLinearMap.proj
      (MixedCentralPolynomialCode.xIndex
        (k := affineBlockCount)
        (TwoControllerLinkedJacobiPolynomialCode.controllersEmbedding i))

@[simp]
theorem clockRawLinearMap_apply
    (y : Projection.BaseSpace) :
    clockRawLinearMap y.1 =
      TwoControllerLinkedJacobiMixedClockProjection.clockRawPoint y :=
  rfl

/-- Canonical compact-base flow for the faithful mixed source. -/
def mixedBaseFlow
    (pΩ pN : RationalCode) :
    Flow ℝ Projection.BaseSpace :=
  CompactAccumulatorPipelineCode.baseFlow
    layout 9 clearingExponent (sourceFieldCode pΩ pN)

/-- The projected clock orbit has velocity `f` times the literal
two-clock polynomial field at every time, including times on the
equator where `f=0`. -/
theorem hasDerivAt_clockRawPoint_mixedBaseFlow
    (pΩ pN : RationalCode)
    (y : Projection.BaseSpace) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ ↦
        TwoControllerLinkedJacobiMixedClockProjection.clockRawPoint
          (mixedBaseFlow pΩ pN s y))
      (clockSlowdown (mixedBaseFlow pΩ pN t y) •
        PolynomialFieldCode.realize
          (HGAS.Clocks.ControllerPhaseProductPolynomialCode.fieldCode
            (![pΩ, pN] : Fin 2 → RationalCode))
          (TwoControllerLinkedJacobiMixedClockProjection.clockRawPoint
            (mixedBaseFlow pΩ pN t y)))
      t := by
  have hcurve :=
    CompactAccumulatorPipelineCode.baseFlow_integralCurve
      layout 9 clearingExponent (sourceFieldCode pΩ pN)
      (sourceFieldCode_termsDegreeLE pΩ pN)
      (baseCompactTangency pΩ pN) y
  have hprojected :=
    clockRawLinearMap.hasFDerivAt.comp_hasDerivAt t (hcurve t)
  change
    HasDerivAt
      ((clockRawLinearMap :
          (Fin (sourceDimension + affineBlockCount) → ℝ) →
            Fin
                TwoControllerLinkedJacobiPolynomialCode.controllerPairDimension →
              ℝ) ∘
        (fun s : ℝ ↦ (mixedBaseFlow pΩ pN s y).1))
      (clockRawLinearMap
        (PolynomialFieldCode.realize
          (CompactAccumulatorPipelineCode.baseFieldCode
            layout clearingExponent (sourceFieldCode pΩ pN))
          (mixedBaseFlow pΩ pN t y).1))
      t at hprojected
  have hraw :
      HasDerivAt
        (fun s : ℝ ↦
          TwoControllerLinkedJacobiMixedClockProjection.clockRawPoint
            (mixedBaseFlow pΩ pN s y))
        (clockRawLinearMap
          (PolynomialFieldCode.realize
            (CompactAccumulatorPipelineCode.baseFieldCode
              layout clearingExponent (sourceFieldCode pΩ pN))
            (mixedBaseFlow pΩ pN t y).1))
        t := by
    simpa only [Function.comp_apply, clockRawLinearMap_apply] using
      hprojected
  have hvelocity :=
    clockVelocity_eq_slowdown_smul pΩ pN
      (mixedBaseFlow pΩ pN t y)
  change
    clockRawLinearMap
        (PolynomialFieldCode.realize
          (CompactAccumulatorPipelineCode.baseFieldCode
            layout clearingExponent (sourceFieldCode pΩ pN))
          (mixedBaseFlow pΩ pN t y).1) =
      _ at hvelocity
  rw [hvelocity] at hraw
  exact hraw

/-! ## Reusable interface to invariant-measure time change -/

/-- Ambient eight-coordinate observation used by the generator criterion.
Its image lies in the literal four-circle variety by
`clockProjection`. -/
def rawClockObservation
    (y : Projection.BaseSpace) :
    Fin
        TwoControllerLinkedJacobiPolynomialCode.controllerPairDimension →
      ℝ :=
  TwoControllerLinkedJacobiMixedClockProjection.clockRawPoint y

theorem continuous_rawClockObservation :
    Continuous rawClockObservation :=
  TwoControllerLinkedJacobiMixedClockProjection.continuous_clockRawPoint

/-- Any ambient `C¹` ODE flow whose generator agrees with the canonical
two-clock polynomial field on the literal clock variety receives the
mixed-base clock observation as an exact time-changed factor.

This theorem is designed for a compactly supported ambient extension of
the clock field.  No assertion is made about that extension away from the
four-circle variety. -/
theorem isObservedGeneratorTimeChange_of_generator_eq_clockField
    (pΩ pN : RationalCode)
    (Φ :
      HGAS.Dynamics.C1ODEFlow
        (Fin
            TwoControllerLinkedJacobiPolynomialCode.controllerPairDimension →
          ℝ))
    (hgenerator :
      ∀ z :
          HGAS.Clocks.ControllerPhaseProductSphereFlow.ClockProductSphere
            2,
        Φ.generator z.1 =
          PolynomialFieldCode.realize
            (HGAS.Clocks.ControllerPhaseProductPolynomialCode.fieldCode
              (![pΩ, pN] : Fin 2 → RationalCode))
            z.1) :
    HGAS.Dynamics.IsObservedGeneratorTimeChange
      (mixedBaseFlow pΩ pN) Φ rawClockObservation
      clockSlowdownBCF := by
  intro y t
  have h :=
    hasDerivAt_clockRawPoint_mixedBaseFlow pΩ pN y t
  have hgen :
      Φ.generator
          (rawClockObservation (mixedBaseFlow pΩ pN t y)) =
        PolynomialFieldCode.realize
          (HGAS.Clocks.ControllerPhaseProductPolynomialCode.fieldCode
            (![pΩ, pN] : Fin 2 → RationalCode))
          (rawClockObservation (mixedBaseFlow pΩ pN t y)) := by
    simpa only [rawClockObservation,
      TwoControllerLinkedJacobiMixedClockProjection.clockProjection_val]
      using
        hgenerator
          (TwoControllerLinkedJacobiMixedClockProjection.clockProjection
            (mixedBaseFlow pΩ pN t y))
  rw [hgen]
  simpa only [rawClockObservation, clockSlowdownBCF_apply,
    clockSlowdownNNReal_coe,
    TwoControllerLinkedJacobiMixedClockProjection.clockProjection_val] using
      h

end HGAS.Modular.TwoControllerLinkedJacobiMixedClockDynamics
