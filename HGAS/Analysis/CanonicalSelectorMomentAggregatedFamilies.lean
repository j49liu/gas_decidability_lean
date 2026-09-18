import HGAS.Analysis.CanonicalSelectorMomentRadicalSummability
import Mathlib.Tactic

/-!
# Supported Fourier families for the seven corrected selector moments

The theta formulae for the detector are naturally written as sums indexed
by `ℤ` or `ℤ × ℤ`.  Those raw formulae can contain repeated exponents.
In particular, centering a moment kills the *sum* of the zero-frequency
coefficients, not every syntactic zero-frequency term separately.

This file turns each of the seven corrected centered moments into the
canonical family required by the cohomological-primitive API:

* detector characters are flattened to the literal fundamental clock
  coordinates `Fin (vars + eqs)`;
* equal exponents are collected;
* zero collected coefficients are discarded; and
* the remaining exponent map is injective and has no zero mode.

The construction also transports the unweighted and radical-height
weighted `ℓ¹` estimates.  It is deliberately packaged as a reusable
structure, so the later real/imaginary drift layout does not have to
repeat any theta-series analysis.
-/

noncomputable section

open Function

namespace HGAS.Analysis.CanonicalSelectorMomentAggregatedFamilies

open HGAS
open HGAS.Clocks
open CanonicalSelectorMomentRadicalSummability

variable {eqs vars : ℕ}

/-- Analytic data of one corrected centered selector moment before equal
Fourier exponents are collected. -/
structure RawCenteredFamily (eqs vars : ℕ) where
  Index : Type
  coefficient : Index → ℂ
  exponent : Index → DetectorPhase eqs vars → ℤ
  zeroMode :
    aggregateFourierCoefficient coefficient exponent 0 = 0
  summable_height :
    ∀ (radicand : Fin (vars + eqs) → ℕ) (heightPower : ℕ),
      Summable fun i ↦
        ‖coefficient i‖ *
          characterHeight radicand (exponent i) ^ heightPower

namespace RawCenteredFamily

/-- The exponent in the actual fundamental-clock indexing used by the
polynomial compiler. -/
def flatExponent (F : RawCenteredFamily eqs vars) :
    F.Index → Fin (vars + eqs) → ℤ :=
  fun i ↦ DetectorCharacterCode.flattenCharacter (F.exponent i)

/-- Fourth-root flattening is injective.  The factor four therefore
creates no new zero-frequency resonance. -/
theorem flattenCharacter_eq_zero_iff
    (a : DetectorPhase eqs vars → ℤ) :
    DetectorCharacterCode.flattenCharacter a = 0 ↔ a = 0 := by
  constructor
  · intro h
    funext phase
    have hi := congrFun h (finSumFinEquiv phase)
    have hi' : 4 * a phase = 0 := by
      simpa [DetectorCharacterCode.flattenCharacter] using hi
    exact (mul_eq_zero.mp hi').resolve_left (by norm_num)
  · rintro rfl
    funext i
    simp [DetectorCharacterCode.flattenCharacter]

/-- Collecting after fourth-root flattening has the same zero coefficient
as collecting in the arithmetic detector indexing. -/
theorem aggregate_flatExponent_zero (F : RawCenteredFamily eqs vars) :
    aggregateFourierCoefficient F.coefficient F.flatExponent 0 = 0 := by
  classical
  calc
    aggregateFourierCoefficient F.coefficient F.flatExponent 0 =
        ∑' i : F.Index,
          if F.flatExponent i = 0 then F.coefficient i else 0 :=
      aggregateFourierCoefficient_eq_tsum_ite
        F.coefficient F.flatExponent 0
    _ =
        ∑' i : F.Index,
          if F.exponent i = 0 then F.coefficient i else 0 := by
      apply tsum_congr
      intro i
      by_cases hi : F.exponent i = 0
      · have hflat : F.flatExponent i = 0 :=
          (flattenCharacter_eq_zero_iff (F.exponent i)).2 hi
        simp [hi, hflat]
      · have hflat : F.flatExponent i ≠ 0 := fun h ↦
          hi ((flattenCharacter_eq_zero_iff (F.exponent i)).1 h)
        simp [hi, hflat]
    _ =
        aggregateFourierCoefficient F.coefficient F.exponent 0 :=
      (aggregateFourierCoefficient_eq_tsum_ite
        F.coefficient F.exponent 0).symm
    _ = 0 := F.zeroMode

/-- Canonical index type after collecting equal flattened exponents and
discarding zero coefficients. -/
abbrev SupportedIndex (F : RawCenteredFamily eqs vars) :=
  AggregateFourierSupport F.coefficient F.flatExponent

/-- Canonical supported coefficient. -/
def supportedCoefficient
    (F : RawCenteredFamily eqs vars) :
    F.SupportedIndex → ℂ :=
  supportedAggregateFourierCoefficient F.coefficient F.flatExponent

/-- Canonical supported exponent in literal fundamental-clock
coordinates. -/
def supportedExponent
    (F : RawCenteredFamily eqs vars) :
    F.SupportedIndex → Fin (vars + eqs) → ℤ :=
  supportedAggregateFourierExponent F.coefficient F.flatExponent

theorem supportedExponent_injective
    (F : RawCenteredFamily eqs vars) :
    Function.Injective F.supportedExponent :=
  supportedAggregateFourierExponent_injective
    F.coefficient F.flatExponent

/-- The canonical supported family satisfies the pointwise zero-mode
hypothesis expected by the primitive theorem. -/
theorem supported_zeroMode
    (F : RawCenteredFamily eqs vars) :
    ∀ i : F.SupportedIndex,
      F.supportedExponent i = 0 → F.supportedCoefficient i = 0 :=
  supportedAggregateFourierCoefficient_zeroMode
    F.coefficient F.flatExponent F.aggregate_flatExponent_zero

/-- The raw height estimate with exponent zero is exactly ordinary
absolute summability. -/
theorem coefficient_summable
    (F : RawCenteredFamily eqs vars)
    (radicand : Fin (vars + eqs) → ℕ) :
    Summable fun i ↦ ‖F.coefficient i‖ := by
  simpa using F.summable_height radicand 0

/-- Absolute summability survives exponent collection and support
restriction. -/
theorem supportedCoefficient_summable
    (F : RawCenteredFamily eqs vars)
    (radicand : Fin (vars + eqs) → ℕ) :
    Summable fun i : F.SupportedIndex ↦ ‖F.supportedCoefficient i‖ :=
  summable_norm_supportedAggregateFourierCoefficient
    F.coefficient F.flatExponent (F.coefficient_summable radicand)

/-- Every fixed radical-height weighted estimate survives exponent
collection and support restriction. -/
theorem supportedCoefficient_weighted_summable
    (F : RawCenteredFamily eqs vars)
    (radicand : Fin (vars + eqs) → ℕ)
    (heightPower : ℕ) :
    Summable fun i : F.SupportedIndex ↦
      ‖F.supportedCoefficient i‖ *
        RadicalSmallDivisor.radicalConjugateHeight
            radicand (F.supportedExponent i) ^ heightPower := by
  exact
    summable_norm_supportedAggregateFourierCoefficient_mul_weight
      F.coefficient F.flatExponent
      (fun a ↦
        RadicalSmallDivisor.radicalConjugateHeight radicand a ^
          heightPower)
      (fun a ↦ pow_nonneg
        (RadicalSmallDivisor.radicalConjugateHeight_nonneg
          radicand a) _)
      (F.coefficient_summable radicand)
      (by
        simpa only [flatExponent, characterHeight] using
          F.summable_height radicand heightPower)

/-- The supported series represents exactly the original raw centered
series. -/
theorem torusFourierSeries_supported
    (F : RawCenteredFamily eqs vars)
    (radicand : Fin (vars + eqs) → ℕ)
    (phase : UnitAddTorus (Fin (vars + eqs))) :
    torusFourierSeries F.supportedCoefficient F.supportedExponent phase =
      torusFourierSeries F.coefficient F.flatExponent phase :=
  torusFourierSeries_supportedAggregateFourierCoefficient
    F.coefficient F.flatExponent (F.coefficient_summable radicand) phase

end RawCenteredFamily

/-! ## The seven literal corrected families -/

/-- `Y - 1`. -/
def unaryMean
    (I : DQLSystem eqs vars) (j : Fin vars) :
    RawCenteredFamily eqs vars where
  Index := CenteredFourierIndex ℤ
  coefficient :=
    centeredFourierCoefficient
      1 CanonicalSelectorMomentZeroModes.thetaCoefficient
  exponent :=
    centeredFourierExponent
      (CanonicalSelectorMomentZeroModes.unaryExponent
        (eqs := eqs) j)
  zeroMode := CanonicalSelectorMomentZeroModes.aggregate_unaryMean_zero j
  summable_height :=
    fun radicand heightPower ↦
      summable_centeredUnaryMean radicand I j heightPower

/-- `Y Q⁻¹ - 1/128`. -/
def unaryFirst
    (I : DQLSystem eqs vars) (j : Fin vars) :
    RawCenteredFamily eqs vars where
  Index := CenteredFourierIndex ℤ
  coefficient :=
    centeredFourierCoefficient
      (((1 / 128 : ℝ) : ℂ))
      CanonicalSelectorMomentZeroModes.thetaCoefficient
  exponent :=
    centeredFourierExponent
      (CanonicalSelectorMomentZeroModes.unaryFirstExponent
        (eqs := eqs) j)
  zeroMode := CanonicalSelectorMomentZeroModes.aggregate_unaryFirst_zero j
  summable_height :=
    fun radicand heightPower ↦
      summable_centeredUnaryFirst radicand I j heightPower

/-- `p₄ - 1`, where the stored root is `θ₄²`. -/
def rootP4
    (j : Fin vars) :
    RawCenteredFamily eqs vars where
  Index := CenteredFourierIndex (ℤ × ℤ)
  coefficient :=
    centeredFourierCoefficient
      1 CanonicalSelectorMomentZeroModes.rootP4Coefficient
  exponent :=
    centeredFourierExponent
      (CanonicalSelectorMomentZeroModes.rootP4Exponent
        (eqs := eqs) j)
  zeroMode := CanonicalSelectorMomentZeroModes.aggregate_rootP4Mean_zero j
  summable_height :=
    fun radicand heightPower ↦
      summable_centeredRootP4 radicand j heightPower

/-- `p₂ Q⁻² - 1/4`, where the stored root is `θ₂²`. -/
def rootP2
    (j : Fin vars) :
    RawCenteredFamily eqs vars where
  Index := CenteredFourierIndex (ℤ × ℤ)
  coefficient :=
    centeredFourierCoefficient
      (((1 / 4 : ℝ) : ℂ))
      CanonicalSelectorMomentZeroModes.rootP2Coefficient
  exponent :=
    centeredFourierExponent
      (CanonicalSelectorMomentZeroModes.rootP2Exponent
        (eqs := eqs) j)
  zeroMode := CanonicalSelectorMomentZeroModes.aggregate_rootP2Mean_zero j
  summable_height :=
    fun radicand heightPower ↦
      summable_centeredRootP2 radicand j heightPower

/-- `F - 1`. -/
def jacobiMean
    (I : DQLSystem eqs vars) (j : Fin vars) :
    RawCenteredFamily eqs vars where
  Index := CenteredFourierIndex ℤ
  coefficient :=
    centeredFourierCoefficient
      1 CanonicalSelectorMomentZeroModes.thetaCoefficient
  exponent :=
    centeredFourierExponent
      (CanonicalSelectorMomentZeroModes.jacobiMeanExponent I j)
  zeroMode :=
    CanonicalSelectorMomentZeroModes.aggregate_jacobiMean_zero I j
  summable_height :=
    fun radicand heightPower ↦
      summable_centeredJacobiMean radicand I j heightPower

/-- `F (QV)⁻¹ - selectorCenter`. -/
def jacobiPlus
    (I : DQLSystem eqs vars) (j : Fin vars) :
    RawCenteredFamily eqs vars where
  Index := CorrectedJacobiSelectorCentering.CenteredThetaIndex
  coefficient :=
    CorrectedJacobiSelectorCentering.centeredCoefficient I j
  exponent :=
    CorrectedJacobiSelectorCentering.centeredPlusExponent I j
  zeroMode :=
    CorrectedJacobiSelectorCentering.aggregate_centeredPlusCoefficient_zero
      I j
  summable_height :=
    fun radicand heightPower ↦
      summable_centeredJacobiPlus radicand I j heightPower

/-- `F Q⁻¹V - selectorCenter`. -/
def jacobiMinus
    (I : DQLSystem eqs vars) (j : Fin vars) :
    RawCenteredFamily eqs vars where
  Index := CorrectedJacobiSelectorCentering.CenteredThetaIndex
  coefficient :=
    CorrectedJacobiSelectorCentering.centeredCoefficient I j
  exponent :=
    CorrectedJacobiSelectorCentering.centeredMinusExponent I j
  zeroMode :=
    CorrectedJacobiSelectorCentering.aggregate_centeredMinusCoefficient_zero
      I j
  summable_height :=
    fun radicand heightPower ↦
      summable_centeredJacobiMinus radicand I j heightPower

end HGAS.Analysis.CanonicalSelectorMomentAggregatedFamilies
