import HGAS.Analysis.CanonicalSelectorMomentAggregatedFamilies
import HGAS.Analysis.RadicalFourierPrimitiveBounds
import HGAS.Analysis.RealifiedTorusFourierFamily
import HGAS.Analysis.TorusCohomologicalPrimitiveVector
import Mathlib.Tactic

/-!
# Quantitative primitive bounds after Fourier support aggregation

Collecting equal Fourier exponents is analytically harmless, but an
effective reduction needs the stronger numerical statement that
collection does not increase any nonnegative weighted `ℓ¹` norm.
This file proves that fact and applies it to radical small divisors.

For the physical clock normalization used by the canonical detector,

```text
                       scale = 1 / (2π),
```

the `2π` in the angular derivative cancels exactly:

```text
                       2π |scale| = 1.
```

Consequently, the `ℓ¹` norm of every supported cohomological primitive is
bounded directly by the raw radical-height-weighted coefficient sum.  No
transcendental constant remains in the final numerical budget.
-/

noncomputable section

open scoped BigOperators

namespace HGAS.Analysis

open HGAS
open HGAS.Clocks
open CanonicalSelectorMomentAggregatedFamilies
open CanonicalSelectorMomentRadicalSummability

variable {d ι : Type*}

/-- Support aggregation and restriction do not increase a nonnegative
weighted coefficient sum. -/
theorem tsum_norm_supportedAggregateFourierCoefficient_mul_weight_le
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (weight : (d → ℤ) → ℝ)
    (hweight0 : ∀ a, 0 ≤ weight a)
    (hcoefficient : Summable fun i ↦ ‖coefficient i‖)
    (hweighted :
      Summable fun i ↦
        ‖coefficient i‖ * weight (exponent i)) :
    (∑' a : AggregateFourierSupport coefficient exponent,
      ‖supportedAggregateFourierCoefficient
          coefficient exponent a‖ *
        weight
          (supportedAggregateFourierExponent
            coefficient exponent a)) ≤
      ∑' i : ι,
        ‖coefficient i‖ * weight (exponent i) := by
  let aggregateTerm : (d → ℤ) → ℝ :=
    fun a ↦
      ‖aggregateFourierCoefficient coefficient exponent a‖ *
        weight a
  let majorant : (d → ℤ) → ℝ :=
    aggregateFourierWeightedMajorant
      coefficient exponent weight
  have haggregate :
      Summable aggregateTerm := by
    exact
      summable_norm_aggregateFourierCoefficient_mul_weight
        coefficient exponent weight hweight0
        hcoefficient hweighted
  have hsupport :
      Summable fun a :
          AggregateFourierSupport coefficient exponent ↦
        ‖supportedAggregateFourierCoefficient
            coefficient exponent a‖ *
          weight
            (supportedAggregateFourierExponent
              coefficient exponent a) := by
    exact
      summable_norm_supportedAggregateFourierCoefficient_mul_weight
        coefficient exponent weight hweight0
        hcoefficient hweighted
  have hmajorant : Summable majorant :=
    summable_aggregateFourierWeightedMajorant
      coefficient exponent weight hweighted
  have hsupportAggregate :
      (∑' a : AggregateFourierSupport coefficient exponent,
        ‖supportedAggregateFourierCoefficient
            coefficient exponent a‖ *
          weight
            (supportedAggregateFourierExponent
              coefficient exponent a)) ≤
        ∑' a : d → ℤ, aggregateTerm a := by
    exact
      hsupport.tsum_le_tsum_of_inj
        (fun a ↦ (a : d → ℤ))
        Subtype.val_injective
        (by
          intro a ha
          exact mul_nonneg (norm_nonneg _) (hweight0 a))
        (by intro a; rfl)
        haggregate
  have haggregateMajorant :
      (∑' a : d → ℤ, aggregateTerm a) ≤
        ∑' a : d → ℤ, majorant a := by
    apply haggregate.tsum_le_tsum
    · intro a
      change
        ‖aggregateFourierCoefficient coefficient exponent a‖ *
            weight a ≤
          aggregateFourierWeightedMajorant
            coefficient exponent weight a
      unfold aggregateFourierWeightedMajorant
      rw [tsum_mul_right]
      exact mul_le_mul_of_nonneg_right
        (norm_aggregateFourierCoefficient_le_majorant
          coefficient exponent hcoefficient a)
        (hweight0 a)
    · exact hmajorant
  have hmajorantRaw :
      (∑' a : d → ℤ, majorant a) =
        ∑' i : ι,
          ‖coefficient i‖ * weight (exponent i) := by
    let raw : ι → ℝ :=
      fun i ↦ ‖coefficient i‖ * weight (exponent i)
    have hfiber :=
      hweighted.hasSum.tsum_fiberwise exponent
    have hcongr :
        majorant =
          fun a : d → ℤ ↦
            ∑' i : FourierExponentFiber exponent a, raw i := by
      funext a
      unfold majorant aggregateFourierWeightedMajorant raw
      apply tsum_congr
      intro i
      rw [i.2]
    rw [hcongr]
    exact hfiber.tsum_eq
  exact
    hsupportAggregate.trans
      (haggregateMajorant.trans_eq hmajorantRaw)

/-- The canonical angular normalization has denominator exactly one. -/
theorem canonicalRadicalScale_denominator_eq_one :
    2 * Real.pi * |1 / (2 * Real.pi)| = 1 := by
  rw [abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
  field_simp [Real.pi_ne_zero]

/-- Quantitative supported-family primitive bound at the canonical
`1/(2π)` physical frequency scale.

The right side is the *raw*, pre-aggregation weighted coefficient sum,
which is the convenient form for explicit lattice majorants.
-/
theorem RawCenteredFamily.primitiveBound_le_rawWeightedTsum
    {eqs vars : ℕ}
    (F : RawCenteredFamily eqs vars)
    (p : Fin (vars + eqs) → ℕ)
    (hp : ∀ i, (p i).Prime)
    (hinjective : Function.Injective p)
    (sign : Fin (vars + eqs) → ℤ)
    (hsign : ∀ i, sign i = 1 ∨ sign i = -1) :
    (∑' i : F.SupportedIndex,
      ‖cohomologicalPrimitiveCoefficient
          F.supportedCoefficient F.supportedExponent
          (fun j ↦
            (1 / (2 * Real.pi)) *
              RadicalIndependence.signedPrimeSqrtFrequency
                p sign j)
          i‖) ≤
      ∑' i : F.Index,
        ‖F.coefficient i‖ *
          RadicalSmallDivisor.radicalConjugateHeight
              p (F.flatExponent i) ^
            (RadicalSmallDivisor.radicalDegree p - 1) := by
  let heightPower := RadicalSmallDivisor.radicalDegree p - 1
  let weight : (Fin (vars + eqs) → ℤ) → ℝ :=
    fun a ↦
      RadicalSmallDivisor.radicalConjugateHeight p a ^ heightPower
  have hscale : (1 / (2 * Real.pi) : ℝ) ≠ 0 := by
    positivity
  have hraw :
      Summable fun i : F.Index ↦
        ‖F.coefficient i‖ * weight (F.flatExponent i) := by
    simpa only [weight, heightPower,
      CanonicalSelectorMomentRadicalSummability.characterHeight,
      RawCenteredFamily.flatExponent] using
      F.summable_height p heightPower
  have hsupported :
      Summable fun i : F.SupportedIndex ↦
        ‖F.supportedCoefficient i‖ *
          weight (F.supportedExponent i) := by
    exact
      F.supportedCoefficient_weighted_summable p heightPower
  have hprimitive :
      Summable fun i : F.SupportedIndex ↦
        ‖cohomologicalPrimitiveCoefficient
            F.supportedCoefficient F.supportedExponent
            (fun j ↦
              (1 / (2 * Real.pi)) *
                RadicalIndependence.signedPrimeSqrtFrequency
                  p sign j)
            i‖ := by
    exact
      summable_norm_cohomologicalPrimitiveCoefficient_of_radical
        (1 / (2 * Real.pi)) hscale p hp hinjective
        sign hsign F.supportedCoefficient F.supportedExponent
        hsupported
  have hpoint :
      ∀ i : F.SupportedIndex,
        ‖cohomologicalPrimitiveCoefficient
            F.supportedCoefficient F.supportedExponent
            (fun j ↦
              (1 / (2 * Real.pi)) *
                RadicalIndependence.signedPrimeSqrtFrequency
                  p sign j)
            i‖ ≤
          ‖F.supportedCoefficient i‖ *
            weight (F.supportedExponent i) := by
    intro i
    have h :=
      norm_cohomologicalPrimitiveCoefficient_le_radicalMajorant
        (1 / (2 * Real.pi)) hscale p hp hinjective
        sign hsign
        (F.supportedCoefficient i)
        (F.supportedExponent i)
    simpa only [radicalPrimitiveCoefficientMajorant,
      canonicalRadicalScale_denominator_eq_one, div_one,
      weight, heightPower] using h
  calc
    (∑' i : F.SupportedIndex,
      ‖cohomologicalPrimitiveCoefficient
          F.supportedCoefficient F.supportedExponent
          (fun j ↦
            (1 / (2 * Real.pi)) *
              RadicalIndependence.signedPrimeSqrtFrequency
                p sign j)
          i‖) ≤
        ∑' i : F.SupportedIndex,
          ‖F.supportedCoefficient i‖ *
            weight (F.supportedExponent i) :=
      hprimitive.tsum_le_tsum hpoint hsupported
    _ ≤
        ∑' i : F.Index,
          ‖F.coefficient i‖ *
            weight (F.flatExponent i) := by
      exact
        tsum_norm_supportedAggregateFourierCoefficient_mul_weight_le
          F.coefficient F.flatExponent weight
          (fun a ↦ pow_nonneg
            (RadicalSmallDivisor.radicalConjugateHeight_nonneg p a) _)
          (F.coefficient_summable p) hraw

/-- Realification does not change an inverse-frequency coordinate bound. -/
theorem primitiveTsum_realifiedCoefficient
    {d ι : Type*} [Fintype d]
    (b : Fin 2)
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (ω : d → ℝ) :
    (∑' i,
      ‖cohomologicalPrimitiveCoefficient
          (realifiedCoefficient b coefficient) exponent ω i‖) =
      ∑' i,
        ‖cohomologicalPrimitiveCoefficient
          coefficient exponent ω i‖ := by
  apply tsum_congr
  intro i
  unfold cohomologicalPrimitiveCoefficient
  split_ifs
  · simp
  · rw [norm_div, norm_div]
    simp [realifiedCoefficient, norm_realificationScalar]

end HGAS.Analysis
