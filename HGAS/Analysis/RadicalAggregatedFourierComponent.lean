import HGAS.Analysis.FourierExponentAggregation
import HGAS.Analysis.RadicalTimeChangedTorusComponentFiniteGraph
import Mathlib.Tactic

/-!
# Aggregated Fourier data for time-changed radical-torus components

Concrete theta-series formulas are naturally written as sums over tuples
of integers.  Different tuples can carry the same character.  In
particular, centering often kills the *sum* of all constant terms, rather
than killing each syntactic term separately.

This module turns such a raw Fourier presentation into the presentation
required by the cohomological primitive:

* terms are collected by their exponent;
* exponents with zero collected coefficient are removed;
* the resulting exponent map is injective;
* the resulting Fourier series is exactly the original series;
* absolute and radical-height-weighted summability are inherited; and
* vanishing of the single collected coefficient at exponent zero gives
  the literal zero-mode hypothesis used by differentiation.

The construction preserves the selected compact component, phase map,
time-change speed, character derivative law, and invariant probability.
It is therefore a reusable adapter between algebraic Fourier expansions
and the compiler-facing radical finite-graph theorem.
-/

noncomputable section

open Function MeasureTheory
open scoped BigOperators BoundedContinuousFunction

namespace HGAS.Analysis

open HGAS.Clocks
open HGAS.CompactAccumulatorPipelineCode

universe u v

variable {d : Type u}
variable {n k l m : ℕ}
variable {layout : Fin n → Fin k ⊕ Fin l}
variable {E M : ℕ} {κ : RationalCode}
variable {P : PolynomialFieldCode n}
variable {h : Fin m → PolynomialCode n}

namespace RadicalTimeChangedTorusFourierComponent

variable
    {ι : Fin m → Type v}
    {scale : ℝ} {p : d → ℕ} {sign : d → ℤ}
    {coefficient : ∀ q, ι q → ℂ}
    {exponent : ∀ q, ι q → d → ℤ}

/-- The canonical index type of nonzero collected Fourier coefficients in
one output coordinate. -/
abbrev AggregatedIndex (q : Fin m) : Type u :=
  AggregateFourierSupport (coefficient q) (exponent q)

/-- The collected coefficient family, restricted to its nonzero
support. -/
def aggregatedCoefficient
    (q : Fin m) (a : AggregatedIndex
      (coefficient := coefficient) (exponent := exponent) q) : ℂ :=
  supportedAggregateFourierCoefficient
    (coefficient q) (exponent q) a

/-- The distinct exponent family carried by the collected support. -/
def aggregatedExponent
    (q : Fin m) (a : AggregatedIndex
      (coefficient := coefficient) (exponent := exponent) q) :
    d → ℤ :=
  supportedAggregateFourierExponent
    (coefficient q) (exponent q) a

theorem aggregatedExponent_injective
    (q : Fin m) :
    Function.Injective
      (aggregatedExponent
        (coefficient := coefficient) (exponent := exponent) q) := by
  exact
    supportedAggregateFourierExponent_injective
      (coefficient q) (exponent q)

/-- Collected coefficients are absolutely summable whenever the raw
coefficients are. -/
theorem summable_norm_aggregatedCoefficient
    (hcoefficient :
      ∀ q, Summable fun i ↦ ‖coefficient q i‖) :
    ∀ q,
      Summable fun a ↦
        ‖aggregatedCoefficient
          (coefficient := coefficient) (exponent := exponent) q a‖ := by
  intro q
  exact
    summable_norm_supportedAggregateFourierCoefficient
      (coefficient q) (exponent q) (hcoefficient q)

/-- A nonnegative weighted `ℓ¹` estimate passes from the raw expression
to its collected support. -/
theorem summable_norm_aggregatedCoefficient_mul_weight
    (weight : (d → ℤ) → ℝ)
    (hweight0 : ∀ a, 0 ≤ weight a)
    (hcoefficient :
      ∀ q, Summable fun i ↦ ‖coefficient q i‖)
    (hweighted :
      ∀ q,
        Summable fun i ↦
          ‖coefficient q i‖ * weight (exponent q i)) :
    ∀ q,
      Summable fun a ↦
        ‖aggregatedCoefficient
            (coefficient := coefficient) (exponent := exponent) q a‖ *
          weight
            (aggregatedExponent
              (coefficient := coefficient) (exponent := exponent) q a) := by
  intro q
  exact
    summable_norm_supportedAggregateFourierCoefficient_mul_weight
      (coefficient q) (exponent q) weight hweight0
      (hcoefficient q) (hweighted q)

/-- Aggregate zero-mode cancellation supplies the termwise zero-mode
condition on the collected support. -/
theorem aggregatedCoefficient_zeroMode
    (hzero :
      ∀ q,
        aggregateFourierCoefficient
          (coefficient q) (exponent q) 0 = 0) :
    ∀ q a,
      aggregatedExponent
          (coefficient := coefficient) (exponent := exponent) q a = 0 →
        aggregatedCoefficient
          (coefficient := coefficient) (exponent := exponent) q a = 0 := by
  intro q
  exact
    supportedAggregateFourierCoefficient_zeroMode
      (coefficient q) (exponent q) (hzero q)

/-- A raw time-changed Fourier component, converted canonically to its
distinct nonzero collected Fourier support.

The coefficient summability assumption is needed only to justify the
fiberwise rearrangement in `drift_eq_fourier`. -/
def aggregateModel
    [Fintype d]
    (G :
      Model layout E M κ P h
        ι scale p sign coefficient exponent)
    (hcoefficient :
      ∀ q, Summable fun i ↦ ‖coefficient q i‖) :
    Model layout E M κ P h
      (AggregatedIndex
        (coefficient := coefficient) (exponent := exponent))
      scale p sign
      (aggregatedCoefficient
        (coefficient := coefficient) (exponent := exponent))
      (aggregatedExponent
        (coefficient := coefficient) (exponent := exponent)) where
  component := G.selectedComponent
  phase :=
    RadicalTimeChangedTorusFourierComponent.phase
      (layout := layout) (E := E) (M := M) (κ := κ)
      (P := P) (h := h) G
  phase_continuous :=
    RadicalTimeChangedTorusFourierComponent.phase_continuous
      (layout := layout) (E := E) (M := M) (κ := κ)
      (P := P) (h := h) G
  speed :=
    RadicalTimeChangedTorusFourierComponent.speed
      (layout := layout) (E := E) (M := M) (κ := κ)
      (P := P) (h := h) G
  speedBound :=
    RadicalTimeChangedTorusFourierComponent.speedBound
      (layout := layout) (E := E) (M := M) (κ := κ)
      (P := P) (h := h) G
  speedBound_nonneg :=
    RadicalTimeChangedTorusFourierComponent.speedBound_nonneg
      (layout := layout) (E := E) (M := M) (κ := κ)
      (P := P) (h := h) G
  speed_le :=
    RadicalTimeChangedTorusFourierComponent.speed_le
      (layout := layout) (E := E) (M := M) (κ := κ)
      (P := P) (h := h) G
  character_derivative :=
    RadicalTimeChangedTorusFourierComponent.character_derivative
      (layout := layout) (E := E) (M := M) (κ := κ)
      (P := P) (h := h) G
  drift_eq_fourier := by
    intro b
    rw [
      RadicalTimeChangedTorusFourierComponent.drift_eq_fourier
        (layout := layout) (E := E) (M := M) (κ := κ)
        (P := P) (h := h) G b]
    apply congrArg
      (fun v : FinVector m ℝ ↦
        (RadicalTimeChangedTorusFourierComponent.speed
          (layout := layout) (E := E) (M := M) (κ := κ)
          (P := P) (h := h) G b) • v)
    funext q
    unfold realTorusFourierVector
    exact congrArg Complex.re
      (torusFourierSeries_supportedAggregateFourierCoefficient
        (coefficient q) (exponent q) (hcoefficient q) _).symm
  probability :=
    RadicalTimeChangedTorusFourierComponent.probability
      (layout := layout) (E := E) (M := M) (κ := κ)
      (P := P) (h := h) G

/-- Radical-height weighted summability for the collected support follows
directly from the raw estimate. -/
theorem summable_norm_aggregatedCoefficient_mul_radicalHeight_pow
    [Fintype d]
    (hcoefficient :
      ∀ q, Summable fun i ↦ ‖coefficient q i‖)
    (hweighted :
      ∀ q,
        Summable fun i ↦
          ‖coefficient q i‖ *
            RadicalSmallDivisor.radicalConjugateHeight
                p (exponent q i) ^
              (RadicalSmallDivisor.radicalDegree p - 1)) :
    ∀ q,
      Summable fun a ↦
        ‖aggregatedCoefficient
            (coefficient := coefficient) (exponent := exponent) q a‖ *
          RadicalSmallDivisor.radicalConjugateHeight
              p
              (aggregatedExponent
                (coefficient := coefficient) (exponent := exponent) q a) ^
            (RadicalSmallDivisor.radicalDegree p - 1) := by
  apply
    summable_norm_aggregatedCoefficient_mul_weight
      (coefficient := coefficient) (exponent := exponent)
      (weight := fun a ↦
        RadicalSmallDivisor.radicalConjugateHeight p a ^
          (RadicalSmallDivisor.radicalDegree p - 1))
  · intro a
    exact pow_nonneg
      (RadicalSmallDivisor.radicalConjugateHeight_nonneg p a) _
  · exact hcoefficient
  · exact hweighted

end RadicalTimeChangedTorusFourierComponent

end HGAS.Analysis
