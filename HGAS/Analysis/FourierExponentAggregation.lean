import HGAS.Analysis.TorusCohomologicalPrimitive
import Mathlib.Tactic

/-!
# Canonical aggregation of repeated Fourier exponents

Analytic expression trees often contain several summands with the same
torus exponent.  In particular a centered observable may have several
individual zero-exponent summands whose *sum* is zero, even though none of
those coefficients vanishes separately.  A cohomological primitive should
see the collected Fourier coefficient, not the accidental syntax of the
expression tree.

For an absolutely summable family

```text
       coefficient : ι → ℂ,
       exponent    : ι → (d → ℤ),
```

this module defines the canonical coefficient at exponent `a` by summing
over the fiber `exponent ⁻¹ {a}`.  It proves:

* absolute summability of the collected coefficient family;
* equality of the collected and original Fourier series;
* preservation of every nonnegative weighted `ℓ¹` estimate; and
* after restricting to the nonzero collected support, distinctness of
  exponents and the termwise zero-mode condition required by the existing
  primitive API.

Thus aggregate zero-mode cancellation is converted into literal
term-by-term vanishing without quotient types or arbitrary choices.
-/

noncomputable section

open Function Set
open scoped BigOperators

namespace HGAS.Analysis

universe u v

variable {d : Type u} {ι : Type v}

/-- The fiber of a raw Fourier expression over one exponent. -/
abbrev FourierExponentFiber
    (exponent : ι → d → ℤ) (a : d → ℤ) :=
  {i : ι // exponent i = a}

/-- Canonical coefficient obtained by collecting every raw term with the
same exponent. -/
def aggregateFourierCoefficient
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (a : d → ℤ) : ℂ :=
  ∑' i : FourierExponentFiber exponent a,
    coefficient i

/-- The collected coefficient can equivalently be computed on the raw
index type by retaining exactly the terms with the requested exponent.
This form is convenient for explicit finite resonance calculations. -/
theorem aggregateFourierCoefficient_eq_tsum_ite
    [DecidableEq (d → ℤ)]
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (a : d → ℤ) :
    aggregateFourierCoefficient coefficient exponent a =
      ∑' i : ι,
        if exponent i = a then coefficient i else 0 := by
  classical
  unfold aggregateFourierCoefficient FourierExponentFiber
  calc
    (∑' i : {i : ι // exponent i = a}, coefficient i) =
        ∑' i : ι,
          {i : ι | exponent i = a}.indicator coefficient i :=
      tsum_subtype {i : ι | exponent i = a} coefficient
    _ = ∑' i : ι,
          if exponent i = a then coefficient i else 0 := by
      apply tsum_congr
      intro i
      simp only [Set.indicator, Set.mem_setOf_eq]
      split_ifs <;> rfl

/-- The fiberwise sum of coefficient norms.  It is the natural majorant
for the norm of `aggregateFourierCoefficient`. -/
def aggregateFourierNormMajorant
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (a : d → ℤ) : ℝ :=
  ∑' i : FourierExponentFiber exponent a,
    ‖coefficient i‖

theorem summable_aggregateFourierNormMajorant
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (hcoefficient : Summable fun i ↦ ‖coefficient i‖) :
    Summable
      (aggregateFourierNormMajorant coefficient exponent) := by
  exact
    (hcoefficient.hasSum.tsum_fiberwise exponent).summable

theorem norm_aggregateFourierCoefficient_le_majorant
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (hcoefficient : Summable fun i ↦ ‖coefficient i‖)
    (a : d → ℤ) :
    ‖aggregateFourierCoefficient coefficient exponent a‖ ≤
      aggregateFourierNormMajorant coefficient exponent a := by
  unfold aggregateFourierCoefficient
    aggregateFourierNormMajorant
  exact
    norm_tsum_le_tsum_norm
      (hcoefficient.subtype
        (fun i ↦ exponent i = a))

/-- Collecting equal exponents cannot increase the coefficient `ℓ¹`
norm. -/
theorem summable_norm_aggregateFourierCoefficient
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (hcoefficient : Summable fun i ↦ ‖coefficient i‖) :
    Summable fun a : d → ℤ ↦
      ‖aggregateFourierCoefficient coefficient exponent a‖ := by
  exact
    (summable_aggregateFourierNormMajorant
      coefficient exponent hcoefficient).of_norm_bounded
      (fun a ↦ by
        simpa only [Real.norm_eq_abs,
          abs_norm] using
          norm_aggregateFourierCoefficient_le_majorant
            coefficient exponent hcoefficient a)

/-- The Fourier series is unchanged when its coefficients are collected
by exponent. -/
theorem torusFourierSeries_aggregateFourierCoefficient
    [Fintype d]
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (hcoefficient : Summable fun i ↦ ‖coefficient i‖)
    (x : UnitAddTorus d) :
    torusFourierSeries
        (aggregateFourierCoefficient coefficient exponent)
        (fun a : d → ℤ ↦ a) x =
      torusFourierSeries coefficient exponent x := by
  let rawTerm : ι → ℂ :=
    fun i ↦ torusSeriesTerm coefficient exponent i x
  have hraw : Summable rawTerm := by
    exact hcoefficient.of_norm_bounded fun i ↦ by
      exact le_of_eq
        (norm_torusSeriesTerm coefficient exponent i x)
  have hfiber :=
    hraw.hasSum.tsum_fiberwise exponent
  have hfiberTerm :
      ∀ a : d → ℤ,
        (∑' i : FourierExponentFiber exponent a,
          rawTerm i) =
        torusSeriesTerm
          (aggregateFourierCoefficient coefficient exponent)
          (fun b : d → ℤ ↦ b) a x := by
    intro a
    rw [torusSeriesTerm, aggregateFourierCoefficient,
      ← tsum_mul_right]
    apply tsum_congr
    intro i
    unfold rawTerm torusSeriesTerm
    rw [i.2]
  unfold torusFourierSeries
  rw [show
      (∑' a : d → ℤ,
        torusSeriesTerm
          (aggregateFourierCoefficient coefficient exponent)
          (fun b : d → ℤ ↦ b) a x) =
        ∑' a : d → ℤ,
          ∑' i : FourierExponentFiber exponent a,
            rawTerm i by
    apply tsum_congr
    intro a
    exact (hfiberTerm a).symm]
  exact hfiber.tsum_eq

/-! ## Preservation of weighted estimates -/

/-- Fiberwise weighted norm majorant. -/
def aggregateFourierWeightedMajorant
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (weight : (d → ℤ) → ℝ)
    (a : d → ℤ) : ℝ :=
  ∑' i : FourierExponentFiber exponent a,
    ‖coefficient i‖ * weight a

theorem summable_aggregateFourierWeightedMajorant
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (weight : (d → ℤ) → ℝ)
    (hweighted :
      Summable fun i ↦
        ‖coefficient i‖ * weight (exponent i)) :
    Summable
      (aggregateFourierWeightedMajorant
        coefficient exponent weight) := by
  have hfiber :=
    hweighted.hasSum.tsum_fiberwise exponent
  apply hfiber.summable.congr
  intro a
  unfold aggregateFourierWeightedMajorant
  apply tsum_congr
  intro i
  rw [i.2]

/-- Any nonnegative weighted `ℓ¹` estimate survives collection of equal
exponents. -/
theorem summable_norm_aggregateFourierCoefficient_mul_weight
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (weight : (d → ℤ) → ℝ)
    (hweight0 : ∀ a, 0 ≤ weight a)
    (hcoefficient : Summable fun i ↦ ‖coefficient i‖)
    (hweighted :
      Summable fun i ↦
        ‖coefficient i‖ * weight (exponent i)) :
    Summable fun a : d → ℤ ↦
      ‖aggregateFourierCoefficient coefficient exponent a‖ *
        weight a := by
  have hmajor :=
    summable_aggregateFourierWeightedMajorant
      coefficient exponent weight hweighted
  apply Summable.of_nonneg_of_le
  · intro a
    exact mul_nonneg (norm_nonneg _) (hweight0 a)
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
  · exact hmajor

/-! ## Canonical distinct-exponent support -/

/-- Exponents whose collected coefficient is nonzero. -/
abbrev AggregateFourierSupport
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ) :=
  Function.support
    (aggregateFourierCoefficient coefficient exponent)

/-- Collected coefficient restricted to its nonzero support. -/
def supportedAggregateFourierCoefficient
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (a : AggregateFourierSupport coefficient exponent) : ℂ :=
  aggregateFourierCoefficient coefficient exponent a

/-- The exponent attached to a supported collected coefficient. -/
def supportedAggregateFourierExponent
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (a : AggregateFourierSupport coefficient exponent) :
    d → ℤ :=
  a

theorem supportedAggregateFourierExponent_injective
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ) :
    Function.Injective
      (supportedAggregateFourierExponent coefficient exponent) := by
  intro a b h
  exact Subtype.ext h

theorem summable_norm_supportedAggregateFourierCoefficient
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (hcoefficient : Summable fun i ↦ ‖coefficient i‖) :
    Summable fun a : AggregateFourierSupport coefficient exponent ↦
      ‖supportedAggregateFourierCoefficient
        coefficient exponent a‖ := by
  exact
    (summable_norm_aggregateFourierCoefficient
      coefficient exponent hcoefficient).subtype _

theorem torusFourierSeries_supportedAggregateFourierCoefficient
    [Fintype d]
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (hcoefficient : Summable fun i ↦ ‖coefficient i‖)
    (x : UnitAddTorus d) :
    torusFourierSeries
        (supportedAggregateFourierCoefficient
          coefficient exponent)
        (supportedAggregateFourierExponent
          coefficient exponent) x =
      torusFourierSeries coefficient exponent x := by
  rw [←
    torusFourierSeries_aggregateFourierCoefficient
      coefficient exponent hcoefficient x]
  unfold torusFourierSeries
  change
    (∑' a : AggregateFourierSupport coefficient exponent,
      torusSeriesTerm
        (aggregateFourierCoefficient coefficient exponent)
        (fun b : d → ℤ ↦ b) a x) =
      ∑' a : d → ℤ,
        torusSeriesTerm
          (aggregateFourierCoefficient coefficient exponent)
          (fun b : d → ℤ ↦ b) a x
  apply tsum_subtype_eq_of_support_subset
    (f := fun a : d → ℤ ↦
      torusSeriesTerm
        (aggregateFourierCoefficient coefficient exponent)
        (fun b : d → ℤ ↦ b) a x)
    (s := AggregateFourierSupport coefficient exponent)
  intro a ha
  change
    aggregateFourierCoefficient coefficient exponent a ≠ 0
  intro hzero
  apply ha
  simp [torusSeriesTerm, hzero]

theorem summable_norm_supportedAggregateFourierCoefficient_mul_weight
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (weight : (d → ℤ) → ℝ)
    (hweight0 : ∀ a, 0 ≤ weight a)
    (hcoefficient : Summable fun i ↦ ‖coefficient i‖)
    (hweighted :
      Summable fun i ↦
        ‖coefficient i‖ * weight (exponent i)) :
    Summable fun a : AggregateFourierSupport coefficient exponent ↦
      ‖supportedAggregateFourierCoefficient
          coefficient exponent a‖ *
        weight
          (supportedAggregateFourierExponent
            coefficient exponent a) := by
  exact
    (summable_norm_aggregateFourierCoefficient_mul_weight
      coefficient exponent weight hweight0
      hcoefficient hweighted).subtype _

/-- Aggregate vanishing at exponent zero becomes the literal termwise
zero-mode condition on the supported family. -/
theorem supportedAggregateFourierCoefficient_zeroMode
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (hzero :
      aggregateFourierCoefficient coefficient exponent 0 = 0) :
    ∀ a : AggregateFourierSupport coefficient exponent,
      supportedAggregateFourierExponent
          coefficient exponent a = 0 →
        supportedAggregateFourierCoefficient
          coefficient exponent a = 0 := by
  intro a ha
  change (a : d → ℤ) = 0 at ha
  change
    aggregateFourierCoefficient coefficient exponent a = 0
  simpa only [ha] using hzero

end HGAS.Analysis
