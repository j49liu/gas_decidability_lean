import HGAS.Dynamics.InvariantDensity
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Tactic

/-!
# Canonical normalization of a bounded nonnegative density

The basic density API takes a normalizing constant `a : ℝ≥0` together
with a proof that

```
                  ∫⁻ x, f x ∂μ = a.
```

For a bounded continuous nonnegative function on a probability space,
this datum is canonical: the integral is finite, so it is the coercion of
the nonnegative real

```
              μ.toFiniteMeasure.testAgainstNN f.
```

This module packages that observation.  Its purpose is not merely
notational.  Later time-change arguments can ask only for the substantive
hypothesis that the clock density is nonzero almost everywhere; the
finite positive normalizing constant and its mass equation are then
constructed rather than carried as separate assumptions.
-/

noncomputable section

open Filter MeasureTheory
open scoped BoundedContinuousFunction ENNReal NNReal

namespace HGAS.Dynamics

variable {X : Type*}
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The canonical finite mass of a bounded continuous nonnegative
density on a probability space. -/
def boundedDensityMass
    (μ : ProbabilityMeasure X) (f : X →ᵇ ℝ≥0) : ℝ≥0 :=
  μ.toFiniteMeasure.testAgainstNN f

omit [BorelSpace X] in
/-- The coercion of `boundedDensityMass` is exactly the original
Lebesgue integral. -/
@[simp]
theorem coe_boundedDensityMass
    (μ : ProbabilityMeasure X) (f : X →ᵇ ℝ≥0) :
    (boundedDensityMass μ f : ENNReal) =
      ∫⁻ x, (f x : ENNReal) ∂(μ : Measure X) := by
  exact FiniteMeasure.testAgainstNN_coe_eq

/-- A density which is nonzero almost everywhere has nonzero canonical
mass.  Probability of the base measure is essential here: it excludes an
improper almost-everywhere filter. -/
theorem boundedDensityMass_ne_zero_of_ae
    (μ : ProbabilityMeasure X) (f : X →ᵇ ℝ≥0)
    (hpositive : ∀ᵐ x ∂(μ : Measure X), f x ≠ 0) :
    boundedDensityMass μ f ≠ 0 := by
  intro hmass
  have hintegral :
      ∫⁻ x, (f x : ENNReal) ∂(μ : Measure X) = 0 := by
    rw [← coe_boundedDensityMass, hmass]
    rfl
  have hzero :
      (fun x ↦ (f x : ENNReal)) =ᵐ[(μ : Measure X)] 0 :=
    (lintegral_eq_zero_iff
      f.continuous.measurable.coe_nnreal_ennreal).mp hintegral
  have himpossible : ∀ᵐ _x ∂(μ : Measure X), False := by
    filter_upwards [hpositive, hzero] with x hx hxeq
    exact hx (ENNReal.coe_eq_zero.mp hxeq)
  apply IsProbabilityMeasure.ne_zero (μ : Measure X)
  simpa only [eventually_false_iff_eq_bot, ae_eq_bot] using
    himpossible

/-- The normalized probability obtained from the canonical mass. -/
def canonicalNormalizedDensityProbability
    (μ : ProbabilityMeasure X) (f : X →ᵇ ℝ≥0)
    (hpositive : ∀ᵐ x ∂(μ : Measure X), f x ≠ 0) :
    ProbabilityMeasure X :=
  normalizedDensityProbability
    (μ : Measure X) f (boundedDensityMass μ f)
    f.continuous.measurable
    (boundedDensityMass_ne_zero_of_ae μ f hpositive)
    (coe_boundedDensityMass μ f).symm

/-- The canonical probability is literally the normalized density
measure with the canonical mass; there is no hidden choice. -/
@[simp]
theorem canonicalNormalizedDensityProbability_toMeasure
    (μ : ProbabilityMeasure X) (f : X →ᵇ ℝ≥0)
    (hpositive : ∀ᵐ x ∂(μ : Measure X), f x ≠ 0) :
    ((canonicalNormalizedDensityProbability μ f hpositive :
        ProbabilityMeasure X) : Measure X) =
      normalizedDensityMeasure
        (μ : Measure X) f (boundedDensityMass μ f) :=
  rfl

end HGAS.Dynamics
