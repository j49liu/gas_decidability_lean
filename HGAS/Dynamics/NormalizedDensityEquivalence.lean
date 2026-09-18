import HGAS.Dynamics.InvariantDensity
import Mathlib.Tactic

/-!
# Almost-everywhere equivalence under a positive normalized density

Let `μ` be a measure and let `f : X → ℝ≥0` have nonzero finite mass
`a`.  The normalized density probability

```
                         dν = (f / a) dμ
```

is always absolutely continuous with respect to `μ`.  If `f` is nonzero
`μ`-almost everywhere, then the converse absolute continuity also holds:
`μ` and `ν` have exactly the same null sets.

This elementary fact is the correct interface for compactification
arguments.  The compactified invariant probability and its source-time
reweighting need not be equal, but any support identity or pointwise
selector conclusion holding almost everywhere for one holds almost
everywhere for the other.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace HGAS.Dynamics

variable {X α : Type*} [MeasurableSpace X]

/-- A nonzero `ℝ≥0` density divided by a nonzero normalizing constant is
still nonzero after coercion to `ℝ≥0∞`. -/
private theorem coe_div_ne_zero
    {u a : ℝ≥0} (hu : u ≠ 0) (ha : a ≠ 0) :
    ((u / a : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
  rw [ENNReal.coe_ne_zero]
  exact div_ne_zero hu ha

/-- The original measure and its normalized positive-density probability
have the same almost-everywhere propositions.

The mass equation is included because it is part of the data defining the
probability.  No integrability assumption on the proposition is needed. -/
theorem ae_normalizedDensityProbability_iff
    (μ : Measure X) (f : X → ℝ≥0) (a : ℝ≥0)
    (hf : Measurable f)
    (ha : a ≠ 0)
    (hmass :
      ∫⁻ x, (f x : ENNReal) ∂μ = (a : ENNReal))
    (hpositive : ∀ᵐ x ∂μ, f x ≠ 0)
    (p : X → Prop) :
    (∀ᵐ x ∂
        ((normalizedDensityProbability μ f a hf ha hmass :
          ProbabilityMeasure X) : Measure X), p x) ↔
      ∀ᵐ x ∂μ, p x := by
  rw [normalizedDensityProbability_toMeasure,
    normalizedDensityMeasure,
    ae_withDensity_iff
      ((hf.div_const a).coe_nnreal_ennreal)]
  constructor
  · intro h
    filter_upwards [h, hpositive] with x hpx hfx
    exact hpx (coe_div_ne_zero hfx ha)
  · intro h
    filter_upwards [h] with x hpx
    exact fun _ ↦ hpx

/-- Eventually equal functions remain eventually equal in either direction
after a normalized density change whose density is nonzero almost
everywhere. -/
theorem eventuallyEq_normalizedDensityProbability_iff
    (μ : Measure X) (f : X → ℝ≥0) (a : ℝ≥0)
    (hf : Measurable f)
    (ha : a ≠ 0)
    (hmass :
      ∫⁻ x, (f x : ENNReal) ∂μ = (a : ENNReal))
    (hpositive : ∀ᵐ x ∂μ, f x ≠ 0)
    (g h : X → α) :
    g =ᵐ[
        ((normalizedDensityProbability μ f a hf ha hmass :
          ProbabilityMeasure X) : Measure X)] h ↔
      g =ᵐ[μ] h :=
  ae_normalizedDensityProbability_iff
    μ f a hf ha hmass hpositive (fun x ↦ g x = h x)

/-- A measurable set has full normalized-density mass exactly when it has
full original mass, provided the density is nonzero almost everywhere. -/
theorem ae_mem_normalizedDensityProbability_iff
    (μ : Measure X) (f : X → ℝ≥0) (a : ℝ≥0)
    (hf : Measurable f)
    (ha : a ≠ 0)
    (hmass :
      ∫⁻ x, (f x : ENNReal) ∂μ = (a : ENNReal))
    (hpositive : ∀ᵐ x ∂μ, f x ≠ 0)
    (s : Set X) :
    (∀ᵐ x ∂
        ((normalizedDensityProbability μ f a hf ha hmass :
          ProbabilityMeasure X) : Measure X), x ∈ s) ↔
      ∀ᵐ x ∂μ, x ∈ s :=
  ae_normalizedDensityProbability_iff
    μ f a hf ha hmass hpositive (fun x ↦ x ∈ s)

end HGAS.Dynamics
