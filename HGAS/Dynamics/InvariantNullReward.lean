import HGAS.Dynamics.UniformNegativeBlocks
import Mathlib.Tactic

/-!
# Reward bounds outside invariant null sets

The compact accumulator argument eventually proves that, in a yes-instance,
every invariant probability gives zero mass to the only region on which the
reward might exceed `-ε`.  This module isolates the short measure-theoretic
conclusion from the much harder drift classification.

The lemmas are intentionally independent of accumulators:

* a pointwise upper bound outside a null set bounds one observable average;
* if the exceptional set is null for every invariant probability, it bounds
  the maximal invariant average;
* one invariant probability with a positive lower bound gives the opposite
  inequality;
* quantitative upper and lower gaps imply an exact logical dichotomy.
-/

noncomputable section

open MeasureTheory Set
open scoped BoundedContinuousFunction

namespace HGAS.Dynamics

variable {X : Type*} [MetricSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- An observable bounded by `c` outside a set of measure zero has average
at most `c`. -/
theorem observableAverage_le_of_null_exception
    (a : X →ᵇ ℝ) (μ : ProbabilityMeasure X)
    (s : Set X) (c : ℝ)
    (hnull : (μ : Measure X) s = 0)
    (hbound : ∀ x, x ∉ s → a x ≤ c) :
    observableAverage a μ ≤ c := by
  have haeOutside :
      ∀ᵐ x ∂(μ : Measure X), x ∉ s := by
    rw [ae_iff]
    simpa only [compl_setOf, not_not] using hnull
  have haeBound :
      ∀ᵐ x ∂(μ : Measure X), a x ≤ c := by
    filter_upwards [haeOutside] with x hx
    exact hbound x hx
  unfold observableAverage
  calc
    (∫ x, a x ∂(μ : Measure X)) ≤
        ∫ _ : X, c ∂(μ : Measure X) := by
      exact integral_mono_ae
        (a.integrable (μ : Measure X))
        (integrable_const c) haeBound
    _ = c := by simp

/-- If one exceptional set is null for every invariant probability, a
pointwise reward bound on its complement also bounds the attained maximal
invariant average. -/
theorem maximalInvariantAverage_le_of_invariantNullException
    [CompactSpace X] [Nonempty X]
    (ϕ : Flow ℝ X) (a : X →ᵇ ℝ)
    (s : Set X) (c : ℝ)
    (hnull :
      ∀ μ : InvariantProbabilityMeasure ϕ,
        (μ.measure : Measure X) s = 0)
    (hbound : ∀ x, x ∉ s → a x ≤ c) :
    maximalInvariantAverage ϕ a ≤ c := by
  let μ : InvariantProbabilityMeasure ϕ :=
    ⟨maximizingInvariantProbability ϕ a,
      maximizingInvariantProbability_invariant ϕ a⟩
  change observableAverage a μ.measure ≤ c
  exact observableAverage_le_of_null_exception
    a μ.measure s c (hnull μ) hbound

/-- A single invariant probability supplies a lower bound for the maximal
invariant average. -/
theorem le_maximalInvariantAverage_of_invariantProbability
    [CompactSpace X] [Nonempty X]
    (ϕ : Flow ℝ X) (a : X →ᵇ ℝ)
    (μ : InvariantProbabilityMeasure ϕ) {c : ℝ}
    (hc : c ≤ observableAverage a μ.measure) :
    c ≤ maximalInvariantAverage ϕ a :=
  hc.trans
    (invariantAverage_le_maximalInvariantAverage
      ϕ a μ.measure μ.invariant)

/-- Quantitative sign gaps on the two logical cases give the exact strict
sign test used by the arithmetic reduction. -/
theorem maximalInvariantAverage_neg_iff_of_two_sided_gap
    [CompactSpace X] [Nonempty X]
    (ϕ : Flow ℝ X) (a : X →ᵇ ℝ)
    (P : Prop) {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ)
    (hupper :
      P → maximalInvariantAverage ϕ a ≤ -ε)
    (hlower :
      ¬P → δ ≤ maximalInvariantAverage ϕ a) :
    maximalInvariantAverage ϕ a < 0 ↔ P := by
  constructor
  · intro hnegative
    by_contra hnot
    have hpositive := hlower hnot
    linarith
  · intro hP
    exact (hupper hP).trans_lt (neg_neg_of_pos hε)

end HGAS.Dynamics

end
