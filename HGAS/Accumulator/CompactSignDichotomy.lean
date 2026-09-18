import HGAS.Accumulator.CompactDriftObstruction
import HGAS.Dynamics.ErgodicMaximalInvariantAverage
import HGAS.Dynamics.InvariantNullReward
import Mathlib.Tactic

/-!
# From compact-accumulator drift to a strict reward sign

This module composes the two reusable ingredients needed in the final
compact source:

1. a positive-mass invariant component in the finite stereographic chart
   must have zero mean drift;
2. the reward is at most `-ε` outside that chart.

Consequently, it is enough that the source classification applies to
ergodic invariant probabilities.  An ergodic maximizing probability
exists.  Its invariant finite chart has mass zero or one; in the
full-mass case the compact-accumulator obstruction forces every drift
coordinate to have zero mean, contradicting the classification.
Therefore the maximizing probability gives the finite chart zero mass,
and the maximal reward is at most `-ε`.

The second theorem adds the no-instance witness: one invariant probability
whose reward is bounded below by a positive `δ`.  These two quantitative
statements give the exact strict-sign equivalence.  No ergodic
decomposition or no-cancellation statement for arbitrary invariant
mixtures is needed: the `hnonzero` hypothesis is required only for
ergodic probabilities.
-/

noncomputable section

open Function MeasureTheory Set
open scoped BoundedContinuousFunction

namespace HGAS

variable {X : Type*} [MetricSpace X]
  [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

/-- Nonzero drift on every positive finite-chart conditional of an
ergodic invariant probability forces the maximal reward below the
pointwise boundary bound.

The proof tests the hypothesis only on an ergodic maximizing probability.
Ergodicity makes the invariant finite chart null or full.  If it were
full, its positive-mass conditional would simultaneously have a nonzero
drift coordinate by `hnonzero` and zero drift in every coordinate by the
compact-accumulator obstruction. -/
theorem maximalInvariantAverage_le_neg_epsilon_of_compactAccumulator
    {ϕ : Flow ℝ X}
    {s : Set X} (hs : MeasurableSet s)
    (hinv : IsInvariant ϕ s)
    {B : Type*} [TopologicalSpace B]
    [MeasurableSpace B] [BorelSpace B]
    {ψ : Flow ℝ B}
    (π : s → B) (hπ : Continuous π)
    (hequiv :
      ∀ t : ℝ,
        Semiconj π ((ϕ.restrict hinv) t) (ψ t))
    {m : ℕ}
    (q : s → FiniteAccumulatorChart m)
    (hq : Continuous q)
    (gb : B →ᵇ FinVector m ℝ)
    (hU :
      ∀ x i t,
        HasDerivAt
          (fun r ↦
            (q ((ϕ.restrict hinv) r x)).1.1.1 i)
          (accumulatorUField
            (q ((ϕ.restrict hinv) t x)).1.1.1
            (q ((ϕ.restrict hinv) t x)).1.1.2
            (gb (π ((ϕ.restrict hinv) t x))) i) t)
    (hW :
      ∀ x t,
        HasDerivAt
          (fun r ↦
            (q ((ϕ.restrict hinv) r x)).1.1.2)
          (accumulatorWField
            (q ((ϕ.restrict hinv) t x)).1.1.1
            (q ((ϕ.restrict hinv) t x)).1.1.2
            (gb (π ((ϕ.restrict hinv) t x)))) t)
    (hnonzero :
      ∀ μ : Dynamics.InvariantProbabilityMeasure ϕ,
        Dynamics.IsErgodicInvariantProbability ϕ μ.measure →
          ∀ hpos : (μ.measure : Measure X) s ≠ 0,
          let ν :=
            μ.restrictToPositiveInvariant hs hpos hinv
          ∃ i : Fin m,
            (∫ b, gb b i
              ∂((ν.mapEquivariant π hπ hequiv).measure :
                Measure B)) ≠ 0)
    (reward : X →ᵇ ℝ) (ε : ℝ)
    (hreward :
      ∀ x, x ∉ s → reward x ≤ -ε) :
    Dynamics.maximalInvariantAverage ϕ reward ≤ -ε := by
  apply
    Dynamics.maximalInvariantAverage_le_of_forall_ergodic
      ϕ reward
  intro μ hμergodic
  have hnull : (μ.measure : Measure X) s = 0 := by
    rcases hμergodic.zero_or_one_of_isInvariant hs hinv with
      hzero | hfull
    · exact hzero
    · have hpos : (μ.measure : Measure X) s ≠ 0 := by
        rw [hfull]
        exact one_ne_zero
      let ν :=
        μ.restrictToPositiveInvariant hs hpos hinv
      obtain ⟨i, hi⟩ := hnonzero μ hμergodic hpos
      exfalso
      apply hi
      exact
        ν.coordinateBaseIntegral_eq_zero_compactAccumulator
          π hπ hequiv q hq gb hU hW i
  exact
    Dynamics.observableAverage_le_of_null_exception
      reward μ.measure s (-ε) hnull hreward

/-- **Abstract strict compact sign dichotomy.**

In the `P` case every positive finite-chart conditional of an ergodic
invariant probability has a nonzero drift; in the `¬P` case a designated
finite graph supplies an invariant probability with positive reward.
Therefore strict negativity of the maximal invariant reward is equivalent
to `P`. -/
theorem maximalInvariantAverage_neg_iff_of_compactAccumulatorGap
    {ϕ : Flow ℝ X}
    {s : Set X} (hs : MeasurableSet s)
    (hinv : IsInvariant ϕ s)
    {B : Type*} [TopologicalSpace B]
    [MeasurableSpace B] [BorelSpace B]
    {ψ : Flow ℝ B}
    (π : s → B) (hπ : Continuous π)
    (hequiv :
      ∀ t : ℝ,
        Semiconj π ((ϕ.restrict hinv) t) (ψ t))
    {m : ℕ}
    (q : s → FiniteAccumulatorChart m)
    (hq : Continuous q)
    (gb : B →ᵇ FinVector m ℝ)
    (hU :
      ∀ x i t,
        HasDerivAt
          (fun r ↦
            (q ((ϕ.restrict hinv) r x)).1.1.1 i)
          (accumulatorUField
            (q ((ϕ.restrict hinv) t x)).1.1.1
            (q ((ϕ.restrict hinv) t x)).1.1.2
            (gb (π ((ϕ.restrict hinv) t x))) i) t)
    (hW :
      ∀ x t,
        HasDerivAt
          (fun r ↦
            (q ((ϕ.restrict hinv) r x)).1.1.2)
          (accumulatorWField
            (q ((ϕ.restrict hinv) t x)).1.1.1
            (q ((ϕ.restrict hinv) t x)).1.1.2
            (gb (π ((ϕ.restrict hinv) t x)))) t)
    (reward : X →ᵇ ℝ) (P : Prop)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hreward :
      ∀ x, x ∉ s → reward x ≤ -ε)
    (hnonzero :
      P →
        ∀ μ : Dynamics.InvariantProbabilityMeasure ϕ,
          Dynamics.IsErgodicInvariantProbability ϕ μ.measure →
            ∀ hpos : (μ.measure : Measure X) s ≠ 0,
            let ν :=
              μ.restrictToPositiveInvariant hs hpos hinv
            ∃ i : Fin m,
              (∫ b, gb b i
                ∂((ν.mapEquivariant π hπ hequiv).measure :
                  Measure B)) ≠ 0)
    (hfiniteGraph :
      ¬P →
        ∃ μ : Dynamics.InvariantProbabilityMeasure ϕ,
          δ ≤ Dynamics.observableAverage reward μ.measure) :
    Dynamics.maximalInvariantAverage ϕ reward < 0 ↔ P := by
  apply Dynamics.maximalInvariantAverage_neg_iff_of_two_sided_gap
    ϕ reward P hε hδ
  · intro hP
    exact
      maximalInvariantAverage_le_neg_epsilon_of_compactAccumulator
        hs hinv π hπ hequiv q hq gb hU hW
        (hnonzero hP) reward ε hreward
  · intro hnot
    obtain ⟨μ, hμ⟩ := hfiniteGraph hnot
    exact
      Dynamics.le_maximalInvariantAverage_of_invariantProbability
        ϕ reward μ hμ

end HGAS

end
