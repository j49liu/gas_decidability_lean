import HGAS.Dynamics.InvariantRestriction
import Mathlib.Dynamics.Ergodic.Action.Basic

/-!
# Ergodic invariant probabilities for continuous real flows

Mathlib provides `ErgodicVAdd` for a group action through typeclasses.
Continuous flows in this project are passed explicitly, so this file gives
the equivalent unbundled interface: invariance of the probability and a
zero--one law for measurable sets which are invariant modulo null sets
under every time map.
-/

noncomputable section

open Filter MeasureTheory Set

namespace HGAS.Dynamics

variable {X : Type*} [TopologicalSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- Ergodicity for a probability preserved by a continuous real flow,
expressed as the measurable zero-one law for sets invariant modulo null
sets under every time map. -/
def IsErgodicInvariantProbability
    (ϕ : Flow ℝ X) (μ : ProbabilityMeasure X) : Prop :=
  IsInvariantProbability ϕ μ ∧
    ∀ A : Set X, MeasurableSet A →
      (∀ t : ℝ, (ϕ t) ⁻¹' A =ᵐ[(μ : Measure X)] A) →
      (μ : Measure X) A = 0 ∨
        (μ : Measure X) A = 1

namespace IsErgodicInvariantProbability

variable {ϕ : Flow ℝ X} {μ : ProbabilityMeasure X}

/-- An ergodic invariant probability is, in particular, invariant. -/
theorem invariant
    (hμ : IsErgodicInvariantProbability ϕ μ) :
    IsInvariantProbability ϕ μ :=
  hμ.1

/-- The zero-one clause of flow ergodicity. -/
theorem zero_or_one
    (hμ : IsErgodicInvariantProbability ϕ μ)
    {s : Set X} (hs : MeasurableSet s)
    (hinv :
      ∀ t : ℝ,
        (ϕ t) ⁻¹' s =ᵐ[(μ : Measure X)] s) :
    (μ : Measure X) s = 0 ∨ (μ : Measure X) s = 1 :=
  hμ.2 s hs hinv

/-- For a literally invariant measurable set, the zero-one law is
equivalently stated as zero mass for the set or for its complement. -/
theorem measure_self_or_compl_eq_zero
    (hμ : IsErgodicInvariantProbability ϕ μ)
    {s : Set X} (hs : MeasurableSet s)
    (hinv : ∀ t : ℝ, (ϕ t) ⁻¹' s = s) :
    (μ : Measure X) s = 0 ∨ (μ : Measure X) sᶜ = 0 := by
  rcases hμ.zero_or_one hs (fun t ↦ by rw [hinv t]) with
    hzero | hone
  · exact Or.inl hzero
  · right
    rw [measure_compl hs (measure_ne_top _ _), hone]
    simp

/-- A measurable forward-invariant set for a two-sided flow has mass zero
or one under an ergodic invariant probability. -/
theorem zero_or_one_of_isInvariant
    (hμ : IsErgodicInvariantProbability ϕ μ)
    {s : Set X} (hs : MeasurableSet s)
    (hinv : IsInvariant ϕ s) :
    (μ : Measure X) s = 0 ∨ (μ : Measure X) s = 1 :=
  hμ.zero_or_one hs fun t ↦ by
    rw [preimage_eq_of_flow_isInvariant ϕ hinv t]

end IsErgodicInvariantProbability

end HGAS.Dynamics
