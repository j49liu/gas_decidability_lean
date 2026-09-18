import HGAS.Dynamics.ErgodicInvariantProbability
import Mathlib.Tactic

/-!
# Ergodicity descends to continuous flow factors

Let `ϕ` and `ψ` be continuous real flows and let

```text
                 π : X → Y
```

be a continuous semiconjugacy.  If `μ` is an ergodic invariant
probability for `ϕ`, then its pushforward `π₊ μ` is an ergodic invariant
probability for `ψ`.

The argument is elementary but useful throughout the project.  A
measurable set in `Y` which is invariant modulo `π₊ μ` pulls back to a
measurable set in `X` which is invariant modulo `μ`.  The zero--one law
upstairs therefore gives the zero--one law downstairs.  Invariance of the
pushforward is the existing `InvariantProbabilityMeasure.mapEquivariant`
construction.

No surjectivity, injectivity, compactness, or finite-fiber assumption is
needed.  In particular this result applies both to quotient maps and to
state-observation maps.
-/

noncomputable section

open Filter Function MeasureTheory Set

namespace HGAS.Dynamics

namespace IsErgodicInvariantProbability

variable {X Y : Type*}
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  {ϕ : Flow ℝ X} {ψ : Flow ℝ Y}
  {μ : ProbabilityMeasure X}

/-- A continuous equivariant pushforward of an ergodic invariant
probability is again ergodic and invariant.

The proof deliberately uses the project's unbundled zero--one definition
of flow ergodicity.  This avoids replacing ergodicity of the whole real
flow by the generally stronger and inappropriate condition of ergodicity
for one chosen time map. -/
theorem mapEquivariant
    (hμ : IsErgodicInvariantProbability ϕ μ)
    (π : X → Y) (hπ : Continuous π)
    (hequiv :
      ∀ t : ℝ, Function.Semiconj π (ϕ t) (ψ t)) :
    IsErgodicInvariantProbability ψ
      (μ.map hπ.measurable.aemeasurable) := by
  let ν :
      InvariantProbabilityMeasure ψ :=
    (⟨μ, hμ.invariant⟩ :
      InvariantProbabilityMeasure ϕ).mapEquivariant
        π hπ hequiv
  refine ⟨ν.invariant, ?_⟩
  intro A hA hAInvariant
  -- Pull the candidate invariant set back to the source.
  have hpreimageMeasurable :
      MeasurableSet (π ⁻¹' A) :=
    hA.preimage hπ.measurable
  have hpreimageInvariant :
      ∀ t : ℝ,
        (ϕ t) ⁻¹' (π ⁻¹' A) =ᵐ[(μ : Measure X)]
          π ⁻¹' A := by
    intro t
    have hpull :
        (fun x ↦ ((ψ t) ⁻¹' A) (π x)) =ᵐ[
          (μ : Measure X)] fun x ↦ A (π x) :=
      ae_of_ae_map hπ.measurable.aemeasurable
        (hAInvariant t)
    filter_upwards [hpull] with x hx
    change (π (ϕ t x) ∈ A) = (π x ∈ A)
    rw [hequiv t x]
    exact hx
  -- Apply source ergodicity and identify pushforward mass with preimage
  -- mass.
  rcases hμ.zero_or_one
      hpreimageMeasurable hpreimageInvariant with
    hzero | hone
  · left
    change Measure.map π (μ : Measure X) A = 0
    rw [Measure.map_apply hπ.measurable hA]
    exact hzero
  · right
    change Measure.map π (μ : Measure X) A = 1
    rw [Measure.map_apply hπ.measurable hA]
    exact hone

/-- Bundled-semiconjugacy form of `mapEquivariant`. -/
theorem mapSemiconjugacy
    (hμ : IsErgodicInvariantProbability ϕ μ)
    {π : X → Y}
    (hπ : Flow.IsSemiconjugacy π ϕ ψ) :
    IsErgodicInvariantProbability ψ
      (μ.map hπ.cont.measurable.aemeasurable) :=
  hμ.mapEquivariant π hπ.cont hπ.semiconj

end IsErgodicInvariantProbability

end HGAS.Dynamics
