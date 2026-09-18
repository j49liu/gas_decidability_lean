import HGAS.Dynamics.ErgodicInvariantProbability
import Mathlib.MeasureTheory.Measure.Typeclasses.ZeroOne

/-!
# Ergodic probabilities for the identity flow

An ergodic probability for a stationary flow is a point mass.  This tiny
lemma is useful whenever an invariant first integral is exposed as a factor:
ergodicity forces that factor to take one almost-surely constant value.

The proof applies the flow zero--one law to every measurable set and then
uses Mathlib's standard-Borel characterization of nonzero zero--one measures.
-/

noncomputable section

open MeasureTheory Set

namespace HGAS.Dynamics

variable {X : Type*} [TopologicalSpace X]
  [MeasurableSpace X] [BorelSpace X]
  [StandardBorelSpace X]

/-- Every ergodic invariant probability of the identity flow is Dirac. -/
theorem exists_eq_dirac_of_isErgodicInvariantProbability_identity
    (μ : ProbabilityMeasure X)
    (hμ : IsErgodicInvariantProbability (Flow.id ℝ X) μ) :
    ∃ x : X, (μ : Measure X) = Measure.dirac x := by
  letI : IsZeroOneMeasure (μ : Measure X) :=
    ⟨by
      intro s hs
      apply hμ.zero_or_one hs
      intro t
      simp [Flow.id_apply]⟩
  have hne : (μ : Measure X) ≠ 0 := by
    intro hzero
    have huniv :=
      congrArg (fun ν : Measure X ↦ ν Set.univ) hzero
    simp at huniv
  letI : NeZero (μ : Measure X) := ⟨hne⟩
  exact IsZeroOneMeasure.exists_eq_dirac

/-- Probability-measure formulation of the same classification. -/
theorem exists_eq_diracProba_of_isErgodicInvariantProbability_identity
    (μ : ProbabilityMeasure X)
    (hμ : IsErgodicInvariantProbability (Flow.id ℝ X) μ) :
    ∃ x : X, μ = MeasureTheory.diracProba x := by
  obtain ⟨x, hx⟩ :=
    exists_eq_dirac_of_isErgodicInvariantProbability_identity μ hμ
  refine ⟨x, ProbabilityMeasure.toMeasure_injective ?_⟩
  simpa [MeasureTheory.diracProba] using hx

end HGAS.Dynamics
