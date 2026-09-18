import HGAS.Dynamics.InvariantProbability
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic

/-!
# Restricting invariant probabilities to invariant sets

Let `ϕ` be a real flow and let `μ` be an invariant probability.  If a
measurable set `s` is invariant and has positive `μ`-mass, then the
normalized restriction

```
μ(· ∩ s) / μ(s)
```

is again an invariant probability.

For a genuine two-sided flow, invariance `ϕₜ(s) ⊆ s` automatically
upgrades to `ϕₜ⁻¹(s) = s`: apply the time `-t` map for the reverse
inclusion.  This exact preimage equality is what makes restriction
commute with pushforward.

The result is stated independently of the Veronese construction because
conditioning on invariant components is useful throughout compact-flow
arguments.
-/

namespace HGAS.Dynamics

open Function MeasureTheory Set

noncomputable section

variable {K : Type*} [TopologicalSpace K] [MeasurableSpace K]
  [BorelSpace K]

omit [MeasurableSpace K] [BorelSpace K] in
theorem preimage_eq_of_flow_isInvariant
    (ϕ : Flow ℝ K) {s : Set K}
    (hs : IsInvariant ϕ s) (t : ℝ) :
    ϕ t ⁻¹' s = s := by
  ext x
  constructor
  · intro hx
    have hback := hs (-t) hx
    simpa [← ϕ.map_add] using hback
  · intro hx
    exact hs t hx

omit [MeasurableSpace K] [BorelSpace K] in
/-- For a two-sided real flow, the complement of an invariant set is
again invariant. -/
theorem isInvariant_compl_of_flow
    (ϕ : Flow ℝ K) {s : Set K}
    (hs : IsInvariant ϕ s) :
    IsInvariant ϕ sᶜ := by
  intro t x hx hmem
  have hback := hs (-t) hmem
  apply hx
  simpa [← ϕ.map_add] using hback

theorem map_restrict_eq_restrict
    (ϕ : Flow ℝ K)
    (μ : InvariantProbabilityMeasure ϕ)
    {s : Set K} (hsm : MeasurableSet s)
    (hsi : IsInvariant ϕ s) (t : ℝ) :
    Measure.map (ϕ t)
        ((μ.measure : Measure K).restrict s) =
      (μ.measure : Measure K).restrict s := by
  have hrestrict :=
    Measure.restrict_map
      (μ := (μ.measure : Measure K))
      (ϕ.continuous_toFun t).measurable hsm
  rw [μ.map_time_toMeasure t,
    preimage_eq_of_flow_isInvariant ϕ hsi t] at hrestrict
  exact hrestrict.symm

theorem isInvariantProbability_normalize_restrict
    [Nonempty K]
    (ϕ : Flow ℝ K)
    (μ : InvariantProbabilityMeasure ϕ)
    {s : Set K} (hsm : MeasurableSet s)
    (hsi : IsInvariant ϕ s)
    (hnonzero :
      μ.measure.toFiniteMeasure.restrict s ≠ 0) :
    IsInvariantProbability ϕ
      (μ.measure.toFiniteMeasure.restrict s).normalize := by
  let ν : FiniteMeasure K :=
    μ.measure.toFiniteMeasure.restrict s
  have hν : ν ≠ 0 := hnonzero
  intro t
  apply ProbabilityMeasure.toMeasure_injective
  simp only [timePushforward, ProbabilityMeasure.toMeasure_map]
  rw [ν.toMeasure_normalize_eq_of_nonzero hν]
  rw [Measure.map_smul]
  have hmap :
      Measure.map (ϕ t) (ν : Measure K) =
        (ν : Measure K) := by
    simpa only [ν, FiniteMeasure.restrict_measure_eq] using
      map_restrict_eq_restrict ϕ μ hsm hsi t
  rw [hmap]

omit [TopologicalSpace K] [BorelSpace K] in
/-- The normalized restriction is concentrated on the set used for the
restriction.  This support fact does not require invariance. -/
theorem ae_mem_normalize_restrict
    [Nonempty K]
    (ν : FiniteMeasure K)
    {s : Set K} (hsm : MeasurableSet s)
    (hnonzero : ν.restrict s ≠ 0) :
    ∀ᵐ x ∂((ν.restrict s).normalize : Measure K), x ∈ s := by
  rw [(ν.restrict s).toMeasure_normalize_eq_of_nonzero hnonzero]
  exact Measure.ae_smul_measure (ae_restrict_mem hsm) _

/-- Condition an invariant probability on an invariant measurable set of
positive mass. -/
noncomputable def normalizeInvariantRestriction
    [Nonempty K]
    (ϕ : Flow ℝ K)
    (μ : InvariantProbabilityMeasure ϕ)
    (s : Set K) (hsm : MeasurableSet s)
    (hsi : IsInvariant ϕ s)
    (hnonzero :
      μ.measure.toFiniteMeasure.restrict s ≠ 0) :
    InvariantProbabilityMeasure ϕ where
  measure := (μ.measure.toFiniteMeasure.restrict s).normalize
  invariant :=
    isInvariantProbability_normalize_restrict
      ϕ μ hsm hsi hnonzero

end

end HGAS.Dynamics
