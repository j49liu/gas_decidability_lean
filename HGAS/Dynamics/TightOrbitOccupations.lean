import HGAS.Dynamics.UniformNegativeBlocks
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Tight occupation measures and full orbit convergence

Let `ϕ` be a continuous real flow and let `x` be a point.  The probability

```text
  mₙ = (1 / (n + 1)) ∫₀ⁿ⁺¹ δ_{ϕₜx} dt
```

is already constructed in `UniformNegativeBlocks` as
`orbitOccupationProbability`.  This file records the compactness argument
used at the end of the Dani--Smillie proof.

There are three logically separate ingredients.

1. Every weak limit of a sequence of increasingly long occupation
   probabilities is invariant.  This is just the endpoint estimate: a
   fixed time translation changes an average by `O(1 / T)`.
2. Tightness makes the family of occupation probabilities relatively
   compact by Prokhorov's theorem.
3. If every invariant accumulation probability satisfying a property `P`
   is one prescribed probability `ν`, and every accumulation probability
   does satisfy `P`, then the entire sequence converges to `ν`.

The property `P` is deliberately abstract.  In the horocycle application
it says that the limiting measure gives zero mass to the union of periodic
horocycles.  Keeping it abstract makes the final compactness argument
usable in other noncompact dynamical systems.
-/

noncomputable section

open Filter Function MeasureTheory Set Topology
open scoped BoundedContinuousFunction

namespace HGAS.Dynamics

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X]

/-- The occupation probability of the first `n + 1` units of the orbit of
`x`. -/
def integerOrbitOccupationProbability
    (ϕ : Flow ℝ X) (x : X) (n : ℕ) :
    ProbabilityMeasure X :=
  orbitOccupationProbability ϕ x (n + 1 : ℝ) (by positivity)

omit [SecondCountableTopology X] in
@[simp]
theorem integral_integerOrbitOccupationProbability
    (ϕ : Flow ℝ X) (f : X →ᵇ ℝ) (x : X) (n : ℕ) :
    (∫ y, f y
        ∂(integerOrbitOccupationProbability ϕ x n : Measure X)) =
      (n + 1 : ℝ)⁻¹ * orbitIntegral ϕ f (n + 1 : ℝ) x := by
  exact integral_orbitOccupationProbability
    ϕ f x (n + 1 : ℝ) (by positivity)

/-- A property holds for all weak accumulation probabilities of the
integer-length occupation measures.

The indexing map is only required to tend to infinity.  This form is
stable under taking further subsequences and is exactly what the abstract
compactness proof needs. -/
def EveryOrbitOccupationLimitSatisfies
    (ϕ : Flow ℝ X) (x : X)
    (P : ProbabilityMeasure X → Prop) : Prop :=
  ∀ (r : ℕ → ℕ) (μ : ProbabilityMeasure X),
    Tendsto r atTop atTop →
    Tendsto
      (integerOrbitOccupationProbability ϕ x ∘ r)
      atTop (𝓝 μ) →
    P μ

omit [SecondCountableTopology X] in
/-- Every weak limit along orbit lengths tending to infinity is invariant.

No compactness or tightness is used here.  The statement is a direct
consequence of the endpoint estimate for finite orbit segments and weak
continuity of pushforward by a fixed time map. -/
theorem isInvariantProbability_of_tendsto_integerOrbitOccupation
    (ϕ : Flow ℝ X) (x : X)
    (r : ℕ → ℕ) (μ : ProbabilityMeasure X)
    (hr : Tendsto r atTop atTop)
    (hμ :
      Tendsto
        (integerOrbitOccupationProbability ϕ x ∘ r)
        atTop (𝓝 μ)) :
    IsInvariantProbability ϕ μ := by
  intro s
  have hpush_to_μ :
      Tendsto
        (fun n ↦
          timePushforward ϕ
            (integerOrbitOccupationProbability ϕ x (r n)) s)
        atTop (𝓝 μ) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    have hbase :
        Tendsto
          (fun n ↦
            ∫ y, f y
              ∂(integerOrbitOccupationProbability ϕ x (r n) :
                Measure X))
          atTop (𝓝 (∫ y, f y ∂(μ : Measure X))) :=
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ) f
    have hdefect :
        Tendsto
          (fun n ↦
            (∫ y, f y
                ∂(timePushforward ϕ
                  (integerOrbitOccupationProbability ϕ x (r n)) s :
                    Measure X)) -
              ∫ y, f y
                ∂(integerOrbitOccupationProbability ϕ x (r n) :
                  Measure X))
          atTop (𝓝 0) := by
      simpa only [integerOrbitOccupationProbability,
        Function.comp_apply] using
        (tendsto_occupation_timePushforward_integral_sub
          ϕ f (fun _ : ℕ ↦ x) s).comp hr
    simpa only [sub_add_cancel, zero_add] using hdefect.add hbase
  have hpush_to_push :
      Tendsto
        (fun n ↦
          timePushforward ϕ
            (integerOrbitOccupationProbability ϕ x (r n)) s)
        atTop (𝓝 (timePushforward ϕ μ s)) :=
    (continuous_timePushforward ϕ s).continuousAt.tendsto.comp hμ
  exact tendsto_nhds_unique hpush_to_push hpush_to_μ

omit [SecondCountableTopology X] in
/-- Invariance is an automatic property of every occupation-measure
accumulation point. -/
theorem everyOrbitOccupationLimitSatisfies_invariant
    (ϕ : Flow ℝ X) (x : X) :
    EveryOrbitOccupationLimitSatisfies ϕ x
      (IsInvariantProbability ϕ) := by
  intro r μ hr hμ
  exact
    isInvariantProbability_of_tendsto_integerOrbitOccupation
      ϕ x r μ hr hμ

/-- **Tight accumulation-point principle.**

Suppose the integer occupation probabilities of `x` form a tight family.
Suppose also that every weak accumulation probability has a property `P`,
and that the only invariant probability with `P` is `ν`.  Then the full
sequence of occupation probabilities converges weakly to `ν`.

The proof uses the subsequence criterion for convergence.  Given any
sequence of indices tending to infinity, Prokhorov compactness supplies a
convergent further subsequence.  Its limit is invariant by the endpoint
estimate, has `P` by assumption, and hence equals `ν`.
-/
theorem tendsto_integerOrbitOccupation_of_tight_of_unique
    (ϕ : Flow ℝ X) (x : X)
    (ν : ProbabilityMeasure X)
    (P : ProbabilityMeasure X → Prop)
    (htight :
      IsTightMeasureSet
        {((m : ProbabilityMeasure X) : Measure X) |
          m ∈ Set.range
            (integerOrbitOccupationProbability ϕ x)})
    (hlimits : EveryOrbitOccupationLimitSatisfies ϕ x P)
    (hunique :
      ∀ μ : ProbabilityMeasure X,
        IsInvariantProbability ϕ μ → P μ → μ = ν) :
    Tendsto
      (integerOrbitOccupationProbability ϕ x)
      atTop (𝓝 ν) := by
  let S : Set (ProbabilityMeasure X) :=
    Set.range (integerOrbitOccupationProbability ϕ x)
  have hcompact : IsCompact (closure S) := by
    apply isCompact_closure_of_isTightMeasureSet
    simpa only [S] using htight
  apply tendsto_of_subseq_tendsto
  intro r hr
  have hrange :
      ∀ n : ℕ,
        integerOrbitOccupationProbability ϕ x (r n) ∈ closure S := by
    intro n
    exact subset_closure ⟨r n, rfl⟩
  obtain ⟨μ, hμclosure, k, hk, hμ⟩ :=
    hcompact.tendsto_subseq hrange
  have hrk : Tendsto (r ∘ k) atTop atTop :=
    hr.comp hk.tendsto_atTop
  have hμ' :
      Tendsto
        (integerOrbitOccupationProbability ϕ x ∘ (r ∘ k))
        atTop (𝓝 μ) := by
    simpa only [Function.comp_def] using hμ
  have hinvariant :
      IsInvariantProbability ϕ μ :=
    isInvariantProbability_of_tendsto_integerOrbitOccupation
      ϕ x (r ∘ k) μ hrk hμ'
  have hP : P μ := hlimits (r ∘ k) μ hrk hμ'
  refine ⟨k, ?_⟩
  simpa only [hunique μ hinvariant hP, Function.comp_def] using hμ

/-- The preceding principle in the common uniqueness-of-invariant-measure
case. -/
theorem tendsto_integerOrbitOccupation_of_tight_of_uniqueInvariant
    (ϕ : Flow ℝ X) (x : X)
    (ν : ProbabilityMeasure X)
    (htight :
      IsTightMeasureSet
        {((m : ProbabilityMeasure X) : Measure X) |
          m ∈ Set.range
            (integerOrbitOccupationProbability ϕ x)})
    (hunique :
      ∀ μ : ProbabilityMeasure X,
        IsInvariantProbability ϕ μ → μ = ν) :
    Tendsto
      (integerOrbitOccupationProbability ϕ x)
      atTop (𝓝 ν) := by
  exact
    tendsto_integerOrbitOccupation_of_tight_of_unique
      ϕ x ν (fun _ ↦ True) htight
      (fun _ _ _ _ ↦ trivial)
      (fun μ hμ _ ↦ hunique μ hμ)

end HGAS.Dynamics
