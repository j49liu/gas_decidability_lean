import HGAS.Dynamics.InvariantProbability
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Order.Compact

/-!
# Compactness of invariant probability measures

Let `K` be a compact metric space equipped with its Borel measurable
structure, and let `ϕ : Flow ℝ K` be continuous.  Mathlib's Prokhorov theory
shows that the whole space `ProbabilityMeasure K` is compact in the weak
topology.  Since pushforward by a continuous time map is continuous, the
probabilities fixed by every time pushforward form a closed, hence compact,
subset.

Consequently, once this subset is known to be nonempty, integration of a
bounded continuous real observable attains both a maximum and a minimum on
it.  This file deliberately takes nonemptiness as a hypothesis where it is
needed: it does not postulate the missing Krylov--Bogolyubov existence step.
-/

noncomputable section

open Function MeasureTheory Set Topology
open scoped BoundedContinuousFunction

namespace HGAS.Dynamics

variable {K : Type*} [MetricSpace K] [MeasurableSpace K] [BorelSpace K]

/-- The set of probability measures invariant under every time map of `ϕ`. -/
def invariantProbabilitySet (ϕ : Flow ℝ K) : Set (ProbabilityMeasure K) :=
  {μ | IsInvariantProbability ϕ μ}

/-- Pushforward by a fixed time map is continuous in the weak topology on
probability measures. -/
theorem continuous_timePushforward (ϕ : Flow ℝ K) (t : ℝ) :
    Continuous (fun μ : ProbabilityMeasure K ↦ timePushforward ϕ μ t) := by
  simpa only [timePushforward] using
    ProbabilityMeasure.continuous_map (ϕ.continuous_toFun t)

/-- The invariant probabilities are a closed subset of all probability
measures. -/
theorem isClosed_invariantProbabilitySet (ϕ : Flow ℝ K) :
    IsClosed (invariantProbabilitySet ϕ) := by
  change IsClosed {μ : ProbabilityMeasure K |
    ∀ t : ℝ, timePushforward ϕ μ t = μ}
  have hclosed :
      IsClosed (⋂ t : ℝ,
        {μ : ProbabilityMeasure K | timePushforward ϕ μ t = id μ}) :=
    isClosed_iInter fun t ↦
      isClosed_eq (continuous_timePushforward ϕ t) continuous_id
  convert hclosed using 1
  ext μ
  simp only [mem_setOf_eq, mem_iInter, id_eq]

/-- The invariant probabilities form a compact set in the weak topology.
The set may still be empty at this stage. -/
theorem isCompact_invariantProbabilitySet [CompactSpace K] (ϕ : Flow ℝ K) :
    IsCompact (invariantProbabilitySet ϕ) :=
  (isClosed_invariantProbabilitySet ϕ).isCompact

/-- A fixed point supplies a concrete member of the invariant-probability
set through its Dirac probability. -/
theorem invariantProbabilitySet_nonempty_of_fixedPoint
    (ϕ : Flow ℝ K) (x : K)
    (hfixed : InvariantProbabilityMeasure.IsFlowFixedPoint ϕ x) :
    (invariantProbabilitySet ϕ).Nonempty := by
  refine ⟨diracProba x, ?_⟩
  exact InvariantProbabilityMeasure.isInvariantProbability_diracProba x hfixed

namespace InvariantProbabilityMeasure

variable {ϕ : Flow ℝ K}

/-- Two bundled invariant probabilities are equal when their underlying
probability measures are equal. -/
@[ext]
theorem ext
    {μ ν : InvariantProbabilityMeasure ϕ}
    (h : μ.measure = ν.measure) : μ = ν := by
  cases μ
  cases ν
  simp_all

theorem measure_injective :
    Function.Injective
      (fun μ : InvariantProbabilityMeasure ϕ ↦ μ.measure) :=
  fun _ _ ↦ ext

/-- The range of the bundle projection is exactly the closed invariant set. -/
theorem range_measure :
    Set.range (fun μ : InvariantProbabilityMeasure ϕ ↦ μ.measure) =
      invariantProbabilitySet ϕ := by
  ext μ
  constructor
  · rintro ⟨ν, rfl⟩
    exact ν.invariant
  · intro hμ
    exact ⟨⟨μ, hμ⟩, rfl⟩

/-- The bundled type carries the topology induced by its underlying
probability measure. -/
instance : TopologicalSpace (InvariantProbabilityMeasure ϕ) :=
  TopologicalSpace.induced
    (fun μ : InvariantProbabilityMeasure ϕ ↦ μ.measure) inferInstance

/-- The projection from bundled invariant probabilities to all probability
measures is a topological embedding. -/
theorem isEmbedding_measure :
    IsEmbedding
      (fun μ : InvariantProbabilityMeasure ϕ ↦ μ.measure) where
  eq_induced := rfl
  injective := measure_injective

/-- The bundled invariant-probability type is compact.  This remains true
even when it is empty; nonemptiness is a separate Krylov--Bogolyubov issue. -/
instance [CompactSpace K] : CompactSpace (InvariantProbabilityMeasure ϕ) := by
  rw [← isCompact_univ_iff]
  apply isEmbedding_measure.isCompact_iff.2
  rw [image_univ, range_measure]
  exact isCompact_invariantProbabilitySet ϕ

/-- Bundled invariant probabilities exist exactly when the closed invariant
subset is nonempty. -/
theorem nonempty_iff_set_nonempty :
    Nonempty (InvariantProbabilityMeasure ϕ) ↔
      (invariantProbabilitySet ϕ).Nonempty := by
  constructor
  · rintro ⟨μ⟩
    exact ⟨μ.measure, μ.invariant⟩
  · rintro ⟨μ, hμ⟩
    exact ⟨⟨μ, hμ⟩⟩

end InvariantProbabilityMeasure

/-- The average of a bounded continuous observable against a probability
measure. -/
def observableAverage (f : K →ᵇ ℝ) (μ : ProbabilityMeasure K) : ℝ :=
  ∫ x, f x ∂(μ : Measure K)

/-- Observable averages vary continuously with the probability measure in
the weak topology. -/
theorem continuous_observableAverage (f : K →ᵇ ℝ) :
    Continuous (observableAverage f) := by
  simpa only [observableAverage] using
    ProbabilityMeasure.continuous_integral_boundedContinuousFunction f

/-- The set of averages attained by invariant probabilities is compact. -/
theorem isCompact_observableAverage_image
    [CompactSpace K] (ϕ : Flow ℝ K) (f : K →ᵇ ℝ) :
    IsCompact (observableAverage f '' invariantProbabilitySet ϕ) :=
  (isCompact_invariantProbabilitySet ϕ).image
    (continuous_observableAverage f)

/-- If an invariant probability exists, a bounded continuous observable has
a maximizing invariant probability. -/
theorem exists_invariantProbability_isMaxOn_average
    [CompactSpace K] (ϕ : Flow ℝ K) (f : K →ᵇ ℝ)
    (hne : (invariantProbabilitySet ϕ).Nonempty) :
    ∃ μ ∈ invariantProbabilitySet ϕ,
      IsMaxOn (observableAverage f) (invariantProbabilitySet ϕ) μ :=
  (isCompact_invariantProbabilitySet ϕ).exists_isMaxOn hne
    (continuous_observableAverage f).continuousOn

/-- If an invariant probability exists, a bounded continuous observable has
a minimizing invariant probability. -/
theorem exists_invariantProbability_isMinOn_average
    [CompactSpace K] (ϕ : Flow ℝ K) (f : K →ᵇ ℝ)
    (hne : (invariantProbabilitySet ϕ).Nonempty) :
    ∃ μ ∈ invariantProbabilitySet ϕ,
      IsMinOn (observableAverage f) (invariantProbabilitySet ϕ) μ :=
  (isCompact_invariantProbabilitySet ϕ).exists_isMinOn hne
    (continuous_observableAverage f).continuousOn

/-- The invariant probabilities maximizing a fixed observable. -/
def maximizingInvariantSet (ϕ : Flow ℝ K) (f : K →ᵇ ℝ) :
    Set (ProbabilityMeasure K) :=
  {μ | μ ∈ invariantProbabilitySet ϕ ∧
    IsMaxOn (observableAverage f) (invariantProbabilitySet ϕ) μ}

/-- The invariant probabilities minimizing a fixed observable. -/
def minimizingInvariantSet (ϕ : Flow ℝ K) (f : K →ᵇ ℝ) :
    Set (ProbabilityMeasure K) :=
  {μ | μ ∈ invariantProbabilitySet ϕ ∧
    IsMinOn (observableAverage f) (invariantProbabilitySet ϕ) μ}

/-- The maximizing invariant-probability set is closed. -/
theorem isClosed_maximizingInvariantSet
    (ϕ : Flow ℝ K) (f : K →ᵇ ℝ) :
    IsClosed (maximizingInvariantSet ϕ f) := by
  rw [show maximizingInvariantSet ϕ f =
      ({μ | μ ∈ invariantProbabilitySet ϕ} ∩
        ⋂ ν ∈ invariantProbabilitySet ϕ,
          {μ | observableAverage f ν ≤ observableAverage f μ}) by
    ext μ
    simp only [maximizingInvariantSet, mem_setOf_eq, mem_inter_iff,
      mem_iInter, isMaxOn_iff]]
  exact (isClosed_invariantProbabilitySet ϕ).inter <|
    isClosed_biInter fun ν _ ↦
      isClosed_le continuous_const (continuous_observableAverage f)

/-- The minimizing invariant-probability set is closed. -/
theorem isClosed_minimizingInvariantSet
    (ϕ : Flow ℝ K) (f : K →ᵇ ℝ) :
    IsClosed (minimizingInvariantSet ϕ f) := by
  rw [show minimizingInvariantSet ϕ f =
      ({μ | μ ∈ invariantProbabilitySet ϕ} ∩
        ⋂ ν ∈ invariantProbabilitySet ϕ,
          {μ | observableAverage f μ ≤ observableAverage f ν}) by
    ext μ
    simp only [minimizingInvariantSet, mem_setOf_eq, mem_inter_iff,
      mem_iInter, isMinOn_iff]]
  exact (isClosed_invariantProbabilitySet ϕ).inter <|
    isClosed_biInter fun ν _ ↦
      isClosed_le (continuous_observableAverage f) continuous_const

/-- The maximizing invariant-probability set is compact. -/
theorem isCompact_maximizingInvariantSet
    [CompactSpace K] (ϕ : Flow ℝ K) (f : K →ᵇ ℝ) :
    IsCompact (maximizingInvariantSet ϕ f) :=
  (isClosed_maximizingInvariantSet ϕ f).isCompact

/-- The minimizing invariant-probability set is compact. -/
theorem isCompact_minimizingInvariantSet
    [CompactSpace K] (ϕ : Flow ℝ K) (f : K →ᵇ ℝ) :
    IsCompact (minimizingInvariantSet ϕ f) :=
  (isClosed_minimizingInvariantSet ϕ f).isCompact

/-- Under the nonemptiness hypothesis, the compact maximizing set is itself
nonempty. -/
theorem maximizingInvariantSet_nonempty
    [CompactSpace K] (ϕ : Flow ℝ K) (f : K →ᵇ ℝ)
    (hne : (invariantProbabilitySet ϕ).Nonempty) :
    (maximizingInvariantSet ϕ f).Nonempty := by
  obtain ⟨μ, hμ, hmax⟩ :=
    exists_invariantProbability_isMaxOn_average ϕ f hne
  exact ⟨μ, hμ, hmax⟩

/-- Under the nonemptiness hypothesis, the compact minimizing set is itself
nonempty. -/
theorem minimizingInvariantSet_nonempty
    [CompactSpace K] (ϕ : Flow ℝ K) (f : K →ᵇ ℝ)
    (hne : (invariantProbabilitySet ϕ).Nonempty) :
    (minimizingInvariantSet ϕ f).Nonempty := by
  obtain ⟨μ, hμ, hmin⟩ :=
    exists_invariantProbability_isMinOn_average ϕ f hne
  exact ⟨μ, hμ, hmin⟩

end HGAS.Dynamics
