import Mathlib.Dynamics.Flow
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Measure.DiracProba

/-!
# Invariant probability measures for continuous flows

This file provides the measure-theoretic interface needed later in the GAS
reduction.  A probability measure is invariant when pushing it forward by
every time map of the flow leaves it unchanged.

The scope here is deliberately foundational.  We prove elementary examples,
invariance of sets and integrals, and functoriality under an equivariant
continuous map.  We do **not** assert existence of invariant measures,
ergodic decomposition, or a Krylov--Bogolyubov theorem.
-/

noncomputable section

open Function MeasureTheory Set
open scoped BoundedContinuousFunction

namespace HGAS.Dynamics

variable {K : Type*} [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K]

/-- Push a probability measure forward by the time-`t` map of a continuous
real flow. -/
def timePushforward (ϕ : Flow ℝ K) (μ : ProbabilityMeasure K) (t : ℝ) :
    ProbabilityMeasure K :=
  μ.map (ϕ.continuous_toFun t).measurable.aemeasurable

/-- A probability measure is invariant for `ϕ` when every time pushforward
equals the original probability measure. -/
def IsInvariantProbability (ϕ : Flow ℝ K) (μ : ProbabilityMeasure K) : Prop :=
  ∀ t : ℝ, timePushforward ϕ μ t = μ

/-- A probability measure packaged together with its invariance proof. -/
structure InvariantProbabilityMeasure (ϕ : Flow ℝ K) where
  /-- The underlying probability measure. -/
  measure : ProbabilityMeasure K
  /-- Invariance under every time map. -/
  invariant : IsInvariantProbability ϕ measure

namespace InvariantProbabilityMeasure

variable {ϕ : Flow ℝ K}

/-- The defining invariance equality, exposed as a projection theorem. -/
theorem timePushforward_eq
    (μ : InvariantProbabilityMeasure ϕ) (t : ℝ) :
    timePushforward ϕ μ.measure t = μ.measure :=
  μ.invariant t

/-- Every probability measure is unchanged by the time-zero map. -/
theorem timePushforward_zero (μ : ProbabilityMeasure K) :
    timePushforward ϕ μ 0 = μ := by
  apply ProbabilityMeasure.toMeasure_injective
  simp [timePushforward, Flow.map_zero]

/-- Every probability measure is invariant for the trivial flow. -/
theorem isInvariantProbability_id (μ : ProbabilityMeasure K) :
    IsInvariantProbability (Flow.id ℝ K) μ := by
  intro t
  apply ProbabilityMeasure.toMeasure_injective
  simp [timePushforward]

/-- Package any probability measure as invariant for the trivial flow. -/
def forIdentityFlow (μ : ProbabilityMeasure K) :
    InvariantProbabilityMeasure (Flow.id ℝ K) :=
  ⟨μ, isInvariantProbability_id μ⟩

/-- A point is fixed by a flow when every time map fixes it. -/
def IsFlowFixedPoint (ϕ : Flow ℝ K) (x : K) : Prop :=
  ∀ t : ℝ, Function.IsFixedPt (ϕ t) x

/-- A Dirac probability at a fixed point is invariant. -/
theorem isInvariantProbability_diracProba
    (x : K) (hfixed : IsFlowFixedPoint ϕ x) :
    IsInvariantProbability ϕ (diracProba x) := by
  intro t
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (ϕ t) (Measure.dirac x) = Measure.dirac x
  rw [Measure.map_dirac' (ϕ.continuous_toFun t).measurable, hfixed t]

/-- Package the Dirac probability at a fixed point as an invariant
probability measure. -/
def diracOfFixedPoint
    (x : K) (hfixed : IsFlowFixedPoint ϕ x) :
    InvariantProbabilityMeasure ϕ :=
  ⟨diracProba x, isInvariantProbability_diracProba x hfixed⟩

/-- Setwise form of invariance: a measurable set and its preimage under any
time map have the same probability. -/
theorem measure_preimage_time
    (μ : InvariantProbabilityMeasure ϕ) (t : ℝ)
    {A : Set K} (hA : MeasurableSet A) :
    μ.measure ((ϕ t) ⁻¹' A) = μ.measure A := by
  calc
    μ.measure ((ϕ t) ⁻¹' A) =
        timePushforward ϕ μ.measure t A := by
          symm
          exact ProbabilityMeasure.map_apply μ.measure
            (ϕ.continuous_toFun t).measurable.aemeasurable hA
    _ = μ.measure A := by rw [μ.timePushforward_eq t]

/-- The underlying ordinary measures also satisfy the pushforward equality.
This bridge is convenient for invoking Mathlib's integration lemmas. -/
theorem map_time_toMeasure
    (μ : InvariantProbabilityMeasure ϕ) (t : ℝ) :
    Measure.map (ϕ t) (μ.measure : Measure K) =
      (μ.measure : Measure K) := by
  have h := congrArg ProbabilityMeasure.toMeasure (μ.timePushforward_eq t)
  simpa only [timePushforward, ProbabilityMeasure.toMeasure_map] using h

/-- A bounded continuous real observable is integrable against an invariant
probability measure.  Invariance is not needed for integrability; finiteness
of the underlying probability measure is enough. -/
theorem integrable_boundedContinuous
    (μ : InvariantProbabilityMeasure ϕ) (f : K →ᵇ ℝ) :
    Integrable f (μ.measure : Measure K) :=
  f.integrable (μ.measure : Measure K)

/-- Integration is invariant under every time map for bounded continuous
real observables. -/
theorem integral_comp_time
    (μ : InvariantProbabilityMeasure ϕ) (t : ℝ) (f : K →ᵇ ℝ) :
    (∫ x, f (ϕ t x) ∂(μ.measure : Measure K)) =
      ∫ x, f x ∂(μ.measure : Measure K) := by
  calc
    (∫ x, f (ϕ t x) ∂(μ.measure : Measure K)) =
        ∫ y, f y ∂Measure.map (ϕ t) (μ.measure : Measure K) := by
          symm
          exact integral_map
            (ϕ.continuous_toFun t).measurable.aemeasurable
            f.continuous.measurable.aestronglyMeasurable
    _ = ∫ y, f y ∂(μ.measure : Measure K) := by
      rw [μ.map_time_toMeasure t]

/-- The time-composed bounded continuous observable is also integrable. -/
theorem integrable_comp_time
    (μ : InvariantProbabilityMeasure ϕ) (t : ℝ) (f : K →ᵇ ℝ) :
    Integrable (fun x ↦ f (ϕ t x)) (μ.measure : Measure K) := by
  have hfmap :
      Integrable f (Measure.map (ϕ t) (μ.measure : Measure K)) := by
    rw [μ.map_time_toMeasure t]
    exact μ.integrable_boundedContinuous f
  exact (integrable_map_measure hfmap.aestronglyMeasurable
    (ϕ.continuous_toFun t).measurable.aemeasurable).mp hfmap

section Factor

variable {L : Type*} [TopologicalSpace L] [MeasurableSpace L] [BorelSpace L]
variable {ψ : Flow ℝ L}

/-- Push an invariant probability forward along a continuous equivariant
map.  Surjectivity is not needed for preservation of invariance. -/
def mapEquivariant
    (μ : InvariantProbabilityMeasure ϕ)
    (π : K → L) (hπ : Continuous π)
    (hequiv : ∀ t : ℝ, Function.Semiconj π (ϕ t) (ψ t)) :
    InvariantProbabilityMeasure ψ where
  measure := μ.measure.map hπ.measurable.aemeasurable
  invariant := by
    intro t
    apply ProbabilityMeasure.toMeasure_injective
    simp only [timePushforward, ProbabilityMeasure.toMeasure_map]
    rw [Measure.map_map (ψ.continuous_toFun t).measurable hπ.measurable]
    rw [← (hequiv t).comp_eq]
    rw [← Measure.map_map hπ.measurable (ϕ.continuous_toFun t).measurable]
    rw [μ.map_time_toMeasure t]

/-- A flow semiconjugacy sends invariant probabilities to invariant
probabilities on the factor. -/
def mapSemiconjugacy
    (μ : InvariantProbabilityMeasure ϕ)
    (π : K → L) (hπ : Flow.IsSemiconjugacy π ϕ ψ) :
    InvariantProbabilityMeasure ψ :=
  μ.mapEquivariant π hπ.cont hπ.semiconj

@[simp]
theorem mapEquivariant_measure
    (μ : InvariantProbabilityMeasure ϕ)
    (π : K → L) (hπ : Continuous π)
    (hequiv : ∀ t : ℝ, Function.Semiconj π (ϕ t) (ψ t)) :
    (μ.mapEquivariant π hπ hequiv).measure =
      μ.measure.map hπ.measurable.aemeasurable :=
  rfl

end Factor

end InvariantProbabilityMeasure

end HGAS.Dynamics
