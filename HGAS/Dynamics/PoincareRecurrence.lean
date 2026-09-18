import HGAS.Dynamics.InvariantProbability
import HGAS.Dynamics.Recurrence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.Tactic

/-!
# Poincaré recurrence for continuous real flows

Mathlib proves topological Poincaré recurrence for a conservative discrete
map: almost every point returns infinitely often to every neighborhood.
This file adapts that theorem to this project's sequential notion
`ForwardRecurrentAt` for a continuous real flow.

The final observation principle is especially useful:

> if one continuous finite-dimensional observation of every orbit has norm
> tending to infinity, then the flow admits no invariant probability.

This is the measure-theoretic last step in nonreal-Bloch escape and is
independent of theta functions.
-/

noncomputable section

open Filter Function MeasureTheory Set Topology

namespace HGAS.Dynamics

variable {K : Type*} [PseudoMetricSpace K]

/-- Topological recurrence for the time-one map produces an explicit
sequence of real return times for the continuous flow. -/
theorem forwardRecurrentAt_zero_of_frequently_iterate_mem_nhds
    (ϕ : Flow ℝ K) (x : K)
    (hx :
      ∀ s ∈ 𝓝 x,
        ∃ᶠ n in atTop, (ϕ 1)^[n] x ∈ s) :
    HGAS.ForwardRecurrentAt
      (fun t : ℝ ↦ ϕ t x) 0 := by
  have hiterate :
      ∀ n : ℕ,
        (ϕ 1)^[n] x = ϕ (n : ℝ) x := by
    intro n
    induction n with
    | zero =>
        simp only [iterate_zero_apply, Nat.cast_zero,
          Flow.map_zero_apply]
    | succ n ih =>
        rw [Function.iterate_succ_apply', ih,
          ← ϕ.map_add]
        norm_num [Nat.cast_succ, add_comm]
  have hexists :
      ∀ k : ℕ, ∃ n : ℕ,
        k ≤ n ∧
          dist ((ϕ 1)^[n] x) x <
            1 / ((k : ℝ) + 1) := by
    intro k
    have hradius :
        0 < 1 / ((k : ℝ) + 1) := by
      positivity
    have hfrequent :=
      hx (Metric.ball x (1 / ((k : ℝ) + 1)))
        (Metric.ball_mem_nhds x hradius)
    obtain ⟨n, hnBall, hkn⟩ :=
      (hfrequent.and_eventually
        (eventually_ge_atTop k)).exists
    exact ⟨n, hkn, Metric.mem_ball.mp hnBall⟩
  choose returnIndex hindex hdist using hexists
  let returnTime : ℕ → ℝ :=
    fun k ↦ (returnIndex k : ℝ)
  have hreturnIndex :
      Tendsto returnIndex atTop atTop := by
    apply Filter.tendsto_atTop_mono' atTop
      (Eventually.of_forall hindex)
    exact tendsto_id
  have hreturnTime :
      Tendsto returnTime atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp
      hreturnIndex
  have hdistZero :
      Tendsto
        (fun k ↦
          dist (ϕ (returnTime k) x) x)
        atTop (𝓝 0) := by
    apply squeeze_zero
      (fun _ ↦ dist_nonneg)
      (fun k ↦ ?_)
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto
          (fun k : ℕ ↦ 1 / ((k : ℝ) + 1))
          atTop (𝓝 0))
    dsimp only [returnTime]
    rw [← hiterate]
    exact (hdist k).le
  refine ⟨returnTime, hreturnTime, ?_⟩
  simpa only [Flow.map_zero_apply] using
    (tendsto_iff_dist_tendsto_zero.mpr hdistZero)

variable [MeasurableSpace K] [BorelSpace K]
  [SecondCountableTopology K]

namespace InvariantProbabilityMeasure

variable {ϕ : Flow ℝ K}

/-- Almost every point of an invariant probability is forward recurrent
for its continuous real-flow orbit. -/
theorem ae_forwardRecurrentAt_zero
    (μ : InvariantProbabilityMeasure ϕ) :
    ∀ᵐ x ∂(μ.measure : Measure K),
      HGAS.ForwardRecurrentAt
        (fun t : ℝ ↦ ϕ t x) 0 := by
  have hpreserving :
      MeasurePreserving (ϕ 1)
        (μ.measure : Measure K)
        (μ.measure : Measure K) :=
    ⟨(ϕ.continuous_toFun 1).measurable,
      μ.map_time_toMeasure 1⟩
  exact
    hpreserving.conservative
      |>.ae_frequently_mem_of_mem_nhds
      |>.mono
        (fun x hx ↦
          forwardRecurrentAt_zero_of_frequently_iterate_mem_nhds
            ϕ x hx)

/-- An invariant probability has at least one forward recurrent point. -/
theorem exists_forwardRecurrentAt_zero
    (μ : InvariantProbabilityMeasure ϕ) :
    ∃ x : K,
      HGAS.ForwardRecurrentAt
        (fun t : ℝ ↦ ϕ t x) 0 :=
  Filter.Eventually.exists μ.ae_forwardRecurrentAt_zero

/-- Recurrence persists under any continuous observation of the state. -/
theorem exists_forwardRecurrentAt_observation
    {E : Type*} [TopologicalSpace E]
    (μ : InvariantProbabilityMeasure ϕ)
    (observation : K → E)
    (hobservation : Continuous observation) :
    ∃ x : K,
      HGAS.ForwardRecurrentAt
        (fun t : ℝ ↦ observation (ϕ t x)) 0 := by
  obtain ⟨x, hx⟩ := μ.exists_forwardRecurrentAt_zero
  exact ⟨x, hx.map hobservation⟩

end InvariantProbabilityMeasure

/-- If a continuous seminormed observation of every orbit escapes to
infinity, the flow has no invariant probability measure. -/
theorem no_invariantProbability_of_observation_norm_tendsto_atTop
    {E : Type*} [SeminormedAddGroup E]
    (ϕ : Flow ℝ K)
    (observation : K → E)
    (hobservation : Continuous observation)
    (hescape :
      ∀ x : K,
        Tendsto
          (fun t : ℝ ↦ ‖observation (ϕ t x)‖)
          atTop atTop) :
    ¬ Nonempty (InvariantProbabilityMeasure ϕ) := by
  rintro ⟨μ⟩
  obtain ⟨x, hx⟩ :=
    μ.exists_forwardRecurrentAt_observation
      observation hobservation
  exact
    (HGAS.not_forwardRecurrentAt_of_norm_tendsto_atTop
      (hescape x)) hx

end HGAS.Dynamics
