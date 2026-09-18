import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Tactic

/-!
# Forward recurrence along a trajectory

For the reduction we repeatedly need the elementary pointwise notion that
a trajectory returns arbitrarily late to its state at a specified time.
The sequence formulation below is convenient for explicit ODE arguments
and does not presuppose that the trajectory has already been bundled as a
topological flow.
-/

namespace HGAS

open Filter Topology

/-- A trajectory is forward recurrent at time `t₀` if some sequence of
times escaping to `+∞` returns to the state occupied at `t₀`. -/
def ForwardRecurrentAt
    {X : Type*} [TopologicalSpace X]
    (γ : ℝ → X) (t₀ : ℝ) : Prop :=
  ∃ τ : ℕ → ℝ,
    Tendsto τ atTop atTop ∧
      Tendsto (fun n ↦ γ (τ n)) atTop (𝓝 (γ t₀))

/-- Forward recurrence is preserved by every continuous observation of
the state. -/
theorem ForwardRecurrentAt.map
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {γ : ℝ → X} {t₀ : ℝ}
    (hγ : ForwardRecurrentAt γ t₀)
    {f : X → Y} (hf : Continuous f) :
    ForwardRecurrentAt (fun t ↦ f (γ t)) t₀ := by
  obtain ⟨τ, hτ, hreturn⟩ := hγ
  exact ⟨τ, hτ, hf.continuousAt.tendsto.comp hreturn⟩

/-- A norm-escaping trajectory cannot return to any one of its finite
states.  This is the pointwise recurrence obstruction used after a
quantitative escape estimate. -/
theorem not_forwardRecurrentAt_of_norm_tendsto_atTop
    {E : Type*} [SeminormedAddGroup E]
    {γ : ℝ → E} {t₀ : ℝ}
    (hescape :
      Tendsto (fun t ↦ ‖γ t‖) atTop atTop) :
    ¬ ForwardRecurrentAt γ t₀ := by
  rintro ⟨τ, hτ, hreturn⟩
  have hreturnNorm :
      Tendsto (fun n ↦ ‖γ (τ n)‖)
        atTop (𝓝 ‖γ t₀‖) :=
    hreturn.norm
  have hescapeAlong :
      Tendsto (fun n ↦ ‖γ (τ n)‖)
        atTop atTop :=
    hescape.comp hτ
  have hlarge :
      ∀ᶠ n in atTop,
        ‖γ (τ n)‖ ≥ ‖γ t₀‖ + 1 :=
    hescapeAlong.eventually
      (eventually_ge_atTop (‖γ t₀‖ + 1))
  have hsmall :
      ∀ᶠ n in atTop,
        ‖γ (τ n)‖ < ‖γ t₀‖ + 1 :=
    hreturnNorm.eventually
      (Iio_mem_nhds (by linarith))
  have hfalse : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [hlarge, hsmall] with n hnLarge hnSmall
    exact (not_lt_of_ge hnLarge) hnSmall
  obtain ⟨_, hcontradiction⟩ :=
    Filter.Eventually.exists hfalse
  exact hcontradiction

end HGAS
