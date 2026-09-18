import HGAS.Dynamics.HomeomorphicFlow
import HGAS.Dynamics.Recurrence
import Mathlib.Topology.Maps.Basic

/-!
# Transport of forward recurrence

The project uses the sequential predicate `HGAS.ForwardRecurrentAt`: a
trajectory is recurrent at `t₀` when it returns to its state at `t₀` along
times tending to `+∞`.  This file records the elementary functoriality
properties needed whenever a trajectory is rewritten in another chart.

There are two logically different directions.

* Every continuous observation sends a recurrent trajectory to a recurrent
  observed trajectory.  This is `ForwardRecurrentAt.map`.
* If the observation is a topological embedding, observed recurrence also
  reflects back to the original trajectory.  No compactness, metrizability,
  or dynamical hypothesis is needed.

Consequently, equivariant continuous maps send recurrent flow orbits to
recurrent factor orbits, while an equivariant homeomorphism preserves
recurrence in both directions.  The final theorem specializes this to the
pullback-flow construction from `HGAS.Dynamics.HomeomorphicFlow`.

The embedding hypothesis in the reverse direction is important.  A finite
covering map is usually not globally injective, so recurrence of its image
does not by itself select the original sheet.  Lifting recurrence through a
nontrivial finite cover therefore remains a separate finite-fiber theorem.
-/

namespace HGAS

open Function Topology

/-- A topological embedding detects forward recurrence exactly.

The forward implication uses the neighborhood-convergence characterization
of an embedding; the reverse implication is ordinary continuity. -/
theorem forwardRecurrentAt_map_iff_of_isEmbedding
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {γ : ℝ → X} {t₀ : ℝ}
    {f : X → Y} (hf : IsEmbedding f) :
    ForwardRecurrentAt (fun t ↦ f (γ t)) t₀ ↔
      ForwardRecurrentAt γ t₀ := by
  constructor
  · rintro ⟨returnTime, htime, hreturn⟩
    refine ⟨returnTime, htime, ?_⟩
    apply (hf.tendsto_nhds_iff).2
    simpa only [Function.comp_apply] using hreturn
  · intro hrec
    exact hrec.map hf.continuous

/-- In particular, changing coordinates by a homeomorphism preserves
forward recurrence in both directions. -/
theorem forwardRecurrentAt_homeomorph_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (γ : ℝ → X) (t₀ : ℝ) :
    ForwardRecurrentAt (fun t ↦ e (γ t)) t₀ ↔
      ForwardRecurrentAt γ t₀ :=
  forwardRecurrentAt_map_iff_of_isEmbedding e.isEmbedding

namespace Dynamics

/-- An equivariant continuous map sends a recurrent orbit of the source
flow to a recurrent orbit of the target flow.

Surjectivity is irrelevant for this pointwise statement, so the theorem is
phrased using only the continuous equivariance data rather than the stronger
bundled `Flow.IsSemiconjugacy`. -/
theorem forwardRecurrentAt_orbit_of_equivariant
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ϕ : Flow ℝ X} {ψ : Flow ℝ Y}
    (π : X → Y) (hπ : Continuous π)
    (hequiv :
      ∀ t : ℝ, Function.Semiconj π (ϕ t) (ψ t))
    (x : X) (t₀ : ℝ)
    (hrec :
      ForwardRecurrentAt (fun t : ℝ ↦ ϕ t x) t₀) :
    ForwardRecurrentAt
      (fun t : ℝ ↦ ψ t (π x)) t₀ := by
  have hmapped :=
    hrec.map hπ
  convert hmapped using 1
  funext t
  exact (hequiv t x).symm

/-- Bundled semiconjugacy form of
`forwardRecurrentAt_orbit_of_equivariant`. -/
theorem forwardRecurrentAt_orbit_of_semiconjugacy
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ϕ : Flow ℝ X} {ψ : Flow ℝ Y}
    {π : X → Y} (hπ : Flow.IsSemiconjugacy π ϕ ψ)
    (x : X) (t₀ : ℝ)
    (hrec :
      ForwardRecurrentAt (fun t : ℝ ↦ ϕ t x) t₀) :
    ForwardRecurrentAt
      (fun t : ℝ ↦ ψ t (π x)) t₀ :=
  forwardRecurrentAt_orbit_of_equivariant
    π hπ.cont hπ.semiconj x t₀ hrec

/-- An equivariant homeomorphism preserves recurrence of corresponding
flow orbits exactly. -/
theorem forwardRecurrentAt_orbit_homeomorph_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ϕ : Flow ℝ X} {ψ : Flow ℝ Y}
    (e : X ≃ₜ Y)
    (hequiv :
      ∀ t : ℝ, Function.Semiconj e (ϕ t) (ψ t))
    (x : X) (t₀ : ℝ) :
    ForwardRecurrentAt
        (fun t : ℝ ↦ ψ t (e x)) t₀ ↔
      ForwardRecurrentAt
        (fun t : ℝ ↦ ϕ t x) t₀ := by
  have horbit :
      (fun t : ℝ ↦ ψ t (e x)) =
        fun t : ℝ ↦ e (ϕ t x) := by
    funext t
    exact (hequiv t x).symm
  rw [horbit]
  exact forwardRecurrentAt_homeomorph_iff
    e (fun t : ℝ ↦ ϕ t x) t₀

/-- Recurrence is unchanged when a flow is pulled back through a
homeomorphism.  This is the concrete coordinate-change interface used by
the project's conjugacy modules. -/
theorem forwardRecurrentAt_pullbackHomeomorph_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (ψ : Flow ℝ Y)
    (x : X) (t₀ : ℝ) :
    ForwardRecurrentAt
        (fun t : ℝ ↦ ψ t (e x)) t₀ ↔
      ForwardRecurrentAt
        (fun t : ℝ ↦ Flow.pullbackHomeomorph e ψ t x) t₀ :=
  forwardRecurrentAt_orbit_homeomorph_iff
    e (Flow.semiconj_pullbackHomeomorph e ψ) x t₀

end Dynamics

end HGAS
