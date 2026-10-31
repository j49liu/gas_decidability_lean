import HGAS.Dynamics.Recurrence
import HGAS.Clocks.RadicalClock
import Mathlib.Topology.Sequences

/-!
# Recurrence of compact-group translations

The intended source trajectories in the revised manuscript are continuous
observations of a torus translation. Their forward recurrence does not
require nonresonance or ergodic theory. Choose a convergent subsequence of
the integer-time orbit. The differences between its terms numbered `2n`
and `n` tend to the identity, while the corresponding time gaps are at
least `n`.
-/

namespace Stability

open Filter Topology HGAS

/-- Every translation orbit defined by an additive homomorphism into a
compact first-countable topological group returns arbitrarily late to its
initial point. Continuity of the homomorphism is not needed for recurrence. -/
theorem forwardRecurrentAt_compact_translation
    {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [CompactSpace G] [FirstCountableTopology G]
    (f : ℝ →+ G) (x : G) :
    ForwardRecurrentAt (fun t ↦ x + f t) 0 := by
  obtain ⟨y, φ, hφ, hlim⟩ :=
    CompactSpace.tendsto_subseq (fun n : ℕ ↦ f (n : ℝ))
  have hdouble : Tendsto (fun n : ℕ ↦ n + n) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ Nat.le_add_right n n) tendsto_id
  have hdiff : Tendsto
      (fun n : ℕ ↦ f (φ (n + n) : ℝ) - f (φ n : ℝ)) atTop (𝓝 (0 : G)) := by
    simpa only [sub_self, Function.comp_def] using (hlim.comp hdouble).sub hlim
  let τ : ℕ → ℝ := fun n ↦ (φ (n + n) : ℝ) - (φ n : ℝ)
  have hτ : Tendsto τ atTop atTop := by
    apply tendsto_atTop_mono (f := fun n : ℕ ↦ (n : ℝ)) ?_
      tendsto_natCast_atTop_atTop
    intro n
    have hgap : (n : ℝ) + (φ n : ℝ) ≤ (φ (n + n) : ℝ) := by
      exact_mod_cast hφ.add_le_nat n n
    dsimp [τ]
    linarith
  refine ⟨τ, hτ, ?_⟩
  have hreturn := (tendsto_const_nhds (x := x)).add hdiff
  simpa only [map_zero, add_zero, τ, map_sub] using hreturn

/-- In particular, every orbit of the finite torus translation used by the
detector is forward recurrent, for arbitrary real frequencies. -/
theorem forwardRecurrentAt_torusTranslation
    {d : Type*} [Finite d] (ω : d → ℝ) (phase : UnitAddTorus d) :
    ForwardRecurrentAt
      (fun t ↦ Clocks.RadicalClock.torusTranslationFlow ω t phase) 0 := by
  letI := Fintype.ofFinite d
  let f : ℝ →+ UnitAddTorus d :=
    { toFun := Clocks.RadicalClock.torusDisplacement ω
      map_zero' := by
        ext i
        simp [Clocks.RadicalClock.torusDisplacement]
      map_add' := by
        intro t u
        ext i
        simp [Clocks.RadicalClock.torusDisplacement, add_mul] }
  exact forwardRecurrentAt_compact_translation f phase

/-- A continuous observation of a torus translation is recurrent as well.
This is the topological step for the manuscript's intended source orbits. -/
theorem forwardRecurrentAt_observed_torusTranslation
    {d X : Type*} [Finite d] [TopologicalSpace X]
    (ω : d → ℝ) (phase : UnitAddTorus d)
    (observe : UnitAddTorus d → X) (hobserve : Continuous observe) :
    ForwardRecurrentAt
      (fun t ↦ observe (Clocks.RadicalClock.torusTranslationFlow ω t phase)) 0 :=
  (forwardRecurrentAt_torusTranslation ω phase).map hobserve

end Stability
