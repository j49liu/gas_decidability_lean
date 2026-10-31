import Stability.Simulation.AlternatingClock
import Stability.Simulation.ForcedCubicRelaxation

/-!
# Forcing mass on finite half-turn partitions

The half-turn estimates use actual integrals of absolute forcing. The
identities below partition those integrals exactly, including the case
of zero half-turns; omitted half-turns can only reduce the total mass.
-/

namespace Stability.Simulation

open Set MeasureTheory
open scoped BigOperators

/-- Absolute forcing is integrable on every half-turn in a supplied
continuous finite interval. -/
theorem intervalIntegrable_forcing_on_halfTurn
    {origin : ℝ} {forcing : ℝ → ℝ} {N n : ℕ}
    (hforcing : ContinuousOn forcing (Icc origin (halfTurnBoundary origin N)))
    (hn : n < N) :
    IntervalIntegrable (fun t ↦ |forcing t|) volume
      (halfTurnBoundary origin n) (halfTurnBoundary origin (n + 1)) :=
  (hforcing.abs.mono (halfTurn_Icc_subset origin hn)).intervalIntegrable_of_Icc
    ((halfTurnBoundary_strictMono origin).monotone (Nat.le_succ n))

/-- The masses of the first `N` half-turns sum exactly to the mass on their
union. No disjointness or mass bound is assumed. -/
theorem sum_halfTurn_forcingMass_eq
    {origin : ℝ} {forcing : ℝ → ℝ} (N : ℕ)
    (hforcing : ContinuousOn forcing (Icc origin (halfTurnBoundary origin N))) :
    ∑ n ∈ Finset.range N,
      forcingMass forcing (halfTurnBoundary origin n) (halfTurnBoundary origin (n + 1)) =
        forcingMass forcing origin (halfTurnBoundary origin N) := by
  simpa only [forcingMass, halfTurnBoundary_zero] using
    intervalIntegral.sum_integral_adjacent_intervals
      (a := halfTurnBoundary origin) (n := N)
      (fun n hn ↦ intervalIntegrable_forcing_on_halfTurn (n := n) hforcing hn)

/-- Every finite selection from the first `N` half-turns has mass at most
the total mass on the supplied interval. -/
theorem sum_selected_halfTurn_forcingMass_le
    {origin : ℝ} {forcing : ℝ → ℝ} (N : ℕ)
    (hforcing : ContinuousOn forcing (Icc origin (halfTurnBoundary origin N)))
    (indices : Finset ℕ) (hindices : indices ⊆ Finset.range N) :
    ∑ n ∈ indices,
      forcingMass forcing (halfTurnBoundary origin n) (halfTurnBoundary origin (n + 1)) ≤
        forcingMass forcing origin (halfTurnBoundary origin N) := by
  rw [← sum_halfTurn_forcingMass_eq N hforcing]
  exact Finset.sum_le_sum_of_subset_of_nonneg hindices fun n _ _ ↦
    forcingMass_nonneg forcing
      ((halfTurnBoundary_strictMono origin).monotone (Nat.le_succ n))

/-- A compute half-turn and its following copy half-turn have exactly the
forcing mass of the complete turn. -/
theorem compute_add_copy_forcingMass_eq
    {origin : ℝ} {forcing : ℝ → ℝ} {N j : ℕ}
    (hforcing : ContinuousOn forcing (Icc origin (halfTurnBoundary origin N)))
    (hj : 2 * j + 2 ≤ N) :
    forcingMass forcing (halfTurnBoundary origin (2 * j))
        (halfTurnBoundary origin (2 * j + 1)) +
      forcingMass forcing (halfTurnBoundary origin (2 * j + 1))
        (halfTurnBoundary origin (2 * j + 2)) =
      forcingMass forcing (halfTurnBoundary origin (2 * j))
        (halfTurnBoundary origin (2 * j + 2)) := by
  have hcompute := intervalIntegrable_forcing_on_halfTurn hforcing
    (show 2 * j < N by omega)
  have hcopy := intervalIntegrable_forcing_on_halfTurn hforcing
    (show 2 * j + 1 < N by omega)
  simpa only [forcingMass, Nat.add_assoc] using
    intervalIntegral.integral_add_adjacent_intervals hcompute hcopy

end Stability.Simulation
