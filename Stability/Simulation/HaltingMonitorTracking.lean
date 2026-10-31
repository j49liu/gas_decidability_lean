import Stability.Simulation.FundedMonitorTracking

/-!
# Tracking a funded halting attempt beyond its halt

Once the exact real reference reaches its halting configuration, it is
fixed and retains its nonexpansive halting neighborhood forever. The
actual monitor therefore keeps tracking that reference for every supplied
number of turns, with the same summable-error bound.
-/

namespace Stability.Simulation.RegisterTransition

open MachineCoordinate

noncomputable section

variable {k s : ℕ}

/-- Sufficient funding reaches a halting configuration that remains the
exact reference for all later real-map iterates. -/
theorem iterate_funded_eq_halted_configuration (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (h B : ℝ)
    (configuration : RegisterMachine.Configuration k s) (T : ℕ) (hB : (T : ℝ) ≤ B)
    (hhalt : (RegisterMachine.run program T configuration).label = none)
    (n : ℕ) (hn : T ≤ n) :
    ∃ countdown : ℝ,
      (transitionMap program entry initial)^[n] (configurationState h B configuration) =
        configurationState h countdown (RegisterMachine.run program T configuration) := by
  obtain ⟨countdown, _, hrun⟩ :=
    iterate_funded_configuration program entry initial h B configuration T hB
  have hfixed : Function.IsFixedPt (transitionMap program entry initial)
      (configurationState h countdown (RegisterMachine.run program T configuration)) := by
    generalize RegisterMachine.run program T configuration = current at hhalt ⊢
    cases current with
    | mk label registers =>
        change label = none at hhalt
        subst label
        exact transitionMap_halted program entry initial h countdown registers
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  refine ⟨countdown, ?_⟩
  rw [Nat.add_comm T m, Function.iterate_add_apply, hrun]
  exact hfixed.iterate m

/-- A clean funded halting attempt has the required local branch at
every exact iterate, including arbitrarily long after its halt. -/
theorem exists_nonexpansive_branch_halting_iterate (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (h B : ℝ)
    (configuration : RegisterMachine.Configuration k s) (T : ℕ) (hB : (T : ℝ) ≤ B)
    (hhalt : (RegisterMachine.run program T configuration).label = none) (n : ℕ) :
    ∃ F : (MachineCoordinate k → ℝ) → MachineCoordinate k → ℝ,
      LipschitzWith 1 F ∧ ∀ x,
        ‖x - (transitionMap program entry initial)^[n] (configurationState h B configuration)‖ ≤
          1 / 8 → transitionMap program entry initial x = F x := by
  by_cases hn : n < T
  · exact exists_nonexpansive_branch_funded_iterate program entry initial h B
      configuration T hB hn
  · obtain ⟨countdown, hrun⟩ := iterate_funded_eq_halted_configuration program entry initial
      h B configuration T hB hhalt n (Nat.le_of_not_gt hn)
    rw [hrun]
    refine ⟨haltBranch (s := s), lipschitzWith_haltBranch, fun x hx ↦ ?_⟩
    apply transitionMap_eq_haltBranch program entry initial
    have hcoordBase := norm_le_pi_norm
      (x - configurationState h countdown (RegisterMachine.run program T configuration)) .label
    have hcoord := hcoordBase.trans hx
    simpa only [Pi.sub_apply, configurationState, registerState, hhalt, realLabel,
      Real.norm_eq_abs] using hcoord

end

end Stability.Simulation.RegisterTransition

namespace Stability.Simulation.ClockedMonitor

open Set MonitorCoordinate

noncomputable section

variable {k s : ℕ}

section

variable (program : RegisterMachine.Program k s) (entry : Fin s) (initial : Fin k → ℕ)
  {origin finish radius : ℝ} {x : ℝ → MonitorCoordinate k → ℝ}
  {forcingA forcingB : ℝ → MachineCoordinate k → ℝ}
  (hx : ContinuousOn x (Icc origin finish))
  (hforcingA : ContinuousOn forcingA (Icc origin finish))
  (hforcingB : ContinuousOn forcingB (Icc origin finish))
  (hderiv : ∀ t ∈ Ioo origin finish, HasDerivAt x
    (field program entry initial (x t) + forcingVector (forcingA t) (forcingB t)) t)
  (hu0 : x origin u = 0) (hv0 : x origin v = -radius) (hradius : 0 ≤ radius)
  (hamplitude : (1 / 2 : ℝ) < radius ^ 2)

include hx hforcingA hforcingB hderiv hu0 hv0 hradius hamplitude

/-- A clean attempt funded for its source halting time keeps tracking
forever: only the supplied segment length bounds `N`, not its funding. -/
theorem forced_halting_tracking_error_lt_fixedBudget (N : ℕ)
    (hend : halfTurnBoundary origin (2 * N) ≤ finish)
    (h B : ℝ) (configuration : RegisterMachine.Configuration k s) (T : ℕ) (hB : (T : ℝ) ≤ B)
    (hhalt : (RegisterMachine.run program T configuration).label = none)
    {δ : ℝ} (hδ : δ ≤ 1 / 16) (hinitial : ‖bufferA (x origin) -
      RegisterTransition.configurationState h B configuration‖ ≤ δ)
    (hmass : forcingMass (jointForcingMagnitude forcingA forcingB) origin finish ≤ 1 / 256) :
    ∀ n ≤ N,
      ‖bufferA (x (halfTurnBoundary origin (2 * n))) -
        (RegisterTransition.transitionMap program entry initial)^[n]
          (RegisterTransition.configurationState h B configuration)‖ < δ + 11 / 1024 := by
  have hmagnitude : ContinuousOn (jointForcingMagnitude forcingA forcingB)
      (Icc origin finish) := hforcingA.norm.sup hforcingB.norm
  have htotal := turnErrorBudget_lt_fixedBudget (x origin clock) N hmagnitude hend hmass
  have htrack := forced_tracking_error_le_of_local_branches program entry initial hx
    hforcingA hforcingB hderiv hu0 hv0 hradius hamplitude N hend
    (RegisterTransition.configurationState h B configuration) hinitial (by linarith)
    (fun n _ ↦ RegisterTransition.exists_nonexpansive_branch_halting_iterate
      program entry initial h B configuration T hB hhalt n)
  intro n hn
  have hprefix := turnErrorBudget_monotone (x origin clock) origin
    (jointForcingMagnitude forcingA forcingB) hn
  exact (htrack n hn).trans_lt (by linarith)

/-- Every complete turn after a sufficiently funded source halt has
identically zero actual monitor output, including between its sample
times. Compute phases stay near the halting label; copy phases close
the output gate regardless of their buffer contents. -/
theorem forced_output_eq_zero_on_halting_turn (j : ℕ)
    (hend : halfTurnBoundary origin (2 * j + 2) ≤ finish)
    (h B : ℝ) (configuration : RegisterMachine.Configuration k s) (T : ℕ) (hB : (T : ℝ) ≤ B)
    (hhalt : (RegisterMachine.run program T configuration).label = none) (hTj : T ≤ j)
    {δ : ℝ} (hδ : δ ≤ 1 / 16) (hinitial : ‖bufferA (x origin) -
      RegisterTransition.configurationState h B configuration‖ ≤ δ)
    (hmass : forcingMass (jointForcingMagnitude forcingA forcingB) origin finish ≤ 1 / 256)
    {t : ℝ} (ht : t ∈ Icc (halfTurnBoundary origin (2 * j))
      (halfTurnBoundary origin (2 * j + 2))) : output (x t) = 0 := by
  have hstart : origin ≤ halfTurnBoundary origin (2 * j) := by
    simpa only [halfTurnBoundary_zero] using
      (halfTurnBoundary_strictMono origin).monotone (Nat.zero_le (2 * j))
  have htime : t ∈ Icc origin finish := ⟨hstart.trans ht.1, ht.2.trans hend⟩
  by_cases hcompute : t ≤ halfTurnBoundary origin (2 * j + 1)
  · have hend' : halfTurnBoundary origin (2 * (j + 1)) ≤ finish := by
      simpa only [show 2 * (j + 1) = 2 * j + 2 by omega] using hend
    have htrack := forced_halting_tracking_error_lt_fixedBudget program entry initial hx
      hforcingA hforcingB hderiv hu0 hv0 hradius hamplitude (j + 1) hend'
      h B configuration T hB hhalt hδ hinitial hmass j (Nat.le_succ j)
    obtain ⟨countdown, hreference⟩ := RegisterTransition.iterate_funded_eq_halted_configuration
      program entry initial h B configuration T hB hhalt j hTj
    rw [hreference] at htrack
    have hendCompute : halfTurnBoundary origin (2 * j + 1) ≤ finish :=
      ((halfTurnBoundary_strictMono origin).monotone (by omega)).trans hend
    have hmotion := held_compute_motion_le_total_mass program entry initial hx hforcingA
      hforcingB hderiv hu0 hv0 hradius j hendCompute ⟨ht.1, hcompute⟩
    let center := RegisterTransition.configurationState h countdown
      (RegisterMachine.run program T configuration)
    have htriangle := norm_sub_le_norm_sub_add_norm_sub (bufferA (x t))
      (bufferA (x (halfTurnBoundary origin (2 * j)))) center
    have hnear : ‖bufferA (x t) - center‖ < 1 / 8 := by
      change ‖bufferA (x (halfTurnBoundary origin (2 * j))) - center‖ < _ at htrack
      linarith
    have hcoord := (norm_le_pi_norm (bufferA (x t) - center) MachineCoordinate.label).trans_lt hnear
    have hlabel : |x t (.a MachineCoordinate.label) - ((s : ℝ) + 1)| < 1 / 8 := by
      simpa only [Pi.sub_apply, center, bufferA, RegisterTransition.configurationState,
        RegisterTransition.registerState, hhalt, RegisterTransition.realLabel,
        Real.norm_eq_abs] using hcoord
    apply le_antisymm (le_of_not_gt ?_) (output_nonneg _)
    intro hpositive
    have hsmall := ((output_pos_iff (x t)).mp hpositive).2.2
    have hlower := (abs_lt.mp hlabel).1
    have hupper := (abs_lt.mp hsmall).2
    linarith [Nat.cast_nonneg (α := ℝ) s]
  · have hdu : ∀ r ∈ Ioo origin finish, HasDerivAt (fun z ↦ x z u) (-x r v) r := by
      intro r hr
      simpa [field, forcingVector] using (hasDerivAt_pi.mp (hderiv r hr)) u
    have hdv : ∀ r ∈ Ioo origin finish, HasDerivAt (fun z ↦ x z v) (x r u) r := by
      intro r hr
      simpa [field, forcingVector] using (hasDerivAt_pi.mp (hderiv r hr)) v
    have hcopy : t ∈ Icc (halfTurnBoundary origin (2 * j + 1))
        (halfTurnBoundary origin ((2 * j + 1) + 1)) :=
      ⟨(lt_of_not_ge hcompute).le, by simpa only [Nat.add_assoc] using ht.2⟩
    have hz := oppositeWeight_eq_zero_on_halfTurn
      ((continuous_apply u).comp_continuousOn hx) ((continuous_apply v).comp_continuousOn hx)
      hdu hdv hu0 hv0 hradius (2 * j + 1) htime hcopy
    have hz' : max (x t u) 0 = 0 := by simpa [pow_add, pow_mul] using hz
    simp [output, hz']

end

end

end Stability.Simulation.ClockedMonitor
