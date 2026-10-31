import Stability.Simulation.FundedRealRun
import Stability.Simulation.RegisterLocalBranches
import Stability.Simulation.ClockedMonitorDynamics

/-!
# Robust tracking of funded register attempts

Natural registers and an unexhausted real countdown put the actual
transition map in a nonexpansive branch on a fixed norm neighborhood.
The funded discrete semantics discharge those conditions along a clean
attempt. Actual held-buffer motion and the forced compute/copy estimate
then bound tracking error by the accumulated clock and forcing allowances.
No simulation estimate is supplied as a hypothesis.
-/

namespace Stability.Simulation.RegisterTransition

open MachineCoordinate

noncomputable section

variable {k s : ℕ}

/-- Around a configuration with enough countdown for one instruction,
the literal transition equals a globally nonexpansive branch. -/
theorem exists_nonexpansive_branch_configuration (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (h c : ℝ)
    (configuration : RegisterMachine.Configuration k s) (hc : 1 ≤ c) :
    ∃ F : (MachineCoordinate k → ℝ) → MachineCoordinate k → ℝ,
      LipschitzWith 1 F ∧ ∀ x, ‖x - configurationState h c configuration‖ ≤ 1 / 8 →
        transitionMap program entry initial x = F x := by
  cases configuration with
  | mk label registers =>
      cases label with
      | none =>
          refine ⟨haltBranch (s := s), lipschitzWith_haltBranch, fun x hx ↦ ?_⟩
          apply transitionMap_eq_haltBranch program entry initial
          exact (norm_le_pi_norm (x - configurationState h c ⟨none, registers⟩) .label).trans hx
      | some q =>
          let center := configurationState h c ⟨some q, registers⟩
          refine ⟨frozenInstructionBranch (program q) center,
            lipschitzWith_frozenInstructionBranch _ _, fun x hx ↦ ?_⟩
          exact transitionMap_eq_frozen_of_near program entry initial q rfl
            (Or.inr hc) (fun i ↦ ⟨registers i, rfl⟩) hx

/-- Every pre-update point of a clean attempt funded for `N` steps has
the required local nonexpansive branch. The countdown may be real. -/
theorem exists_nonexpansive_branch_funded_iterate (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (h B : ℝ)
    (configuration : RegisterMachine.Configuration k s) (N : ℕ) (hB : (N : ℝ) ≤ B)
    {n : ℕ} (hn : n < N) :
    ∃ F : (MachineCoordinate k → ℝ) → MachineCoordinate k → ℝ,
      LipschitzWith 1 F ∧ ∀ x,
        ‖x - (transitionMap program entry initial)^[n] (configurationState h B configuration)‖ ≤
          1 / 8 → transitionMap program entry initial x = F x := by
  have hnReal : (n : ℝ) + 1 ≤ N := by exact_mod_cast Nat.succ_le_of_lt hn
  obtain ⟨countdown, hcountdown, hrun⟩ := iterate_funded_configuration
    program entry initial h B configuration n (by linarith)
  rw [hrun]
  exact exists_nonexpansive_branch_configuration program entry initial h countdown
    (RegisterMachine.run program n configuration) (by linarith)

end

end Stability.Simulation.RegisterTransition

namespace Stability.Simulation.ClockedMonitor

open Set MonitorCoordinate MeasureTheory
open scoped BigOperators

noncomputable section

variable {k s : ℕ}

/-- Actual accumulated allowances for the first `n` compute/copy turns. -/
def turnErrorBudget (clockAtOrigin origin : ℝ) (forcing : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (2 * n), halfTurnErrorAllowance (gain : ℝ) clockAtOrigin origin forcing i

theorem turnErrorBudget_succ (clockAtOrigin origin : ℝ) (forcing : ℝ → ℝ) (n : ℕ) :
    turnErrorBudget clockAtOrigin origin forcing (n + 1) =
      turnErrorBudget clockAtOrigin origin forcing n +
        halfTurnErrorAllowance (gain : ℝ) clockAtOrigin origin forcing (2 * n) +
        halfTurnErrorAllowance (gain : ℝ) clockAtOrigin origin forcing (2 * n + 1) := by
  unfold turnErrorBudget
  rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega, Finset.sum_range_succ,
    Finset.sum_range_succ]

theorem turnErrorBudget_monotone (clockAtOrigin origin : ℝ) (forcing : ℝ → ℝ) :
    Monotone (turnErrorBudget clockAtOrigin origin forcing) := by
  intro n m hnm
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
  intro i _ _
  have hmass := forcingMass_nonneg forcing
    ((halfTurnBoundary_strictMono origin).monotone (Nat.le_succ i))
  unfold halfTurnErrorAllowance
  have hclock := clockError_nonneg (clockAtOrigin + Real.pi / 2 + (i : ℝ) * Real.pi)
  positivity

/-- The explicit fixed-gain allowance is uniformly summable even when
the supplied segment extends beyond the turns being counted. -/
theorem turnErrorBudget_lt_fixedBudget {origin finish : ℝ} (clockAtOrigin : ℝ)
    {forcing : ℝ → ℝ} (N : ℕ)
    (hforcing : ContinuousOn forcing (Icc origin finish))
    (hend : halfTurnBoundary origin (2 * N) ≤ finish)
    (hmass : forcingMass forcing origin finish ≤ 1 / 256) :
    turnErrorBudget clockAtOrigin origin forcing N < 11 / 1024 := by
  have hstart : origin ≤ halfTurnBoundary origin (2 * N) := by
    simpa only [halfTurnBoundary_zero] using
      (halfTurnBoundary_strictMono origin).monotone (Nat.zero_le (2 * N))
  have hsum := sum_halfTurnErrorAllowance_lt_fixedBudget clockAtOrigin (2 * N)
    (hforcing.mono (Icc_subset_Icc le_rfl hend))
    ((forcingMass_le hforcing ⟨hstart, hend⟩).trans hmass)
  simpa only [turnErrorBudget, gain, Rat.cast_pow, Rat.cast_ofNat] using hsum

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

include hx hforcingA hforcingB hderiv hu0 hv0 hradius

/-- On an actual compute half-turn, the held buffer moves by at most
the joint forcing mass of the whole supplied solution segment. -/
theorem held_compute_motion_le_total_mass (j : ℕ)
    (hend : halfTurnBoundary origin (2 * j + 1) ≤ finish)
    {t : ℝ} (ht : t ∈ Icc (halfTurnBoundary origin (2 * j))
      (halfTurnBoundary origin (2 * j + 1))) :
    ‖bufferA (x t) - bufferA (x (halfTurnBoundary origin (2 * j)))‖ ≤
      forcingMass (jointForcingMagnitude forcingA forcingB) origin finish := by
  have hstart : origin ≤ halfTurnBoundary origin (2 * j) := by
    simpa only [halfTurnBoundary_zero] using
      (halfTurnBoundary_strictMono origin).monotone (Nat.zero_le (2 * j))
  have horder := (halfTurnBoundary_strictMono origin).monotone (Nat.le_succ (2 * j))
  have hsubset := Icc_subset_Icc hstart hend
  have hmagnitude : ContinuousOn (jointForcingMagnitude forcingA forcingB)
      (Icc origin finish) := hforcingA.norm.sup hforcingB.norm
  have hdu : ∀ r ∈ Ioo origin finish, HasDerivAt (fun z ↦ x z u) (-x r v) r := by
    intro r hr
    simpa [field, forcingVector] using (hasDerivAt_pi.mp (hderiv r hr)) u
  have hdv : ∀ r ∈ Ioo origin finish, HasDerivAt (fun z ↦ x z v) (x r u) r := by
    intro r hr
    simpa [field, forcingVector] using (hasDerivAt_pi.mp (hderiv r hr)) v
  have hheld : ∀ r ∈ Ioo (halfTurnBoundary origin (2 * j))
      (halfTurnBoundary origin (2 * j + 1)),
      HasDerivAt (fun z ↦ bufferA (x z)) (forcingA r) r := by
    intro r hr
    have hz := oppositeWeight_eq_zero_on_halfTurn
      ((continuous_apply u).comp_continuousOn hx) ((continuous_apply v).comp_continuousOn hx)
      hdu hdv hu0 hv0 hradius (2 * j) (hsubset (Ioo_subset_Icc_self hr))
      (Ioo_subset_Icc_self hr)
    have hz' : max (-x r u) 0 = 0 := by simpa [pow_mul] using hz
    apply hasDerivAt_pi.mpr
    intro i
    simpa [bufferA, field, forcingVector, hz'] using
      (hasDerivAt_pi.mp (hderiv r (Ioo_subset_Ioo hstart hend hr))) (.a i)
  have hmotion := norm_sub_le_forcingMass_of_hasDerivAt
    ((continuous_bufferA.comp_continuousOn hx).mono hsubset) (hforcingA.mono hsubset)
    (hmagnitude.mono hsubset) (fun _ _ ↦ le_max_left _ _) hheld ht
  apply hmotion.trans
  exact intervalIntegral.integral_mono_interval hstart horder hend
    (Filter.Eventually.of_forall (fun _ ↦ abs_nonneg _))
    (hmagnitude.abs.intervalIntegrable_of_Icc (hstart.trans (horder.trans hend)))

/-- Actual monitor solutions track an orbit through concrete local
nonexpansive branches. The hypothesis concerns only the transition map
on norm balls; the continuous update estimate is proved from the ODE. -/
theorem forced_tracking_error_le_of_local_branches
    (hamplitude : (1 / 2 : ℝ) < radius ^ 2) (N : ℕ)
    (hend : halfTurnBoundary origin (2 * N) ≤ finish)
    (center : MachineCoordinate k → ℝ) {δ : ℝ}
    (hinitial : ‖bufferA (x origin) - center‖ ≤ δ)
    (hmargin : δ + turnErrorBudget (x origin clock) origin
        (jointForcingMagnitude forcingA forcingB) N +
      forcingMass (jointForcingMagnitude forcingA forcingB) origin finish ≤ 1 / 8)
    (hbranches : ∀ n < N,
      ∃ F : (MachineCoordinate k → ℝ) → MachineCoordinate k → ℝ,
        LipschitzWith 1 F ∧ ∀ y,
          ‖y - (RegisterTransition.transitionMap program entry initial)^[n] center‖ ≤ 1 / 8 →
            RegisterTransition.transitionMap program entry initial y = F y) :
    ∀ n ≤ N,
      ‖bufferA (x (halfTurnBoundary origin (2 * n))) -
        (RegisterTransition.transitionMap program entry initial)^[n] center‖ ≤
      δ + turnErrorBudget (x origin clock) origin (jointForcingMagnitude forcingA forcingB) n := by
  intro n
  induction n with
  | zero =>
      intro _
      simpa [turnErrorBudget] using hinitial
  | succ n ih =>
      intro hn
      have hnN : n < N := by omega
      have hprevious := ih (by omega)
      obtain ⟨F, hF, hlocal⟩ := hbranches n hnN
      let cn := (RegisterTransition.transitionMap program entry initial)^[n] center
      have hcenter : RegisterTransition.transitionMap program entry initial cn = F cn :=
        hlocal cn (by simp [cn])
      have hendCompute : halfTurnBoundary origin (2 * n + 1) ≤ finish :=
        ((halfTurnBoundary_strictMono origin).monotone (by omega)).trans hend
      have hlocalPath : ∀ t ∈ Icc (halfTurnBoundary origin (2 * n))
          (halfTurnBoundary origin (2 * n + 1)),
          RegisterTransition.transitionMap program entry initial (bufferA (x t)) =
            F (bufferA (x t)) := by
        intro t ht
        apply hlocal
        have hmotion := held_compute_motion_le_total_mass program entry initial hx hforcingA
          hforcingB hderiv hu0 hv0 hradius n hendCompute ht
        have htriangle := norm_sub_le_norm_sub_add_norm_sub (bufferA (x t))
          (bufferA (x (halfTurnBoundary origin (2 * n)))) cn
        have hbudget := turnErrorBudget_monotone (x origin clock) origin
          (jointForcingMagnitude forcingA forcingB) (show n ≤ N by omega)
        change ‖bufferA (x (halfTurnBoundary origin (2 * n))) - cn‖ ≤ _ at hprevious
        change ‖bufferA (x t) - cn‖ ≤ _
        linarith
      have hupdate := forced_update_error_le program entry initial hx hforcingA hforcingB
        hderiv hu0 hv0 hradius hamplitude hF n
        (((halfTurnBoundary_strictMono origin).monotone (by omega)).trans hend) hlocalPath
      have hFerror := hF.norm_sub_le (bufferA (x (halfTurnBoundary origin (2 * n)))) cn
      simp only [NNReal.coe_one, one_mul] at hFerror
      have htriangle := norm_sub_le_norm_sub_add_norm_sub
        (bufferA (x (halfTurnBoundary origin (2 * n + 2))))
        (F (bufferA (x (halfTurnBoundary origin (2 * n))))) (F cn)
      rw [Function.iterate_succ_apply', show 2 * (n + 1) = 2 * n + 2 by omega,
        turnErrorBudget_succ]
      change ‖bufferA (x (halfTurnBoundary origin (2 * n + 2))) -
        RegisterTransition.transitionMap program entry initial cn‖ ≤ _
      rw [hcenter]
      change ‖bufferA (x (halfTurnBoundary origin (2 * n))) - cn‖ ≤ _ at hprevious
      linarith

/-- A clean attempt with real funding at least `N` satisfies the tracking
bound for its first `N` updates. All branch hypotheses are discharged
from the actual register semantics. -/
theorem forced_funded_tracking_error_le
    (hamplitude : (1 / 2 : ℝ) < radius ^ 2) (N : ℕ)
    (hend : halfTurnBoundary origin (2 * N) ≤ finish)
    (h B : ℝ) (configuration : RegisterMachine.Configuration k s) (hB : (N : ℝ) ≤ B)
    {δ : ℝ} (hinitial : ‖bufferA (x origin) -
      RegisterTransition.configurationState h B configuration‖ ≤ δ)
    (hmargin : δ + turnErrorBudget (x origin clock) origin
        (jointForcingMagnitude forcingA forcingB) N +
      forcingMass (jointForcingMagnitude forcingA forcingB) origin finish ≤ 1 / 8) :
    ∀ n ≤ N,
      ‖bufferA (x (halfTurnBoundary origin (2 * n))) -
        (RegisterTransition.transitionMap program entry initial)^[n]
          (RegisterTransition.configurationState h B configuration)‖ ≤
      δ + turnErrorBudget (x origin clock) origin (jointForcingMagnitude forcingA forcingB) n :=
  forced_tracking_error_le_of_local_branches program entry initial hx hforcingA hforcingB
    hderiv hu0 hv0 hradius hamplitude N hend _ hinitial hmargin
    (fun _ hn ↦ RegisterTransition.exists_nonexpansive_branch_funded_iterate
      program entry initial h B configuration N hB hn)

/-- With the fixed forcing budget, an initial error at most `1/16`
suffices for the entire funded attempt; the accumulated tracking error
is strictly below its initial allowance plus `11/1024`. -/
theorem forced_funded_tracking_error_lt_fixedBudget
    (hamplitude : (1 / 2 : ℝ) < radius ^ 2) (N : ℕ)
    (hend : halfTurnBoundary origin (2 * N) ≤ finish)
    (h B : ℝ) (configuration : RegisterMachine.Configuration k s) (hB : (N : ℝ) ≤ B)
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
  have htrack := forced_funded_tracking_error_le program entry initial hx hforcingA hforcingB
    hderiv hu0 hv0 hradius hamplitude N hend h B configuration hB hinitial (by linarith)
  intro n hn
  have hprefix := turnErrorBudget_monotone (x origin clock) origin
    (jointForcingMagnitude forcingA forcingB) hn
  exact (htrack n hn).trans_lt (by linarith)

end

end

end Stability.Simulation.ClockedMonitor
