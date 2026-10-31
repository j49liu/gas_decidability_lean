import Stability.Simulation.MonitorEvents

/-!
# Bounding actual monitor events under a small forcing budget

A clean attempt funded for its source halting time never visits the reset
label, before or after halt. Tracking therefore suppresses its actual
output throughout every later turn. Positive-output turns themselves
raise the budget until such an attempt has been funded.
-/

namespace Stability.Simulation.RegisterTransition

open MachineCoordinate

noncomputable section

variable {k s : ℕ}

theorem realLabel_one_le (label : Option (Fin s)) : (1 : ℝ) ≤ realLabel label := by
  cases label with
  | none => simp only [realLabel]; linarith [Nat.cast_nonneg (α := ℝ) s]
  | some q => simp only [realLabel]; linarith [Nat.cast_nonneg (α := ℝ) q.val]

/-- A funded halting reference always has an active or halting label,
never the reset label, including before the source computation halts. -/
theorem iterate_halting_label_one_le (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (h B : ℝ)
    (configuration : RegisterMachine.Configuration k s) (T : ℕ) (hB : (T : ℝ) ≤ B)
    (hhalt : (RegisterMachine.run program T configuration).label = none) (n : ℕ) :
    1 ≤ ((transitionMap program entry initial)^[n]
      (configurationState h B configuration)) label := by
  by_cases hn : n < T
  · have hnReal : (n : ℝ) ≤ T := by exact_mod_cast hn.le
    obtain ⟨countdown, _, hrun⟩ := iterate_funded_configuration program entry initial h B
      configuration n (hnReal.trans hB)
    rw [hrun]
    exact realLabel_one_le _
  · obtain ⟨countdown, hrun⟩ := iterate_funded_eq_halted_configuration program entry initial
      h B configuration T hB hhalt n (Nat.le_of_not_gt hn)
    rw [hrun]
    exact realLabel_one_le _

end

end Stability.Simulation.RegisterTransition

namespace Stability.Simulation.ClockedMonitor

open Set MonitorCoordinate MeasureTheory

noncomputable section

variable {k s : ℕ}

/-- A buffer label near any legal active or halting label closes the
actual output gate. -/
theorem output_eq_zero_of_label_near_ge_one (x : MonitorCoordinate k → ℝ)
    {label : ℝ} (hlabel : 1 ≤ label)
    (hnear : |x (.a MachineCoordinate.label) - label| ≤ 1 / 8) : output x = 0 := by
  apply le_antisymm (le_of_not_gt ?_) (output_nonneg _)
  intro hp
  have hsmall := ((output_pos_iff x).mp hp).2.2
  have hlower := (abs_le.mp hnear).1
  have hupper := (abs_lt.mp hsmall).2
  linarith

private theorem exists_event_with_large_previous_count
    (event : ℕ → Prop) [DecidablePred event] (N T : ℕ)
    (hcount : T < productiveCount event N) :
    ∃ j < N, event j ∧ T ≤ productiveCount event j := by
  induction N with
  | zero => simp at hcount
  | succ N ih =>
      by_cases hbefore : T < productiveCount event N
      · obtain ⟨j, hj, hevent, hprevious⟩ := ih hbefore
        exact ⟨j, Nat.lt_succ_of_lt hj, hevent, hprevious⟩
      · rw [productiveCount_succ] at hcount
        by_cases hevent : event N
        · simp only [hevent, if_true] at hcount
          exact ⟨N, Nat.lt_succ_self N, hevent, by omega⟩
        · simp only [hevent, if_false, add_zero] at hcount
          exact False.elim (hbefore hcount)

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

/-- Every turn of a sufficiently funded halting attempt has zero
actual output, including turns before its halt and between sample times. -/
theorem forced_output_eq_zero_on_funded_halting_turn
    (hamplitude : (1 / 2 : ℝ) < radius ^ 2) (j : ℕ)
    (hend : halfTurnBoundary origin (2 * j + 2) ≤ finish)
    (h B : ℝ) (configuration : RegisterMachine.Configuration k s) (T : ℕ) (hB : (T : ℝ) ≤ B)
    (hhalt : (RegisterMachine.run program T configuration).label = none)
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
    let center := (RegisterTransition.transitionMap program entry initial)^[j]
      (RegisterTransition.configurationState h B configuration)
    have hlabel : 1 ≤ center MachineCoordinate.label :=
      RegisterTransition.iterate_halting_label_one_le program entry initial h B
        configuration T hB hhalt j
    have hendCompute : halfTurnBoundary origin (2 * j + 1) ≤ finish :=
      ((halfTurnBoundary_strictMono origin).monotone (by omega)).trans hend
    have hmotion := held_compute_motion_le_total_mass program entry initial hx hforcingA
      hforcingB hderiv hu0 hv0 hradius j hendCompute ⟨ht.1, hcompute⟩
    have htriangle := norm_sub_le_norm_sub_add_norm_sub (bufferA (x t))
      (bufferA (x (halfTurnBoundary origin (2 * j)))) center
    have hnear : ‖bufferA (x t) - center‖ < 1 / 8 := by
      change ‖bufferA (x (halfTurnBoundary origin (2 * j))) - center‖ < _ at htrack
      linarith
    exact output_eq_zero_of_label_near_ge_one (x t) hlabel
      ((norm_le_pi_norm (bufferA (x t) - center) MachineCoordinate.label).trans hnear.le)
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

/-- A sufficiently funded actual output event suppresses all later
complete-turn output. The reset may start from arbitrary garbage buffers. -/
theorem forced_output_eq_zero_after_funded_event (i j : ℕ) (hij : i < j)
    (hend : halfTurnBoundary origin (2 * j + 2) ≤ finish)
    (hevent : outputEvent origin x i) (T : ℕ)
    (hhalt : (RegisterMachine.run program T ⟨some entry, initial⟩).label = none)
    (hgrant : (T : ℝ) ≤ max (sampledBudget origin x i) 0 + 1)
    (hmass : forcingMass (jointForcingMagnitude forcingA forcingB) origin finish ≤ 1 / 256)
    {t : ℝ} (ht : t ∈ Icc (halfTurnBoundary origin (2 * j))
      (halfTurnBoundary origin (2 * j + 2))) : output (x t) = 0 := by
  let newOrigin := halfTurnBoundary origin (2 * (i + 1))
  let B := max (sampledBudget origin x i) 0 + 1
  have hstart : origin ≤ halfTurnBoundary origin (2 * i) := by
    simpa only [halfTurnBoundary_zero] using
      (halfTurnBoundary_strictMono origin).monotone (Nat.zero_le (2 * i))
  have horder : halfTurnBoundary origin (2 * i) ≤ newOrigin :=
    (halfTurnBoundary_strictMono origin).monotone (by omega)
  have hnewEnd : newOrigin ≤ finish :=
    ((halfTurnBoundary_strictMono origin).monotone (by omega)).trans hend
  have hnewStart : origin ≤ newOrigin := hstart.trans horder
  have hturnEnd : halfTurnBoundary origin (2 * i + 2) ≤ finish := by
    simpa only [newOrigin, show 2 * (i + 1) = 2 * i + 2 by omega] using hnewEnd
  have hmagnitude : ContinuousOn (jointForcingMagnitude forcingA forcingB)
      (Icc origin finish) := hforcingA.norm.sup hforcingB.norm
  have hmassTurn : forcingMass (jointForcingMagnitude forcingA forcingB)
      (halfTurnBoundary origin (2 * i)) (halfTurnBoundary origin (2 * i + 2)) ≤ 1 / 16 := by
    have hsub := intervalIntegral.integral_mono_interval (μ := volume) hstart
      ((halfTurnBoundary_strictMono origin).monotone (by omega)) hturnEnd
      (Filter.Eventually.of_forall (fun _ ↦ abs_nonneg _))
      (hmagnitude.abs.intervalIntegrable_of_Icc (hnewStart.trans hnewEnd))
    change forcingMass _ _ _ ≤ forcingMass _ _ _ at hsub
    linarith
  have hreset := forced_reset_error_le program entry initial hx hforcingA hforcingB hderiv
    hu0 hv0 hradius i hturnEnd hmassTurn hevent
  have hallowance : turnErrorAllowance (x origin clock) origin
      (jointForcingMagnitude forcingA forcingB) i < 11 / 1024 := by
    have hbudget := turnErrorBudget_lt_fixedBudget (x origin clock) (i + 1)
      hmagnitude hnewEnd hmass
    have hprevious : 0 ≤ turnErrorBudget (x origin clock) origin
        (jointForcingMagnitude forcingA forcingB) i := by
      rw [← sum_turnErrorAllowance]
      exact Finset.sum_nonneg (fun n _ ↦ turnErrorAllowance_nonneg _ _ _ n)
    rw [turnErrorBudget_succ] at hbudget
    unfold turnErrorAllowance
    linarith
  have hclean : RegisterTransition.resetBranch entry initial
      (bufferA (x (halfTurnBoundary origin (2 * i)))) =
        RegisterTransition.configurationState B B ⟨some entry, initial⟩ := by
    funext coordinate
    cases coordinate <;> rfl
  have hnear : ‖bufferA (x newOrigin) -
      RegisterTransition.configurationState B B ⟨some entry, initial⟩‖ ≤ 11 / 1024 := by
    rw [hclean] at hreset
    change ‖bufferA (x newOrigin) - _‖ ≤ _ at hreset
    exact hreset.trans hallowance.le
  obtain ⟨m, hj⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hij)
  have hshiftStart : halfTurnBoundary newOrigin (2 * m) =
      halfTurnBoundary origin (2 * j) := by
    dsimp only [newOrigin]
    rw [halfTurnBoundary_add]
    congr 1
    omega
  have hshiftEnd : halfTurnBoundary newOrigin (2 * m + 2) =
      halfTurnBoundary origin (2 * j + 2) := by
    dsimp only [newOrigin]
    rw [halfTurnBoundary_add]
    congr 1
    omega
  have haligned := aligned_at_turn_boundary program entry initial hx hderiv hu0 hv0
    (i + 1) hnewEnd
  have hamp := amplitude_lower_of_outputEvent program entry initial hx hderiv hu0 hv0
    i hturnEnd hevent
  have hmassRest : forcingMass (jointForcingMagnitude forcingA forcingB) newOrigin finish ≤
      1 / 256 := by
    apply le_trans ?_ hmass
    exact intervalIntegral.integral_mono_interval hnewStart hnewEnd le_rfl
      (Filter.Eventually.of_forall (fun _ ↦ abs_nonneg _))
      (hmagnitude.abs.intervalIntegrable_of_Icc (hnewStart.trans hnewEnd))
  apply forced_output_eq_zero_on_funded_halting_turn program entry initial
    (hx.mono (Icc_subset_Icc hnewStart le_rfl))
    (hforcingA.mono (Icc_subset_Icc hnewStart le_rfl))
    (hforcingB.mono (Icc_subset_Icc hnewStart le_rfl))
    (fun r hr ↦ hderiv r (Ioo_subset_Ioo hnewStart le_rfl hr))
    haligned.1 haligned.2 hradius hamp m (by rwa [hshiftEnd]) B B ⟨some entry, initial⟩
    T hgrant hhalt (by norm_num : (11 / 1024 : ℝ) ≤ 1 / 16) hnear hmassRest
  simpa only [hshiftStart, hshiftEnd] using ht

/-- A source halt after `T` instructions bounds the number of actual
positive-output turns by `T + 1`, uniformly over all initial buffers.
Only the phase is aligned; the amplitude condition is derived from an
event if one exists. The forcing budget is its actual integral. -/
theorem eventCount_le_haltingTime_add_one (N T : ℕ)
    (hend : halfTurnBoundary origin (2 * N) ≤ finish)
    (hhalt : (RegisterMachine.run program T ⟨some entry, initial⟩).label = none)
    (hmass : forcingMass (jointForcingMagnitude forcingA forcingB) origin finish ≤ 1 / 256) :
    eventCount origin x N ≤ T + 1 := by
  classical
  by_contra! hcount
  change T + 1 < productiveCount (outputEvent origin x) N at hcount
  obtain ⟨j, hjN, heventj, hpreviousj⟩ :=
    exists_event_with_large_previous_count (outputEvent origin x) N (T + 1) hcount
  obtain ⟨i, hij, heventi, hpreviousi⟩ :=
    exists_event_with_large_previous_count (outputEvent origin x) j T (by omega)
  have hiN : i < N := hij.trans hjN
  have endFor (r : ℕ) (hr : r < N) : halfTurnBoundary origin (2 * r + 2) ≤ finish :=
    ((halfTurnBoundary_strictMono origin).monotone (by omega)).trans hend
  have hamp := amplitude_lower_of_outputEvent program entry initial hx hderiv hu0 hv0
    j (endFor j hjN) heventj
  have hstartN : origin ≤ halfTurnBoundary origin (2 * N) := by
    simpa only [halfTurnBoundary_zero] using
      (halfTurnBoundary_strictMono origin).monotone (Nat.zero_le (2 * N))
  have hmagnitude : ContinuousOn (jointForcingMagnitude forcingA forcingB)
      (Icc origin finish) := hforcingA.norm.sup hforcingB.norm
  have massFor (r : ℕ) (hr : r < N) :
      forcingMass (jointForcingMagnitude forcingA forcingB)
        (halfTurnBoundary origin (2 * r)) (halfTurnBoundary origin (2 * r + 2)) ≤ 1 / 16 := by
    have hstart : origin ≤ halfTurnBoundary origin (2 * r) := by
      simpa only [halfTurnBoundary_zero] using
        (halfTurnBoundary_strictMono origin).monotone (Nat.zero_le (2 * r))
    have hsub := intervalIntegral.integral_mono_interval (μ := volume) hstart
      ((halfTurnBoundary_strictMono origin).monotone (by omega)) (endFor r hr)
      (Filter.Eventually.of_forall (fun _ ↦ abs_nonneg _))
      (hmagnitude.abs.intervalIntegrable_of_Icc (hstartN.trans hend))
    change forcingMass _ _ _ ≤ forcingMass _ _ _ at hsub
    linarith
  have hiEnd : halfTurnBoundary origin (2 * i) ≤ finish :=
    ((halfTurnBoundary_strictMono origin).monotone (by omega)).trans hend
  have herror := turnErrorBudget_lt_fixedBudget (x origin clock) i hmagnitude hiEnd hmass
  have hgrant := restartBudget_gt_of_productiveCount_ge
    (sampledBudget origin x)
    (turnErrorAllowance (x origin clock) origin (jointForcingMagnitude forcingA forcingB))
    (outputEvent origin x) i T
    (fun r _ ↦ turnErrorAllowance_nonneg _ _ _ r)
    (fun r hr ↦ sampledBudget_nondecrease program entry initial hx hforcingA hforcingB
      hderiv hu0 hv0 hradius hamp r (endFor r (hr.trans hiN)))
    (fun r hr hp ↦ sampledBudget_reset_of_outputEvent program entry initial hx hforcingA hforcingB
      hderiv hu0 hv0 hradius r (endFor r (hr.trans hiN)) (massFor r (hr.trans hiN)) hp)
    hpreviousi (by rw [sum_turnErrorAllowance]; linarith)
  obtain ⟨t, ht, hp⟩ := heventj
  have hz := forced_output_eq_zero_after_funded_event program entry initial hx hforcingA hforcingB
    hderiv hu0 hv0 hradius i j hij (endFor j hjN) heventi T hhalt hgrant.le hmass ht
  rw [hz] at hp
  exact lt_irrefl _ hp

end

end

end Stability.Simulation.ClockedMonitor
