import Stability.Simulation.MonitorEventBound
import Stability.Simulation.OscillatorPhase

/-!
# Uniform integrals of the actual monitor output

The literal output lies between zero and two. Only positive-output turns
contribute to its integral. The actual event-count theorem therefore gives
a bound independent of the initial buffers and of the observation horizon.
-/

namespace Stability.Simulation.ClockedMonitor

open Set MonitorCoordinate MeasureTheory
open scoped BigOperators

noncomputable section

variable {k s : ℕ}

theorem continuous_output : Continuous (output (k := k)) := by
  unfold output amplitudeCutoff labelGate unitClamp
  fun_prop

/-- The amplitude cutoff gives a universal bound on the actual output. -/
theorem output_le_two (x : MonitorCoordinate k → ℝ) : output x ≤ 2 := by
  by_cases hp : 0 < output x
  · have hfeatures := (output_pos_iff x).mp hp
    have hu : x u ≤ 2 := by
      apply (sq_le_sq₀ hfeatures.2.1.le (by norm_num : (0 : ℝ) ≤ 2)).mp
      nlinarith [sq_nonneg (x v)]
    have hweight : 0 ≤ max (x u) 0 := le_max_right _ _
    calc
      output x ≤ amplitudeCutoff (x u ^ 2 + x v ^ 2) * max (x u) 0 := by
        exact mul_le_of_le_one_right
          (mul_nonneg (amplitudeCutoff_nonneg _) hweight) (labelGate_le_one _)
      _ ≤ max (x u) 0 := mul_le_of_le_one_left hweight (amplitudeCutoff_le_one _)
      _ ≤ 2 := max_le hu (by norm_num)
  · exact (le_of_not_gt hp).trans (by norm_num)

/-- The output integral is bounded by twice the interval length. -/
theorem integral_output_le_length {a b : ℝ} {x : ℝ → MonitorCoordinate k → ℝ}
    (hab : a ≤ b) (hx : ContinuousOn x (Icc a b)) :
    (∫ t in a..b, output (x t)) ≤ 2 * (b - a) := by
  have hbound := intervalIntegral.integral_mono_on (μ := volume) hab
    ((continuous_output.comp_continuousOn hx).intervalIntegrable_of_Icc hab)
    (intervalIntegrable_const (c := (2 : ℝ))) (fun t _ ↦ output_le_two (x t))
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using hbound

open Classical in
private theorem integral_output_on_turn_le_indicator
    {origin finish : ℝ} {x : ℝ → MonitorCoordinate k → ℝ}
    (hx : ContinuousOn x (Icc origin finish)) (j : ℕ)
    (hend : halfTurnBoundary origin (2 * j + 2) ≤ finish) :
    (∫ t in halfTurnBoundary origin (2 * j)..halfTurnBoundary origin (2 * j + 2),
      output (x t)) ≤ if outputEvent origin x j then 4 * Real.pi else 0 := by
  classical
  have hstart : origin ≤ halfTurnBoundary origin (2 * j) := by
    simpa only [halfTurnBoundary_zero] using
      (halfTurnBoundary_strictMono origin).monotone (Nat.zero_le (2 * j))
  have horder := (halfTurnBoundary_strictMono origin).monotone
    (show 2 * j ≤ 2 * j + 2 by omega)
  by_cases hevent : outputEvent origin x j
  · rw [if_pos hevent]
    have h := integral_output_le_length horder (hx.mono (Icc_subset_Icc hstart hend))
    have hlength : halfTurnBoundary origin (2 * j + 2) -
        halfTurnBoundary origin (2 * j) = 2 * Real.pi := by
      simp only [halfTurnBoundary, Nat.cast_add, Nat.cast_ofNat]
      ring
    rw [hlength] at h
    linarith
  · rw [if_neg hevent]
    have hz : ∀ t ∈ Icc (halfTurnBoundary origin (2 * j))
        (halfTurnBoundary origin (2 * j + 2)), output (x t) = 0 := by
      intro t ht
      exact le_antisymm (le_of_not_gt (fun hp ↦ hevent ⟨t, ht, hp⟩)) (output_nonneg _)
    have heq : (∫ t in halfTurnBoundary origin (2 * j)..halfTurnBoundary origin (2 * j + 2),
        output (x t)) = ∫ _ in halfTurnBoundary origin (2 * j)..
          halfTurnBoundary origin (2 * j + 2), (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      simpa only [uIcc_of_le horder] using hz
    rw [heq, intervalIntegral.integral_zero]

/-- The integral over complete turns is controlled by their actual event
count, without a simulation or halting premise. -/
theorem integral_output_le_eventCount
    {origin finish : ℝ} {x : ℝ → MonitorCoordinate k → ℝ}
    (hx : ContinuousOn x (Icc origin finish)) (N : ℕ)
    (hend : halfTurnBoundary origin (2 * N) ≤ finish) :
    (∫ t in origin..halfTurnBoundary origin (2 * N), output (x t)) ≤
      4 * Real.pi * (eventCount origin x N : ℝ) := by
  classical
  have endFor (j : ℕ) (hj : j < N) : halfTurnBoundary origin (2 * j + 2) ≤ finish :=
    ((halfTurnBoundary_strictMono origin).monotone (by omega)).trans hend
  have hsum := Finset.sum_le_sum (s := Finset.range N) (fun j hj ↦
    integral_output_on_turn_le_indicator hx j (endFor j (Finset.mem_range.mp hj)))
  have htel := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (a := fun j ↦ halfTurnBoundary origin (2 * j)) (n := N)
    (f := fun t ↦ output (x t)) (fun j hj ↦ by
      have hstart : origin ≤ halfTurnBoundary origin (2 * j) := by
        simpa only [halfTurnBoundary_zero] using
          (halfTurnBoundary_strictMono origin).monotone (Nat.zero_le (2 * j))
      have horder := (halfTurnBoundary_strictMono origin).monotone
        (show 2 * j ≤ 2 * (j + 1) by omega)
      apply ((continuous_output.comp_continuousOn hx).mono
        (Icc_subset_Icc hstart ?_)).intervalIntegrable_of_Icc horder
      simpa only [show 2 * (j + 1) = 2 * j + 2 by omega] using endFor j hj)
  simp only [show 2 * 0 = 0 by omega, halfTurnBoundary_zero,
    show ∀ j : ℕ, 2 * (j + 1) = 2 * j + 2 by omega] at htel
  rw [htel] at hsum
  have hcount : (∑ j ∈ Finset.range N, if outputEvent origin x j then 4 * Real.pi else 0) =
      4 * Real.pi * (eventCount origin x N : ℝ) := by
    rw [← Finset.sum_filter]
    simp [eventCount, productiveCount, mul_comm]
  simpa only [hcount] using hsum

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

/-- The actual aligned output integral is uniformly bounded when the
source halts, independently of all initial machine-buffer values. -/
theorem integral_output_complete_turns_le (N T : ℕ)
    (hend : halfTurnBoundary origin (2 * N) ≤ finish)
    (hhalt : (RegisterMachine.run program T ⟨some entry, initial⟩).label = none)
    (hmass : forcingMass (jointForcingMagnitude forcingA forcingB) origin finish ≤ 1 / 256) :
    (∫ t in origin..halfTurnBoundary origin (2 * N), output (x t)) ≤
      4 * Real.pi * ((T : ℝ) + 1) := by
  have hcount := eventCount_le_haltingTime_add_one program entry initial hx hforcingA hforcingB
    hderiv hu0 hv0 hradius N T hend hhalt hmass
  have hreal : (eventCount origin x N : ℝ) ≤ (T : ℝ) + 1 := by exact_mod_cast hcount
  exact (integral_output_le_eventCount hx N hend).trans
    (mul_le_mul_of_nonneg_left hreal (by positivity))

end

/-- The actual output integral is uniformly bounded on every finite
solution segment, with arbitrary initial phase, amplitude, and buffers.
The two endpoint pieces cost at most one period each. -/
theorem integral_output_le_halting_bound (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ)
    {a b : ℝ} {x : ℝ → MonitorCoordinate k → ℝ}
    {forcingA forcingB : ℝ → MachineCoordinate k → ℝ} (hab : a ≤ b)
    (hx : ContinuousOn x (Icc a b))
    (hforcingA : ContinuousOn forcingA (Icc a b))
    (hforcingB : ContinuousOn forcingB (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt x
      (field program entry initial (x t) + forcingVector (forcingA t) (forcingB t)) t)
    (T : ℕ) (hhalt : (RegisterMachine.run program T ⟨some entry, initial⟩).label = none)
    (hmass : forcingMass (jointForcingMagnitude forcingA forcingB) a b ≤ 1 / 256) :
    (∫ t in a..b, output (x t)) ≤ 4 * Real.pi * ((T : ℝ) + 3) := by
  by_cases hlong : a + 2 * Real.pi ≤ b
  · obtain ⟨τ, hτ, radius, hradius, _, huτ, hvτ⟩ := exists_aligned_oscillator_phase hlong
      ((continuous_apply u).comp_continuousOn hx) ((continuous_apply v).comp_continuousOn hx)
      (fun t ht ↦ by simpa [field, forcingVector] using (hasDerivAt_pi.mp (hderiv t ht)) u)
      (fun t ht ↦ by simpa [field, forcingVector] using (hasDerivAt_pi.mp (hderiv t ht)) v)
    have hτb : τ ≤ b := hτ.2.trans hlong
    let N : ℕ := ⌊(b - τ) / (2 * Real.pi)⌋₊
    let endTime := halfTurnBoundary τ (2 * N)
    have hperiod : (0 : ℝ) < 2 * Real.pi := by positivity
    have hfloor : (N : ℝ) ≤ (b - τ) / (2 * Real.pi) :=
      Nat.floor_le (div_nonneg (sub_nonneg.mpr hτb) hperiod.le)
    have hceiling : (b - τ) / (2 * Real.pi) < (N : ℝ) + 1 := Nat.lt_floor_add_one _
    have hendFormula : endTime = τ + (N : ℝ) * (2 * Real.pi) := by
      dsimp [endTime, halfTurnBoundary]
      push_cast
      ring
    have hτEnd : τ ≤ endTime := by
      rw [hendFormula]
      exact le_add_of_nonneg_right (by positivity)
    have hendb : endTime ≤ b := by
      have hmul := (le_div_iff₀ hperiod).mp hfloor
      rw [hendFormula]
      linarith
    have htailLength : b - endTime ≤ 2 * Real.pi := by
      have hmul := (div_lt_iff₀ hperiod).mp hceiling
      rw [hendFormula]
      nlinarith
    have hmagnitude : ContinuousOn (jointForcingMagnitude forcingA forcingB) (Icc a b) :=
      hforcingA.norm.sup hforcingB.norm
    have hmassTail : forcingMass (jointForcingMagnitude forcingA forcingB) τ b ≤ 1 / 256 := by
      apply le_trans ?_ hmass
      exact intervalIntegral.integral_mono_interval hτ.1 hτb le_rfl
        (Filter.Eventually.of_forall (fun _ ↦ abs_nonneg _))
        (hmagnitude.abs.intervalIntegrable_of_Icc hab)
    have hmiddle := integral_output_complete_turns_le program entry initial
      (hx.mono (Icc_subset_Icc hτ.1 le_rfl))
      (hforcingA.mono (Icc_subset_Icc hτ.1 le_rfl))
      (hforcingB.mono (Icc_subset_Icc hτ.1 le_rfl))
      (fun t ht ↦ hderiv t (Ioo_subset_Ioo hτ.1 le_rfl ht)) huτ hvτ hradius
      N T hendb hhalt hmassTail
    have hprefix := integral_output_le_length hτ.1 (hx.mono (Icc_subset_Icc le_rfl hτb))
    have htail := integral_output_le_length hendb
      (hx.mono (Icc_subset_Icc (hτ.1.trans hτEnd) le_rfl))
    have houtput := continuous_output.comp_continuousOn hx
    have haddPrefix := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      ((houtput.mono (Icc_subset_Icc le_rfl hτb)).intervalIntegrable_of_Icc hτ.1)
      ((houtput.mono (Icc_subset_Icc hτ.1 hendb)).intervalIntegrable_of_Icc hτEnd)
    have haddTail := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      ((houtput.mono (Icc_subset_Icc le_rfl hendb)).intervalIntegrable_of_Icc
        (hτ.1.trans hτEnd))
      ((houtput.mono (Icc_subset_Icc (hτ.1.trans hτEnd) le_rfl)).intervalIntegrable_of_Icc hendb)
    simp only [Function.comp_apply] at haddPrefix haddTail
    change (∫ t in τ..endTime, output (x t)) ≤ _ at hmiddle
    linarith [hτ.2]
  · have hshort : b - a ≤ 2 * Real.pi := by linarith
    have h := integral_output_le_length hab hx
    have hT : (1 : ℝ) ≤ (T : ℝ) + 3 := by linarith [Nat.cast_nonneg (α := ℝ) T]
    have hscale := mul_le_mul_of_nonneg_left hT (by positivity : (0 : ℝ) ≤ 4 * Real.pi)
    linarith

end

end Stability.Simulation.ClockedMonitor
