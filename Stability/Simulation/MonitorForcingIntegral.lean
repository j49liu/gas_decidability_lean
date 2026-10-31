import Stability.Simulation.MonitorOutputIntegral

/-!
# Actual output bounds for arbitrary continuous forcing

The continuous cumulative forcing integral supplies actual cut times with
mass exactly `1/256`. Induction over these pieces applies the small-mass
monitor theorem to each restricted trajectory. The resulting estimate is
linear in the total forcing mass and independent of the initial state.
-/

namespace Stability.Simulation.ClockedMonitor

open Set MeasureTheory

noncomputable section

variable {k s : ℕ}

private theorem integral_output_le_nat_mass (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (T : ℕ)
    (hhalt : (RegisterMachine.run program T ⟨some entry, initial⟩).label = none) (N : ℕ)
    {a b : ℝ} {x : ℝ → MonitorCoordinate k → ℝ}
    {forcingA forcingB : ℝ → MachineCoordinate k → ℝ} (hab : a ≤ b)
    (hx : ContinuousOn x (Icc a b))
    (hforcingA : ContinuousOn forcingA (Icc a b))
    (hforcingB : ContinuousOn forcingB (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt x
      (field program entry initial (x t) + forcingVector (forcingA t) (forcingB t)) t)
    (hmass : forcingMass (jointForcingMagnitude forcingA forcingB) a b ≤ (N : ℝ) / 256) :
    (∫ t in a..b, output (x t)) ≤ 4 * Real.pi * ((T : ℝ) + 3) * ((N : ℝ) + 1) := by
  induction N generalizing a b with
  | zero =>
      have hsmall : forcingMass (jointForcingMagnitude forcingA forcingB) a b ≤ 1 / 256 := by
        norm_num at hmass
        linarith
      simpa only [Nat.cast_zero, zero_add, mul_one] using
        integral_output_le_halting_bound program entry initial hab hx hforcingA hforcingB
          hderiv T hhalt hsmall
  | succ N ih =>
      by_cases hsmall : forcingMass (jointForcingMagnitude forcingA forcingB) a b ≤ 1 / 256
      · have h := integral_output_le_halting_bound program entry initial hab hx hforcingA hforcingB
          hderiv T hhalt hsmall
        have hscale : 1 ≤ ((N + 1 : ℕ) : ℝ) + 1 := by
          have := Nat.cast_nonneg (α := ℝ) (N + 1)
          linarith
        have hC : 0 ≤ 4 * Real.pi * ((T : ℝ) + 3) := by positivity
        have hscaled := mul_le_mul_of_nonneg_left hscale hC
        exact h.trans (by simpa only [mul_one] using hscaled)
      · have hmagnitude : ContinuousOn (jointForcingMagnitude forcingA forcingB) (Icc a b) :=
          hforcingA.norm.sup hforcingB.norm
        have hlevel : (1 / 256 : ℝ) ∈
            Icc (forcingMass (jointForcingMagnitude forcingA forcingB) a a)
              (forcingMass (jointForcingMagnitude forcingA forcingB) a b) :=
          ⟨by simp only [forcingMass_self]; norm_num, (lt_of_not_ge hsmall).le⟩
        obtain ⟨τ, hτ, hτmass⟩ := intermediate_value_Icc hab
          (continuousOn_forcingMass hab hmagnitude) hlevel
        have hleft : Icc a τ ⊆ Icc a b := Icc_subset_Icc le_rfl hτ.2
        have hright : Icc τ b ⊆ Icc a b := Icc_subset_Icc hτ.1 le_rfl
        have hmassSplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
          ((hmagnitude.abs.mono hleft).intervalIntegrable_of_Icc hτ.1)
          ((hmagnitude.abs.mono hright).intervalIntegrable_of_Icc hτ.2)
        change forcingMass _ a τ + forcingMass _ τ b = forcingMass _ a b at hmassSplit
        have htailMass : forcingMass (jointForcingMagnitude forcingA forcingB) τ b ≤
            (N : ℝ) / 256 := by
          push_cast at hmass
          linarith
        have hprefix := integral_output_le_halting_bound program entry initial hτ.1
          (hx.mono hleft) (hforcingA.mono hleft) (hforcingB.mono hleft)
          (fun t ht ↦ hderiv t (Ioo_subset_Ioo le_rfl hτ.2 ht)) T hhalt hτmass.le
        have htail := ih hτ.2 (hx.mono hright) (hforcingA.mono hright) (hforcingB.mono hright)
          (fun t ht ↦ hderiv t (Ioo_subset_Ioo hτ.1 le_rfl ht)) htailMass
        have houtput := continuous_output.comp_continuousOn hx
        have houtputSplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
          ((houtput.mono hleft).intervalIntegrable_of_Icc hτ.1)
          ((houtput.mono hright).intervalIntegrable_of_Icc hτ.2)
        simp only [Function.comp_apply] at houtputSplit
        push_cast
        nlinarith

/-- Uniform actual output bound for arbitrary continuous buffer forcing.
The dependence is on its integral, not on a pointwise forcing cap. -/
theorem integral_output_le_forcing_mass (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ)
    {a b : ℝ} {x : ℝ → MonitorCoordinate k → ℝ}
    {forcingA forcingB : ℝ → MachineCoordinate k → ℝ} (hab : a ≤ b)
    (hx : ContinuousOn x (Icc a b))
    (hforcingA : ContinuousOn forcingA (Icc a b))
    (hforcingB : ContinuousOn forcingB (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt x
      (field program entry initial (x t) + forcingVector (forcingA t) (forcingB t)) t)
    (T : ℕ) (hhalt : (RegisterMachine.run program T ⟨some entry, initial⟩).label = none) :
    (∫ t in a..b, output (x t)) ≤ 4 * Real.pi * ((T : ℝ) + 3) *
      (256 * forcingMass (jointForcingMagnitude forcingA forcingB) a b + 2) := by
  let mass := forcingMass (jointForcingMagnitude forcingA forcingB) a b
  have hmassNonneg : 0 ≤ mass := forcingMass_nonneg _ hab
  let N : ℕ := ⌊256 * mass⌋₊ + 1
  have hfloor : ((⌊256 * mass⌋₊ : ℕ) : ℝ) ≤ 256 * mass := Nat.floor_le (by positivity)
  have hceiling : 256 * mass < ((⌊256 * mass⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hmass : mass ≤ (N : ℝ) / 256 := by
    dsimp only [N]
    push_cast
    linarith
  have hsize : (N : ℝ) + 1 ≤ 256 * mass + 2 := by
    dsimp only [N]
    push_cast
    linarith
  exact (integral_output_le_nat_mass program entry initial T hhalt N hab hx hforcingA hforcingB
    hderiv hmass).trans (mul_le_mul_of_nonneg_left hsize (by positivity))

end

end Stability.Simulation.ClockedMonitor
