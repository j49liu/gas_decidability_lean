import Stability.Simulation.RegisterTransitionFormula

/-!
# The actual oscillator-gated register monitor

The finite coordinate field uses the constructed real transition map.
Its output counts visits to the reset strip, only during compute phases
and only for oscillator amplitudes in the specified window. This file
defines the field and proves its output-support properties; it does not
assert existence or completeness of its trajectories.

Source: equations (4.1) and (4.2), https://arxiv.org/html/2609.22058v2#S4.
-/

namespace Stability.Simulation

inductive MonitorCoordinate (k : ℕ) where
  | clock
  | u
  | v
  | a (coordinate : MachineCoordinate k)
  | b (coordinate : MachineCoordinate k)
  deriving DecidableEq, Fintype

namespace ClockedMonitor

open MonitorCoordinate

def gain : ℚ := 2 ^ 20

theorem gain_pos : (0 : ℝ) < (gain : ℝ) := by norm_num [gain]

noncomputable section

variable {k s : ℕ}

def bufferA (x : MonitorCoordinate k → ℝ) : MachineCoordinate k → ℝ := fun i ↦ x (.a i)

def bufferB (x : MonitorCoordinate k → ℝ) : MachineCoordinate k → ℝ := fun i ↦ x (.b i)

/-- The literal clocked field, with componentwise cubic relaxation. -/
def field (program : RegisterMachine.Program k s) (entry : Fin s) (initial : Fin k → ℕ)
    (x : MonitorCoordinate k → ℝ) : MonitorCoordinate k → ℝ
  | .clock => 1
  | .u => -x v
  | .v => x u
  | .a i => (gain : ℝ) * (1 + x clock ^ 2) ^ 2 * max (-x u) 0 *
      (x (.b i) - x (.a i)) ^ 3
  | .b i => (gain : ℝ) * (1 + x clock ^ 2) ^ 2 * max (x u) 0 *
      (RegisterTransition.transitionMap program entry initial (bufferA x) i - x (.b i)) ^ 3

def amplitudeCutoff (squaredRadius : ℝ) : ℝ := max (1 - 2 * |squaredRadius - 1|) 0

/-- The actual nonnegative monitor output. -/
def output (x : MonitorCoordinate k → ℝ) : ℝ :=
  amplitudeCutoff (x u ^ 2 + x v ^ 2) * max (x u) 0 *
    labelGate (4 * x (.a MachineCoordinate.label))

theorem amplitudeCutoff_nonneg (squaredRadius : ℝ) : 0 ≤ amplitudeCutoff squaredRadius :=
  le_max_right _ _

theorem amplitudeCutoff_le_one (squaredRadius : ℝ) : amplitudeCutoff squaredRadius ≤ 1 := by
  exact max_le (by linarith [abs_nonneg (squaredRadius - 1)]) zero_le_one

theorem amplitudeCutoff_pos_iff (squaredRadius : ℝ) :
    0 < amplitudeCutoff squaredRadius ↔ 1 / 2 < squaredRadius ∧ squaredRadius < 3 / 2 := by
  simp only [amplitudeCutoff, lt_max_iff, lt_self_iff_false, or_false]
  constructor
  · intro h
    have hbound : |squaredRadius - 1| < 1 / 2 := by linarith
    have hpair := abs_lt.mp hbound
    constructor <;> linarith
  · rintro ⟨hl, hu⟩
    have hbound : |squaredRadius - 1| < 1 / 2 := abs_lt.mpr ⟨by linarith, by linarith⟩
    linarith

theorem labelGate_pos_iff (x : ℝ) : 0 < labelGate x ↔ |x| < 1 / 4 := by
  simp only [labelGate, unitClamp, lt_min_iff, lt_max_iff]
  constructor
  · rintro ⟨h | h, _⟩
    · linarith
    · exact False.elim (lt_irrefl _ h)
  · intro h
    exact ⟨Or.inl (by linarith), zero_lt_one⟩

theorem output_nonneg (x : MonitorCoordinate k → ℝ) : 0 ≤ output x :=
  mul_nonneg (mul_nonneg (amplitudeCutoff_nonneg _) (le_max_right _ _)) (labelGate_nonneg _)

/-- Positive output forces a compute phase, the small reset strip, and
the amplitude window required by the gain estimates. -/
theorem output_pos_iff (x : MonitorCoordinate k → ℝ) :
    0 < output x ↔
      (1 / 2 < x u ^ 2 + x v ^ 2 ∧ x u ^ 2 + x v ^ 2 < 3 / 2) ∧
        0 < x u ∧ |x (.a MachineCoordinate.label)| < 1 / 16 := by
  constructor
  · intro h
    have hprod := pos_of_mul_pos_left h (labelGate_nonneg _)
    have hgate := pos_of_mul_pos_right h
      (mul_nonneg (amplitudeCutoff_nonneg _) (le_max_right _ _))
    have hcutoff := pos_of_mul_pos_left hprod (le_max_right _ _)
    have hu := pos_of_mul_pos_right hprod (amplitudeCutoff_nonneg _)
    have hu' : 0 < x u := (lt_max_iff.mp hu).resolve_right (lt_irrefl _)
    have hlabel := (labelGate_pos_iff _).mp hgate
    rw [abs_mul] at hlabel
    norm_num at hlabel
    exact ⟨(amplitudeCutoff_pos_iff _).mp hcutoff, hu', by linarith⟩
  · rintro ⟨hamp, hu, hlabel⟩
    have hcutoff := (amplitudeCutoff_pos_iff _).mpr hamp
    have hgate : 0 < labelGate (4 * x (.a MachineCoordinate.label)) := by
      apply (labelGate_pos_iff _).mpr
      rw [abs_mul]
      norm_num
      linarith
    exact mul_pos (mul_pos hcutoff (lt_max_of_lt_left hu)) hgate

/-- Outside the oscillator-amplitude window the actual output vanishes. -/
theorem output_eq_zero_of_amplitude_outside (x : MonitorCoordinate k → ℝ)
    (houtside : x u ^ 2 + x v ^ 2 ≤ 1 / 2 ∨ 3 / 2 ≤ x u ^ 2 + x v ^ 2) :
    output x = 0 := by
  apply le_antisymm _ (output_nonneg x)
  by_contra h
  have hpos := (output_pos_iff x).mp (lt_of_not_ge h)
  rcases houtside with hl | hu <;> linarith [hpos.1.1, hpos.1.2]

end

end ClockedMonitor

end Stability.Simulation
