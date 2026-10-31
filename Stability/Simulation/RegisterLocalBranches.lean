import Stability.Simulation.RegisterTransition

/-!
# Nonexpansive local branches of the real transition map

Near a state with natural-number registers and a countdown outside `(0,1)`,
the zero tests are constant. An active instruction therefore translates
the non-label coordinates and assigns a constant label. This is the
local nonexpansive map used by the compute/copy estimate.

Source: Lemma 3.3(c), https://arxiv.org/html/2609.22058v2#S3.
-/

namespace Stability.Simulation

/-- The zero test is constant on a radius-`1/8` neighborhood of a point
outside the open unit interval. -/
theorem zeroGate_eq_of_near {x center : ℝ}
    (hcenter : center ≤ 0 ∨ 1 ≤ center) (hnear : |x - center| ≤ 1 / 8) :
    zeroGate x = zeroGate center := by
  have h := abs_le.mp hnear
  rcases hcenter with hc | hc
  · rw [zeroGate_eq_one (by linarith : x ≤ 1 / 4),
      zeroGate_eq_one (by linarith : center ≤ 1 / 4)]
  · rw [zeroGate_eq_zero (by linarith : 3 / 4 ≤ x),
      zeroGate_eq_zero (by linarith : 3 / 4 ≤ center)]

theorem zeroGate_eq_of_near_nat {x : ℝ} (n : ℕ) (hnear : |x - (n : ℝ)| ≤ 1 / 8) :
    zeroGate x = zeroGate (n : ℝ) := by
  apply zeroGate_eq_of_near _ hnear
  rcases Nat.eq_zero_or_pos n with hn | hn
  · left
    simp [hn]
  · right
    exact_mod_cast hn

namespace RegisterTransition

open MachineCoordinate

noncomputable section

variable {k s : ℕ}

/-- Freeze only the zero tests at `center`; the registers and administrative
coordinates still vary by translations, while the target label is constant. -/
def frozenInstructionBranch (instruction : RegisterMachine.Instruction k s)
    (center x : MachineCoordinate k → ℝ) : MachineCoordinate k → ℝ :=
  match instruction with
  | .inc i next => fun
      | .budget => x budget
      | .countdown => x countdown - 1
      | .label => (1 - zeroGate (center countdown)) * realLabel next
      | .register j =>
          x (.register j) + if j = i then 1 - zeroGate (center countdown) else 0
  | .dec i zero positive => fun
      | .budget => x budget
      | .countdown => x countdown - 1
      | .label => (1 - zeroGate (center countdown)) *
          (zeroGate (center (.register i)) * realLabel zero +
            (1 - zeroGate (center (.register i))) * realLabel positive)
      | .register j => x (.register j) -
          if j = i then
            (1 - zeroGate (center countdown)) * (1 - zeroGate (center (.register i)))
          else 0

theorem frozenInstructionBranch_at_center (instruction : RegisterMachine.Instruction k s)
    (center : MachineCoordinate k → ℝ) :
    frozenInstructionBranch instruction center center = instructionBranch instruction center := by
  cases instruction <;> rfl

/-- Frozen branches are nonexpansive globally, even when the frozen gate
values are not zero or one. Only their constancy is needed here. -/
theorem lipschitzWith_frozenInstructionBranch (instruction : RegisterMachine.Instruction k s)
    (center : MachineCoordinate k → ℝ) :
    LipschitzWith 1 (frozenInstructionBranch instruction center) := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro coordinate
  have h := norm_le_pi_norm (x - y) coordinate
  cases instruction <;> cases coordinate <;> simp_all [frozenInstructionBranch]

theorem lipschitzWith_haltBranch : LipschitzWith 1 (haltBranch (k := k) (s := s)) := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro coordinate
  have h := norm_le_pi_norm (x - y) coordinate
  cases coordinate <;> simp_all [haltBranch]

/-- Near natural registers and an admissible countdown, the literal
instruction agrees with the globally nonexpansive frozen branch. -/
theorem instructionBranch_eq_frozen_of_near
    (instruction : RegisterMachine.Instruction k s)
    {center x : MachineCoordinate k → ℝ}
    (hcountdown : center countdown ≤ 0 ∨ 1 ≤ center countdown)
    (hregisters : ∀ i : Fin k, ∃ n : ℕ, center (.register i) = (n : ℝ))
    (hnear : ‖x - center‖ ≤ 1 / 8) :
    instructionBranch instruction x = frozenInstructionBranch instruction center x := by
  have hcoord (coordinate : MachineCoordinate k) : |x coordinate - center coordinate| ≤ 1 / 8 :=
    (norm_le_pi_norm (x - center) coordinate).trans hnear
  have hc := zeroGate_eq_of_near hcountdown (hcoord countdown)
  have hr (i : Fin k) : zeroGate (x (.register i)) = zeroGate (center (.register i)) := by
    obtain ⟨n, hn⟩ := hregisters i
    rw [hn]
    exact zeroGate_eq_of_near_nat n (by simpa only [hn] using hcoord (.register i))
  cases instruction <;> ext coordinate <;> cases coordinate <;>
    simp [instructionBranch, frozenInstructionBranch, hc, hr]

/-- The required local target identity is derived for an actual finite
program, with every regularity assumption exposed. -/
theorem transitionMap_eq_frozen_of_near (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (q : Fin s)
    {center x : MachineCoordinate k → ℝ}
    (hlabel : center label = realLabel (some q))
    (hcountdown : center countdown ≤ 0 ∨ 1 ≤ center countdown)
    (hregisters : ∀ i : Fin k, ∃ n : ℕ, center (.register i) = (n : ℝ))
    (hnear : ‖x - center‖ ≤ 1 / 8) :
    transitionMap program entry initial x = frozenInstructionBranch (program q) center x := by
  have hlabelNear : |x label - realLabel (some q)| ≤ 1 / 8 := by
    rw [← hlabel]
    exact (norm_le_pi_norm (x - center) label).trans hnear
  rw [transitionMap_eq_instructionBranch program entry initial q hlabelNear]
  exact instructionBranch_eq_frozen_of_near (program q) hcountdown hregisters hnear

end

end RegisterTransition

end Stability.Simulation
