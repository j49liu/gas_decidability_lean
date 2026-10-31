import Stability.Simulation.ClockedMonitor
import Stability.Simulation.ClockedDoubleBufferUpdate
import Stability.Simulation.HeldBufferMotion

/-!
# Actual forced monitor trajectories satisfy the update estimates

The hypotheses give the derivative of the literal monitor vector field,
with forcing confined to its two buffers. The coordinate equations, held
phases, and update estimate are derived from that vector equation. A
positive-output event under a small forcing budget yields a clean reset.

The starting phase is explicitly aligned. Global existence, alignment of
arbitrary oscillator data, and the full output-integral bound are separate.
-/

namespace Stability.Simulation.ClockedMonitor

open Set MonitorCoordinate

noncomputable section

variable {k s : ℕ}

/-- External forcing acts only on the two buffers; the clocks remain exact. -/
def forcingVector (forcingA forcingB : MachineCoordinate k → ℝ) : MonitorCoordinate k → ℝ
  | .a i => forcingA i
  | .b i => forcingB i
  | _ => 0

theorem continuous_bufferA : Continuous (bufferA (k := k)) := by
  apply continuous_pi
  intro i
  exact continuous_apply (MonitorCoordinate.a i)

theorem continuous_bufferB : Continuous (bufferB (k := k)) := by
  apply continuous_pi
  intro i
  exact continuous_apply (MonitorCoordinate.b i)

section

variable (program : RegisterMachine.Program k s) (entry : Fin s) (initial : Fin k → ℕ)
  {origin finish radius : ℝ} {x : ℝ → MonitorCoordinate k → ℝ}
  {forcingA forcingB : ℝ → MachineCoordinate k → ℝ}
  (hx : ContinuousOn x (Icc origin finish))
  (hforcingA : ContinuousOn forcingA (Icc origin finish))
  (hforcingB : ContinuousOn forcingB (Icc origin finish))
  (hderiv : ∀ t ∈ Ioo origin finish,
    HasDerivAt x
      (field program entry initial (x t) + forcingVector (forcingA t) (forcingB t)) t)
  (hu0 : x origin u = 0) (hv0 : x origin v = -radius)
  (hradius : 0 ≤ radius) (hamplitude : (1 / 2 : ℝ) < radius ^ 2)

include hx hforcingA hforcingB hderiv hu0 hv0 hradius hamplitude

/-- A genuine solution segment of the literal forced monitor satisfies
the compute/copy error bound whenever its local transition branch is nonexpansive. -/
theorem forced_update_error_le {F : (MachineCoordinate k → ℝ) → MachineCoordinate k → ℝ}
    (hF : LipschitzWith 1 F) (j : ℕ)
    (hend : halfTurnBoundary origin (2 * j + 2) ≤ finish)
    (hlocal : ∀ t ∈ Icc (halfTurnBoundary origin (2 * j))
      (halfTurnBoundary origin (2 * j + 1)),
      RegisterTransition.transitionMap program entry initial (bufferA (x t)) = F (bufferA (x t))) :
    ‖bufferA (x (halfTurnBoundary origin (2 * j + 2))) -
        F (bufferA (x (halfTurnBoundary origin (2 * j))))‖ ≤
      halfTurnErrorAllowance (gain : ℝ) (x origin clock) origin
        (jointForcingMagnitude forcingA forcingB) (2 * j) +
      halfTurnErrorAllowance (gain : ℝ) (x origin clock) origin
        (jointForcingMagnitude forcingA forcingB) (2 * j + 1) := by
  have hcoord (i : MonitorCoordinate k) (t : ℝ) (ht : t ∈ Ioo origin finish) :=
    (hasDerivAt_pi.mp (hderiv t ht)) i
  apply clocked_doubleBuffer_update_error_le gain_pos hradius hamplitude
    ((continuous_apply clock).comp_continuousOn hx)
    (fun t ht ↦ by simpa [field, forcingVector] using hcoord clock t ht)
    ((continuous_apply u).comp_continuousOn hx)
    ((continuous_apply v).comp_continuousOn hx)
    (fun t ht ↦ by simpa [field, forcingVector] using hcoord u t ht)
    (fun t ht ↦ by simpa [field, forcingVector] using hcoord v t ht)
    hu0 hv0 (continuous_bufferA.comp_continuousOn hx) (continuous_bufferB.comp_continuousOn hx)
    hforcingA hforcingB
    (fun i t ht ↦ by simpa [field, forcingVector, bufferA, bufferB] using hcoord (.a i) t ht)
    (fun i t ht ↦ by simpa [field, forcingVector, bufferA, bufferB] using hcoord (.b i) t ht)
    hF j hend hlocal

omit hamplitude

/-- Positive output somewhere in a complete turn, with at most `1/16`
joint forcing mass in that turn, makes its actual update a clean reset.
No initial restrictions are placed on either buffer. The amplitude
condition is derived from the output event, not assumed. -/
theorem forced_reset_error_le (j : ℕ)
    (hend : halfTurnBoundary origin (2 * j + 2) ≤ finish)
    (hmass : forcingMass (jointForcingMagnitude forcingA forcingB)
      (halfTurnBoundary origin (2 * j)) (halfTurnBoundary origin (2 * j + 2)) ≤ 1 / 16)
    (hevent : ∃ t ∈ Icc (halfTurnBoundary origin (2 * j))
      (halfTurnBoundary origin (2 * j + 2)), 0 < output (x t)) :
    ‖bufferA (x (halfTurnBoundary origin (2 * j + 2))) -
        RegisterTransition.resetBranch entry initial
          (bufferA (x (halfTurnBoundary origin (2 * j))))‖ ≤
      halfTurnErrorAllowance (gain : ℝ) (x origin clock) origin
        (jointForcingMagnitude forcingA forcingB) (2 * j) +
      halfTurnErrorAllowance (gain : ℝ) (x origin clock) origin
        (jointForcingMagnitude forcingA forcingB) (2 * j + 1) := by
  have hstart : origin ≤ halfTurnBoundary origin (2 * j) := by
    simpa only [halfTurnBoundary_zero] using
      (halfTurnBoundary_strictMono origin).monotone (Nat.zero_le (2 * j))
  have h₀₁ : halfTurnBoundary origin (2 * j) ≤ halfTurnBoundary origin (2 * j + 1) :=
    (halfTurnBoundary_strictMono origin).monotone (by omega)
  have h₁₂ : halfTurnBoundary origin (2 * j + 1) ≤ halfTurnBoundary origin (2 * j + 2) :=
    (halfTurnBoundary_strictMono origin).monotone (by omega)
  have hturn := Icc_subset_Icc hstart hend
  have hcompute := Icc_subset_Icc hstart (h₁₂.trans hend)
  have hcomputeOpen := Ioo_subset_Ioo hstart (h₁₂.trans hend)
  have hcoord (i : MonitorCoordinate k) (t : ℝ) (ht : t ∈ Ioo origin finish) :=
    (hasDerivAt_pi.mp (hderiv t ht)) i
  have hu := (continuous_apply u).comp_continuousOn hx
  have hv := (continuous_apply v).comp_continuousOn hx
  have hdu : ∀ t ∈ Ioo origin finish, HasDerivAt (fun r ↦ x r u) (-x t v) t := by
    intro t ht
    simpa [field, forcingVector] using hcoord u t ht
  have hdv : ∀ t ∈ Ioo origin finish, HasDerivAt (fun r ↦ x r v) (x t u) t := by
    intro t ht
    simpa [field, forcingVector] using hcoord v t ht
  have hactiveAmplitude : (1 / 2 : ℝ) < radius ^ 2 := by
    obtain ⟨t, ht, hpositive⟩ := hevent
    have hconserved := oscillator_amplitude_sq_eq hu hv hdu hdv (hturn ht)
    simp only [Function.comp_apply] at hconserved
    rw [hu0, hv0] at hconserved
    have hwindow := ((output_pos_iff (x t)).mp hpositive).1.1
    nlinarith
  have hlabelDeriv : ∀ t ∈ Ioo (halfTurnBoundary origin (2 * j))
      (halfTurnBoundary origin (2 * j + 1)),
      HasDerivAt (fun r ↦ x r (.a MachineCoordinate.label))
        (forcingA t MachineCoordinate.label) t := by
    intro t ht
    have hz := oppositeWeight_eq_zero_on_halfTurn hu hv hdu hdv hu0 hv0 hradius
      (2 * j) (hcompute (Ioo_subset_Icc_self ht)) (Ioo_subset_Icc_self ht)
    have hz' : max (-x t u) 0 = 0 := by simpa [pow_mul] using hz
    simpa [field, forcingVector, hz'] using
      hcoord (.a MachineCoordinate.label) t (hcomputeOpen ht)
  have hlabelEvent : ∃ t ∈ Icc (halfTurnBoundary origin (2 * j))
      (halfTurnBoundary origin (2 * j + 1)), |x t (.a MachineCoordinate.label)| < 1 / 16 := by
    obtain ⟨t, ht, hpositive⟩ := hevent
    have hfeatures := (output_pos_iff (x t)).mp hpositive
    have hcomputeTime : t ≤ halfTurnBoundary origin (2 * j + 1) := by
      by_contra h
      have hhalf : t ∈ Icc (halfTurnBoundary origin (2 * j + 1))
          (halfTurnBoundary origin (2 * j + 1 + 1)) := by
        simp only [Nat.add_assoc]
        exact ⟨le_of_lt (lt_of_not_ge h), ht.2⟩
      have hz := oppositeWeight_eq_zero_on_halfTurn hu hv hdu hdv hu0 hv0 hradius
        (2 * j + 1) (hturn ht) hhalf
      have hz' : max (x t u) 0 = 0 := by simpa [pow_add, pow_mul] using hz
      have hnonpos : x t u ≤ 0 := by rw [← hz']; exact le_max_left _ _
      exact (not_lt_of_ge hnonpos) hfeatures.2.1
    exact ⟨t, ⟨ht.1, hcomputeTime⟩, hfeatures.2.2⟩
  have hmagnitude : ContinuousOn (jointForcingMagnitude forcingA forcingB)
      (Icc origin finish) := hforcingA.norm.sup hforcingB.norm
  have hcomputeMass : forcingMass (jointForcingMagnitude forcingA forcingB)
      (halfTurnBoundary origin (2 * j)) (halfTurnBoundary origin (2 * j + 1)) ≤ 1 / 16 :=
    (forcingMass_le (hmagnitude.mono hturn) ⟨h₀₁, h₁₂⟩).trans hmass
  have hnear := held_label_lt_one_eighth_of_event
    ((continuous_apply (MonitorCoordinate.a (MachineCoordinate.label (k := k)))).comp_continuousOn
      (hx.mono hcompute))
    ((continuous_apply MachineCoordinate.label).comp_continuousOn (hforcingA.mono hcompute))
    (hmagnitude.mono hcompute)
    (fun t _ ↦ (norm_le_pi_norm (forcingA t) MachineCoordinate.label).trans (le_max_left _ _))
    hlabelDeriv hcomputeMass hlabelEvent
  apply forced_update_error_le program entry initial hx hforcingA hforcingB hderiv
    hu0 hv0 hradius hactiveAmplitude
    (RegisterTransition.lipschitzWith_resetBranch entry initial) j hend
  intro t ht
  exact RegisterTransition.transitionMap_eq_resetBranch program entry initial (hnear t ht).le

end

end

end Stability.Simulation.ClockedMonitor
