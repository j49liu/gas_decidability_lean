import Stability.Simulation.FormulaLocalExistence
import Stability.Simulation.ClockedMonitorDynamics

/-!
# Bounds on arbitrary partial compute and copy phases

The estimates use the actual forced monitor equations and its constructed
transition map. They require only a fixed sign of the oscillator on the
supplied interval, not an aligned phase, positive amplitude, or valid
machine state. In particular, they apply to an initial partial half-turn.

These finite-segment estimates do not yet prove global continuation.
-/

namespace Stability.Simulation

open Set Metric MeasureTheory

noncomputable section

/-- A bounded target bounds coordinatewise cubic relaxation in the finite
sup norm, including intervals with zero gain. -/
theorem norm_le_max_initial_target_add_forcingMass
    {ι : Type*} [Fintype ι] {start finish targetBound : ℝ}
    {y target forcing : ℝ → ι → ℝ} {rate magnitude : ℝ → ℝ}
    (horder : start ≤ finish)
    (hy : ContinuousOn y (Icc start finish))
    (hforcing : ContinuousOn forcing (Icc start finish))
    (hmagnitude : ContinuousOn magnitude (Icc start finish))
    (hnonneg : ∀ t ∈ Icc start finish, 0 ≤ rate t)
    (hbound : ∀ t ∈ Icc start finish, ‖forcing t‖ ≤ magnitude t)
    (htarget : ∀ t ∈ Icc start finish, ‖target t‖ ≤ targetBound)
    (hderiv : ∀ i t, t ∈ Ioo start finish →
      HasDerivAt (fun s ↦ y s i) (rate t * (target t i - y t i) ^ 3 + forcing t i) t)
    {t : ℝ} (ht : t ∈ Icc start finish) :
    ‖y t‖ ≤ max ‖y start‖ targetBound + forcingMass magnitude start finish := by
  apply (pi_norm_le_iff_of_nonneg (by
    have := forcingMass_nonneg magnitude horder
    exact add_nonneg ((norm_nonneg _).trans (le_max_left _ _)) this)).mpr
  intro i
  have hscalar := abs_le_max_initial_target_add_total_forcingMass horder
    ((continuous_apply i).comp_continuousOn hy)
    ((continuous_apply i).comp_continuousOn hforcing) hnonneg
    (fun s hs ↦ (norm_le_pi_norm (target s) i).trans (htarget s hs)) (hderiv i) ht
  have hmass : forcingMass (fun s ↦ forcing s i) start finish ≤
      forcingMass magnitude start finish := by
    apply intervalIntegral.integral_mono_on horder
      (((continuous_apply i).comp_continuousOn hforcing).abs.intervalIntegrable_of_Icc horder)
      (hmagnitude.abs.intervalIntegrable_of_Icc horder)
    intro s hs
    exact (norm_le_pi_norm (forcing s) i).trans ((hbound s hs).trans (le_abs_self _))
  exact hscalar.trans (add_le_add (max_le_max (norm_le_pi_norm (y start) i) le_rfl) hmass)

namespace RegisterTransition

variable {k s : ℕ}

/-- The actual real transition has a finite bound on every norm ball.
The bound depends on the program, input, and ball, not on a trajectory. -/
theorem exists_norm_bound (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (radius : ℝ) :
    ∃ bound ≥ (0 : ℝ), ∀ x : MachineCoordinate k → ℝ, ‖x‖ ≤ radius →
      ‖transitionMap program entry initial x‖ ≤ bound := by
  have hc : Continuous (transitionMap program entry initial) := by
    simpa only [eval_transitionFormula] using
      (AbsFormula.locallyLipschitz_family (transitionFormula program entry initial)).continuous
  have hcomp := isCompact_closedBall (0 : MachineCoordinate k → ℝ) radius
  obtain ⟨bound, hbound⟩ := hcomp.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max bound 0, le_max_right _ _, fun x hx ↦ ?_⟩
  exact (hbound x (by simpa only [mem_closedBall, dist_zero_right] using hx)).trans
    (le_max_left _ _)

end RegisterTransition

namespace ClockedMonitor

open MonitorCoordinate

variable {k s : ℕ}

section

variable (program : RegisterMachine.Program k s) (entry : Fin s) (initial : Fin k → ℕ)
  {start finish : ℝ} {x : ℝ → MonitorCoordinate k → ℝ}
  {forcingA forcingB : ℝ → MachineCoordinate k → ℝ}
  (horder : start ≤ finish)
  (hx : ContinuousOn x (Icc start finish))
  (hforcingA : ContinuousOn forcingA (Icc start finish))
  (hforcingB : ContinuousOn forcingB (Icc start finish))
  (hderiv : ∀ t ∈ Ioo start finish,
    HasDerivAt x
      (field program entry initial (x t) + forcingVector (forcingA t) (forcingB t)) t)

include horder hx hforcingA hforcingB hderiv

/-- On any compute-phase segment the held buffer stays within its actual
forcing mass, and the other buffer is controlled by a bound for `H` on
that ball. Such a bound exists by `RegisterTransition.exists_norm_bound`. -/
theorem forced_compute_phase_bounds {targetBound : ℝ}
    (hsign : ∀ t ∈ Icc start finish, 0 ≤ x t u)
    (htarget : ∀ y : MachineCoordinate k → ℝ,
      ‖y‖ ≤ ‖bufferA (x start)‖ +
        forcingMass (jointForcingMagnitude forcingA forcingB) start finish →
      ‖RegisterTransition.transitionMap program entry initial y‖ ≤ targetBound)
    {t : ℝ} (ht : t ∈ Icc start finish) :
    ‖bufferA (x t)‖ ≤ ‖bufferA (x start)‖ +
        forcingMass (jointForcingMagnitude forcingA forcingB) start finish ∧
      ‖bufferB (x t)‖ ≤ max ‖bufferB (x start)‖ targetBound +
        forcingMass (jointForcingMagnitude forcingA forcingB) start finish := by
  have hmagnitude : ContinuousOn (jointForcingMagnitude forcingA forcingB)
      (Icc start finish) := hforcingA.norm.sup hforcingB.norm
  have hcoord (i : MonitorCoordinate k) (r : ℝ) (hr : r ∈ Ioo start finish) :=
    (hasDerivAt_pi.mp (hderiv r hr)) i
  have haDeriv : ∀ r ∈ Ioo start finish, HasDerivAt (fun z ↦ bufferA (x z)) (forcingA r) r := by
    intro r hr
    apply hasDerivAt_pi.mpr
    intro i
    have hz : max (-x r u) 0 = 0 := max_eq_right (neg_nonpos.mpr (hsign r (Ioo_subset_Icc_self hr)))
    simpa [bufferA, field, forcingVector, hz] using hcoord (.a i) r hr
  have hA (r : ℝ) (hr : r ∈ Icc start finish) :
      ‖bufferA (x r)‖ ≤ ‖bufferA (x start)‖ +
        forcingMass (jointForcingMagnitude forcingA forcingB) start finish := by
    have hd := norm_sub_le_forcingMass_of_hasDerivAt
      (continuous_bufferA.comp_continuousOn hx) hforcingA hmagnitude
      (fun _ _ ↦ le_max_left _ _) haDeriv hr
    simp only [Function.comp_apply] at hd
    have hnorm := norm_le_norm_sub_add (bufferA (x r)) (bufferA (x start))
    linarith
  refine ⟨hA t ht, ?_⟩
  apply norm_le_max_initial_target_add_forcingMass horder
    (continuous_bufferB.comp_continuousOn hx) hforcingB hmagnitude
    (rate := fun r ↦ (gain : ℝ) * (1 + x r clock ^ 2) ^ 2 * max (x r u) 0)
    (fun _ _ ↦ by have := gain_pos; positivity)
    (fun _ _ ↦ le_max_right _ _) (fun r hr ↦ htarget _ (hA r hr))
    (fun i r hr ↦ ?_) ht
  simpa [bufferA, bufferB, field, forcingVector] using hcoord (.b i) r hr

/-- On any copy-phase segment no transition-map bound is needed: the
held buffer bounds the copying buffer. This includes arbitrary garbage
initial values and degenerate oscillator amplitude. -/
theorem forced_copy_phase_bounds
    (hsign : ∀ t ∈ Icc start finish, x t u ≤ 0)
    {t : ℝ} (ht : t ∈ Icc start finish) :
    ‖bufferB (x t)‖ ≤ ‖bufferB (x start)‖ +
        forcingMass (jointForcingMagnitude forcingA forcingB) start finish ∧
      ‖bufferA (x t)‖ ≤
        max ‖bufferA (x start)‖ (‖bufferB (x start)‖ +
          forcingMass (jointForcingMagnitude forcingA forcingB) start finish) +
        forcingMass (jointForcingMagnitude forcingA forcingB) start finish := by
  have hmagnitude : ContinuousOn (jointForcingMagnitude forcingA forcingB)
      (Icc start finish) := hforcingA.norm.sup hforcingB.norm
  have hcoord (i : MonitorCoordinate k) (r : ℝ) (hr : r ∈ Ioo start finish) :=
    (hasDerivAt_pi.mp (hderiv r hr)) i
  have hbDeriv : ∀ r ∈ Ioo start finish, HasDerivAt (fun z ↦ bufferB (x z)) (forcingB r) r := by
    intro r hr
    apply hasDerivAt_pi.mpr
    intro i
    have hz : max (x r u) 0 = 0 := max_eq_right (hsign r (Ioo_subset_Icc_self hr))
    simpa [bufferB, field, forcingVector, hz] using hcoord (.b i) r hr
  have hB (r : ℝ) (hr : r ∈ Icc start finish) :
      ‖bufferB (x r)‖ ≤ ‖bufferB (x start)‖ +
        forcingMass (jointForcingMagnitude forcingA forcingB) start finish := by
    have hd := norm_sub_le_forcingMass_of_hasDerivAt
      (continuous_bufferB.comp_continuousOn hx) hforcingB hmagnitude
      (fun _ _ ↦ le_max_right _ _) hbDeriv hr
    simp only [Function.comp_apply] at hd
    have hnorm := norm_le_norm_sub_add (bufferB (x r)) (bufferB (x start))
    linarith
  refine ⟨hB t ht, ?_⟩
  apply norm_le_max_initial_target_add_forcingMass horder
    (continuous_bufferA.comp_continuousOn hx) hforcingA hmagnitude
    (rate := fun r ↦ (gain : ℝ) * (1 + x r clock ^ 2) ^ 2 * max (-x r u) 0)
    (fun _ _ ↦ by have := gain_pos; positivity)
    (fun _ _ ↦ le_max_left _ _) hB (fun i r hr ↦ ?_) ht
  simpa [bufferA, bufferB, field, forcingVector] using hcoord (.a i) r hr

end

/-- One bound works for every partial phase with the prescribed initial
buffer and forcing caps. It is chosen before the interval or trajectory,
so finite phase partitions may iterate this estimate without assuming
that a solution is already globally bounded. -/
theorem exists_uniform_phase_bound (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M) :
    ∃ bound ≥ (0 : ℝ), ∀ (start finish : ℝ)
      (x : ℝ → MonitorCoordinate k → ℝ)
      (forcingA forcingB : ℝ → MachineCoordinate k → ℝ),
      start ≤ finish → ContinuousOn x (Icc start finish) →
      ContinuousOn forcingA (Icc start finish) →
      ContinuousOn forcingB (Icc start finish) →
      (∀ t ∈ Ioo start finish, HasDerivAt x
        (field program entry initial (x t) + forcingVector (forcingA t) (forcingB t)) t) →
      ‖bufferA (x start)‖ ≤ R → ‖bufferB (x start)‖ ≤ R →
      forcingMass (jointForcingMagnitude forcingA forcingB) start finish ≤ M →
      ((∀ t ∈ Icc start finish, 0 ≤ x t u) ∨
        (∀ t ∈ Icc start finish, x t u ≤ 0)) →
      ∀ t ∈ Icc start finish, ‖bufferA (x t)‖ ≤ bound ∧ ‖bufferB (x t)‖ ≤ bound := by
  obtain ⟨targetBound, htargetNonneg, htarget⟩ :=
    RegisterTransition.exists_norm_bound program entry initial (R + M)
  refine ⟨max R targetBound + 2 * M, by positivity, ?_⟩
  intro start finish x forcingA forcingB horder hx hforcingA hforcingB hderiv
    hA₀ hB₀ hmass hsign t ht
  have hmassNonneg := forcingMass_nonneg (jointForcingMagnitude forcingA forcingB) horder
  have hRmax := le_max_left R targetBound
  rcases hsign with hcompute | hcopy
  · have htarget' (y : MachineCoordinate k → ℝ)
        (hy : ‖y‖ ≤ ‖bufferA (x start)‖ +
          forcingMass (jointForcingMagnitude forcingA forcingB) start finish) :
        ‖RegisterTransition.transitionMap program entry initial y‖ ≤ targetBound :=
      htarget y (hy.trans (add_le_add hA₀ hmass))
    have h := forced_compute_phase_bounds program entry initial horder hx hforcingA hforcingB
      hderiv hcompute htarget' ht
    constructor
    · linarith [h.1]
    · have hmax := max_le_max hB₀ (le_refl targetBound)
      linarith [h.2]
  · have h := forced_copy_phase_bounds program entry initial horder hx hforcingA hforcingB
      hderiv hcopy ht
    constructor
    · have hmax : max ‖bufferA (x start)‖
          (‖bufferB (x start)‖ + forcingMass (jointForcingMagnitude forcingA forcingB)
            start finish) ≤ R + M :=
        max_le (by linarith) (add_le_add hB₀ hmass)
      linarith [h.2]
    · linarith [h.1]

end ClockedMonitor

end

end Stability.Simulation
