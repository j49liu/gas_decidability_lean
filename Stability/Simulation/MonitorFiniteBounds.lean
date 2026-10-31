import Stability.Simulation.MonitorPhaseBounds
import Stability.Simulation.OscillatorPartition

/-!
# Uniform finite-horizon bounds for the forced monitor

The partial-phase bounds are iterated over an actual oscillator sign
partition. The resulting bound is chosen from the initial norm, time
horizon, and forcing-mass caps before the solution segment is supplied.
This is an a priori estimate, not an existence or continuation theorem.
-/

namespace Stability.Simulation.ClockedMonitor

open Set MonitorCoordinate MeasureTheory

noncomputable section

variable {k s : ℕ}

private theorem forcingMass_subinterval_le
    {a b c d : ℝ} {forcing : ℝ → ℝ}
    (hca : c ≤ a) (hab : a ≤ b) (hbd : b ≤ d)
    (hf : ContinuousOn forcing (Icc c d)) :
    forcingMass forcing a b ≤ forcingMass forcing c d :=
  intervalIntegral.integral_mono_interval hca hab hbd
    (Filter.Eventually.of_forall (fun _ ↦ abs_nonneg _))
    (hf.abs.intervalIntegrable_of_Icc (hca.trans (hab.trans hbd)))

/-- A fixed number of constant-sign pieces has a bound independent of
the partition and the solution, including repeated partition endpoints. -/
theorem exists_uniform_partition_bound (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (N : ℕ)
    {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M) :
    ∃ bound ≥ (0 : ℝ), ∀ (start finish : ℝ) (boundary : ℕ → ℝ)
      (x : ℝ → MonitorCoordinate k → ℝ)
      (forcingA forcingB : ℝ → MachineCoordinate k → ℝ),
      boundary 0 = start → boundary N = finish → Monotone boundary →
      ContinuousOn x (Icc start finish) →
      ContinuousOn forcingA (Icc start finish) →
      ContinuousOn forcingB (Icc start finish) →
      (∀ t ∈ Ioo start finish, HasDerivAt x
        (field program entry initial (x t) + forcingVector (forcingA t) (forcingB t)) t) →
      ‖bufferA (x start)‖ ≤ R → ‖bufferB (x start)‖ ≤ R →
      forcingMass (jointForcingMagnitude forcingA forcingB) start finish ≤ M →
      (∀ n < N, (∀ t ∈ Icc (boundary n) (boundary (n + 1)), 0 ≤ x t u) ∨
        (∀ t ∈ Icc (boundary n) (boundary (n + 1)), x t u ≤ 0)) →
      ∀ t ∈ Icc start finish, ‖bufferA (x t)‖ ≤ bound ∧ ‖bufferB (x t)‖ ≤ bound := by
  induction N with
  | zero =>
      refine ⟨R, hR, ?_⟩
      intro start finish boundary x forcingA forcingB hstart hfinish _ _ _ _ _ hA hB _ _ t ht
      have heq : start = finish := hstart.symm.trans hfinish
      have ht' : t = start := by rw [← heq] at ht; exact le_antisymm ht.2 ht.1
      simpa only [ht'] using And.intro hA hB
  | succ N ih =>
      obtain ⟨previous, hprevious, hprefix⟩ := ih
      obtain ⟨next, hnext, hphase⟩ :=
        exists_uniform_phase_bound program entry initial hprevious hM
      refine ⟨max previous next, le_max_of_le_left hprevious, ?_⟩
      intro start finish boundary x forcingA forcingB hstart hfinish hmono hx hforcingA hforcingB
        hderiv hA hB hmass hsign t ht
      have hstartMiddle : start ≤ boundary N := by
        rw [← hstart]
        exact hmono (Nat.zero_le N)
      have hmiddleFinish : boundary N ≤ finish := by
        rw [← hfinish]
        exact hmono (Nat.le_succ N)
      have hprefixSubset : Icc start (boundary N) ⊆ Icc start finish :=
        Icc_subset_Icc le_rfl hmiddleFinish
      have hlastSubset : Icc (boundary N) finish ⊆ Icc start finish :=
        Icc_subset_Icc hstartMiddle le_rfl
      have hmagnitude : ContinuousOn (jointForcingMagnitude forcingA forcingB)
          (Icc start finish) := hforcingA.norm.sup hforcingB.norm
      have hprefixBound := hprefix start (boundary N) boundary x forcingA forcingB hstart rfl hmono
        (hx.mono hprefixSubset) (hforcingA.mono hprefixSubset) (hforcingB.mono hprefixSubset)
        (fun r hr ↦ hderiv r (Ioo_subset_Ioo le_rfl hmiddleFinish hr)) hA hB
        ((forcingMass_subinterval_le le_rfl hstartMiddle hmiddleFinish hmagnitude).trans hmass)
        (fun n hn ↦ hsign n (Nat.lt_succ_of_lt hn))
      have hmiddle := hprefixBound (boundary N) ⟨hstartMiddle, le_rfl⟩
      have hlastSign : (∀ r ∈ Icc (boundary N) finish, 0 ≤ x r u) ∨
          (∀ r ∈ Icc (boundary N) finish, x r u ≤ 0) := by
        simpa only [hfinish] using hsign N (Nat.lt_succ_self N)
      have hlastBound := hphase (boundary N) finish x forcingA forcingB hmiddleFinish
        (hx.mono hlastSubset) (hforcingA.mono hlastSubset) (hforcingB.mono hlastSubset)
        (fun r hr ↦ hderiv r (Ioo_subset_Ioo hstartMiddle le_rfl hr)) hmiddle.1 hmiddle.2
        ((forcingMass_subinterval_le hstartMiddle hmiddleFinish le_rfl hmagnitude).trans hmass)
        hlastSign
      by_cases hbefore : t ≤ boundary N
      · have h := hprefixBound t ⟨ht.1, hbefore⟩
        exact ⟨h.1.trans (le_max_left _ _), h.2.trans (le_max_left _ _)⟩
      · have h := hlastBound t ⟨(lt_of_not_ge hbefore).le, ht.2⟩
        exact ⟨h.1.trans (le_max_right _ _), h.2.trans (le_max_right _ _)⟩

/-- On every bounded time horizon, actual oscillator dynamics provide
enough constant-sign pieces to bound both buffers uniformly. -/
theorem exists_uniform_buffer_bound (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (T : ℝ)
    {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M) :
    ∃ bound ≥ (0 : ℝ), ∀ (start finish : ℝ)
      (x : ℝ → MonitorCoordinate k → ℝ)
      (forcingA forcingB : ℝ → MachineCoordinate k → ℝ),
      start ≤ finish → finish - start ≤ T → ContinuousOn x (Icc start finish) →
      ContinuousOn forcingA (Icc start finish) →
      ContinuousOn forcingB (Icc start finish) →
      (∀ t ∈ Ioo start finish, HasDerivAt x
        (field program entry initial (x t) + forcingVector (forcingA t) (forcingB t)) t) →
      ‖bufferA (x start)‖ ≤ R → ‖bufferB (x start)‖ ≤ R →
      forcingMass (jointForcingMagnitude forcingA forcingB) start finish ≤ M →
      ∀ t ∈ Icc start finish, ‖bufferA (x t)‖ ≤ bound ∧ ‖bufferB (x t)‖ ≤ bound := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((T + 2 * Real.pi) / Real.pi)
  have hcount : T + 2 * Real.pi ≤ (N : ℝ) * Real.pi :=
    ((div_lt_iff₀ Real.pi_pos).mp hN).le
  obtain ⟨bound, hbound, hpartition⟩ :=
    exists_uniform_partition_bound program entry initial N hR hM
  refine ⟨bound, hbound, ?_⟩
  intro start finish x forcingA forcingB horder htime hx hforcingA hforcingB hderiv hA hB hmass
  have hcoord (i : MonitorCoordinate k) (t : ℝ) (ht : t ∈ Ioo start finish) :=
    (hasDerivAt_pi.mp (hderiv t ht)) i
  obtain ⟨boundary, hstart, hfinish, hmono, _, hsign⟩ := exists_oscillator_sign_partition horder
    (by linarith : finish - start + 2 * Real.pi ≤ (N : ℝ) * Real.pi)
    ((continuous_apply u).comp_continuousOn hx) ((continuous_apply v).comp_continuousOn hx)
    (fun t ht ↦ by simpa [field, forcingVector] using hcoord u t ht)
    (fun t ht ↦ by simpa [field, forcingVector] using hcoord v t ht)
  exact hpartition start finish boundary x forcingA forcingB hstart hfinish hmono
    hx hforcingA hforcingB hderiv hA hB hmass hsign

/-- The full monitor state has a uniform finite-horizon bound from only
its initial norm and the actual joint forcing mass. No phase, amplitude,
label, or register restrictions are imposed on the initial state. -/
theorem exists_uniform_finite_bound (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (T : ℝ)
    {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M) :
    ∃ bound ≥ (0 : ℝ), ∀ (start finish : ℝ)
      (x : ℝ → MonitorCoordinate k → ℝ)
      (forcingA forcingB : ℝ → MachineCoordinate k → ℝ),
      start ≤ finish → finish - start ≤ T → ContinuousOn x (Icc start finish) →
      ContinuousOn forcingA (Icc start finish) →
      ContinuousOn forcingB (Icc start finish) →
      (∀ t ∈ Ioo start finish, HasDerivAt x
        (field program entry initial (x t) + forcingVector (forcingA t) (forcingB t)) t) →
      ‖x start‖ ≤ R →
      forcingMass (jointForcingMagnitude forcingA forcingB) start finish ≤ M →
      ∀ t ∈ Icc start finish, ‖x t‖ ≤ bound := by
  obtain ⟨bufferBound, hbufferNonneg, hbuffers⟩ :=
    exists_uniform_buffer_bound program entry initial T hR hM
  refine ⟨max bufferBound (max (R + T) (2 * R)),
    le_max_of_le_left hbufferNonneg, ?_⟩
  intro start finish x forcingA forcingB horder htime hx hforcingA hforcingB hderiv
    hinitial hmass t ht
  have hinitialCoord (i : MonitorCoordinate k) : |x start i| ≤ R :=
    (norm_le_pi_norm (x start) i).trans hinitial
  have hA : ‖bufferA (x start)‖ ≤ R :=
    (pi_norm_le_iff_of_nonneg hR).mpr (fun i ↦ hinitialCoord (.a i))
  have hB : ‖bufferB (x start)‖ ≤ R :=
    (pi_norm_le_iff_of_nonneg hR).mpr (fun i ↦ hinitialCoord (.b i))
  have hbuf := hbuffers start finish x forcingA forcingB horder htime hx hforcingA hforcingB
    hderiv hA hB hmass t ht
  have hcoord (i : MonitorCoordinate k) (r : ℝ) (hr : r ∈ Ioo start finish) :=
    (hasDerivAt_pi.mp (hderiv r hr)) i
  have hclock := unitSpeedClock_eq ((continuous_apply clock).comp_continuousOn hx)
    (fun r hr ↦ by simpa [field, forcingVector] using hcoord clock r hr) ht
  have hclockBound : |x t clock| ≤ R + T := by
    simp only [Function.comp_apply] at hclock
    rw [hclock]
    have htriangle := abs_add_le (x start clock) (t - start)
    rw [abs_of_nonneg (sub_nonneg.mpr ht.1)] at htriangle
    linarith [hinitialCoord clock, ht.2]
  have hamp := oscillator_amplitude_sq_eq
    ((continuous_apply u).comp_continuousOn hx) ((continuous_apply v).comp_continuousOn hx)
    (fun r hr ↦ by simpa [field, forcingVector] using hcoord u r hr)
    (fun r hr ↦ by simpa [field, forcingVector] using hcoord v r hr) ht
  simp only [Function.comp_apply] at hamp
  have huInitial : x start u ^ 2 ≤ R ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hR).mpr (hinitialCoord u)
  have hvInitial : x start v ^ 2 ≤ R ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hR).mpr (hinitialCoord v)
  have huBound : |x t u| ≤ 2 * R := by
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 2 * R)).mp
    rw [sq_abs]
    nlinarith [sq_nonneg (x t v), sq_nonneg R]
  have hvBound : |x t v| ≤ 2 * R := by
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 2 * R)).mp
    rw [sq_abs]
    nlinarith [sq_nonneg (x t u), sq_nonneg R]
  apply (pi_norm_le_iff_of_nonneg (le_max_of_le_left hbufferNonneg)).mpr
  intro i
  cases i with
  | clock => exact hclockBound.trans ((le_max_left _ _).trans (le_max_right _ _))
  | u => exact huBound.trans ((le_max_right _ _).trans (le_max_right _ _))
  | v => exact hvBound.trans ((le_max_right _ _).trans (le_max_right _ _))
  | a i => exact ((norm_le_pi_norm (bufferA (x t)) i).trans hbuf.1).trans (le_max_left _ _)
  | b i => exact ((norm_le_pi_norm (bufferB (x t)) i).trans hbuf.2).trans (le_max_left _ _)

end

end Stability.Simulation.ClockedMonitor
