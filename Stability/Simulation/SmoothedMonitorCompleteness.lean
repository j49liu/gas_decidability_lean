import Stability.Simulation.MonitorCompleteness
import Stability.Simulation.ClockedMonitorLift
import Stability.Simulation.SmoothingPerturbation

/-!
# Global forward existence for the smoothed monitor

Smoothing uses the same precision polynomial as the actual radical lift.
The clock and oscillator coordinates are unchanged. The remaining
residual is a continuous buffer forcing with uniformly bounded integral,
so the proved forced finite-horizon estimates give global continuation.
-/

namespace Stability.Simulation.ClockedMonitor

open AbsFormula Set MonitorCoordinate MeasureTheory

noncomputable section

variable {k s : ℕ}

/-- The monitor's literal formulas smoothed at their shared precision. -/
def smoothedField (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) (ε : ℚ) (x : MonitorCoordinate k → ℝ) : MonitorCoordinate k → ℝ :=
  fun i ↦ smoothEval (polynomialValue x (precision program entry initial ε)) x
    (fieldFormula program entry initial i)

theorem contDiff_smoothedField (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1) :
    ContDiff ℝ ⊤ (smoothedField program entry initial ε) := by
  rw [contDiff_pi]
  intro i
  exact contDiff_smoothEval_precisionPolynomial (formulas program entry initial) clock hε hεOne
    (fieldFormula program entry initial i)

@[simp] theorem smoothedField_clock (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (ε : ℚ) (x : MonitorCoordinate k → ℝ) :
    smoothedField program entry initial ε x clock = 1 := by
  simp [smoothedField, fieldFormula, smoothEval]

@[simp] theorem smoothedField_u (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (ε : ℚ) (x : MonitorCoordinate k → ℝ) :
    smoothedField program entry initial ε x u = -x v := by
  simp [smoothedField, fieldFormula, AbsFormula.sub, smoothEval]

@[simp] theorem smoothedField_v (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (ε : ℚ) (x : MonitorCoordinate k → ℝ) :
    smoothedField program entry initial ε x v = x u := by
  simp [smoothedField, fieldFormula, smoothEval]

/-- The actual smoothing residual has no clock or oscillator component. -/
theorem smoothedField_eq_forced (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (ε : ℚ) (x : MonitorCoordinate k → ℝ) :
    smoothedField program entry initial ε x = field program entry initial x +
      forcingVector
        (bufferA (smoothedField program entry initial ε x - field program entry initial x))
        (bufferB (smoothedField program entry initial ε x - field program entry initial x)) := by
  funext i
  cases i <;> simp [forcingVector, bufferA, bufferB, field]

private theorem norm_bufferA_le (x : MonitorCoordinate k → ℝ) : ‖bufferA x‖ ≤ ‖x‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr (fun i ↦ norm_le_pi_norm x (.a i))

private theorem norm_bufferB_le (x : MonitorCoordinate k → ℝ) : ‖bufferB x‖ ≤ ‖x‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr (fun i ↦ norm_le_pi_norm x (.b i))

/-- The buffer residual is bounded by the error of the shared field/output
family, so the output's presence in the precision cannot weaken this estimate. -/
theorem norm_smoothedField_sub_le_smoothingError (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (ε : ℚ) (x : MonitorCoordinate k → ℝ) :
    ‖smoothedField program entry initial ε x - field program entry initial x‖ ≤
      ‖smoothingError (formulas program entry initial) clock ε x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  have hi : (smoothedField program entry initial ε x - field program entry initial x) i =
      smoothingError (formulas program entry initial) clock ε x (some i) := by
    simp only [Pi.sub_apply, smoothingError, formulas, eval_fieldFormula]
    rfl
  rw [hi]
  exact norm_le_pi_norm _ (some i)

/-- The actual residual along a smoothed solution has joint buffer mass
less than `ε π`. The clock equation is derived from that solution. -/
theorem smoothed_forcingMass_lt_pi (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1)
    {a b : ℝ} {x : ℝ → MonitorCoordinate k → ℝ} (hab : a ≤ b)
    (hx : ContinuousOn x (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt x (smoothedField program entry initial ε (x t)) t) :
    forcingMass
      (jointForcingMagnitude
        (fun t ↦ bufferA (smoothedField program entry initial ε (x t) -
          field program entry initial (x t)))
        (fun t ↦ bufferB (smoothedField program entry initial ε (x t) -
          field program entry initial (x t)))) a b < (ε : ℝ) * Real.pi := by
  let residual (t : ℝ) := smoothedField program entry initial ε (x t) -
    field program entry initial (x t)
  have hresidual : ContinuousOn residual (Icc a b) :=
    ((contDiff_smoothedField program entry initial hε hεOne).continuous.comp_continuousOn hx).sub
      ((locallyLipschitz_field program entry initial).continuous.comp_continuousOn hx)
  have hclock : ∀ t ∈ Ioo a b, HasDerivAt (fun r ↦ x r clock) 1 t := by
    intro t ht
    simpa only [smoothedField_clock] using (hasDerivAt_pi.mp (hderiv t ht)) clock
  have herror := integral_norm_smoothingError_lt_pi (formulas program entry initial) clock
    hε hεOne hab hx hclock
  apply lt_of_le_of_lt ?_ herror
  change (∫ t in a..b, |max ‖bufferA (residual t)‖ ‖bufferB (residual t)‖|) ≤ _
  have hmag : ContinuousOn (fun t ↦ max ‖bufferA (residual t)‖ ‖bufferB (residual t)‖)
      (Icc a b) := (continuous_bufferA.comp_continuousOn hresidual).norm.sup
        (continuous_bufferB.comp_continuousOn hresidual).norm
  have herrorContinuous :=
    (continuous_smoothingError (formulas program entry initial) clock hε hεOne).comp_continuousOn hx
  apply intervalIntegral.integral_mono_on hab (hmag.abs.intervalIntegrable_of_Icc hab)
    (herrorContinuous.norm.intervalIntegrable_of_Icc hab)
  intro t _
  rw [abs_of_nonneg ((norm_nonneg _).trans (le_max_left _ _))]
  apply (max_le (norm_bufferA_le (residual t)) (norm_bufferB_le (residual t))).trans
  exact norm_smoothedField_sub_le_smoothingError program entry initial ε (x t)

/-- The actual smoothed monitor is forward complete for every real
initial state. Its existence proof uses the proved forced-segment bound,
not an assumed global perturbed trajectory. -/
theorem forwardComplete_smoothedField (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1) :
    HGAS.ForwardComplete (smoothedField program entry initial ε) := by
  intro x₀
  have hεReal : (0 : ℝ) < ε := by exact_mod_cast hε
  apply exists_global_forward_solution_of_finite_bounds
    ((contDiff_smoothedField program entry initial hε hεOne).of_le
      (by simp : (1 : WithTop ℕ∞) ≤ ⊤)).locallyLipschitz x₀
  intro T _
  obtain ⟨bound, _, hbound⟩ := exists_uniform_finite_bound program entry initial T
    (R := ‖x₀‖) (M := (ε : ℝ) * Real.pi) (norm_nonneg _)
    (mul_nonneg hεReal.le Real.pi_pos.le)
  refine ⟨bound, ?_⟩
  intro b hb x hx₀ hx hderiv
  let residual (t : ℝ) := smoothedField program entry initial ε (x t) -
    field program entry initial (x t)
  have hresidual : ContinuousOn residual (Icc 0 b) :=
    ((contDiff_smoothedField program entry initial hε hεOne).continuous.comp_continuousOn hx).sub
      ((locallyLipschitz_field program entry initial).continuous.comp_continuousOn hx)
  apply hbound 0 b x (fun t ↦ bufferA (residual t)) (fun t ↦ bufferB (residual t))
    hb.1 (by simpa using hb.2) hx
    (continuous_bufferA.comp_continuousOn hresidual)
    (continuous_bufferB.comp_continuousOn hresidual)
    (fun t ht ↦ ?_) (by rw [hx₀])
    (smoothed_forcingMass_lt_pi program entry initial hε hεOne hb.1 hx hderiv).le
  convert hderiv t ht using 1
  exact (smoothedField_eq_forced program entry initial ε (x t)).symm

end

end Stability.Simulation.ClockedMonitor
