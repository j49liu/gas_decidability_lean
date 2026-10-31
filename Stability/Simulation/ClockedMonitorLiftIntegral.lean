import Stability.Simulation.ClockedMonitorLiftForcing
import Stability.Simulation.MonitorForcingIntegral

/-!
# Integral bounds for the actual rational lift residual

Every finite lifted trajectory projects to a forced monitor. Its actual
forcing mass is at most the integrable smoothing tail plus the integral
of the weighted defect. Halting therefore gives an explicit upper bound
on the projected monitor output, with no dependence on the initial state
or segment length.
-/

namespace Stability.Simulation.ClockedMonitor

noncomputable section

open AbsFormula MonitorCoordinate Set MeasureTheory

variable {k s : ℕ}

theorem integral_lifted_clockTail_le (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1)
    {a b : ℝ} {y : ℝ → LiftCoordinate program entry initial ε → ℝ} (hab : a ≤ b)
    (hy : ContinuousOn y (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt y (liftedField program entry initial ε (y t)) t) :
    (∫ t in a..b, (ε : ℝ) / (1 + y t (Sum.inl clock) ^ 2)) ≤ (ε : ℝ) * Real.pi := by
  have hclock := (continuous_apply (Sum.inl clock)).comp_continuousOn hy
  have hclockDeriv : ∀ t ∈ Ioo a b, HasDerivAt (fun r ↦ y r (Sum.inl clock)) 1 t := by
    intro t ht
    simpa only [liftedField_clock_of_state program entry initial hε hεOne] using
      (hasDerivAt_pi.mp (hderiv t ht)) (Sum.inl clock)
  have hclockValue (t : ℝ) (ht : t ∈ Icc a b) :
      y t (Sum.inl clock) = (y a (Sum.inl clock) - a) + t := by
    have h := unitSpeedClock_eq hclock hclockDeriv ht
    simp only [Function.comp_apply] at h
    linarith only [h]
  have heq : (∫ t in a..b, (ε : ℝ) / (1 + y t (Sum.inl clock) ^ 2)) =
      ∫ t in a..b, (ε : ℝ) / (1 + ((y a (Sum.inl clock) - a) + t) ^ 2) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hab] at ht
    dsimp only
    rw [hclockValue t ht]
  rw [heq]
  exact (integral_clockTail_lt_pi (by exact_mod_cast hε) _ a b).le

theorem forcingMass_liftResidual_le (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1)
    {a b : ℝ} {y : ℝ → LiftCoordinate program entry initial ε → ℝ} (hab : a ≤ b)
    (hy : ContinuousOn y (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt y (liftedField program entry initial ε (y t)) t) :
    forcingMass (jointForcingMagnitude
      (fun t ↦ bufferA (liftResidual program entry initial ε (y t)))
      (fun t ↦ bufferB (liftResidual program entry initial ε (y t)))) a b ≤
      (ε : ℝ) * Real.pi + ∫ t in a..b, weightedDefect program entry initial ε (y t) := by
  have hres := (continuous_liftResidual program entry initial hε hεOne).comp_continuousOn hy
  have hA := continuous_bufferA.comp_continuousOn hres
  have hB := continuous_bufferB.comp_continuousOn hres
  have hR : ContinuousOn (fun t ↦ weightedDefect program entry initial ε (y t)) (Icc a b) :=
    (continuous_weightedDefect program entry initial ε).comp_continuousOn hy
  have htail : ContinuousOn (fun t ↦ (ε : ℝ) / (1 + y t (Sum.inl clock) ^ 2)) (Icc a b) :=
    continuousOn_const.div
      (continuousOn_const.add (((continuous_apply (Sum.inl clock)).comp_continuousOn hy).pow 2))
      (fun t _ ↦ ne_of_gt (by positivity))
  have hcomparison := intervalIntegral.integral_mono_on (μ := volume) hab
    ((hA.norm.sup hB.norm).abs.intervalIntegrable_of_Icc hab)
    ((htail.add hR).intervalIntegrable_of_Icc hab) (fun t _ ↦ by
      rw [abs_of_nonneg ((norm_nonneg _).trans (le_max_left _ _))]
      exact joint_liftResidual_le program entry initial hε hεOne (y t))
  change forcingMass _ a b ≤ _ at hcomparison
  apply hcomparison.trans
  simp only [Pi.add_apply]
  rw [intervalIntegral.integral_add (htail.intervalIntegrable_of_Icc hab)
    (hR.intervalIntegrable_of_Icc hab)]
  exact add_le_add_left
    (integral_lifted_clockTail_le program entry initial hε hεOne hab hy hderiv) _

/-- The monitor theorem is applied to the actual projected curve and
its computed residual; no simulation property is supplied as a hypothesis. -/
theorem integral_projected_output_le (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1)
    {a b : ℝ} {y : ℝ → LiftCoordinate program entry initial ε → ℝ} (hab : a ≤ b)
    (hy : ContinuousOn y (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt y (liftedField program entry initial ε (y t)) t)
    (T : ℕ) (hhalt : (RegisterMachine.run program T ⟨some entry, initial⟩).label = none) :
    (∫ t in a..b, output (y t ∘ Sum.inl)) ≤
      4 * Real.pi * ((T : ℝ) + 3) *
        (256 * ((ε : ℝ) * Real.pi +
          ∫ t in a..b, weightedDefect program entry initial ε (y t)) + 2) := by
  have hbase : ContinuousOn (fun t ↦ y t ∘ Sum.inl) (Icc a b) :=
    (continuous_pi fun i ↦ continuous_apply (Sum.inl i)).comp_continuousOn hy
  have hres := (continuous_liftResidual program entry initial hε hεOne).comp_continuousOn hy
  have houtput := integral_output_le_forcing_mass program entry initial hab hbase
    (continuous_bufferA.comp_continuousOn hres) (continuous_bufferB.comp_continuousOn hres)
    (fun t ht ↦ hasDerivAt_projected_forced program entry initial hε hεOne (hderiv t ht)) T hhalt
  apply houtput.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add_left
  exact mul_le_mul_of_nonneg_left
    (forcingMass_liftResidual_le program entry initial hε hεOne hab hy hderiv) (by norm_num)

end

end Stability.Simulation.ClockedMonitor
