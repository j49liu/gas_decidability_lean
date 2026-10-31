import Stability.Simulation.ClockedMonitorLiftIntegral
import Stability.Simulation.QuadraticPenalty
import Stability.Simulation.PolynomialFractionRegularity

/-!
# Halting bounds every finite penalized-output integral

The actual projected monitor has forcing at most the smoothing tail
plus R = W times the quartic-defect norm. Its output integral has a
linear cost in that forcing. Subtracting (1 + clock²)R² absorbs that
linear cost uniformly. The bound below applies to every supplied finite
trajectory of the actual rational lift, including arbitrary off-graph
initial states. No forward completeness of those trajectories is claimed.
-/

namespace Stability.Simulation.ClockedMonitor

noncomputable section

open AbsFormula MonitorCoordinate Set MeasureTheory

variable {k s : ℕ}

theorem continuous_penalizedOutput (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1) :
    Continuous (fun y ↦ PolynomialFraction.value y (penalizedOutput program entry initial ε)) :=
  PolynomialFraction.continuous_value (penalizedOutput program entry initial ε)
    (fun y ↦ ne_of_gt (zero_lt_one.trans_le
      (penalizedOutput_denominator_one_le program entry initial hε hεOne y)))

theorem penalizedOutput_le_original (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1)
    (y : LiftCoordinate program entry initial ε → ℝ) :
    PolynomialFraction.value y (penalizedOutput program entry initial ε) ≤
      output (y ∘ Sum.inl) + (ε : ℝ) / (1 + y (Sum.inl clock) ^ 2) +
        weightedDefect program entry initial ε y -
        (1 + y (Sum.inl clock) ^ 2) * weightedDefect program entry initial ε y ^ 2 := by
  have herror := (le_abs_self _).trans
    (rationalOutput_original_error_le program entry initial hε hεOne y)
  rw [penalizedOutput_value program entry initial hε hεOne, penaltyPolynomial_value]
  change PolynomialFraction.value y (rationalOutput program entry initial ε) -
      (1 + y (Sum.inl clock) ^ 2) * weightedDefect program entry initial ε y ^ 2 ≤ _
  linarith only [herror]

def penalizedIntegralBound (T : ℕ) (ε : ℚ) : ℝ :=
  let C := 4 * Real.pi * ((T : ℝ) + 3)
  2 * C + (256 * C + 1) * (ε : ℝ) * Real.pi + Real.pi * (256 * C + 1) ^ 2 / 4

/-- A source halt gives one upper bound for all finite rational-lift
output integrals, with no bound on the initial state or segment length. -/
theorem integral_penalizedOutput_le_of_halts (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1)
    {a b : ℝ} {y : ℝ → LiftCoordinate program entry initial ε → ℝ} (hab : a ≤ b)
    (hy : ContinuousOn y (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt y (liftedField program entry initial ε (y t)) t)
    (T : ℕ) (hhalt : (RegisterMachine.run program T ⟨some entry, initial⟩).label = none) :
    (∫ t in a..b, PolynomialFraction.value (y t) (penalizedOutput program entry initial ε)) ≤
      penalizedIntegralBound T ε := by
  let C : ℝ := 4 * Real.pi * ((T : ℝ) + 3)
  let R : ℝ → ℝ := fun t ↦ weightedDefect program entry initial ε (y t)
  let θ : ℝ → ℝ := fun t ↦ y t (Sum.inl clock)
  let o : ℝ → ℝ := fun t ↦ output (y t ∘ Sum.inl)
  let tail : ℝ → ℝ := fun t ↦ (ε : ℝ) / (1 + θ t ^ 2)
  let P : ℝ → ℝ := fun t ↦ (1 + θ t ^ 2) * R t ^ 2
  have hθ : ContinuousOn θ (Icc a b) :=
    (continuous_apply (Sum.inl clock)).comp_continuousOn hy
  have hθderiv : ∀ t ∈ Ioo a b, HasDerivAt θ 1 t := by
    intro t ht
    simpa only [liftedField_clock_of_state program entry initial hε hεOne] using
      (hasDerivAt_pi.mp (hderiv t ht)) (Sum.inl clock)
  have hR : ContinuousOn R (Icc a b) :=
    (continuous_weightedDefect program entry initial ε).comp_continuousOn hy
  have ho : ContinuousOn o (Icc a b) := continuous_output.comp_continuousOn
    ((continuous_pi fun i ↦ continuous_apply (Sum.inl i)).comp_continuousOn hy)
  have htail : ContinuousOn tail (Icc a b) :=
    continuousOn_const.div (continuousOn_const.add (hθ.pow 2))
      (fun t _ ↦ ne_of_gt (by positivity))
  have hP : ContinuousOn P (Icc a b) := (continuousOn_const.add (hθ.pow 2)).mul (hR.pow 2)
  have hg := (continuous_penalizedOutput program entry initial hε hεOne).comp_continuousOn hy
  have hcompare := intervalIntegral.integral_mono_on (μ := volume) hab
    (hg.intervalIntegrable_of_Icc hab)
    ((((ho.add htail).add hR).sub hP).intervalIntegrable_of_Icc hab)
    (fun t _ ↦ penalizedOutput_le_original program entry initial hε hεOne (y t))
  change (∫ t in a..b, PolynomialFraction.value (y t) (penalizedOutput program entry initial ε)) ≤
    ∫ t in a..b, o t + tail t + R t - P t at hcompare
  have hsum : IntervalIntegrable (fun t ↦ o t + tail t) volume a b :=
    (ho.add htail).intervalIntegrable_of_Icc hab
  have hsumR : IntervalIntegrable (fun t ↦ o t + tail t + R t) volume a b :=
    ((ho.add htail).add hR).intervalIntegrable_of_Icc hab
  rw [intervalIntegral.integral_sub hsumR (hP.intervalIntegrable_of_Icc hab),
    intervalIntegral.integral_add hsum (hR.intervalIntegrable_of_Icc hab),
    intervalIntegral.integral_add (ho.intervalIntegrable_of_Icc hab)
      (htail.intervalIntegrable_of_Icc hab)] at hcompare
  have hout := integral_projected_output_le program entry initial hε hεOne hab hy hderiv T hhalt
  change (∫ t in a..b, o t) ≤ C * (256 * ((ε : ℝ) * Real.pi + ∫ t in a..b, R t) + 2) at hout
  have htailBound := integral_lifted_clockTail_le program entry initial hε hεOne hab hy hderiv
  change (∫ t in a..b, tail t) ≤ (ε : ℝ) * Real.pi at htailBound
  have hpenalty := integral_clockWeightedPenalty_le hab hθ hθderiv hR (256 * C + 1)
  change (∫ t in a..b, (256 * C + 1) * R t - P t) ≤
    Real.pi * (256 * C + 1) ^ 2 / 4 at hpenalty
  have hcost : IntervalIntegrable (fun t ↦ (256 * C + 1) * R t) volume a b :=
    (continuousOn_const.mul hR).intervalIntegrable_of_Icc hab
  rw [intervalIntegral.integral_sub hcost (hP.intervalIntegrable_of_Icc hab),
    intervalIntegral.integral_const_mul] at hpenalty
  apply hcompare.trans
  calc
    _ ≤ C * (256 * ((ε : ℝ) * Real.pi + ∫ t in a..b, R t) + 2) +
        (ε : ℝ) * Real.pi + (∫ t in a..b, R t) - ∫ t in a..b, P t := by
      exact sub_le_sub_right (add_le_add_left (add_le_add hout htailBound) _) _
    _ = 2 * C + (256 * C + 1) * (ε : ℝ) * Real.pi +
        ((256 * C + 1) * (∫ t in a..b, R t) - ∫ t in a..b, P t) := by ring
    _ ≤ penalizedIntegralBound T ε := add_le_add_right hpenalty _

end

end Stability.Simulation.ClockedMonitor
