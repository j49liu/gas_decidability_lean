import Stability.Simulation.ClockedMonitorPenalty
import Stability.Simulation.SmoothedMonitorCompleteness

/-!
# The actual off-graph lift as a forced monitor

Projection of the rational field differs from the original monitor only
in its two buffers. The resulting forcing is continuous and is bounded
pointwise by the smoothing tail plus the constructed weighted defect.
The output obeys the same bound. No approximate trajectory or forcing
decomposition is assumed.
-/

namespace Stability.Simulation.ClockedMonitor

noncomputable section

open AbsFormula MonitorCoordinate Set

variable {k s : ℕ}

def weightedDefect (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) (ε : ℚ) (y : LiftCoordinate program entry initial ε → ℝ) : ℝ :=
  polynomialValue y (errorWeight program entry initial ε) * defectSize program entry initial ε y

theorem weightedDefect_nonneg (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) (ε : ℚ) (y : LiftCoordinate program entry initial ε → ℝ) :
    0 ≤ weightedDefect program entry initial ε y :=
  mul_nonneg (zero_le_one.trans (errorWeight_one_le program entry initial ε y))
    (Real.sqrt_nonneg _)

theorem continuous_weightedDefect (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (ε : ℚ) :
    Continuous (weightedDefect program entry initial ε) := by
  have hW : Continuous (fun y ↦ polynomialValue y (errorWeight program entry initial ε)) :=
    (AbsFormula.contDiff_polynomialValue (fun i ↦ by fun_prop)
      (errorWeight program entry initial ε) : ContDiff ℝ ⊤ _).continuous
  have hE : Continuous (fun y ↦ polynomialValue y (defectEnergy program entry initial ε)) :=
    (AbsFormula.contDiff_polynomialValue (fun i ↦ by fun_prop)
      (defectEnergy program entry initial ε) : ContDiff ℝ ⊤ _).continuous
  exact hW.mul hE.sqrt

def liftResidual (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) (ε : ℚ) (y : LiftCoordinate program entry initial ε → ℝ) :
    MonitorCoordinate k → ℝ :=
  (liftedField program entry initial ε y) ∘ Sum.inl - field program entry initial (y ∘ Sum.inl)

theorem continuous_liftResidual (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1) :
    Continuous (liftResidual program entry initial ε) := by
  apply Continuous.sub
  · apply continuous_pi
    intro i
    exact (continuous_apply (Sum.inl i)).comp
      (contDiff_liftedField program entry initial hε hεOne).continuous
  · exact (locallyLipschitz_field program entry initial).continuous.comp
      (continuous_pi fun i ↦ continuous_apply (Sum.inl i))

private theorem state_eta {α β : Type*} (y : α ⊕ β → ℝ) :
    Sum.elim (y ∘ Sum.inl) (y ∘ Sum.inr) = y := by
  funext i
  cases i <;> rfl

theorem liftedField_clock_of_state (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1)
    (y : LiftCoordinate program entry initial ε → ℝ) :
    liftedField program entry initial ε y (Sum.inl .clock) = 1 := by
  simpa only [state_eta] using liftedField_clock program entry initial hε hεOne
    (y ∘ Sum.inl) (y ∘ Sum.inr)

theorem liftedField_eq_forced (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1)
    (y : LiftCoordinate program entry initial ε → ℝ) :
    (liftedField program entry initial ε y) ∘ Sum.inl =
      field program entry initial (y ∘ Sum.inl) +
        forcingVector (bufferA (liftResidual program entry initial ε y))
          (bufferB (liftResidual program entry initial ε y)) := by
  have hc := liftedField_clock program entry initial hε hεOne (y ∘ Sum.inl) (y ∘ Sum.inr)
  have hu := liftedField_u program entry initial hε hεOne (y ∘ Sum.inl) (y ∘ Sum.inr)
  have hv := liftedField_v program entry initial hε hεOne (y ∘ Sum.inl) (y ∘ Sum.inr)
  rw [state_eta] at hc hu hv
  funext i
  cases i <;> simp [forcingVector, bufferA, bufferB, liftResidual, field, hc, hu, hv]

theorem abs_liftResidual_le (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1)
    (y : LiftCoordinate program entry initial ε → ℝ) (i : MonitorCoordinate k) :
    |liftResidual program entry initial ε y i| ≤
      (ε : ℝ) / (1 + y (Sum.inl clock) ^ 2) + weightedDefect program entry initial ε y := by
  have hrad := liftedField_error_le program entry initial hε hεOne
    (y ∘ Sum.inl) (y ∘ Sum.inr) i
  rw [state_eta] at hrad
  have hsmooth := smoothEval_error_le_clockTail (formulas program entry initial)
    clock hε hεOne (y ∘ Sum.inl) (some i)
  simp only [formulas, eval_fieldFormula] at hsmooth
  have htriangle := abs_sub_le
    (liftedField program entry initial ε y (Sum.inl i))
    (smoothEval (polynomialValue (y ∘ Sum.inl) (precision program entry initial ε))
      (y ∘ Sum.inl) (fieldFormula program entry initial i))
    (field program entry initial (y ∘ Sum.inl) i)
  change |liftedField program entry initial ε y (Sum.inl i) -
    field program entry initial (y ∘ Sum.inl) i| ≤ _
  dsimp only [weightedDefect, precision, Function.comp_apply] at hrad hsmooth htriangle ⊢
  exact (htriangle.trans (add_le_add hrad hsmooth)).trans_eq (add_comm _ _)

theorem norm_liftResidual_le (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1)
    (y : LiftCoordinate program entry initial ε → ℝ) :
    ‖liftResidual program entry initial ε y‖ ≤
      (ε : ℝ) / (1 + y (Sum.inl clock) ^ 2) + weightedDefect program entry initial ε y := by
  have hεReal : (0 : ℝ) ≤ ε := by exact_mod_cast hε.le
  apply (pi_norm_le_iff_of_nonneg
    (add_nonneg (by positivity) (weightedDefect_nonneg program entry initial ε y))).mpr
  intro i
  exact abs_liftResidual_le program entry initial hε hεOne y i

theorem joint_liftResidual_le (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1)
    (y : LiftCoordinate program entry initial ε → ℝ) :
    max ‖bufferA (liftResidual program entry initial ε y)‖
      ‖bufferB (liftResidual program entry initial ε y)‖ ≤
        (ε : ℝ) / (1 + y (Sum.inl clock) ^ 2) + weightedDefect program entry initial ε y := by
  apply le_trans _ (norm_liftResidual_le program entry initial hε hεOne y)
  apply max_le
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      (fun i ↦ norm_le_pi_norm (liftResidual program entry initial ε y) (.a i))
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      (fun i ↦ norm_le_pi_norm (liftResidual program entry initial ε y) (.b i))

theorem rationalOutput_original_error_le (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1)
    (y : LiftCoordinate program entry initial ε → ℝ) :
    |PolynomialFraction.value y (rationalOutput program entry initial ε) - output (y ∘ Sum.inl)| ≤
      (ε : ℝ) / (1 + y (Sum.inl clock) ^ 2) + weightedDefect program entry initial ε y := by
  have hrad := rationalOutput_error_le program entry initial hε hεOne
    (y ∘ Sum.inl) (y ∘ Sum.inr)
  rw [state_eta] at hrad
  have hsmooth := smoothEval_error_le_clockTail (formulas program entry initial)
    clock hε hεOne (y ∘ Sum.inl) none
  simp only [formulas, eval_outputFormula] at hsmooth
  have htriangle := abs_sub_le
    (PolynomialFraction.value y (rationalOutput program entry initial ε))
    (smoothEval (polynomialValue (y ∘ Sum.inl) (precision program entry initial ε))
      (y ∘ Sum.inl) outputFormula) (output (y ∘ Sum.inl))
  dsimp only [weightedDefect, precision, Function.comp_apply] at hrad hsmooth htriangle ⊢
  exact (htriangle.trans (add_le_add hrad hsmooth)).trans_eq (add_comm _ _)

/-- The actual finite-solution derivative projects to the actual forced
monitor equation, with the residual defined above. -/
theorem hasDerivAt_projected_forced (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1)
    {y : ℝ → LiftCoordinate program entry initial ε → ℝ} {t : ℝ}
    (hy : HasDerivAt y (liftedField program entry initial ε (y t)) t) :
    HasDerivAt (fun r ↦ y r ∘ Sum.inl)
      (field program entry initial (y t ∘ Sum.inl) +
        forcingVector (bufferA (liftResidual program entry initial ε (y t)))
          (bufferB (liftResidual program entry initial ε (y t)))) t := by
  rw [← liftedField_eq_forced program entry initial hε hεOne]
  apply hasDerivAt_pi.mpr
  intro i
  exact (hasDerivAt_pi.mp hy) (Sum.inl i)

end

end Stability.Simulation.ClockedMonitor
