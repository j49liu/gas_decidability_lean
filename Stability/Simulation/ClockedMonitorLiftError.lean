import Stability.Simulation.ClockedMonitorLift
import Stability.Simulation.CompiledFormulaError
import Stability.Simulation.CompiledPolynomialFormula

/-!
# Exact clocks and global errors of the monitor's rational lift

The clock and oscillator coordinates agree exactly with the original
monitor at every lifted state. One explicit polynomial weight controls
each buffer and output error relative to the shared smoothing, even
away from the quartic constraint graph.
-/

namespace Stability.Simulation.ClockedMonitor

noncomputable section

open AbsFormula

variable {k s : ℕ}

def errorWeight (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) (ε : ℚ) :
    MvPolynomial (LiftCoordinate program entry initial ε) ℚ :=
  CompiledFormulaLift.familyErrorWeight (precision program entry initial ε)
    (formulaList program entry initial)

def defectEnergy (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) (ε : ℚ) :
    MvPolynomial (LiftCoordinate program entry initial ε) ℚ :=
  RadicalDefectBounds.defectEnergy (finiteRadicalFamily (precision program entry initial ε)
    (formulaList program entry initial)).radicands

def defectSize (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) (ε : ℚ) (y : LiftCoordinate program entry initial ε → ℝ) : ℝ :=
  Real.sqrt (polynomialValue y (defectEnergy program entry initial ε))

theorem errorWeight_one_le (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) (ε : ℚ) (y : LiftCoordinate program entry initial ε → ℝ) :
    1 ≤ polynomialValue y (errorWeight program entry initial ε) :=
  CompiledFormulaLift.familyErrorWeight_one_le _ _ y

theorem liftedField_error_le (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1)
    (x : MonitorCoordinate k → ℝ)
    (w : Fin (finiteRadicalFamily (precision program entry initial ε)
      (formulaList program entry initial)).rootCount → ℝ) (i : MonitorCoordinate k) :
    |liftedField program entry initial ε (Sum.elim x w) (Sum.inl i) -
      smoothEval (polynomialValue x (precision program entry initial ε)) x
        (fieldFormula program entry initial i)| ≤
      polynomialValue (Sum.elim x w) (errorWeight program entry initial ε) *
        defectSize program entry initial ε (Sum.elim x w) := by
  have h := CompiledFormulaLift.baseFraction_error_le_family
    (precision program entry initial ε) (formulaList program entry initial) x
    (precision_one_le program entry initial hε hεOne x) w
    (formulaPosition program entry initial (some i))
  simpa only [formulaList_get, formulas] using h

theorem rationalOutput_error_le (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1)
    (x : MonitorCoordinate k → ℝ)
    (w : Fin (finiteRadicalFamily (precision program entry initial ε)
      (formulaList program entry initial)).rootCount → ℝ) :
    |PolynomialFraction.value (Sum.elim x w) (rationalOutput program entry initial ε) -
      smoothEval (polynomialValue x (precision program entry initial ε)) x outputFormula| ≤
      polynomialValue (Sum.elim x w) (errorWeight program entry initial ε) *
        defectSize program entry initial ε (Sum.elim x w) := by
  have h := CompiledFormulaLift.baseFraction_error_le_family
    (precision program entry initial ε) (formulaList program entry initial) x
    (precision_one_le program entry initial hε hεOne x) w
    (formulaPosition program entry initial none)
  simpa only [formulaList_get, formulas] using h

private theorem liftedField_polynomial_coordinate (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1)
    (x : MonitorCoordinate k → ℝ)
    (w : Fin (finiteRadicalFamily (precision program entry initial ε)
      (formulaList program entry initial)).rootCount → ℝ) (i : MonitorCoordinate k)
    (hi : radicalCount (fieldFormula program entry initial i) = 0) :
    liftedField program entry initial ε (Sum.elim x w) (Sum.inl i) =
      field program entry initial x i := by
  have h := CompiledFormulaLift.baseFraction_value_of_radicalCount_eq_zero
    (precision program entry initial ε) (formulaList program entry initial) x
    (zero_lt_one.trans_le (precision_one_le program entry initial hε hεOne x)) w
    (formulaPosition program entry initial (some i))
    (by simpa only [formulaList_get, formulas] using hi)
  simpa only [formulaList_get, formulas, eval_fieldFormula] using h

theorem liftedField_clock (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1)
    (x : MonitorCoordinate k → ℝ)
    (w : Fin (finiteRadicalFamily (precision program entry initial ε)
      (formulaList program entry initial)).rootCount → ℝ) :
    liftedField program entry initial ε (Sum.elim x w) (Sum.inl .clock) = 1 :=
  liftedField_polynomial_coordinate program entry initial hε hεOne x w .clock rfl

theorem liftedField_u (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1)
    (x : MonitorCoordinate k → ℝ)
    (w : Fin (finiteRadicalFamily (precision program entry initial ε)
      (formulaList program entry initial)).rootCount → ℝ) :
    liftedField program entry initial ε (Sum.elim x w) (Sum.inl .u) = -x .v :=
  liftedField_polynomial_coordinate program entry initial hε hεOne x w .u rfl

theorem liftedField_v (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1)
    (x : MonitorCoordinate k → ℝ)
    (w : Fin (finiteRadicalFamily (precision program entry initial ε)
      (formulaList program entry initial)).rootCount → ℝ) :
    liftedField program entry initial ε (Sum.elim x w) (Sum.inl .v) = x .u :=
  liftedField_polynomial_coordinate program entry initial hε hεOne x w .v rfl

end

end Stability.Simulation.ClockedMonitor
