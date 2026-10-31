import Stability.Simulation.FormulaFamilyList
import Stability.Simulation.ClockedMonitorFormula

/-!
# The actual rational lift of the clocked monitor

The field and output share one precision polynomial and one ordered root
program. The finite order is fixed by the monitor coordinate type, not by
the input. This module connects the monitor's literal formula family to
the rational compiler; it leaves off-graph error bounds and global
continuation to their own modules.
-/

namespace Stability.Simulation.ClockedMonitor

noncomputable section

open AbsFormula

variable {k s : ℕ}

def formulaOrder (k : ℕ) : Option (MonitorCoordinate k) ≃
    Fin (Fintype.card (Option (MonitorCoordinate k))) := Fintype.equivFin _

def formulaList (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) : List (AbsFormula (MonitorCoordinate k)) :=
  familyList (formulaOrder k) (formulas program entry initial)

def formulaPosition (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) (i : Option (MonitorCoordinate k)) :
    Fin (formulaList program entry initial).length :=
  familyPosition (formulaOrder k) (formulas program entry initial) i

theorem formulaList_get (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) (i : Option (MonitorCoordinate k)) :
    (formulaList program entry initial).get (formulaPosition program entry initial i) =
      formulas program entry initial i := familyList_get _ _ _

def precision (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) (ε : ℚ) : MvPolynomial (MonitorCoordinate k) ℚ :=
  precisionPolynomial (formulas program entry initial) MonitorCoordinate.clock ε

theorem precision_one_le (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1)
    (x : MonitorCoordinate k → ℝ) :
    1 ≤ polynomialValue x (precision program entry initial ε) :=
  one_le_precisionPolynomial _ _ hε hεOne x

abbrev LiftCoordinate (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) (ε : ℚ) :=
  MonitorCoordinate k ⊕ Fin (finiteRadicalFamily (precision program entry initial ε)
    (formulaList program entry initial)).rootCount

def rationalField (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) (ε : ℚ) :
    LiftCoordinate program entry initial ε →
      PolynomialFraction (LiftCoordinate program entry initial ε) :=
  CompiledFormulaLift.field (precision program entry initial ε) (formulaList program entry initial)
    (fun i ↦ formulaPosition program entry initial (some i))

def rationalOutput (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) (ε : ℚ) :
    PolynomialFraction (LiftCoordinate program entry initial ε) :=
  CompiledFormulaLift.baseFraction (precision program entry initial ε)
    (formulaList program entry initial) (formulaPosition program entry initial none)

def liftedField (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) (ε : ℚ) :
    (LiftCoordinate program entry initial ε → ℝ) →
      LiftCoordinate program entry initial ε → ℝ :=
  CompiledFormulaLift.realize (precision program entry initial ε)
    (formulaList program entry initial) (fun i ↦ formulaPosition program entry initial (some i))

def liftGraph (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) (ε : ℚ) :
    (MonitorCoordinate k → ℝ) → LiftCoordinate program entry initial ε → ℝ :=
  CompiledFormulaLift.graph (precision program entry initial ε) (formulaList program entry initial)

theorem rationalField_denominator_one_le (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1)
    (y : LiftCoordinate program entry initial ε → ℝ)
    (i : LiftCoordinate program entry initial ε) :
    1 ≤ polynomialValue y (rationalField program entry initial ε i).denominator :=
  CompiledFormulaLift.field_denominator_one_le _ _ _
    (precision_one_le program entry initial hε hεOne) y i

theorem rationalOutput_denominator_one_le (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1)
    (y : LiftCoordinate program entry initial ε → ℝ) :
    1 ≤ polynomialValue y (rationalOutput program entry initial ε).denominator :=
  CompiledFormulaLift.baseFraction_denominator_one_le _ _ _ y
    (precision_one_le program entry initial hε hεOne _)

theorem contDiff_liftedField (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1) :
    ContDiff ℝ ⊤ (liftedField program entry initial ε) :=
  CompiledFormulaLift.contDiff_realize _ _ _ (precision_one_le program entry initial hε hεOne)

theorem rationalOutput_on_graph (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1)
    (x : MonitorCoordinate k → ℝ) :
    PolynomialFraction.value (liftGraph program entry initial ε x)
      (rationalOutput program entry initial ε) =
      smoothEval (polynomialValue x (precision program entry initial ε)) x outputFormula := by
  have h := CompiledFormulaLift.baseFraction_value_on_graph
    (precision program entry initial ε) (formulaList program entry initial) x
    (precision_one_le program entry initial hε hεOne x)
    (formulaPosition program entry initial none)
  simpa only [formulaList_get, formulas] using h

/-- A trajectory of the monitor's actual smoothed formulas lifts to the
actual rational field. No lifted trajectory is an input to the theorem. -/
theorem hasDerivAt_liftGraph (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1)
    {x : ℝ → MonitorCoordinate k → ℝ} {t : ℝ}
    (hx : HasDerivAt x (fun i ↦ smoothEval
      (polynomialValue (x t) (precision program entry initial ε)) (x t)
      (fieldFormula program entry initial i)) t) :
    HasDerivAt (fun u ↦ liftGraph program entry initial ε (x u))
      (liftedField program entry initial ε (liftGraph program entry initial ε (x t))) t := by
  apply CompiledFormulaLift.hasDerivAt_graph _ _ _
    (precision_one_le program entry initial hε hεOne)
  simpa only [formulaList_get, formulas] using hx

end

end Stability.Simulation.ClockedMonitor
