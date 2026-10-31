import Stability.Simulation.ClockedMonitorPenalty
import Stability.Simulation.ClockedMonitorClearing
import Stability.Simulation.CompiledFormulaErrorResources
import Stability.Simulation.PolynomialFractionSubtractionResources

/-!
# Fixed degree budgets for the monitor error construction

The actual common error weight, quartic-defect energy, and polynomial
penalty have degree bounds independent of loaded register values and
rational precision. The penalized output retains its original denominator.
-/

namespace Stability.Simulation.ClockedMonitor

noncomputable section

open AbsFormula

variable {k s : ℕ}

def errorWeightDegreeBound (program : RegisterMachine.Program k s) (entry : Fin s) : ℕ :=
  CompiledFormulaLift.errorDegreeBound (radicalDegreeBound program entry)
    (fixedRootCount program entry)

def defectEnergyDegreeBound (program : RegisterMachine.Program k s) (entry : Fin s) : ℕ :=
  2 * max 4 (2 * radicalDegreeBound program entry)

theorem errorWeight_totalDegree_le (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (ε : ℚ) :
    (errorWeight program entry initial ε).totalDegree ≤ errorWeightDegreeBound program entry := by
  have h := CompiledFormulaLift.familyErrorWeight_totalDegree_le
    (precision program entry initial ε) (precision_totalDegree_le program entry initial ε)
    (formulaList program entry initial)
  simpa only [radicalFamilyDegreeBound_eq_fixed, rootCount_eq_fixed, errorWeightDegreeBound] using h

theorem defectEnergy_totalDegree_le (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (ε : ℚ) :
    (defectEnergy program entry initial ε).totalDegree ≤ defectEnergyDegreeBound program entry :=
  RadicalDefectBounds.defectEnergy_totalDegree_le
    (finiteRadicalFamily (precision program entry initial ε)
      (formulaList program entry initial)).radicands
    (finiteRadicands_totalDegree_le program entry initial ε)

def penaltyDegreeBound (program : RegisterMachine.Program k s) (entry : Fin s) : ℕ :=
  2 + 2 * errorWeightDegreeBound program entry + defectEnergyDegreeBound program entry

def penalizedOutputDegreeBound (program : RegisterMachine.Program k s) (entry : Fin s) : ℕ :=
  penaltyDegreeBound program entry + rationalDegreeBound program entry

/-- The degree budget follows the literal clock factor, squared error
weight, and defect energy in the actual penalty polynomial. -/
theorem penaltyPolynomial_totalDegree_le (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (ε : ℚ) :
    (penaltyPolynomial program entry initial ε).totalDegree ≤ penaltyDegreeBound program entry := by
  have hclock : (1 + MvPolynomial.X (Sum.inl MonitorCoordinate.clock) ^ 2 :
      MvPolynomial (LiftCoordinate program entry initial ε) ℚ).totalDegree ≤ 2 := by
    exact (MvPolynomial.totalDegree_add _ _).trans (by simp)
  apply (MvPolynomial.totalDegree_mul _ _).trans
  apply Nat.add_le_add _ (defectEnergy_totalDegree_le program entry initial ε)
  apply (MvPolynomial.totalDegree_mul _ _).trans
  exact Nat.add_le_add hclock ((MvPolynomial.totalDegree_pow _ _).trans
    (Nat.mul_le_mul_left 2 (errorWeight_totalDegree_le program entry initial ε)))

/-- This is a resource bound for the actual penalized fraction, without
any positivity assumption on the precision coefficient. -/
theorem penalizedOutput_degreesLE (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (ε : ℚ) :
    PolynomialFraction.DegreesLE (penalizedOutput program entry initial ε)
      (penalizedOutputDegreeBound program entry) :=
  PolynomialFraction.subPolynomial_degreesLE _
    (rationalOutput_degreesLE program entry initial ε)
    (penaltyPolynomial_totalDegree_le program entry initial ε)

/-- Subtraction preserves the sharper original denominator budget. -/
theorem penalizedOutput_denominator_totalDegree_le (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (ε : ℚ) :
    (penalizedOutput program entry initial ε).denominator.totalDegree ≤
      rationalDegreeBound program entry := (rationalOutput_degreesLE program entry initial ε).2

end

end Stability.Simulation.ClockedMonitor
