import Stability.Simulation.ClockedMonitorLift

/-!
# Input-independent resources of the compiled monitor

The chosen register input changes rational constants, not the formula
trees. Consequently the precision degree bound and the exact number of
auxiliary coordinates are fixed for a fixed program. These statements
concern the actual shared compiler, including its output formula.
-/

namespace Stability.Simulation.ClockedMonitor

noncomputable section

open AbsFormula

variable {k s : ℕ}

theorem formulaList_eraseConstants (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial other : Fin k → ℕ) :
    (formulaList program entry initial).map eraseConstants =
      (formulaList program entry other).map eraseConstants := by
  simp only [formulaList, familyList, List.map_ofFn]
  congr 1
  funext i
  exact eraseConstants_formulas program entry initial other _

/-- The bound depends on the fixed program, not the loaded input or
the rational smoothing precision. -/
def precisionDegreeBound (program : RegisterMachine.Program k s) (entry : Fin s) : ℕ :=
  2 + familyDegreeBound (formulas program entry (fun _ ↦ 0))

theorem precision_totalDegree_le (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (ε : ℚ) :
    (precision program entry initial ε).totalDegree ≤ precisionDegreeBound program entry := by
  have hshape := familyDegreeBound_eq_of_eraseConstants_eq
    (eraseConstants_formulas program entry initial (fun _ ↦ 0))
  exact (precisionPolynomial_totalDegree_le _ _ _).trans_eq (congrArg (2 + ·) hshape)

/-- The exact auxiliary count is independent of both input values and
the precision coefficient, including zero or coincident constants. -/
theorem rootCount_eq (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial other : Fin k → ℕ) (ε η : ℚ) :
    (finiteRadicalFamily (precision program entry initial ε)
      (formulaList program entry initial)).rootCount =
    (finiteRadicalFamily (precision program entry other η)
      (formulaList program entry other)).rootCount := by
  rw [(finiteRadicalFamily_counts _ _).1, (finiteRadicalFamily_counts _ _).1]
  have hshape := congrArg (fun es : List (AbsFormula (MonitorCoordinate k)) ↦
    (es.map radicalCount).sum) (formulaList_eraseConstants program entry initial other)
  simpa only [List.map_map, Function.comp_def, radicalCount_eraseConstants] using hshape

def radicalDegreeBound (program : RegisterMachine.Program k s) (entry : Fin s) : ℕ :=
  radicalFamilyDegreeBound (precisionDegreeBound program entry)
    (formulaList program entry (fun _ ↦ 0))

/-- All finite radicands before root-square substitution share a bound
depending only on the fixed program and entry label. -/
theorem finiteRadicands_totalDegree_le (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (ε : ℚ)
    (j : Fin (finiteRadicalFamily (precision program entry initial ε)
      (formulaList program entry initial)).rootCount) :
    ((finiteRadicalFamily (precision program entry initial ε)
      (formulaList program entry initial)).radicands j).totalDegree ≤
        radicalDegreeBound program entry := by
  have hbound := (finiteRadicalFamily_totalDegree_le (precision program entry initial ε)
    (precision_totalDegree_le program entry initial ε) (formulaList program entry initial)).1 j
  have hshape := congrArg (radicalFamilyDegreeBound (precisionDegreeBound program entry))
    (formulaList_eraseConstants program entry initial (fun _ ↦ 0))
  simp only [radicalFamilyDegreeBound_eraseConstants] at hshape
  exact hbound.trans_eq hshape

end

end Stability.Simulation.ClockedMonitor
