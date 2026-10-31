import Stability.Simulation.ClockedMonitorResources
import Stability.Simulation.CompiledLiftResources

/-!
# Fixed degree resources and joint clearing for the actual monitor

The loaded register values and rational precision change coefficients,
not the resource bounds below. The field and output are cleared together
by one product of their actual denominators. No off-graph penalty is
added, and no time-reparametrization or simulation claim is made here.
-/

namespace Stability.Simulation.ClockedMonitor

noncomputable section

open AbsFormula PolynomialFraction

variable {k s : ℕ}

/-- The exact shared root count evaluated at one fixed reference input. -/
def fixedRootCount (program : RegisterMachine.Program k s) (entry : Fin s) : ℕ :=
  (finiteRadicalFamily (precision program entry (fun _ ↦ 0) 1)
    (formulaList program entry (fun _ ↦ 0))).rootCount

theorem rootCount_eq_fixed (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) (ε : ℚ) :
    (finiteRadicalFamily (precision program entry initial ε)
      (formulaList program entry initial)).rootCount = fixedRootCount program entry :=
  rootCount_eq program entry initial (fun _ ↦ 0) ε 1

theorem radicalFamilyDegreeBound_eq_fixed (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) :
    AbsFormula.radicalFamilyDegreeBound (precisionDegreeBound program entry)
      (formulaList program entry initial) = radicalDegreeBound program entry := by
  have h := congrArg (AbsFormula.radicalFamilyDegreeBound (precisionDegreeBound program entry))
    (formulaList_eraseConstants program entry initial (fun _ ↦ 0))
  simpa only [AbsFormula.radicalFamilyDegreeBound_eraseConstants] using h

/-- Common numerator/denominator budget for the base and output fractions. -/
def baseDegreeBound (program : RegisterMachine.Program k s) (entry : Fin s) : ℕ :=
  max (2 * radicalDegreeBound program entry)
    (fixedRootCount program entry * precisionDegreeBound program entry)

def rationalDegreeBound (program : RegisterMachine.Program k s) (entry : Fin s) : ℕ :=
  TriangularLift.degreeBound (Fintype.card (MonitorCoordinate k) + fixedRootCount program entry)
    (2 * radicalDegreeBound program entry) (baseDegreeBound program entry)
    (fixedRootCount program entry)

theorem baseFraction_degreesLE (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) (ε : ℚ) (i : Fin (formulaList program entry initial).length) :
    DegreesLE (CompiledFormulaLift.baseFraction (precision program entry initial ε)
      (formulaList program entry initial) i) (baseDegreeBound program entry) := by
  have h := CompiledFormulaLift.baseFraction_degreesLE (precision program entry initial ε)
    (precision_totalDegree_le program entry initial ε) (formulaList program entry initial) i
  simpa only [radicalFamilyDegreeBound_eq_fixed, rootCount_eq_fixed, baseDegreeBound] using h

theorem rationalField_degreesLE (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) (ε : ℚ) (i : LiftCoordinate program entry initial ε) :
    DegreesLE (rationalField program entry initial ε i) (rationalDegreeBound program entry) := by
  have hD (j) : (liftRadicand (precision program entry initial ε)
      (formulaList program entry initial) j).totalDegree ≤ 2 * radicalDegreeBound program entry :=
    (RadicalProgram.squareRootsPolynomial_totalDegree_le _).trans
      (Nat.mul_le_mul_left 2 (finiteRadicands_totalDegree_le program entry initial ε j))
  have h := TriangularLift.field_degreesLE _ _ hD
    (fun j ↦ baseFraction_degreesLE program entry initial ε
      (formulaPosition program entry initial (some j))) i
  simpa only [rootCount_eq_fixed, rationalDegreeBound] using h

theorem rationalOutput_degreesLE (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) (ε : ℚ) :
    DegreesLE (rationalOutput program entry initial ε) (rationalDegreeBound program entry) :=
  (baseFraction_degreesLE program entry initial ε (formulaPosition program entry initial none)).mono
    (TriangularLift.le_degreeBound _ _ _ _)

/-- One family for joint clearing: `none` is the output and `some i` is
the i-th lifted field coordinate. -/
def rationalFamily (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) (ε : ℚ) :
    Option (LiftCoordinate program entry initial ε) →
      PolynomialFraction (LiftCoordinate program entry initial ε)
  | none => rationalOutput program entry initial ε
  | some i => rationalField program entry initial ε i

def clearingPolynomial (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) (ε : ℚ) : MvPolynomial (LiftCoordinate program entry initial ε) ℚ :=
  commonDenominator (rationalFamily program entry initial ε)

def clearedField (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) (ε : ℚ) (i : LiftCoordinate program entry initial ε) :
    MvPolynomial (LiftCoordinate program entry initial ε) ℚ :=
  clearedNumerator (rationalFamily program entry initial ε) (some i)

def clearedOutput (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) (ε : ℚ) : MvPolynomial (LiftCoordinate program entry initial ε) ℚ :=
  clearedNumerator (rationalFamily program entry initial ε) none

def clearedDegreeBound (program : RegisterMachine.Program k s) (entry : Fin s) : ℕ :=
  (Fintype.card (MonitorCoordinate k) + fixedRootCount program entry + 1) *
    rationalDegreeBound program entry

theorem rationalFamily_degreesLE (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) (ε : ℚ) (i : Option (LiftCoordinate program entry initial ε)) :
    DegreesLE (rationalFamily program entry initial ε i) (rationalDegreeBound program entry) := by
  cases i with
  | none => exact rationalOutput_degreesLE program entry initial ε
  | some i => exact rationalField_degreesLE program entry initial ε i

private theorem family_card (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) (ε : ℚ) :
    Fintype.card (Option (LiftCoordinate program entry initial ε)) =
      Fintype.card (MonitorCoordinate k) + fixedRootCount program entry + 1 := by
  simp only [Fintype.card_option, LiftCoordinate, Fintype.card_sum, Fintype.card_fin,
    rootCount_eq_fixed]

theorem clearingPolynomial_totalDegree_le (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (ε : ℚ) :
    (clearingPolynomial program entry initial ε).totalDegree ≤
      clearedDegreeBound program entry := by
  simpa only [family_card, clearedDegreeBound] using commonDenominator_degree_le
    (rationalFamily program entry initial ε) (rationalFamily_degreesLE program entry initial ε)

theorem clearedField_totalDegree_le (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (ε : ℚ)
    (i : LiftCoordinate program entry initial ε) :
    (clearedField program entry initial ε i).totalDegree ≤ clearedDegreeBound program entry := by
  simpa only [family_card, clearedDegreeBound] using clearedNumerator_degree_le
    (rationalFamily program entry initial ε)
    (rationalFamily_degreesLE program entry initial ε) (some i)

theorem clearedOutput_totalDegree_le (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (ε : ℚ) :
    (clearedOutput program entry initial ε).totalDegree ≤ clearedDegreeBound program entry := by
  simpa only [family_card, clearedDegreeBound] using clearedNumerator_degree_le
    (rationalFamily program entry initial ε) (rationalFamily_degreesLE program entry initial ε) none

theorem rationalFamily_denominator_one_le (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1)
    (y : LiftCoordinate program entry initial ε → ℝ)
    (i : Option (LiftCoordinate program entry initial ε)) :
    1 ≤ polynomialValue y (rationalFamily program entry initial ε i).denominator := by
  cases i with
  | none => exact rationalOutput_denominator_one_le program entry initial hε hεOne y
  | some i => exact rationalField_denominator_one_le program entry initial hε hεOne y i

/-- The common clearing polynomial is positive on the entire lifted
space, not only on the canonical root graph. -/
theorem clearingPolynomial_one_le (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1)
    (y : LiftCoordinate program entry initial ε → ℝ) :
    1 ≤ polynomialValue y (clearingPolynomial program entry initial ε) :=
  commonDenominator_one_le _ y (rationalFamily_denominator_one_le program entry initial hε hεOne y)

/-- Every jointly cleared coordinate equals its original rational value
times the same positive multiplier. -/
theorem clearedFamily_value (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1)
    (y : LiftCoordinate program entry initial ε → ℝ)
    (i : Option (LiftCoordinate program entry initial ε)) :
    polynomialValue y (clearedNumerator (rationalFamily program entry initial ε) i) =
      polynomialValue y (clearingPolynomial program entry initial ε) *
        value y (rationalFamily program entry initial ε i) :=
  clearedNumerator_value _ y
    (rationalFamily_denominator_one_le program entry initial hε hεOne y) i

end

end Stability.Simulation.ClockedMonitor
