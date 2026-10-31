import Stability.Computability.ClockedMonitorRadicalCode
import Stability.Computability.PolynomialErrorWeightCast
import Stability.Simulation.ClockedMonitorPenalty

/-!
# Input-effective error weight and penalty of the monitor

The code uses the fixed root count and the fixed formula order. Equal-root
casts and the formula-position equivalence identify its decoded polynomial
with the existing monitor penalty. The casts appear only in the correctness
proof: the primitive-recursive program operates on one fixed code space.
-/

namespace Stability.ClockedMonitorCode

open HGAS Simulation PolynomialErrorWeightCode

noncomputable section

variable {k s n : ℕ}

def orderedOutputNumeratorCode (program : RegisterMachine.Program k s) (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n)
    (i : Fin (Fintype.card (Option (MonitorCoordinate k)))) :
    (Fin k → ℕ) → PolynomialCode n :=
  fun initial ↦ (outputCode program entry ε e ((ClockedMonitor.formulaOrder k).symm i) initial).1

theorem orderedOutputNumeratorCode_primrec (program : RegisterMachine.Program k s)
    (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n)
    (i : Fin (Fintype.card (Option (MonitorCoordinate k)))) :
    Primrec (orderedOutputNumeratorCode program entry ε e i) :=
  Primrec.fst.comp (outputCode_primrec program entry ε e _)

def errorWeightCode (program : RegisterMachine.Program k s) (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n) :
    (Fin k → ℕ) → PolynomialCode n :=
  fun initial ↦ familyWeight e (fun j ↦ radicandCode program entry ε e j initial)
    (fun i ↦ orderedOutputNumeratorCode program entry ε e i initial)

def penaltyCode (program : RegisterMachine.Program k s) (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n) :
    (Fin k → ℕ) → PolynomialCode n :=
  fun initial ↦ penalty e MonitorCoordinate.clock
    (fun j ↦ radicandCode program entry ε e j initial)
    (fun i ↦ orderedOutputNumeratorCode program entry ε e i initial)

theorem errorWeightCode_primrec (program : RegisterMachine.Program k s) (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n) :
    Primrec (errorWeightCode program entry ε e) :=
  familyWeight_primrec e (fun initial j ↦ radicandCode program entry ε e j initial)
    (fun initial i ↦ orderedOutputNumeratorCode program entry ε e i initial)
    (radicandCode_primrec program entry ε e) (orderedOutputNumeratorCode_primrec program entry ε e)

theorem penaltyCode_primrec (program : RegisterMachine.Program k s) (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n) :
    Primrec (penaltyCode program entry ε e) :=
  penalty_primrec e MonitorCoordinate.clock
    (fun initial j ↦ radicandCode program entry ε e j initial)
    (fun initial i ↦ orderedOutputNumeratorCode program entry ε e i initial)
    (radicandCode_primrec program entry ε e) (orderedOutputNumeratorCode_primrec program entry ε e)

set_option maxHeartbeats 800000 in
-- Projection elaboration compares the generated monitor's dependent root-coordinate types.
theorem decode_orderedOutputNumeratorCode (program : RegisterMachine.Program k s)
    (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n)
    (i : Fin (Fintype.card (Option (MonitorCoordinate k)))) (initial : Fin k → ℕ) :
    PolynomialCode.decode (orderedOutputNumeratorCode program entry ε e i initial) =
      MvPolynomial.rename (coordinateEquiv program entry ε e initial)
        (CompiledFormulaLift.outputAt (ClockedMonitor.precision program entry initial ε)
          (ClockedMonitor.formulaList program entry initial)
          (ClockedMonitor.formulaPosition program entry initial
            ((ClockedMonitor.formulaOrder k).symm i))).numerator := by
  have h := congrArg (fun p : MvPolynomial (Fin n) ℚ × ℕ ↦ p.1)
    (decode_outputCode program entry ε e ((ClockedMonitor.formulaOrder k).symm i) initial)
  simpa only [orderedOutputNumeratorCode] using h

def outputPositionEquiv (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) : Fin (Fintype.card (Option (MonitorCoordinate k))) ≃
      Fin (ClockedMonitor.formulaList program entry initial).length :=
  finCongr (by simp [ClockedMonitor.formulaList, AbsFormula.familyList])

set_option maxHeartbeats 800000 in
-- The two position presentations unfold the fixed finite monitor formula enumeration.
theorem outputPositionEquiv_apply (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) (i : Fin (Fintype.card (Option (MonitorCoordinate k)))) :
    outputPositionEquiv program entry initial i =
      ClockedMonitor.formulaPosition program entry initial
        ((ClockedMonitor.formulaOrder k).symm i) := by
  apply Fin.ext
  simp only [outputPositionEquiv, ClockedMonitor.formulaPosition, AbsFormula.familyPosition,
    finCongr_apply, Fin.val_cast, Equiv.apply_symm_apply]

theorem sum_formulaPositions {A : Type*} [AddCommMonoid A]
    (program : RegisterMachine.Program k s) (entry : Fin s) (initial : Fin k → ℕ)
    (f : Fin (ClockedMonitor.formulaList program entry initial).length → A) :
    (∑ i, f (ClockedMonitor.formulaPosition program entry initial
      ((ClockedMonitor.formulaOrder k).symm i))) = ∑ j, f j := by
  simpa only [outputPositionEquiv_apply] using
    (outputPositionEquiv program entry initial).sum_comp f

set_option maxHeartbeats 800000 in
-- Reindexing the actual family requires comparing its dependent generated root spaces.
theorem errorWeight_eq_ordered (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) (ε : ℚ) :
    ClockedMonitor.errorWeight program entry initial ε =
      1 + ∑ i : Fin (Fintype.card (Option (MonitorCoordinate k))),
        RadicalDefectBounds.polynomialWeight
          (AbsFormula.finiteRadicalFamily (ClockedMonitor.precision program entry initial ε)
            (ClockedMonitor.formulaList program entry initial)).radicands
          (CompiledFormulaLift.outputAt (ClockedMonitor.precision program entry initial ε)
            (ClockedMonitor.formulaList program entry initial)
            (ClockedMonitor.formulaPosition program entry initial
              ((ClockedMonitor.formulaOrder k).symm i))).numerator := by
  unfold ClockedMonitor.errorWeight CompiledFormulaLift.familyErrorWeight
    CompiledFormulaLift.outputErrorWeight
  exact congrArg (fun p : MvPolynomial (ClockedMonitor.LiftCoordinate program entry initial ε) ℚ ↦
    1 + p) (sum_formulaPositions program entry initial (fun j ↦
    RadicalDefectBounds.polynomialWeight
      (AbsFormula.finiteRadicalFamily (ClockedMonitor.precision program entry initial ε)
        (ClockedMonitor.formulaList program entry initial)).radicands
      (CompiledFormulaLift.outputAt (ClockedMonitor.precision program entry initial ε)
        (ClockedMonitor.formulaList program entry initial) j).numerator)).symm

theorem decode_errorWeightCode (program : RegisterMachine.Program k s) (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n)
    (initial : Fin k → ℕ) :
    PolynomialCode.decode (errorWeightCode program entry ε e initial) =
      MvPolynomial.rename (coordinateEquiv program entry ε e initial)
        (ClockedMonitor.errorWeight program entry initial ε) := by
  rw [errorWeight_eq_ordered]
  exact decode_familyWeight_cast (ClockedMonitor.rootCount_eq_fixed program entry initial ε) e
    (fun j ↦ radicandCode program entry ε e j initial) _
    (fun j ↦ decode_radicandCode program entry ε e j initial)
    (fun i ↦ orderedOutputNumeratorCode program entry ε e i initial) _
    (fun i ↦ decode_orderedOutputNumeratorCode program entry ε e i initial)

theorem decode_penaltyCode (program : RegisterMachine.Program k s) (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n)
    (initial : Fin k → ℕ) :
    PolynomialCode.decode (penaltyCode program entry ε e initial) =
      MvPolynomial.rename (coordinateEquiv program entry ε e initial)
        (ClockedMonitor.penaltyPolynomial program entry initial ε) := by
  rw [ClockedMonitor.penaltyPolynomial, errorWeight_eq_ordered]
  exact decode_penalty_cast (ClockedMonitor.rootCount_eq_fixed program entry initial ε) e
    MonitorCoordinate.clock (fun j ↦ radicandCode program entry ε e j initial) _
    (fun j ↦ decode_radicandCode program entry ε e j initial)
    (fun i ↦ orderedOutputNumeratorCode program entry ε e i initial) _
    (fun i ↦ decode_orderedOutputNumeratorCode program entry ε e i initial)

end

end Stability.ClockedMonitorCode
