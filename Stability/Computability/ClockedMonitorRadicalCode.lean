import Stability.Computability.ClockedMonitorTemplate
import Stability.Computability.FormulaPrecisionCode
import Stability.Computability.FiniteFormulaRadicalCode
import Stability.Simulation.ClockedMonitorClearing

/-!
# Input-effective finite radical data for the actual monitor

The program, smoothing accuracy, finite formula order, and extended
coordinate equivalence are fixed. The initial natural registers are the
only input. The decoded codes equal the actual precision, radicands, and
stored output fractions after the proved fixed-dimension coordinate cast.
-/

namespace Stability.ClockedMonitorCode

open HGAS Simulation FormulaTemplate

noncomputable section

variable {k s n : ℕ}

def templates (program : RegisterMachine.Program k s) (entry : Fin s) :
    List (FormulaTemplate (Fin k → ℕ) (MonitorCoordinate k)) :=
  List.ofFn fun i ↦
    ClockedMonitorTemplate.formulas program entry ((ClockedMonitor.formulaOrder k).symm i)

@[simp]
theorem instantiate_templates (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) :
    (templates program entry).map (instantiate · initial) =
      ClockedMonitor.formulaList program entry initial := by
  simp only [templates, ClockedMonitor.formulaList, AbsFormula.familyList, List.map_ofFn]
  congr 1
  funext i
  exact ClockedMonitorTemplate.instantiate_formulas program entry initial _

theorem primitiveConstants_templates (program : RegisterMachine.Program k s) (entry : Fin s) :
    ∀ f ∈ templates program entry, PrimitiveConstants f := by
  intro f hf
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
  exact ClockedMonitorTemplate.primitiveConstants_formulas program entry _

def precisionCode (program : RegisterMachine.Program k s) (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n) :
    (Fin k → ℕ) → PolynomialCode n :=
  FormulaTemplate.precisionCode (ClockedMonitor.formulaOrder k) (fun i ↦ e (.inl i))
    (ClockedMonitorTemplate.formulas program entry) MonitorCoordinate.clock ε

theorem precisionCode_primrec (program : RegisterMachine.Program k s) (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n) :
    Primrec (precisionCode program entry ε e) :=
  FormulaTemplate.precisionCode_primrec _ _ _ _ ε
    (ClockedMonitorTemplate.primitiveConstants_formulas program entry)

theorem decode_precisionCode (program : RegisterMachine.Program k s) (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n)
    (initial : Fin k → ℕ) :
    PolynomialCode.decode (precisionCode program entry ε e initial) =
      MvPolynomial.rename (fun i ↦ e (.inl i))
        (ClockedMonitor.precision program entry initial ε) := by
  simpa only [ClockedMonitorTemplate.instantiate_formulas] using
    FormulaTemplate.decode_precisionCode (ClockedMonitor.formulaOrder k)
      (fun i ↦ e (.inl i)) (ClockedMonitorTemplate.formulas program entry)
      MonitorCoordinate.clock ε initial

/-- Reindex the actual input-dependent lift into the fixed extended space. -/
def coordinateEquiv (program : RegisterMachine.Program k s) (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n)
    (initial : Fin k → ℕ) : ClockedMonitor.LiftCoordinate program entry initial ε ≃ Fin n :=
  (Equiv.sumCongr (Equiv.refl _)
    (finCongr (ClockedMonitor.rootCount_eq_fixed program entry initial ε)))
    |>.trans e

theorem coordinateEquiv_coe (program : RegisterMachine.Program k s) (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n)
    (initial : Fin k → ℕ) :
    ⇑(coordinateEquiv program entry ε e initial) =
      e ∘ Sum.map id (Fin.cast (ClockedMonitor.rootCount_eq_fixed program entry initial ε)) := rfl

def radicandCode (program : RegisterMachine.Program k s) (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n)
    (j : Fin (ClockedMonitor.fixedRootCount program entry)) : (Fin k → ℕ) → PolynomialCode n :=
  FormulaTemplate.radicandCode e (precisionCode program entry ε e) (templates program entry) j

theorem radicandCode_primrec (program : RegisterMachine.Program k s) (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n)
    (j : Fin (ClockedMonitor.fixedRootCount program entry)) :
    Primrec (radicandCode program entry ε e j) :=
  FormulaTemplate.radicandCode_primrec e _ (precisionCode_primrec program entry ε e)
    (templates program entry) (primitiveConstants_templates program entry) j

/-- Exact decoded radicands, with the explicit fixed-root index cast. -/
theorem decode_radicandCode (program : RegisterMachine.Program k s) (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n)
    (j : Fin (ClockedMonitor.fixedRootCount program entry)) (initial : Fin k → ℕ) :
    PolynomialCode.decode (radicandCode program entry ε e j initial) =
      MvPolynomial.rename (coordinateEquiv program entry ε e initial)
        ((AbsFormula.finiteRadicalFamily (ClockedMonitor.precision program entry initial ε)
          (ClockedMonitor.formulaList program entry initial)).radicands
            (j.cast (ClockedMonitor.rootCount_eq_fixed program entry initial ε).symm)) := by
  rw [coordinateEquiv_coe]
  exact FormulaTemplate.decode_radicandCode_of_formulaList_eq e
    (precisionCode program entry ε e) (fun x ↦ ClockedMonitor.precision program entry x ε)
    (decode_precisionCode program entry ε e) (templates program entry) initial
    (ClockedMonitor.formulaList program entry initial) (instantiate_templates program entry initial)
    (ClockedMonitor.rootCount_eq_fixed program entry initial ε) j

def position (program : RegisterMachine.Program k s) (entry : Fin s)
    (i : Option (MonitorCoordinate k)) : Fin (templates program entry).length :=
  (ClockedMonitor.formulaOrder k i).cast (List.length_ofFn).symm

def outputCode (program : RegisterMachine.Program k s) (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n)
    (i : Option (MonitorCoordinate k)) : (Fin k → ℕ) → PowerFractionCode n :=
  FormulaTemplate.outputCode e (precisionCode program entry ε e) (templates program entry)
    (position program entry i)

theorem outputCode_primrec (program : RegisterMachine.Program k s) (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n)
    (i : Option (MonitorCoordinate k)) : Primrec (outputCode program entry ε e i) :=
  FormulaTemplate.outputCode_primrec e _ (precisionCode_primrec program entry ε e)
    (templates program entry) (primitiveConstants_templates program entry)
    (position program entry i)

set_option maxHeartbeats 800000 in
-- Dependent list-position casts expose the monitor's large fixed syntax tree during elaboration.
/-- Exact stored output fractions at the actual monitor's formula positions. -/
theorem decode_outputCode (program : RegisterMachine.Program k s) (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n)
    (i : Option (MonitorCoordinate k)) (initial : Fin k → ℕ) :
    let f := CompiledFormulaLift.outputAt (ClockedMonitor.precision program entry initial ε)
      (ClockedMonitor.formulaList program entry initial)
      (ClockedMonitor.formulaPosition program entry initial i)
    (PolynomialCode.decode (outputCode program entry ε e i initial).1,
      (outputCode program entry ε e i initial).2) =
        (MvPolynomial.rename (coordinateEquiv program entry ε e initial) f.numerator,
          f.exponent) := by
  rw [coordinateEquiv_coe]
  have h := FormulaTemplate.decode_outputCode_of_formulaList_eq e
    (precisionCode program entry ε e) (fun x ↦ ClockedMonitor.precision program entry x ε)
    (decode_precisionCode program entry ε e) (templates program entry) initial
    (ClockedMonitor.formulaList program entry initial) (instantiate_templates program entry initial)
    (ClockedMonitor.rootCount_eq_fixed program entry initial ε)
    (position program entry i)
  have hget := List.getD_eq_get
    (AbsFormula.finiteRadicalFamily (ClockedMonitor.precision program entry initial ε)
      (ClockedMonitor.formulaList program entry initial)).outputs
    (⟨0, 0⟩ : PowerFraction (ClockedMonitor.LiftCoordinate program entry initial ε))
    ((ClockedMonitor.formulaPosition program entry initial i).cast
      (AbsFormula.finiteRadicalFamily_counts _ _).2.symm)
  change (AbsFormula.finiteRadicalFamily (ClockedMonitor.precision program entry initial ε)
    (ClockedMonitor.formulaList program entry initial)).outputs.getD
      (position program entry i).val ⟨0, 0⟩ = _ at hget
  rw [hget] at h
  exact h

end

end Stability.ClockedMonitorCode
