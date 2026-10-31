import Stability.Computability.FormulaTemplate

/-!
# The actual monitor as a fixed effective formula template

Only the reset branch reads the initial registers. All other formulas
are fixed constants of the compiler. The equalities below concern the
literal syntax trees, so they preserve radical allocation and all later
structural majorants, not merely real-valued evaluations.
-/

namespace Stability

open HGAS Simulation FormulaTemplate

namespace RegisterTransitionTemplate

variable {k s : ℕ}

def reset (entry : Fin s) :
    MachineCoordinate k → FormulaTemplate (Fin k → ℕ) (MachineCoordinate k)
  | .register i => .constant (fun initial ↦ RationalCode.ofNat (initial i))
  | c => ofFormula (RegisterTransition.resetFormula entry (fun _ ↦ 0) c)

@[simp]
theorem instantiate_reset (entry : Fin s) (initial : Fin k → ℕ)
    (coordinate : MachineCoordinate k) :
    (reset entry coordinate).instantiate initial =
      RegisterTransition.resetFormula entry initial coordinate := by
  cases coordinate <;> simp [reset, FormulaTemplate.instantiate,
    RegisterTransition.resetFormula]

theorem primitiveConstants_reset (entry : Fin s) (coordinate : MachineCoordinate k) :
    PrimitiveConstants (reset entry coordinate) := by
  cases coordinate with
  | register i =>
    exact RationalCode.ofNat_primrec.comp
      (Primrec.fin_app.comp Primrec.id (Primrec.const i))
  | budget | countdown | label => exact primitiveConstants_ofFormula _

/-- The only input-dependent subtree is the reset formula. -/
def transition (program : RegisterMachine.Program k s) (entry : Fin s)
    (coordinate : MachineCoordinate k) : FormulaTemplate (Fin k → ℕ) (MachineCoordinate k) :=
  .add
    (.add (ofFormula (RegisterTransition.haltFormula (s := s) coordinate))
      (.mul (ofFormula (.labelGateFormula (.coordinate .label)))
        ((reset entry coordinate).sub
          (ofFormula (RegisterTransition.haltFormula (s := s) coordinate)))))
    (ofFormula (.sumFin fun q : Fin s ↦
      .mul (.labelGateFormula (.sub (.coordinate .label)
        (.constant (RegisterTransition.rationalLabel (some q)))))
        ((RegisterTransition.instructionFormula (program q) coordinate).sub
          (RegisterTransition.haltFormula (s := s) coordinate))))

@[simp]
theorem instantiate_transition (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) (coordinate : MachineCoordinate k) :
    (transition program entry coordinate).instantiate initial =
      RegisterTransition.transitionFormula program entry initial coordinate := by
  simp [transition, FormulaTemplate.instantiate, RegisterTransition.transitionFormula]

theorem primitiveConstants_transition (program : RegisterMachine.Program k s)
    (entry : Fin s) (coordinate : MachineCoordinate k) :
    PrimitiveConstants (transition program entry coordinate) :=
  ⟨⟨primitiveConstants_ofFormula _, primitiveConstants_ofFormula _,
    (primitiveConstants_reset entry coordinate).sub (primitiveConstants_ofFormula _)⟩,
    primitiveConstants_ofFormula _⟩

end RegisterTransitionTemplate

namespace ClockedMonitorTemplate

variable {k s : ℕ}

def field (program : RegisterMachine.Program k s) (entry : Fin s) :
    MonitorCoordinate k → FormulaTemplate (Fin k → ℕ) (MonitorCoordinate k)
  | .b i =>
      .mul (ofFormula (.mul ClockedMonitor.rateFormula (.positivePart (.coordinate .u))))
        (.pow (.sub
          (.mapCoordinates MonitorCoordinate.a
            (RegisterTransitionTemplate.transition program entry i))
          (.coordinate (.b i))) 3)
  | c => ofFormula (ClockedMonitor.fieldFormula program entry (fun _ ↦ 0) c)

@[simp]
theorem instantiate_field (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) (coordinate : MonitorCoordinate k) :
    (field program entry coordinate).instantiate initial =
      ClockedMonitor.fieldFormula program entry initial coordinate := by
  cases coordinate <;> simp [field, FormulaTemplate.instantiate, ClockedMonitor.fieldFormula]

theorem primitiveConstants_field (program : RegisterMachine.Program k s)
    (entry : Fin s) (coordinate : MonitorCoordinate k) :
    PrimitiveConstants (field program entry coordinate) := by
  cases coordinate with
  | b i =>
    have ht := PrimitiveConstants.mapCoordinates
      (RegisterTransitionTemplate.primitiveConstants_transition program entry i) MonitorCoordinate.a
    exact ⟨primitiveConstants_ofFormula _,
      (ht.sub (show PrimitiveConstants
        (.coordinate (.b i) : FormulaTemplate (Fin k → ℕ) (MonitorCoordinate k))
          from trivial)).pow 3⟩
  | clock | u | v | a i => exact primitiveConstants_ofFormula _

/-- `none` denotes the output and `some i` denotes field coordinate `i`. -/
def formulas (program : RegisterMachine.Program k s) (entry : Fin s) :
    Option (MonitorCoordinate k) → FormulaTemplate (Fin k → ℕ) (MonitorCoordinate k)
  | none => ofFormula ClockedMonitor.outputFormula
  | some i => field program entry i

@[simp]
theorem instantiate_formulas (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) (coordinate : Option (MonitorCoordinate k)) :
    (formulas program entry coordinate).instantiate initial =
      ClockedMonitor.formulas program entry initial coordinate := by
  cases coordinate <;> simp [formulas, ClockedMonitor.formulas]

theorem primitiveConstants_formulas (program : RegisterMachine.Program k s)
    (entry : Fin s) (coordinate : Option (MonitorCoordinate k)) :
    PrimitiveConstants (formulas program entry coordinate) := by
  cases coordinate with
  | none => exact primitiveConstants_ofFormula _
  | some i => exact primitiveConstants_field program entry i

/-- The actual monitor's majorants have primitive-recursive sparse codes
in every fixed finite coordinate encoding. -/
theorem majorants_primrec {n : ℕ} (r : MonitorCoordinate k → Fin n)
    (program : RegisterMachine.Program k s) (entry : Fin s)
    (coordinate : Option (MonitorCoordinate k)) :
    Primrec (majorantsCode r (formulas program entry coordinate)) :=
  majorantsCode_primrec r _ (primitiveConstants_formulas program entry coordinate)

end ClockedMonitorTemplate

end Stability
