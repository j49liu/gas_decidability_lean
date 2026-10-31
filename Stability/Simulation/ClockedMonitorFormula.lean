import Stability.Simulation.ClockedMonitor

/-!
# A concrete formula family for the monitor and its output

The field coordinates and output are represented in the same finite
absolute-value syntax consumed by smoothing and radical extraction.
For a fixed program, every input changes only rational constants. Raw
encoding and primitive-recursive compiler theorems remain separate.
-/

namespace Stability.Simulation

namespace AbsFormula

variable {σ τ : Type*}

/-- Rename coordinates without changing the formula tree. -/
def mapCoordinates (rename : σ → τ) : AbsFormula σ → AbsFormula τ
  | .coordinate i => .coordinate (rename i)
  | .constant c => .constant c
  | .add e f => .add (mapCoordinates rename e) (mapCoordinates rename f)
  | .mul e f => .mul (mapCoordinates rename e) (mapCoordinates rename f)
  | .abs e => .abs (mapCoordinates rename e)

/-- Natural powers are literal repeated multiplications in the syntax. -/
def pow (e : AbsFormula σ) : ℕ → AbsFormula σ
  | 0 => .constant 1
  | n + 1 => .mul (pow e n) e

@[simp] theorem eval_mapCoordinates (rename : σ → τ) (e : AbsFormula σ) (x : τ → ℝ) :
    eval x (mapCoordinates rename e) = eval (x ∘ rename) e := by
  induction e <;> simp_all [mapCoordinates, eval, Function.comp_def]

@[simp] theorem eval_pow (e : AbsFormula σ) (n : ℕ) (x : σ → ℝ) :
    eval x (pow e n) = eval x e ^ n := by
  induction n with
  | zero => simp [pow, eval]
  | succ n ih => simp [pow, eval, ih, pow_succ]

theorem eraseConstants_mapCoordinates (rename : σ → τ) (e : AbsFormula σ) :
    eraseConstants (mapCoordinates rename e) = mapCoordinates rename (eraseConstants e) := by
  induction e <;> simp_all [mapCoordinates, eraseConstants]

end AbsFormula

namespace ClockedMonitor

open MonitorCoordinate

variable {k s : ℕ}

def rateFormula : AbsFormula (MonitorCoordinate k) :=
  .mul (.constant gain) (.pow (.add (.constant 1) (.pow (.coordinate clock) 2)) 2)

def fieldFormula (program : RegisterMachine.Program k s) (entry : Fin s) (initial : Fin k → ℕ) :
    MonitorCoordinate k → AbsFormula (MonitorCoordinate k)
  | .clock => .constant 1
  | .u => .sub (.constant 0) (.coordinate v)
  | .v => .coordinate u
  | .a i => .mul (.mul rateFormula (.positivePart (.sub (.constant 0) (.coordinate u))))
      (.pow (.sub (.coordinate (.b i)) (.coordinate (.a i))) 3)
  | .b i => .mul (.mul rateFormula (.positivePart (.coordinate u)))
      (.pow (.sub
        (.mapCoordinates MonitorCoordinate.a
          (RegisterTransition.transitionFormula program entry initial i))
        (.coordinate (.b i))) 3)

def outputFormula : AbsFormula (MonitorCoordinate k) :=
  .mul
    (.mul
      (.positivePart (.sub (.constant 1)
        (.mul (.constant 2) (.abs (.sub
          (.add (.pow (.coordinate u) 2) (.pow (.coordinate v) 2)) (.constant 1))))))
      (.positivePart (.coordinate u)))
    (.labelGateFormula (.mul (.constant 4) (.coordinate (.a MachineCoordinate.label))))

/-- `none` denotes the output formula; `some i` denotes field coordinate `i`. -/
def formulas (program : RegisterMachine.Program k s) (entry : Fin s) (initial : Fin k → ℕ) :
    Option (MonitorCoordinate k) → AbsFormula (MonitorCoordinate k)
  | none => outputFormula
  | some coordinate => fieldFormula program entry initial coordinate

@[simp] theorem eval_rateFormula (x : MonitorCoordinate k → ℝ) :
    AbsFormula.eval x rateFormula = (gain : ℝ) * (1 + x clock ^ 2) ^ 2 := by
  simp [rateFormula, AbsFormula.eval]

/-- The formulas evaluate to the actual gated vector field using the
already constructed real transition map. -/
theorem eval_fieldFormula (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (x : MonitorCoordinate k → ℝ)
    (coordinate : MonitorCoordinate k) :
    AbsFormula.eval x (fieldFormula program entry initial coordinate) =
      field program entry initial x coordinate := by
  have hA : (fun i ↦ x (.a i)) = bufferA x := rfl
  cases coordinate <;>
    simp [fieldFormula, field, AbsFormula.eval, RegisterTransition.eval_transitionFormula,
      Function.comp_def, hA]

theorem eval_outputFormula (x : MonitorCoordinate k → ℝ) :
    AbsFormula.eval x outputFormula = output x := by
  simp [outputFormula, output, amplitudeCutoff, AbsFormula.eval]

/-- Changing the loaded input does not change a field coordinate's syntax tree. -/
theorem eraseConstants_fieldFormula (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial otherInitial : Fin k → ℕ) (coordinate : MonitorCoordinate k) :
    AbsFormula.eraseConstants (fieldFormula program entry initial coordinate) =
      AbsFormula.eraseConstants (fieldFormula program entry otherInitial coordinate) := by
  cases coordinate with
  | clock => rfl
  | u => rfl
  | v => rfl
  | a i => rfl
  | b i =>
      have hshape := RegisterTransition.eraseConstants_transitionFormula
        program entry initial otherInitial i
      simp only [fieldFormula, AbsFormula.pow, AbsFormula.sub, AbsFormula.eraseConstants,
        AbsFormula.eraseConstants_mapCoordinates, hshape]

/-- The entire finite field/output family has input-independent shape. -/
theorem eraseConstants_formulas (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial otherInitial : Fin k → ℕ) (coordinate : Option (MonitorCoordinate k)) :
    AbsFormula.eraseConstants (formulas program entry initial coordinate) =
      AbsFormula.eraseConstants (formulas program entry otherInitial coordinate) := by
  cases coordinate with
  | none => rfl
  | some i => exact eraseConstants_fieldFormula program entry initial otherInitial i

end ClockedMonitor

end Stability.Simulation
