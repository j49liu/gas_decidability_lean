import Stability.Simulation.RegisterTransition
import Stability.Simulation.FormulaResources

/-!
# Absolute-value formulas for the actual transition map

Each coordinate is compiled to the finite rational `AbsFormula` syntax.
Evaluation recovers the literal real INC/DEC transition map. For a fixed
program and entry label, changing the initial registers changes only
constant values, not the syntax tree or coordinate labels.

These are explicit syntax constructions and semantic proofs. A theorem
about primitive-recursive raw-code encodings is a separate obligation.

Source: Section 3, https://arxiv.org/html/2609.22058v2#S3.
-/

namespace Stability.Simulation

namespace AbsFormula

variable {σ : Type*}

/-- Subtraction encoded using addition, multiplication, and a rational constant. -/
def sub (e f : AbsFormula σ) : AbsFormula σ := .add e (.mul (.constant (-1)) f)

/-- The positive part, with no semantic branch in the syntax. -/
def positivePart (e : AbsFormula σ) : AbsFormula σ :=
  .mul (.constant (1 / 2)) (.add e (.abs e))

/-- Clamping to the unit interval as an absolute-value formula. -/
def clamp (e : AbsFormula σ) : AbsFormula σ :=
  .mul (.constant (1 / 2)) (.add (sub (.abs e) (.abs (e.sub (.constant 1)))) (.constant 1))

def labelGateFormula (e : AbsFormula σ) : AbsFormula σ :=
  clamp (sub (.constant 2) (.mul (.constant 8) (.abs e)))

def zeroGateFormula (e : AbsFormula σ) : AbsFormula σ :=
  clamp (sub (.constant (3 / 2)) (.mul (.constant 2) e))

/-- A fixed-order sum over a finite coordinate family, retaining zero terms. -/
def sumFin : {n : ℕ} → (Fin n → AbsFormula σ) → AbsFormula σ
  | 0, _ => .constant 0
  | n + 1, f => .add (f 0) (sumFin (fun i : Fin n ↦ f i.succ))

@[simp] theorem eval_sub (x : σ → ℝ) (e f : AbsFormula σ) :
    eval x (e.sub f) = eval x e - eval x f := by
  simp [sub, eval, sub_eq_add_neg]

@[simp] theorem eval_positivePart (x : σ → ℝ) (e : AbsFormula σ) :
    eval x (positivePart e) = max (eval x e) 0 := by
  rcases le_total 0 (eval x e) with h | h
  · simp [positivePart, eval, abs_of_nonneg h, max_eq_left h]
    ring
  · simp [positivePart, eval, abs_of_nonpos h, max_eq_right h]

@[simp] theorem eval_clamp (x : σ → ℝ) (e : AbsFormula σ) :
    eval x (clamp e) = unitClamp (eval x e) := by
  rw [unitClamp_eq_abs]
  simp [clamp, eval, sub, sub_eq_add_neg]
  ring

@[simp] theorem eval_labelGateFormula (x : σ → ℝ) (e : AbsFormula σ) :
    eval x (labelGateFormula e) = labelGate (eval x e) := by
  simp [labelGateFormula, eval, labelGate]

@[simp] theorem eval_zeroGateFormula (x : σ → ℝ) (e : AbsFormula σ) :
    eval x (zeroGateFormula e) = zeroGate (eval x e) := by
  simp [zeroGateFormula, eval, zeroGate]

@[simp] theorem eval_sumFin (x : σ → ℝ) {n : ℕ} (f : Fin n → AbsFormula σ) :
    eval x (sumFin f) = ∑ i : Fin n, eval x (f i) := by
  induction n with
  | zero => simp [sumFin, eval]
  | succ n ih => simp [sumFin, eval, ih, Fin.sum_univ_succ]

end AbsFormula

namespace RegisterTransition

open MachineCoordinate

variable {k s : ℕ}

/-- Rational encoding of a machine label, with zero reserved for restart. -/
def rationalLabel : Option (Fin s) → ℚ
  | none => (s : ℚ) + 1
  | some q => (q.val : ℚ) + 1

@[simp] theorem rationalLabel_cast (q : Option (Fin s)) :
    (rationalLabel q : ℝ) = realLabel q := by
  cases q <;> simp [rationalLabel, realLabel]

def resetFormula (entry : Fin s) (initial : Fin k → ℕ) :
    MachineCoordinate k → AbsFormula (MachineCoordinate k)
  | .budget => .add (.positivePart (.coordinate budget)) (.constant 1)
  | .countdown => .add (.positivePart (.coordinate budget)) (.constant 1)
  | .label => .constant (rationalLabel (some entry))
  | .register i => .constant (initial i)

def haltFormula : MachineCoordinate k → AbsFormula (MachineCoordinate k)
  | .label => .constant ((s : ℚ) + 1)
  | coordinate => .coordinate coordinate

def instructionFormula (instruction : RegisterMachine.Instruction k s) :
    MachineCoordinate k → AbsFormula (MachineCoordinate k) :=
  let available : AbsFormula (MachineCoordinate k) :=
    .sub (.constant 1) (.zeroGateFormula (.coordinate countdown))
  match instruction with
  | .inc i next => fun
      | .budget => .coordinate budget
      | .countdown => .sub (.coordinate countdown) (.constant 1)
      | .label => .mul available (.constant (rationalLabel next))
      | .register j => .add (.coordinate (.register j))
          (if j = i then available else .constant 0)
  | .dec i zero positive =>
      let isZero := AbsFormula.zeroGateFormula (.coordinate (.register i))
      fun
      | .budget => .coordinate budget
      | .countdown => .sub (.coordinate countdown) (.constant 1)
      | .label => .mul available
          (.add (.mul isZero (.constant (rationalLabel zero)))
            (.mul (.sub (.constant 1) isZero) (.constant (rationalLabel positive))))
      | .register j => .sub (.coordinate (.register j))
          (if j = i then .mul available (.sub (.constant 1) isZero) else .constant 0)

/-- The finite formula family for the global map, without executing the program. -/
def transitionFormula (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (coordinate : MachineCoordinate k) :
    AbsFormula (MachineCoordinate k) :=
  .add
    (.add (haltFormula (s := s) coordinate)
      (.mul (.labelGateFormula (.coordinate label))
        ((resetFormula entry initial coordinate).sub (haltFormula (s := s) coordinate))))
    (.sumFin fun q : Fin s ↦
      .mul (.labelGateFormula (.sub (.coordinate label) (.constant (rationalLabel (some q)))))
        ((instructionFormula (program q) coordinate).sub (haltFormula (s := s) coordinate)))

@[simp] theorem eval_resetFormula (entry : Fin s) (initial : Fin k → ℕ)
    (x : MachineCoordinate k → ℝ) (coordinate : MachineCoordinate k) :
    AbsFormula.eval x (resetFormula entry initial coordinate) =
      resetBranch entry initial x coordinate := by
  cases coordinate <;> simp [resetFormula, resetBranch, AbsFormula.eval]

@[simp] theorem eval_haltFormula (x : MachineCoordinate k → ℝ)
    (coordinate : MachineCoordinate k) :
    AbsFormula.eval x (haltFormula (s := s) coordinate) = haltBranch (s := s) x coordinate := by
  cases coordinate <;> simp [haltFormula, haltBranch, AbsFormula.eval]

@[simp] theorem eval_instructionFormula (instruction : RegisterMachine.Instruction k s)
    (x : MachineCoordinate k → ℝ) (coordinate : MachineCoordinate k) :
    AbsFormula.eval x (instructionFormula instruction coordinate) =
      instructionBranch instruction x coordinate := by
  cases instruction <;> cases coordinate <;>
    simp [instructionFormula, instructionBranch, AbsFormula.eval, apply_ite] <;>
    split_ifs <;> simp_all

/-- Evaluating the generated formula family gives the actual real transition map. -/
theorem eval_transitionFormula (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (x : MachineCoordinate k → ℝ)
    (coordinate : MachineCoordinate k) :
    AbsFormula.eval x (transitionFormula program entry initial coordinate) =
      transitionMap program entry initial x coordinate := by
  simp [transitionFormula, transitionMap, AbsFormula.eval]

/-- Changing the loaded input changes only constants, even when distinct
constant occurrences had the same value before the change. -/
theorem eraseConstants_transitionFormula (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial otherInitial : Fin k → ℕ) (coordinate : MachineCoordinate k) :
    AbsFormula.eraseConstants (transitionFormula program entry initial coordinate) =
      AbsFormula.eraseConstants (transitionFormula program entry otherInitial coordinate) := by
  have hreset : AbsFormula.eraseConstants (resetFormula entry initial coordinate) =
      AbsFormula.eraseConstants (resetFormula entry otherInitial coordinate) := by
    cases coordinate <;> rfl
  simp only [transitionFormula, AbsFormula.eraseConstants, AbsFormula.sub, hreset]

/-- Fixed shape gives input-independent radical counts and majorant degree
bounds, without asserting anything about raw-code computation. -/
theorem transitionFormula_resources_eq (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial otherInitial : Fin k → ℕ) (coordinate : MachineCoordinate k) :
    AbsFormula.majorantDegreeBound (transitionFormula program entry initial coordinate) =
        AbsFormula.majorantDegreeBound (transitionFormula program entry otherInitial coordinate) ∧
      AbsFormula.radicalCount (transitionFormula program entry initial coordinate) =
        AbsFormula.radicalCount (transitionFormula program entry otherInitial coordinate) :=
  AbsFormula.resources_eq_of_eraseConstants_eq
    (eraseConstants_transitionFormula program entry initial otherInitial coordinate)

end RegisterTransition

end Stability.Simulation
