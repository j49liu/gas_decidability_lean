import Stability.Computability.RegisterMachineStackBlocks
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Finite-control dispatch for compiled stack instructions

A block family is allocated in disjoint finite label ranges, one range
per finite local-store value. All ranges share a supplied continuation
program. Thus the compiled program is fixed while the initial control
label, rather than the program, carries the local store.
-/

namespace Stability.RegisterMachine

variable {k a b m n s : ℕ}

/-- Reindex active control labels without changing register values. -/
def Configuration.reindex (e : Fin m → Fin n) (c : Configuration k m) : Configuration k n :=
  ⟨c.label.map e, c.registers⟩

theorem execute_reindex (e : Fin m → Fin n) (i : Instruction k m) (r : Fin k → ℕ) :
    execute (i.reindex e) r = (execute i r).reindex e := by
  cases i with
  | inc j next => rfl
  | dec j zero positive =>
      by_cases h : r j = 0 <;> simp [execute, Instruction.reindex, Configuration.reindex, h]

/-- A literal code relabelling commutes with total execution. -/
theorem step_reindex {P : Program k m} {Q : Program k n} (e : Fin m → Fin n)
    (hcode : ∀ q, Q (e q) = (P q).reindex e) (c : Configuration k m) :
    step Q (c.reindex e) = (step P c).reindex e := by
  cases c with
  | mk label r =>
      cases label with
      | none => rfl
      | some q =>
          change execute (Q (e q)) r = (execute (P q) r).reindex e
          rw [hcode, execute_reindex]

theorem run_reindex {P : Program k m} {Q : Program k n} (e : Fin m → Fin n)
    (hcode : ∀ q, Q (e q) = (P q).reindex e) (steps : ℕ) (c : Configuration k m) :
    run Q steps (c.reindex e) = (run P steps c).reindex e := by
  induction steps generalizing c with
  | zero => rfl
  | succ steps ih => rw [run_succ, run_succ, step_reindex e hcode, ih]

/-- Once control enters the allocated continuation, its own execution is
unchanged except for the fixed label offset. -/
theorem run_assembleBlock_continuation (body : Fin m → Instruction k (m + n))
    (continuation : Program k n) (steps : ℕ) (c : Configuration k n) :
    run (assembleBlock body continuation) steps (c.reindex (Fin.natAdd m)) =
      (run continuation steps c).reindex (Fin.natAdd m) :=
  run_reindex (Fin.natAdd m) (assembleBlock_right body continuation) steps c

/-- Labels of one selected block, followed by the shared continuation. -/
def dispatchLabel (i : Fin a) : Fin (b + n) → Fin (a * b + n) :=
  Fin.addCases (fun q ↦ (finProdFinEquiv (i, q)).castAdd n) (Fin.natAdd (a * b))

/-- Allocate all members of a finite family of internal blocks. -/
def dispatchBlockCode (body : Fin a → Fin b → Instruction k (b + n)) :
    Fin (a * b) → Instruction k (a * b + n) :=
  fun q ↦
    let iq := finProdFinEquiv.symm q
    (body iq.1 iq.2).reindex (dispatchLabel iq.1)

/-- The one fixed program containing every finite-store branch. -/
def dispatchProgram (body : Fin a → Fin b → Instruction k (b + n))
    (continuation : Program k n) : Program k (a * b + n) :=
  assembleBlock (dispatchBlockCode body) continuation

/-- The allocated code agrees instruction by instruction with each
selected local block and its shared continuation. -/
theorem dispatchProgram_code (body : Fin a → Fin b → Instruction k (b + n))
    (continuation : Program k n) (i : Fin a) (q : Fin (b + n)) :
    dispatchProgram body continuation (dispatchLabel i q) =
      (assembleBlock (body i) continuation q).reindex (dispatchLabel i) := by
  induction q using Fin.addCases with
  | left q => simp [dispatchProgram, dispatchLabel, dispatchBlockCode]
  | right q =>
      cases h : continuation q with
      | inc j next =>
          simp [dispatchProgram, dispatchLabel, h, Instruction.reindex,
            Option.map_map, Function.comp_def]
      | dec j zero positive =>
          simp [dispatchProgram, dispatchLabel, h, Instruction.reindex,
            Option.map_map, Function.comp_def]

/-- Every selected member executes inside the one allocated program. -/
theorem run_dispatchProgram (body : Fin a → Fin b → Instruction k (b + n))
    (continuation : Program k n) (i : Fin a) (steps : ℕ) (c : Configuration k (b + n)) :
    run (dispatchProgram body continuation) steps (c.reindex (dispatchLabel i)) =
      (run (assembleBlock (body i) continuation) steps c).reindex (dispatchLabel i) :=
  run_reindex (dispatchLabel i) (dispatchProgram_code body continuation i) steps c

namespace TM2Encoding

open Turing.PartrecToTM2

/-- Encode the five possible local-store values in finite control. -/
def storeCode : Option Γ' → Fin 5
  | none => 0
  | some .consₗ => 1
  | some .cons => 2
  | some .bit0 => 3
  | some .bit1 => 4

@[simp]
theorem digitSymbol_storeCode (store : Option Γ') : digitSymbol (storeCode store) = store := by
  cases store with
  | none => rfl
  | some a => cases a <;> rfl

@[simp]
theorem storeCode_digitSymbol (i : Fin 5) : storeCode (digitSymbol i) = i := by
  fin_cases i <;> rfl

/-- A finite control-table entry uses one zero test of the reserved
scratch register. It is still an ordinary DEC instruction, not a new jump. -/
def controlBlockCode (exit : Option (Fin n)) : Fin 1 → Instruction 5 (1 + n) :=
  fun _ ↦ .dec 4 (exit.map (Fin.natAdd 1)) (exit.map (Fin.natAdd 1))

/-- Five finite control-table entries implement load, branch, or goto
once their target is evaluated on the finite local store. -/
def controlDispatchProgram (exit : Option Γ' → Option (Fin n))
    (continuation : Program 5 n) : Program 5 (5 + n) :=
  dispatchProgram (fun i : Fin 5 ↦ controlBlockCode (exit (digitSymbol i))) continuation

theorem run_controlDispatchProgram (store : Option Γ') (S : K' → List Γ')
    (exit : Option Γ' → Option (Fin n)) (continuation : Program 5 n) :
    run (controlDispatchProgram exit continuation) 1
      ⟨some (dispatchLabel (storeCode store) ((0 : Fin 1).castAdd n)), encodeStacks S⟩ =
      ⟨(exit store).map (Fin.natAdd 5), encodeStacks S⟩ := by
  have h := run_dispatchProgram
    (fun i : Fin 5 ↦ controlBlockCode (exit (digitSymbol i))) continuation
    (storeCode store) 1 ⟨some ((0 : Fin 1).castAdd n), encodeStacks S⟩
  simp only [digitSymbol_storeCode] at h
  have hlocal : run (assembleBlock (controlBlockCode (exit store)) continuation) 1
      ⟨some ((0 : Fin 1).castAdd n), encodeStacks S⟩ =
      ⟨(exit store).map (Fin.natAdd 1), encodeStacks S⟩ := by
    simp [run, step, controlBlockCode, execute]
  rw [hlocal] at h
  simpa [controlDispatchProgram, Configuration.reindex, dispatchLabel,
    Option.map_map, Function.comp_def] using h

/-- One fixed sixty-label program implements push for every local-store
value. No program choice depends on the runtime store. -/
def pushDispatchProgram (j : K') (f : Option Γ' → Γ')
    (exit : Option Γ' → Option (Fin n)) (continuation : Program 5 n) : Program 5 (60 + n) :=
  dispatchProgram (fun i : Fin 5 ↦ pushBlockCode (stackRegister j) 4
    (symbolCode (f (digitSymbol i))) (exit (digitSymbol i))) continuation

/-- The push family preserves the other stacks and uses its initial
control label to select the old local store. -/
theorem run_pushDispatchProgram (j : K') (f : Option Γ' → Γ') (store : Option Γ')
    (S : K' → List Γ') (exit : Option Γ' → Option (Fin n)) (continuation : Program 5 n) :
    run (pushDispatchProgram j f exit continuation)
      ((6 * contentsCode (S j) + 1) + (2 * (5 * contentsCode (S j)) + 1) +
        ((symbolCode (f store)).val + 1))
      ⟨some (dispatchLabel (storeCode store) ((0 : Fin 12).castAdd n)), encodeStacks S⟩ =
      ⟨(exit store).map (Fin.natAdd 60), encodeStacks (Function.update S j (f store :: S j))⟩ := by
  have h := run_dispatchProgram (fun i : Fin 5 ↦ pushBlockCode (stackRegister j) 4
    (symbolCode (f (digitSymbol i))) (exit (digitSymbol i))) continuation (storeCode store)
    ((6 * contentsCode (S j) + 1) + (2 * (5 * contentsCode (S j)) + 1) +
      ((symbolCode (f store)).val + 1))
    ⟨some ((0 : Fin 12).castAdd n), encodeStacks S⟩
  simp only [digitSymbol_storeCode] at h
  change run (pushDispatchProgram j f exit continuation) _ _ =
    (run (stackPushProgram (stackRegister j) 4 (symbolCode (f store)) (exit store) continuation)
      _ _).reindex (dispatchLabel (storeCode store)) at h
  rw [run_push_stackEncoding] at h
  simpa [Configuration.reindex, dispatchLabel, Option.map_map, Function.comp_def] using h

/-- One fixed eighty-label program implements pop and the finite store
update for all old stores and all popped head options. -/
def popDispatchProgram (j : K') (f : Option Γ' → Option Γ' → Option Γ')
    (exit : Option Γ' → Option (Fin n)) (continuation : Program 5 n) : Program 5 (80 + n) :=
  dispatchProgram (fun i : Fin 5 ↦ popBlockCode (stackRegister j) 4
    (fun d ↦ exit (f (digitSymbol i) (digitSymbol d)))) continuation

theorem run_popDispatchProgram (j : K') (f : Option Γ' → Option Γ' → Option Γ')
    (store : Option Γ') (S : K' → List Γ')
    (exit : Option Γ' → Option (Fin n)) (continuation : Program 5 n) :
    run (popDispatchProgram j f exit continuation)
      ((6 * (contentsCode (S j) / 5) + contentsCode (S j) % 5 + 1) +
        (2 * (contentsCode (S j) / 5) + 1))
      ⟨some (dispatchLabel (storeCode store) ((0 : Fin 16).castAdd n)), encodeStacks S⟩ =
      ⟨(exit (f store (S j).head?)).map (Fin.natAdd 80),
        encodeStacks (Function.update S j (S j).tail)⟩ := by
  have h := run_dispatchProgram (fun i : Fin 5 ↦ popBlockCode (stackRegister j) 4
    (fun d ↦ exit (f (digitSymbol i) (digitSymbol d)))) continuation (storeCode store)
    ((6 * (contentsCode (S j) / 5) + contentsCode (S j) % 5 + 1) +
      (2 * (contentsCode (S j) / 5) + 1))
    ⟨some ((0 : Fin 16).castAdd n), encodeStacks S⟩
  simp only [digitSymbol_storeCode] at h
  change run (popDispatchProgram j f exit continuation) _ _ =
    (run (stackPopProgram (stackRegister j) 4 (fun d ↦ exit (f store (digitSymbol d))) continuation)
      _ _).reindex (dispatchLabel (storeCode store)) at h
  rw [run_pop_stackEncoding j S (fun head ↦ exit (f store head)) continuation] at h
  simpa [Configuration.reindex, dispatchLabel, Option.map_map, Function.comp_def] using h

end TM2Encoding

end Stability.RegisterMachine
