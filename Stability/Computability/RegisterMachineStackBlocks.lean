import Stability.Computability.RegisterMachineArithmetic
import Mathlib.Computability.TuringMachine.ToPartrec

/-!
# Explicit finite programs for base-five stack operations

Each block is allocated before a supplied continuation program. The
twelve-label push block and sixteen-label pop block use one value register
and one zero scratch register. The pop's five exits distinguish empty
stack from the four symbols. The other registers are unchanged.

These are executable finite INC/DEC programs. The arithmetic correctness
proofs unfold their code and invoke the instruction-level macro theorems.
-/

namespace Stability.RegisterMachine

open Function

variable {k m n : ℕ}

/-- Rename every active target of one instruction; halt remains halt. -/
def Instruction.reindex (e : Fin m → Fin n) : Instruction k m → Instruction k n
  | .inc i next => .inc i (next.map e)
  | .dec i zero positive => .dec i (zero.map e) (positive.map e)

/-- Allocate a finite block before a continuation program. Internal
instructions may refer to either part; continuation targets are shifted. -/
def assembleBlock (body : Fin m → Instruction k (m + n)) (continuation : Program k n) :
    Program k (m + n) :=
  Fin.addCases body (fun q ↦ (continuation q).reindex (Fin.natAdd m))

@[simp]
theorem assembleBlock_left (body : Fin m → Instruction k (m + n))
    (continuation : Program k n) (q : Fin m) :
    assembleBlock body continuation (q.castAdd n) = body q := by
  simp [assembleBlock]

@[simp]
theorem assembleBlock_right (body : Fin m → Instruction k (m + n))
    (continuation : Program k n) (q : Fin n) :
    assembleBlock body continuation (q.natAdd m) =
      (continuation q).reindex (Fin.natAdd m) := by
  simp [assembleBlock]

private def pushDigitLabels (d : Fin 4) : List (Fin 12) :=
  ![[11], [10, 11], [9, 10, 11], [8, 9, 10, 11]] d

private theorem pushDigitLabels_length (d : Fin 4) :
    (pushDigitLabels d).length = d.val + 1 := by
  fin_cases d <;> rfl

/-- The twelve literal instructions for pushing one of four symbols. -/
def pushBlockCode (value scratch : Fin k) (d : Fin 4) (exit : Option (Fin n)) :
    Fin 12 → Instruction k (12 + n) :=
  let L := Fin.castAdd n
  let E := exit.map (Fin.natAdd 12)
  ![.dec value (some (L 6)) (some (L 1)),
    .inc scratch (some (L 2)), .inc scratch (some (L 3)),
    .inc scratch (some (L 4)), .inc scratch (some (L 5)), .inc scratch (some (L 0)),
    .dec scratch (blockEntry ((pushDigitLabels d).map L) E) (some (L 7)),
    .inc value (some (L 6)),
    .inc value (some (L 9)), .inc value (some (L 10)),
    .inc value (some (L 11)), .inc value E]

/-- A base-five push block followed by an arbitrary finite continuation. -/
def stackPushProgram (value scratch : Fin k) (d : Fin 4) (exit : Option (Fin n))
    (continuation : Program k n) : Program k (12 + n) :=
  assembleBlock (pushBlockCode value scratch d exit) continuation

/-- The allocated push program inserts digit `d+1`, clears its scratch,
and reaches the chosen continuation without executing that continuation. -/
theorem run_stackPushProgram (value scratch : Fin k) (hne : value ≠ scratch)
    (d : Fin 4) (exit : Option (Fin n)) (continuation : Program k n)
    (r : Fin k → ℕ) (hscratch : r scratch = 0) :
    run (stackPushProgram value scratch d exit continuation)
      ((6 * r value + 1) + (2 * (5 * r value) + 1) + (d.val + 1))
      ⟨some ((0 : Fin 12).castAdd n), r⟩ =
      ⟨exit.map (Fin.natAdd 12), update (update r scratch 0) value
        (5 * r value + (d.val + 1))⟩ := by
  let L : Fin 12 → Fin (12 + n) := Fin.castAdd n
  have hbase : IncrementChain (stackPushProgram value scratch d exit continuation)
      scratch [L 1, L 2, L 3, L 4, L 5] (some (L 0)) := by
    simp [IncrementChain, blockEntry, stackPushProgram, pushBlockCode, L]
  have hdigit : IncrementChain (stackPushProgram value scratch d exit continuation)
      value ((pushDigitLabels d).map L) (exit.map (Fin.natAdd 12)) := by
    fin_cases d <;>
      simp [IncrementChain, blockEntry, stackPushProgram, pushBlockCode, pushDigitLabels, L]
  have h := run_stackPush (P := stackPushProgram value scratch d exit continuation)
    (multiply := L 0) (copy := L 6) (add := L 7) (value := value) (scratch := scratch)
    (base := [L 1, L 2, L 3, L 4, L 5]) (digit := (pushDigitLabels d).map L)
    (exit := exit.map (Fin.natAdd 12)) hne
    (by simp [stackPushProgram, pushBlockCode, blockEntry, L]) hbase
    (by simp [stackPushProgram, pushBlockCode, L])
    (by simp [stackPushProgram, pushBlockCode, L]) hdigit r hscratch
  simpa only [List.length_cons, List.length_nil, List.length_map,
    pushDigitLabels_length] using h

/-- The sixteen literal instructions for a pop, with one finite exit
for each remainder. Exit zero denotes the empty-stack case. -/
def popBlockCode (value scratch : Fin k) (exit : Fin 5 → Option (Fin n)) :
    Fin 16 → Instruction k (16 + n) :=
  let L := Fin.castAdd n
  let E := fun j ↦ (exit j).map (Fin.natAdd 16)
  ![.dec value (some (L 6)) (some (L 1)),
    .dec value (some (L 8)) (some (L 2)),
    .dec value (some (L 10)) (some (L 3)),
    .dec value (some (L 12)) (some (L 4)),
    .dec value (some (L 14)) (some (L 5)),
    .inc scratch (some (L 0)),
    .dec scratch (E 0) (some (L 7)), .inc value (some (L 6)),
    .dec scratch (E 1) (some (L 9)), .inc value (some (L 8)),
    .dec scratch (E 2) (some (L 11)), .inc value (some (L 10)),
    .dec scratch (E 3) (some (L 13)), .inc value (some (L 12)),
    .dec scratch (E 4) (some (L 15)), .inc value (some (L 14))]

/-- A base-five pop block followed by an arbitrary finite continuation. -/
def stackPopProgram (value scratch : Fin k) (exit : Fin 5 → Option (Fin n))
    (continuation : Program k n) : Program k (16 + n) :=
  assembleBlock (popBlockCode value scratch exit) continuation

/-- The allocated pop program removes the least-significant digit,
dispatches through finite control, and restores its scratch to zero. -/
theorem run_stackPopProgram (value scratch : Fin k) (hne : value ≠ scratch)
    (exit : Fin 5 → Option (Fin n)) (continuation : Program k n)
    (r : Fin k → ℕ) (hscratch : r scratch = 0) :
    run (stackPopProgram value scratch exit continuation)
      ((6 * (r value / 5) + r value % 5 + 1) + (2 * (r value / 5) + 1))
      ⟨some ((0 : Fin 16).castAdd n), r⟩ =
      ⟨(exit ⟨r value % 5, Nat.mod_lt _ (by decide)⟩).map (Fin.natAdd 16),
        update (update r scratch 0) value (r value / 5)⟩ := by
  let L : Fin 16 → Fin (16 + n) := Fin.castAdd n
  let tests : List (Fin (16 + n) × Option (Fin (16 + n))) :=
    [(L 0, some (L 6)), (L 1, some (L 8)), (L 2, some (L 10)),
      (L 3, some (L 12)), (L 4, some (L 14))]
  apply run_stackPop (P := stackPopProgram value scratch exit continuation)
    (quotientAdd := L 5) (value := value) (scratch := scratch) (tests := tests)
    (by simp [tests]) hne
    (by simp [DecrementChain, decrementEntry, blockEntry, tests,
      stackPopProgram, popBlockCode, L])
    (by simp [decrementEntry, blockEntry, tests, stackPopProgram, popBlockCode, L])
    ![L 6, L 8, L 10, L 12, L 14] ![L 7, L 9, L 11, L 13, L 15]
    (fun j ↦ (exit j).map (Fin.natAdd 16))
  · intro j; fin_cases j <;> rfl
  · intro j; fin_cases j <;> rfl
  · intro j; fin_cases j <;> rfl
  · exact hscratch

namespace TM2Encoding

open Turing.PartrecToTM2

/-- The four symbols used by Mathlib's universal stack machine. -/
def symbolCode : Γ' → Fin 4
  | .consₗ => 0
  | .cons => 1
  | .bit0 => 2
  | .bit1 => 3

/-- Zero is empty; the four nonzero remainders encode the local store. -/
def digitSymbol : Fin 5 → Option Γ' :=
  ![none, some .consₗ, some .cons, some .bit0, some .bit1]

/-- Four fixed stack registers; register four is reserved for scratch. -/
def stackRegister : K' → Fin 5
  | .main => 0
  | .rev => 1
  | .aux => 2
  | .stack => 3

theorem stackRegister_ne_scratch (j : K') : stackRegister j ≠ 4 := by
  cases j <;> decide

/-- Base-five encoding of the actual Mathlib stack alphabet. -/
def contentsCode (S : List Γ') : ℕ := stackNumeral 5 (S.map symbolCode)

@[simp]
theorem contentsCode_cons (a : Γ') (S : List Γ') :
    contentsCode (a :: S) = 5 * contentsCode S + ((symbolCode a).val + 1) := rfl

@[simp]
theorem contentsCode_div (S : List Γ') : contentsCode S / 5 = contentsCode S.tail := by
  cases S with
  | nil => rfl
  | cons a S => exact stackNumeral_cons_div (b := 5) (symbolCode a) (S.map symbolCode)

/-- The remainder identifies exactly the option returned by TM2 pop. -/
theorem digitSymbol_contentsCode_mod (S : List Γ') :
    digitSymbol ⟨contentsCode S % 5, Nat.mod_lt _ (by decide)⟩ = S.head? := by
  cases S with
  | nil => rfl
  | cons a S =>
      have hmod : contentsCode (a :: S) % 5 = (symbolCode a).val + 1 :=
        stackNumeral_cons_mod (b := 5) (symbolCode a) (S.map symbolCode)
      simp only [hmod, List.head?_cons]
      cases a <;> rfl

/-- All four actual stacks, with one shared scratch register initially zero. -/
def encodeStacks (S : K' → List Γ') : Fin 5 → ℕ :=
  ![contentsCode (S .main), contentsCode (S .rev),
    contentsCode (S .aux), contentsCode (S .stack), 0]

@[simp]
theorem encodeStacks_scratch (S : K' → List Γ') : encodeStacks S 4 = 0 := rfl

@[simp]
theorem encodeStacks_stackRegister (S : K' → List Γ') (j : K') :
    encodeStacks S (stackRegister j) = contentsCode (S j) := by
  cases j <;> rfl

theorem encodeStacks_update (S : K' → List Γ') (j : K') (L : List Γ') :
    encodeStacks (update S j L) = update (encodeStacks S) (stackRegister j) (contentsCode L) := by
  funext i
  cases j <;> fin_cases i <;> simp [encodeStacks, stackRegister]

/-- One actual TM2 push is implemented by a finite twelve-label INC/DEC
block on five registers. The other stacks and the zero scratch are preserved. -/
theorem run_push_stackEncoding (j : K') (a : Γ') (S : K' → List Γ')
    (exit : Option (Fin n)) (continuation : Program 5 n) :
    run (stackPushProgram (stackRegister j) 4 (symbolCode a) exit continuation)
      ((6 * contentsCode (S j) + 1) + (2 * (5 * contentsCode (S j)) + 1) +
        ((symbolCode a).val + 1))
      ⟨some ((0 : Fin 12).castAdd n), encodeStacks S⟩ =
      ⟨exit.map (Fin.natAdd 12), encodeStacks (update S j (a :: S j))⟩ := by
  have h := run_stackPushProgram (stackRegister j) 4 (stackRegister_ne_scratch j)
    (symbolCode a) exit continuation (encodeStacks S) rfl
  rw [encodeStacks_stackRegister] at h
  rw [h, encodeStacks_update, contentsCode_cons]
  congr 2
  exact update_eq_self 4 (encodeStacks S)

/-- One actual TM2 pop is implemented by a finite sixteen-label INC/DEC
block. Its head option is passed to the finite continuation dispatch;
the selected stack becomes its tail and scratch is restored to zero. -/
theorem run_pop_stackEncoding (j : K') (S : K' → List Γ')
    (exit : Option Γ' → Option (Fin n)) (continuation : Program 5 n) :
    run (stackPopProgram (stackRegister j) 4 (fun d ↦ exit (digitSymbol d)) continuation)
      ((6 * (contentsCode (S j) / 5) + contentsCode (S j) % 5 + 1) +
        (2 * (contentsCode (S j) / 5) + 1))
      ⟨some ((0 : Fin 16).castAdd n), encodeStacks S⟩ =
      ⟨(exit (S j).head?).map (Fin.natAdd 16), encodeStacks (update S j (S j).tail)⟩ := by
  have h := run_stackPopProgram (stackRegister j) 4 (stackRegister_ne_scratch j)
    (fun d ↦ exit (digitSymbol d)) continuation (encodeStacks S) rfl
  rw [encodeStacks_stackRegister] at h
  rw [h]
  simp only [digitSymbol_contentsCode_mod, encodeStacks_update, contentsCode_div]
  congr 2
  exact update_eq_self 4 (encodeStacks S)

/-- The push block simulates the literal Mathlib `push; goto store`
statement, including its unchanged finite local store. -/
theorem run_push_stepAux (j : K') (f : Option Γ' → Γ') (store : Option Γ')
    (S : K' → List Γ') (exit : Option Γ' → Option (Fin n)) (continuation : Program 5 n) :
    let out : Turing.TM2.Cfg (fun _ : K' ↦ Γ') (Option Γ') (Option Γ') :=
      Turing.TM2.stepAux (.push j f (.goto id)) store S
    run (stackPushProgram (stackRegister j) 4 (symbolCode (f store)) (exit store) continuation)
      ((6 * contentsCode (S j) + 1) + (2 * (5 * contentsCode (S j)) + 1) +
        ((symbolCode (f store)).val + 1))
      ⟨some ((0 : Fin 12).castAdd n), encodeStacks S⟩ =
      ⟨(exit out.var).map (Fin.natAdd 12), encodeStacks out.stk⟩ :=
  run_push_stackEncoding j (f store) S (exit store) continuation

/-- The pop block simulates the literal Mathlib `pop; goto store`
statement, including any update of the finite store from the old store
and the popped head. No source stack operation is assumed correct. -/
theorem run_pop_stepAux (j : K') (f : Option Γ' → Option Γ' → Option Γ')
    (store : Option Γ') (S : K' → List Γ')
    (exit : Option Γ' → Option (Fin n)) (continuation : Program 5 n) :
    let out : Turing.TM2.Cfg (fun _ : K' ↦ Γ') (Option Γ') (Option Γ') :=
      Turing.TM2.stepAux (.pop j f (.goto id)) store S
    run (stackPopProgram (stackRegister j) 4
        (fun d ↦ exit (f store (digitSymbol d))) continuation)
      ((6 * (contentsCode (S j) / 5) + contentsCode (S j) % 5 + 1) +
        (2 * (contentsCode (S j) / 5) + 1))
      ⟨some ((0 : Fin 16).castAdd n), encodeStacks S⟩ =
      ⟨(exit out.var).map (Fin.natAdd 16), encodeStacks out.stk⟩ :=
  run_pop_stackEncoding j S (fun head ↦ exit (f store head)) continuation

end TM2Encoding

end Stability.RegisterMachine
