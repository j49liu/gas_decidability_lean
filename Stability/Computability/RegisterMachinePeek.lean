import Stability.Computability.RegisterMachineDispatch

/-!
# Peek by finite-control pop and restoration

Peek uses the proved pop block, then restores a nonempty popped head.
The old store and the head option occupy a finite product of control
labels; no additional register is used. Empty-head restoration is one
DEC on the zero scratch register. The complete program has 380 internal
labels and preserves all four stacks and the scratch invariant.
-/

namespace Stability.RegisterMachine.TM2Encoding

open Turing.PartrecToTM2

variable {n : ℕ}

/-- Restore a head option after popping a stack. -/
def restoreStacks (S : K' → List Γ') (j : K') : Option Γ' → K' → List Γ'
  | none => S
  | some a => Function.update S j (a :: S j)

/-- A stored head has either a one-step empty restoration or the
previously verified push execution time. -/
def restoreSteps (head : Option Γ') (N : ℕ) : ℕ :=
  match head with
  | none => 1
  | some a => (6 * N + 1) + (2 * (5 * N) + 1) + ((symbolCode a).val + 1)

/-- The finite restore branch carries both the old store and popped head. -/
def restoreEntry (store head : Option Γ') : Fin (300 + n) :=
  dispatchLabel (finProdFinEquiv (storeCode store, storeCode head))
    ((0 : Fin 12).castAdd n)

/-- Twenty-five fixed restoration branches, each with twelve labels.
The empty branch uses only its first label. -/
def restoreBlockCode (j : K') (f : Option Γ' → Option Γ' → Option Γ')
    (exit : Option Γ' → Option (Fin n)) (i : Fin 25) : Fin 12 → Instruction 5 (12 + n) :=
  let pair : Fin 5 × Fin 5 := finProdFinEquiv.symm i
  let store := digitSymbol pair.1
  match digitSymbol pair.2 with
  | none => fun _ ↦ .dec 4 ((exit (f store none)).map (Fin.natAdd 12))
      ((exit (f store none)).map (Fin.natAdd 12))
  | some a => pushBlockCode (stackRegister j) 4 (symbolCode a) (exit (f store (some a)))

/-- The one finite restoration program for every old-store/head pair. -/
def restoreDispatchProgram (j : K') (f : Option Γ' → Option Γ' → Option Γ')
    (exit : Option Γ' → Option (Fin n)) (continuation : Program 5 n) : Program 5 (300 + n) :=
  dispatchProgram (restoreBlockCode j f exit) continuation

/-- Restoration preserves other stacks and sends the updated finite
store to its continuation. -/
theorem run_restoreDispatchProgram (j : K') (f : Option Γ' → Option Γ' → Option Γ')
    (store head : Option Γ') (S : K' → List Γ')
    (exit : Option Γ' → Option (Fin n)) (continuation : Program 5 n) :
    run (restoreDispatchProgram j f exit continuation) (restoreSteps head (contentsCode (S j)))
      ⟨some (restoreEntry store head), encodeStacks S⟩ =
      ⟨(exit (f store head)).map (Fin.natAdd 300), encodeStacks (restoreStacks S j head)⟩ := by
  have h := run_dispatchProgram (restoreBlockCode j f exit) continuation
    (finProdFinEquiv (storeCode store, storeCode head))
    (restoreSteps head (contentsCode (S j)))
    ⟨some ((0 : Fin 12).castAdd n), encodeStacks S⟩
  simp only [restoreBlockCode, Equiv.symm_apply_apply, digitSymbol_storeCode] at h
  cases head with
  | none =>
      have hlocal : run (assembleBlock
          (fun _ : Fin 12 ↦ Instruction.dec (4 : Fin 5)
            ((exit (f store none)).map (Fin.natAdd 12))
            ((exit (f store none)).map (Fin.natAdd 12))) continuation) 1
          ⟨some ((0 : Fin 12).castAdd n), encodeStacks S⟩ =
          ⟨(exit (f store none)).map (Fin.natAdd 12), encodeStacks S⟩ := by
        simp [run, step, execute]
      rw [show restoreSteps none (contentsCode (S j)) = 1 from rfl, hlocal] at h
      simpa [restoreDispatchProgram, restoreEntry, restoreStacks,
        Configuration.reindex, dispatchLabel, Option.map_map, Function.comp_def] using h
  | some a =>
      change run (restoreDispatchProgram j f exit continuation) _ _ =
        (run (stackPushProgram (stackRegister j) 4 (symbolCode a)
          (exit (f store (some a))) continuation) _ _).reindex
            (dispatchLabel (finProdFinEquiv (storeCode store, storeCode (some a)))) at h
      simp only [restoreSteps] at h
      rw [run_push_stackEncoding j a S (exit (f store (some a))) continuation] at h
      simpa [restoreEntry, restoreStacks, Configuration.reindex, dispatchLabel,
        Option.map_map, Function.comp_def] using h

/-- Reattaching the actual popped head restores the actual original stack. -/
theorem restoreStacks_tail_head (S : K' → List Γ') (j : K') :
    restoreStacks (Function.update S j (S j).tail) j (S j).head? = S := by
  cases h : S j with
  | nil =>
      simp only [List.tail_nil, List.head?_nil, restoreStacks]
      rw [← h]
      exact Function.update_eq_self j S
  | cons a L =>
      funext i
      by_cases hi : i = j
      · subst i; simp [restoreStacks, h]
      · simp [restoreStacks, hi]

/-- The finite pop stage remembers its old store in the selected
restoration label. Its continuation is the entire restoration program. -/
def peekDispatchProgram (j : K') (f : Option Γ' → Option Γ' → Option Γ')
    (exit : Option Γ' → Option (Fin n)) (continuation : Program 5 n) :
    Program 5 (80 + (300 + n)) :=
  dispatchProgram (fun i : Fin 5 ↦ popBlockCode (stackRegister j) 4
    (fun d ↦ some (restoreEntry (digitSymbol i) (digitSymbol d))))
    (restoreDispatchProgram j f exit continuation)

/-- The pop portion reaches the restoration selected by both finite
store values, with the actual source stack replaced by its tail. -/
theorem run_peek_popStage (j : K') (f : Option Γ' → Option Γ' → Option Γ')
    (store : Option Γ') (S : K' → List Γ')
    (exit : Option Γ' → Option (Fin n)) (continuation : Program 5 n) :
    run (peekDispatchProgram j f exit continuation)
      ((6 * (contentsCode (S j) / 5) + contentsCode (S j) % 5 + 1) +
        (2 * (contentsCode (S j) / 5) + 1))
      ⟨some (dispatchLabel (storeCode store) ((0 : Fin 16).castAdd (300 + n))), encodeStacks S⟩ =
      ⟨some ((restoreEntry store (S j).head?).natAdd 80),
        encodeStacks (Function.update S j (S j).tail)⟩ := by
  have h := run_dispatchProgram (fun i : Fin 5 ↦ popBlockCode (stackRegister j) 4
    (fun d ↦ some (restoreEntry (digitSymbol i) (digitSymbol d))))
    (restoreDispatchProgram j f exit continuation) (storeCode store)
    ((6 * (contentsCode (S j) / 5) + contentsCode (S j) % 5 + 1) +
      (2 * (contentsCode (S j) / 5) + 1))
    ⟨some ((0 : Fin 16).castAdd (300 + n)), encodeStacks S⟩
  simp only [digitSymbol_storeCode] at h
  change run (peekDispatchProgram j f exit continuation) _ _ =
    (run (stackPopProgram (stackRegister j) 4
      (fun d ↦ some (restoreEntry store (digitSymbol d)))
      (restoreDispatchProgram j f exit continuation)) _ _).reindex
        (dispatchLabel (storeCode store)) at h
  rw [run_pop_stackEncoding j S (fun head ↦ some (restoreEntry store head))] at h
  simpa [Configuration.reindex, dispatchLabel] using h

/-- The complete finite peek program preserves all four stacks and the
zero scratch while passing the prescribed updated store to its exit. -/
theorem run_peekDispatchProgram (j : K') (f : Option Γ' → Option Γ' → Option Γ')
    (store : Option Γ') (S : K' → List Γ')
    (exit : Option Γ' → Option (Fin n)) (continuation : Program 5 n) :
    run (peekDispatchProgram j f exit continuation)
      (((6 * (contentsCode (S j) / 5) + contentsCode (S j) % 5 + 1) +
        (2 * (contentsCode (S j) / 5) + 1)) +
        restoreSteps (S j).head? (contentsCode (S j).tail))
      ⟨some (dispatchLabel (storeCode store) ((0 : Fin 16).castAdd (300 + n))), encodeStacks S⟩ =
      ⟨(exit (f store (S j).head?)).map (fun q ↦ (q.natAdd 300).natAdd 80), encodeStacks S⟩ := by
  rw [run_add, run_peek_popStage]
  change run (assembleBlock _ (restoreDispatchProgram j f exit continuation)) _
    ((⟨some (restoreEntry store (S j).head?),
      encodeStacks (Function.update S j (S j).tail)⟩ : Configuration 5 (300 + n)).reindex
        (Fin.natAdd 80)) = _
  rw [run_assembleBlock_continuation]
  have hrestore := run_restoreDispatchProgram j f store (S j).head?
    (Function.update S j (S j).tail) exit continuation
  simp only [Function.update_self] at hrestore
  rw [hrestore, restoreStacks_tail_head]
  simp [Configuration.reindex, Option.map_map, Function.comp_def]

/-- The complete register program simulates Mathlib's literal
`peek; goto store`, with the stack family unchanged. -/
theorem run_peek_stepAux (j : K') (f : Option Γ' → Option Γ' → Option Γ')
    (store : Option Γ') (S : K' → List Γ')
    (exit : Option Γ' → Option (Fin n)) (continuation : Program 5 n) :
    let out : Turing.TM2.Cfg (fun _ : K' ↦ Γ') (Option Γ') (Option Γ') :=
      Turing.TM2.stepAux (.peek j f (.goto id)) store S
    run (peekDispatchProgram j f exit continuation)
      (((6 * (contentsCode (S j) / 5) + contentsCode (S j) % 5 + 1) +
        (2 * (contentsCode (S j) / 5) + 1)) +
        restoreSteps (S j).head? (contentsCode (S j).tail))
      ⟨some (dispatchLabel (storeCode store) ((0 : Fin 16).castAdd (300 + n))), encodeStacks S⟩ =
      ⟨(exit out.var).map (fun q ↦ (q.natAdd 300).natAdd 80), encodeStacks out.stk⟩ :=
  run_peekDispatchProgram j f store S exit continuation

end Stability.RegisterMachine.TM2Encoding
