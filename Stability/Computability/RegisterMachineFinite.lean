import Stability.Computability.RegisterMachineStatement

/-!
# Finite cyclic assembly of compiled stack statements

The internal instructions of a compiled statement do not depend on its
external continuation. This permits assembling all supported root
statements into one finite program and wiring goto exits backward.
-/

namespace Stability.RegisterMachine

variable {k a b n : ℕ}

private theorem local_code_prefix
    (body : Fin a → Instruction k (a + (b + n))) (P Q : Program k (b + n))
    (h : ∀ r : Fin b, P (r.castAdd n) = Q (r.castAdd n)) (r : Fin (a + b)) :
    ((assembleBlock body P).cast (Nat.add_assoc a b n).symm) (r.castAdd n) =
      ((assembleBlock body Q).cast (Nat.add_assoc a b n).symm) (r.castAdd n) := by
  induction r using Fin.addCases with
  | left r =>
      change (assembleBlock body P (r.castAdd (b + n))).reindex _ =
        (assembleBlock body Q (r.castAdd (b + n))).reindex _
      rw [assembleBlock_left, assembleBlock_left]
  | right r =>
      change (assembleBlock body P ((r.castAdd n).natAdd a)).reindex _ =
        (assembleBlock body Q ((r.castAdd n).natAdd a)).reindex _
      rw [assembleBlock_right, assembleBlock_right, h]

namespace TM2Encoding

open Turing.PartrecToTM2

variable {Λ : Type*}

set_option maxRecDepth 2048 in
/-- Compiled internal instructions are independent of the supplied
external continuation; only copied external instructions depend on it. -/
theorem compileStatement_local_code (q : StackStatement Λ) {n : ℕ}
    (exit : Λ → Option Γ' → Option (Fin n)) (P Q : Program 5 n)
    (r : Fin (statementSize q)) :
    compileStatement q exit P (r.castAdd n) = compileStatement q exit Q (r.castAdd n) := by
  induction q generalizing n with
  | push j f q ih => exact local_code_prefix _ _ _ (ih exit P Q) r
  | pop j f q ih => exact local_code_prefix _ _ _ (ih exit P Q) r
  | load f q ih => exact local_code_prefix _ _ _ (ih exit P Q) r
  | goto f =>
      exact congrArg id (show _ = _ from (assembleBlock_left _ P r).trans
        (assembleBlock_left _ Q r).symm)
  | halt =>
      exact congrArg id (show _ = _ from (assembleBlock_left _ P r).trans
        (assembleBlock_left _ Q r).symm)
  | peek j f q ih =>
      induction r using Fin.addCases with
      | left r =>
          induction r using Fin.addCases (m := 80) (n := 300) with
          | left r =>
              change (assembleBlock _ _ (r.castAdd (300 + (statementSize q + n)))).reindex _ =
                (assembleBlock _ _ (r.castAdd (300 + (statementSize q + n)))).reindex _
              rw [assembleBlock_left, assembleBlock_left]
          | right r =>
              change (assembleBlock _ _ ((r.castAdd (statementSize q + n)).natAdd 80)).reindex _ =
                (assembleBlock _ _ ((r.castAdd (statementSize q + n)).natAdd 80)).reindex _
              simp only [assembleBlock_right]
              change ((assembleBlock _ _ (r.castAdd (statementSize q + n))).reindex _).reindex _ =
                ((assembleBlock _ _ (r.castAdd (statementSize q + n))).reindex _).reindex _
              rw [assembleBlock_left, assembleBlock_left]
      | right r =>
          have hr : ((r.natAdd 380).castAdd n).cast
              (show (380 + statementSize q) + n = 80 + (300 + (statementSize q + n)) by omega) =
              ((r.castAdd n).natAdd 300).natAdd 80 := by
            apply Fin.ext
            simp
            omega
          simp only [compileStatement, Program.cast, statementSize]
          rw [hr]
          simp only [peekDispatchProgram, dispatchProgram, restoreDispatchProgram,
            assembleBlock_right]
          change (((compileStatement q exit P (r.castAdd n)).reindex _).reindex _).reindex _ =
            (((compileStatement q exit Q (r.castAdd n)).reindex _).reindex _).reindex _
          rw [ih]
  | branch f q₁ q₂ ih₁ ih₂ =>
      induction r using Fin.addCases with
      | left r =>
          change
            (assembleBlock _ _ (r.castAdd (statementSize q₁ + (statementSize q₂ + n)))).reindex _ =
            (assembleBlock _ _ (r.castAdd (statementSize q₁ + (statementSize q₂ + n)))).reindex _
          rw [assembleBlock_left, assembleBlock_left]
      | right r =>
          induction r using Fin.addCases with
          | left r =>
              change (assembleBlock _ _ ((r.castAdd (statementSize q₂ + n)).natAdd 5)).reindex _ =
                (assembleBlock _ _ ((r.castAdd (statementSize q₂ + n)).natAdd 5)).reindex _
              simp only [assembleBlock_right]
              rw [ih₁]
          | right r =>
              change
                (assembleBlock _ _ (((r.castAdd n).natAdd (statementSize q₁)).natAdd 5)).reindex _ =
                (assembleBlock _ _ (((r.castAdd n).natAdd (statementSize q₁)).natAdd 5)).reindex _
              simp only [assembleBlock_right]
              rw [compileStatement_continuation_code, compileStatement_continuation_code, ih₂]

variable {a b : ℕ}

/-- Allocate one disjoint block of width `b` for each of the finitely
many source labels. Unused padding will halt and is never entered by
the simulation theorem. -/
def rootAllocation (M : Fin a → StackStatement (Fin a))
    (hsize : ∀ i, statementSize (M i) ≤ b) (i : Fin a)
    (r : Fin (statementSize (M i))) : Fin (a * b) :=
  finProdFinEquiv (i, r.castLE (hsize i))

/-- A source goto selects the compiled root and its new finite store. -/
def rootEntry (M : Fin a → StackStatement (Fin a))
    (hsize : ∀ i, statementSize (M i) ≤ b) (i : Fin a) (store : Option Γ') : Fin (a * b) :=
  rootAllocation M hsize i (statementEntry (M i) store)

private def rootExit (M : Fin a → StackStatement (Fin a))
    (hsize : ∀ i, statementSize (M i) ≤ b) (i : Fin a) (store : Option Γ') : Option (Fin (a * b)) :=
  some (rootEntry M hsize i store)

/-- One literal finite INC/DEC program for an entire finite-control TM2
machine. Every goto is wired into the already allocated root blocks.
The dummy continuation is used only when constructing internal code;
its instructions are not copied into this program. -/
def finiteProgram (M : Fin a → StackStatement (Fin a))
    (hsize : ∀ i, statementSize (M i) ≤ b) : Program 5 (a * b) := fun q ↦
  let ir := finProdFinEquiv.symm q
  if h : ir.2.val < statementSize (M ir.1) then
    (compileStatement (M ir.1) (rootExit M hsize) (fun _ ↦ .dec 4 none none)
      ((⟨ir.2.val, h⟩ : Fin (statementSize (M ir.1))).castAdd (a * b))).reindex
        (blockEmbedding (rootAllocation M hsize ir.1))
  else .dec 4 none none

/-- Literal instruction equations at every allocated internal label. -/
theorem finiteProgram_internal_code (M : Fin a → StackStatement (Fin a))
    (hsize : ∀ i, statementSize (M i) ≤ b) (i : Fin a)
    (r : Fin (statementSize (M i))) :
    finiteProgram M hsize (rootAllocation M hsize i r) =
      (compileStatement (M i) (rootExit M hsize) (finiteProgram M hsize)
        (r.castAdd (a * b))).reindex (blockEmbedding (rootAllocation M hsize i)) := by
  have hpair : finProdFinEquiv.symm (rootAllocation M hsize i r) =
      (i, r.castLE (hsize i)) := Equiv.symm_apply_apply _ _
  unfold finiteProgram
  rw [hpair]
  simp only [Fin.val_castLE]
  rw [dif_pos r.isLt]
  exact congrArg (Instruction.reindex (blockEmbedding (rootAllocation M hsize i)))
    (compileStatement_local_code (M i) (rootExit M hsize) _ _ r)

/-- The complete compiled statement folds into the cyclic finite program.
External labels fold by identity, so no exit-behavior assumption occurs. -/
theorem finiteProgram_embedding_code (M : Fin a → StackStatement (Fin a))
    (hsize : ∀ i, statementSize (M i) ≤ b) (i : Fin a)
    (r : Fin (statementSize (M i) + a * b)) :
    finiteProgram M hsize (blockEmbedding (rootAllocation M hsize i) r) =
      (compileStatement (M i) (rootExit M hsize) (finiteProgram M hsize) r).reindex
        (blockEmbedding (rootAllocation M hsize i)) := by
  induction r using Fin.addCases with
  | left r => simpa only [blockEmbedding_internal] using finiteProgram_internal_code M hsize i r
  | right r =>
      rw [blockEmbedding_external, compileStatement_continuation_code]
      cases finiteProgram M hsize r <;>
        simp [Instruction.reindex, Option.map_map, Function.comp_def]

/-- Encode an actual finite-control TM2 configuration using four numeral
stack registers, one zero scratch, and the root/store control label. -/
def encodeConfiguration (M : Fin a → StackStatement (Fin a))
    (hsize : ∀ i, statementSize (M i) ≤ b)
    (c : Turing.TM2.Cfg (fun _ : K' ↦ Γ') (Fin a) (Option Γ')) : Configuration 5 (a * b) :=
  ⟨c.l.map (fun i ↦ rootEntry M hsize i c.var), encodeStacks c.stk⟩

/-- One step of the actual finite-control TM2 machine is simulated in
positive finite time by the single cyclic INC/DEC program. -/
theorem run_finiteProgram_stepAux (M : Fin a → StackStatement (Fin a))
    (hsize : ∀ i, statementSize (M i) ≤ b) (i : Fin a)
    (store : Option Γ') (S : K' → List Γ') :
    ∃ steps : ℕ, 0 < steps ∧
      run (finiteProgram M hsize) steps (encodeConfiguration M hsize ⟨some i, store, S⟩) =
        encodeConfiguration M hsize (Turing.TM2.stepAux (M i) store S) := by
  obtain ⟨steps, hpos, hrun⟩ := run_compileStatement (M i) (rootExit M hsize)
    (finiteProgram M hsize) store S
  have h := run_reindex (blockEmbedding (rootAllocation M hsize i))
    (finiteProgram_embedding_code M hsize i) steps
    ⟨some ((statementEntry (M i) store).castAdd (a * b)), encodeStacks S⟩
  rw [hrun] at h
  refine ⟨steps, hpos, ?_⟩
  cases hl : (Turing.TM2.stepAux (M i) store S).l <;>
    simpa [encodeConfiguration, rootEntry, statementOutput, rootExit, hl,
      Configuration.reindex, Option.map_map, Function.comp_def] using h

private theorem reaches_one_run {k s : ℕ} (P : Program k s) (steps : ℕ)
    (hpos : 0 < steps) (c : Configuration k s) (hactive : c.label ≠ none) :
    StateTransition.Reaches₁ (transition P) c (run P steps c) := by
  cases steps with
  | zero => omega
  | succ steps =>
      cases c with
      | mk label r =>
          cases label with
          | none => exact (hactive rfl).elim
          | some q =>
              apply Relation.TransGen.head'_iff.mpr
              exact ⟨execute (P q) r, rfl, reaches_run P steps (execute (P q) r)⟩

/-- The actual finite compiler is a positive-step refinement of Mathlib's
partial TM2 transition. This is derived from the literal code, rather
than supplied as a universality or simulation hypothesis. -/
theorem finiteProgram_respects (M : Fin a → StackStatement (Fin a))
    (hsize : ∀ i, statementSize (M i) ≤ b) :
    StateTransition.Respects (Turing.TM2.step M) (transition (finiteProgram M hsize))
      (fun c d ↦ encodeConfiguration M hsize c = d) := by
  apply StateTransition.fun_respects.mpr
  intro c
  cases c with
  | mk label store S =>
      cases label with
      | none => rfl
      | some i =>
          obtain ⟨steps, hpos, hrun⟩ := run_finiteProgram_stepAux M hsize i store S
          change StateTransition.Reaches₁ (transition (finiteProgram M hsize))
            (encodeConfiguration M hsize ⟨some i, store, S⟩)
            (encodeConfiguration M hsize (Turing.TM2.stepAux (M i) store S))
          rw [← hrun]
          exact reaches_one_run _ steps hpos _ (by simp [encodeConfiguration])

/-- Exact halting equivalence for the single finite INC/DEC program and
the finite-control TM2 machine from which it was compiled. -/
theorem finiteProgram_halts_iff (M : Fin a → StackStatement (Fin a))
    (hsize : ∀ i, statementSize (M i) ≤ b)
    (c : Turing.TM2.Cfg (fun _ : K' ↦ Γ') (Fin a) (Option Γ')) :
    Halts (finiteProgram M hsize) (encodeConfiguration M hsize c) ↔
      (StateTransition.eval (Turing.TM2.step M) c).Dom := by
  rw [halts_iff_eval_dom]
  exact StateTransition.tr_eval_dom (finiteProgram_respects M hsize) rfl

/-- A concrete sufficient block width, calculated from the finite source
program. No size bound has to be assumed by callers. -/
def finiteProgramWidth (M : Fin a → StackStatement (Fin a)) : ℕ :=
  Finset.univ.sup (fun i ↦ statementSize (M i))

theorem statementSize_le_finiteProgramWidth (M : Fin a → StackStatement (Fin a)) (i : Fin a) :
    statementSize (M i) ≤ finiteProgramWidth M := by
  exact Finset.le_sup (f := fun i ↦ statementSize (M i)) (Finset.mem_univ i)

/-- The finite INC/DEC compiler with its block bound calculated internally. -/
def compileFiniteMachine (M : Fin a → StackStatement (Fin a)) :
    Program 5 (a * finiteProgramWidth M) :=
  finiteProgram M (statementSize_le_finiteProgramWidth M)

/-- Halting equivalence for the bound-free finite-machine compiler. -/
theorem compileFiniteMachine_halts_iff (M : Fin a → StackStatement (Fin a))
    (c : Turing.TM2.Cfg (fun _ : K' ↦ Γ') (Fin a) (Option Γ')) :
    Halts (compileFiniteMachine M)
      (encodeConfiguration M (statementSize_le_finiteProgramWidth M) c) ↔
      (StateTransition.eval (Turing.TM2.step M) c).Dom :=
  finiteProgram_halts_iff M (statementSize_le_finiteProgramWidth M) c

end TM2Encoding

end Stability.RegisterMachine
