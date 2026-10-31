import Stability.Computability.RegisterMachineEmbedding

/-!
# Finite compilation of stack-machine statements

The compiler allocates every branch of the actual Mathlib statement
syntax. The five possible local-store values occupy finite control;
the registers contain only the four base-five stacks and a zero scratch.
Goto targets remain external so that finite root blocks can later be
wired into a cyclic program.
-/

namespace Stability.RegisterMachine

variable {k m n : ℕ}

/-- Transport a finite program along an equality of label counts. -/
def Program.cast (h : m = n) (P : Program k m) : Program k n :=
  fun q ↦ (P (q.cast h.symm)).reindex (Fin.cast h)

theorem run_program_cast (h : m = n) (P : Program k m) (steps : ℕ)
    (c : Configuration k m) :
    run (P.cast h) steps (c.reindex (Fin.cast h)) =
      (run P steps c).reindex (Fin.cast h) := by
  apply run_reindex
  intro q
  simp [Program.cast]

@[simp]
theorem Instruction.reindex_reindex {s : ℕ} (i : Instruction k m)
    (e : Fin m → Fin n) (f : Fin n → Fin s) :
    (i.reindex e).reindex f = i.reindex (f ∘ e) := by
  cases i <;> simp [Instruction.reindex, Option.map_map]

/-- An instruction-level continuation inclusion composes through a
fresh prefix, with the expected sum of label offsets. -/
private theorem continuation_code_prefix {a b : ℕ}
    (body : Fin a → Instruction k (a + (b + n)))
    (Q : Program k (b + n)) (P : Program k n)
    (hQ : ∀ q, Q (q.natAdd b) = (P q).reindex (Fin.natAdd b)) (q : Fin n) :
    ((assembleBlock body Q).cast (Nat.add_assoc a b n).symm) (q.natAdd (a + b)) =
      (P q).reindex (Fin.natAdd (a + b)) := by
  have hlabel : (q.natAdd (a + b)).cast (Nat.add_assoc a b n) =
      (q.natAdd b).natAdd a := by apply Fin.ext; simp [Nat.add_assoc]
  simp only [Program.cast, hlabel, assembleBlock_right, hQ, Instruction.reindex_reindex]
  congr 1
  funext r
  apply Fin.ext
  simp [Function.comp_def, Nat.add_assoc]

namespace TM2Encoding

open Turing.PartrecToTM2

variable {Λ : Type*}

/-- Statements of the four-stack, four-symbol machine used in Mathlib's
partial-recursive evaluator. Only the external label type varies. -/
abbrev StackStatement (Λ : Type*) := Turing.TM2.Stmt (fun _ : K' ↦ Γ') Λ (Option Γ')

/-- Number of allocated INC/DEC labels, including all finite-store
branches and all nested statement branches. -/
def statementSize : StackStatement Λ → ℕ
  | .push _ _ q => 60 + statementSize q
  | .pop _ _ q => 80 + statementSize q
  | .peek _ _ q => 380 + statementSize q
  | .load _ q => 5 + statementSize q
  | .branch _ q₁ q₂ => 5 + (statementSize q₁ + statementSize q₂)
  | .goto _ => 5
  | .halt => 5

private def familyEntry (b : ℕ) (hb : 0 < b) (store : Option Γ') : Fin (5 * b) :=
  finProdFinEquiv (storeCode store, ⟨0, hb⟩)

/-- The entry for a statement depends only on its finite local store. -/
def statementEntry : (q : StackStatement Λ) → Option Γ' → Fin (statementSize q)
  | .push _ _ q, store => (familyEntry 12 (by decide) store).castAdd (statementSize q)
  | .pop _ _ q, store => (familyEntry 16 (by decide) store).castAdd (statementSize q)
  | .peek _ _ q, store =>
      ((familyEntry 16 (by decide) store).castAdd 300).castAdd (statementSize q)
  | .load _ q, store => (storeCode store).castAdd (statementSize q)
  | .branch _ q₁ q₂, store => (storeCode store).castAdd (statementSize q₁ + statementSize q₂)
  | .goto _, store => storeCode store
  | .halt, store => storeCode store

/-- The literal finite program for one complete statement. External
goto destinations may depend on both the label and the current store. -/
def compileStatement (q : StackStatement Λ) {n : ℕ}
    (exit : Λ → Option Γ' → Option (Fin n)) (continuation : Program 5 n) :
    Program 5 (statementSize q + n) :=
  match q with
  | .push j f q =>
      (pushDispatchProgram j f (fun store ↦ some ((statementEntry q store).castAdd n))
        (compileStatement q exit continuation)).cast (Nat.add_assoc ..).symm
  | .pop j f q =>
      (popDispatchProgram j f (fun store ↦ some ((statementEntry q store).castAdd n))
        (compileStatement q exit continuation)).cast (Nat.add_assoc ..).symm
  | .peek j f q =>
      (peekDispatchProgram j f (fun store ↦ some ((statementEntry q store).castAdd n))
        (compileStatement q exit continuation)).cast (by simp only [statementSize]; omega)
  | .load f q =>
      (controlDispatchProgram (fun store ↦ some ((statementEntry q (f store)).castAdd n))
        (compileStatement q exit continuation)).cast (Nat.add_assoc ..).symm
  | .branch f q₁ q₂ =>
      let tail := compileStatement q₂ exit continuation
      let branches := compileStatement q₁
        (fun l store ↦ (exit l store).map (Fin.natAdd (statementSize q₂))) tail
      (controlDispatchProgram (fun store ↦ some (if f store then
          (statementEntry q₁ store).castAdd (statementSize q₂ + n) else
          ((statementEntry q₂ store).castAdd n).natAdd (statementSize q₁))) branches).cast
        (by simp [statementSize, Nat.add_assoc])
  | .goto f => controlDispatchProgram (fun store ↦ exit (f store) store) continuation
  | .halt => controlDispatchProgram (fun _ ↦ none) continuation

/-- The compiler does not alter the supplied external continuation. -/
theorem compileStatement_continuation_code (q : StackStatement Λ) {n : ℕ}
    (exit : Λ → Option Γ' → Option (Fin n)) (continuation : Program 5 n) (r : Fin n) :
    compileStatement q exit continuation (r.natAdd (statementSize q)) =
      (continuation r).reindex (Fin.natAdd (statementSize q)) := by
  induction q generalizing n with
  | push j f q ih =>
      exact continuation_code_prefix _ _ _ (ih exit continuation) r
  | pop j f q ih =>
      exact continuation_code_prefix _ _ _ (ih exit continuation) r
  | load f q ih =>
      exact continuation_code_prefix _ _ _ (ih exit continuation) r
  | peek j f q ih =>
      have hlabel : (r.natAdd (statementSize (.peek j f q))).cast
          (show statementSize (.peek j f q) + n = 80 + (300 + (statementSize q + n)) by
            simp only [statementSize]; omega) =
          ((r.natAdd (statementSize q)).natAdd 300).natAdd 80 := by
        apply Fin.ext; simp [statementSize]; omega
      simp only [compileStatement, Program.cast, hlabel, peekDispatchProgram,
        dispatchProgram, assembleBlock_right, restoreDispatchProgram, ih,
        Instruction.reindex_reindex]
      congr 1
      funext z
      apply Fin.ext
      simp [Function.comp_def, statementSize]
      omega
  | branch f q₁ q₂ ih₁ ih₂ =>
      have hlabel : (r.natAdd (statementSize (.branch f q₁ q₂))).cast
          (show statementSize (.branch f q₁ q₂) + n =
            5 + (statementSize q₁ + (statementSize q₂ + n)) by
            simp [statementSize, Nat.add_assoc]) =
          ((r.natAdd (statementSize q₂)).natAdd (statementSize q₁)).natAdd 5 := by
        apply Fin.ext; simp [statementSize, Nat.add_assoc]
      simp only [compileStatement, Program.cast, hlabel, controlDispatchProgram,
        dispatchProgram, assembleBlock_right, ih₁, ih₂, Instruction.reindex_reindex]
      congr 1
      funext z
      apply Fin.ext
      simp [Function.comp_def, statementSize, Nat.add_assoc]
  | goto f => exact assembleBlock_right _ _ r
  | halt => exact assembleBlock_right _ _ r

/-- Once a compiled statement jumps to an external label, the supplied
continuation runs unchanged. -/
theorem run_compileStatement_continuation (q : StackStatement Λ) {n : ℕ}
    (exit : Λ → Option Γ' → Option (Fin n)) (continuation : Program 5 n)
    (steps : ℕ) (c : Configuration 5 n) :
    run (compileStatement q exit continuation) steps
      (c.reindex (Fin.natAdd (statementSize q))) =
      (run continuation steps c).reindex (Fin.natAdd (statementSize q)) :=
  run_reindex _ (compileStatement_continuation_code q exit continuation) steps c

/-- The result of a source statement, with its goto destination resolved
by the external finite control table. Source halt remains actual halt. -/
def statementOutput {n : ℕ} (exit : Λ → Option Γ' → Option (Fin n))
    (out : Turing.TM2.Cfg (fun _ : K' ↦ Γ') Λ (Option Γ')) : Configuration 5 n :=
  ⟨out.l.bind (fun l ↦ exit l out.var), encodeStacks out.stk⟩

private theorem prefix_run {a b : ℕ}
    (body : Fin a → Instruction 5 (a + b)) (Q : Program 5 b)
    (s t : ℕ) (start : Configuration 5 (a + b)) (mid finish : Configuration 5 b)
    (hs : run (assembleBlock body Q) s start = mid.reindex (Fin.natAdd a))
    (ht : run Q t mid = finish) :
    run (assembleBlock body Q) (s + t) start = finish.reindex (Fin.natAdd a) := by
  rw [run_add, hs, run_assembleBlock_continuation, ht]

/-- Compiling a source goto takes one literal DEC instruction and reaches
the resolved external label without executing its instruction. -/
theorem run_compileStatement_goto {n : ℕ} (f : Option Γ' → Λ)
    (exit : Λ → Option Γ' → Option (Fin n)) (continuation : Program 5 n)
    (store : Option Γ') (S : K' → List Γ') :
    run (compileStatement (.goto f) exit continuation) 1
      ⟨some ((statementEntry (.goto f) store).castAdd n), encodeStacks S⟩ =
      (statementOutput exit (Turing.TM2.stepAux (.goto f) store S)).reindex
        (Fin.natAdd (statementSize (.goto f))) := by
  simpa [compileStatement, statementEntry, statementSize, statementOutput,
    Configuration.reindex, dispatchLabel, finProdFinEquiv, Fin.ext_iff] using
    run_controlDispatchProgram store S (fun v ↦ exit (f v) v) continuation

/-- Compiling source halt takes one literal DEC instruction and reaches
the machine's ordinary `none` halt configuration. -/
theorem run_compileStatement_halt {n : ℕ}
    (exit : Λ → Option Γ' → Option (Fin n)) (continuation : Program 5 n)
    (store : Option Γ') (S : K' → List Γ') :
    run (compileStatement .halt exit continuation) 1
      ⟨some ((statementEntry (.halt : StackStatement Λ) store).castAdd n), encodeStacks S⟩ =
      (statementOutput exit (Turing.TM2.stepAux .halt store S)).reindex
        (Fin.natAdd (statementSize (.halt : StackStatement Λ))) := by
  simpa [compileStatement, statementEntry, statementSize, statementOutput,
    Configuration.reindex, dispatchLabel, finProdFinEquiv, Fin.ext_iff] using
    run_controlDispatchProgram store S (fun _ ↦ (none : Option (Fin n))) continuation

/-- A proved child execution composes with the literal compiled push.
No property of an external exit instruction is required. -/
theorem run_compileStatement_push {n : ℕ} (j : K') (f : Option Γ' → Γ')
    (q : StackStatement Λ) (exit : Λ → Option Γ' → Option (Fin n))
    (continuation : Program 5 n) (store : Option Γ') (S : K' → List Γ')
    (steps : ℕ)
    (hchild : run (compileStatement q exit continuation) steps
      ⟨some ((statementEntry q store).castAdd n),
        encodeStacks (Function.update S j (f store :: S j))⟩ =
      (statementOutput exit
        (Turing.TM2.stepAux q store (Function.update S j (f store :: S j)))).reindex
          (Fin.natAdd (statementSize q))) :
    run (compileStatement (.push j f q) exit continuation)
      (((6 * contentsCode (S j) + 1) + (2 * (5 * contentsCode (S j)) + 1) +
        ((symbolCode (f store)).val + 1)) + steps)
      ⟨some ((statementEntry (.push j f q) store).castAdd n), encodeStacks S⟩ =
      (statementOutput exit (Turing.TM2.stepAux (.push j f q) store S)).reindex
        (Fin.natAdd (statementSize (.push j f q))) := by
  have hfirst := run_pushDispatchProgram j f store S
    (fun v ↦ some ((statementEntry q v).castAdd n)) (compileStatement q exit continuation)
  have hrun := prefix_run (a := 60) _ (compileStatement q exit continuation) _ steps _
    ⟨some ((statementEntry q store).castAdd n),
      encodeStacks (Function.update S j (f store :: S j))⟩ _ hfirst hchild
  change run (pushDispatchProgram j f (fun v ↦ some ((statementEntry q v).castAdd n))
    (compileStatement q exit continuation)) _ _ = _ at hrun
  have hcast := run_program_cast (Nat.add_assoc 60 (statementSize q) n).symm
    (pushDispatchProgram j f (fun v ↦ some ((statementEntry q v).castAdd n))
      (compileStatement q exit continuation))
    (((6 * contentsCode (S j) + 1) + (2 * (5 * contentsCode (S j)) + 1) +
      ((symbolCode (f store)).val + 1)) + steps)
    ⟨some (dispatchLabel (storeCode store) ((0 : Fin 12).castAdd (statementSize q + n))),
      encodeStacks S⟩
  rw [hrun] at hcast
  simpa [compileStatement, statementEntry, statementSize, familyEntry,
    Configuration.reindex, dispatchLabel, Option.map_map, Function.comp_def,
    Fin.natAdd_natAdd] using hcast

/-- The compiled pop passes the actual head to the finite store update,
removes that head, and then executes its compiled child. -/
theorem run_compileStatement_pop {n : ℕ} (j : K')
    (f : Option Γ' → Option Γ' → Option Γ')
    (q : StackStatement Λ) (exit : Λ → Option Γ' → Option (Fin n))
    (continuation : Program 5 n) (store : Option Γ') (S : K' → List Γ')
    (steps : ℕ)
    (hchild : run (compileStatement q exit continuation) steps
      ⟨some ((statementEntry q (f store (S j).head?)).castAdd n),
        encodeStacks (Function.update S j (S j).tail)⟩ =
      (statementOutput exit
        (Turing.TM2.stepAux q (f store (S j).head?) (Function.update S j (S j).tail))).reindex
          (Fin.natAdd (statementSize q))) :
    run (compileStatement (.pop j f q) exit continuation)
      (((6 * (contentsCode (S j) / 5) + contentsCode (S j) % 5 + 1) +
        (2 * (contentsCode (S j) / 5) + 1)) + steps)
      ⟨some ((statementEntry (.pop j f q) store).castAdd n), encodeStacks S⟩ =
      (statementOutput exit (Turing.TM2.stepAux (.pop j f q) store S)).reindex
        (Fin.natAdd (statementSize (.pop j f q))) := by
  have hfirst := run_popDispatchProgram j f store S
    (fun v ↦ some ((statementEntry q v).castAdd n)) (compileStatement q exit continuation)
  have hrun := prefix_run (a := 80) _ (compileStatement q exit continuation) _ steps _
    ⟨some ((statementEntry q (f store (S j).head?)).castAdd n),
      encodeStacks (Function.update S j (S j).tail)⟩ _ hfirst hchild
  change run (popDispatchProgram j f (fun v ↦ some ((statementEntry q v).castAdd n))
    (compileStatement q exit continuation)) _ _ = _ at hrun
  have hcast := run_program_cast (Nat.add_assoc 80 (statementSize q) n).symm
    (popDispatchProgram j f (fun v ↦ some ((statementEntry q v).castAdd n))
      (compileStatement q exit continuation))
    (((6 * (contentsCode (S j) / 5) + contentsCode (S j) % 5 + 1) +
      (2 * (contentsCode (S j) / 5) + 1)) + steps)
    ⟨some (dispatchLabel (storeCode store) ((0 : Fin 16).castAdd (statementSize q + n))),
      encodeStacks S⟩
  rw [hrun] at hcast
  simpa [compileStatement, statementEntry, statementSize, familyEntry,
    Configuration.reindex, dispatchLabel, Option.map_map, Function.comp_def,
    Fin.natAdd_natAdd] using hcast

/-- A load is a finite table of ordinary zero tests; only the child entry
changes, while all stack registers remain unchanged. -/
theorem run_compileStatement_load {n : ℕ} (f : Option Γ' → Option Γ')
    (q : StackStatement Λ) (exit : Λ → Option Γ' → Option (Fin n))
    (continuation : Program 5 n) (store : Option Γ') (S : K' → List Γ')
    (steps : ℕ)
    (hchild : run (compileStatement q exit continuation) steps
      ⟨some ((statementEntry q (f store)).castAdd n), encodeStacks S⟩ =
      (statementOutput exit (Turing.TM2.stepAux q (f store) S)).reindex
        (Fin.natAdd (statementSize q))) :
    run (compileStatement (.load f q) exit continuation) (1 + steps)
      ⟨some ((statementEntry (.load f q) store).castAdd n), encodeStacks S⟩ =
      (statementOutput exit (Turing.TM2.stepAux (.load f q) store S)).reindex
        (Fin.natAdd (statementSize (.load f q))) := by
  have hfirst := run_controlDispatchProgram store S
    (fun v ↦ some ((statementEntry q (f v)).castAdd n)) (compileStatement q exit continuation)
  have hrun := prefix_run (a := 5) _ (compileStatement q exit continuation) 1 steps _
    ⟨some ((statementEntry q (f store)).castAdd n), encodeStacks S⟩ _ hfirst hchild
  change run (controlDispatchProgram (fun v ↦ some ((statementEntry q (f v)).castAdd n))
    (compileStatement q exit continuation)) _ _ = _ at hrun
  have hcast := run_program_cast (Nat.add_assoc 5 (statementSize q) n).symm
    (controlDispatchProgram (fun v ↦ some ((statementEntry q (f v)).castAdd n))
      (compileStatement q exit continuation)) (1 + steps)
    ⟨some (dispatchLabel (storeCode store) ((0 : Fin 1).castAdd (statementSize q + n))),
      encodeStacks S⟩
  rw [hrun] at hcast
  simpa [compileStatement, statementEntry, statementSize,
    Configuration.reindex, dispatchLabel, Option.map_map, Function.comp_def,
    Fin.natAdd_natAdd, finProdFinEquiv] using hcast

set_option maxRecDepth 2048 in
/-- Peek restores the entire stack before executing its child, whose
finite store receives the actual old head. -/
theorem run_compileStatement_peek {n : ℕ} (j : K')
    (f : Option Γ' → Option Γ' → Option Γ')
    (q : StackStatement Λ) (exit : Λ → Option Γ' → Option (Fin n))
    (continuation : Program 5 n) (store : Option Γ') (S : K' → List Γ')
    (steps : ℕ)
    (hchild : run (compileStatement q exit continuation) steps
      ⟨some ((statementEntry q (f store (S j).head?)).castAdd n), encodeStacks S⟩ =
      (statementOutput exit (Turing.TM2.stepAux q (f store (S j).head?) S)).reindex
        (Fin.natAdd (statementSize q))) :
    run (compileStatement (.peek j f q) exit continuation)
      ((((6 * (contentsCode (S j) / 5) + contentsCode (S j) % 5 + 1) +
        (2 * (contentsCode (S j) / 5) + 1)) +
        restoreSteps (S j).head? (contentsCode (S j).tail)) + steps)
      ⟨some ((statementEntry (.peek j f q) store).castAdd n), encodeStacks S⟩ =
      (statementOutput exit (Turing.TM2.stepAux (.peek j f q) store S)).reindex
        (Fin.natAdd (statementSize (.peek j f q))) := by
  let Q := compileStatement q exit continuation
  let E := fun v ↦ some ((statementEntry q v).castAdd n)
  let mid : Configuration 5 (statementSize q + n) :=
    ⟨E (f store (S j).head?), encodeStacks S⟩
  have hfirst := run_peekDispatchProgram j f store S E Q
  have hnext : run (peekDispatchProgram j f E Q) steps
      ((mid.reindex (Fin.natAdd 300)).reindex (Fin.natAdd 80)) =
      (((statementOutput exit (Turing.TM2.stepAux q (f store (S j).head?) S)).reindex
        (Fin.natAdd (statementSize q))).reindex (Fin.natAdd 300)).reindex (Fin.natAdd 80) := by
    change run (assembleBlock _ (assembleBlock _ Q)) steps _ = _
    rw [run_assembleBlock_continuation, run_assembleBlock_continuation]
    change ((run Q steps mid).reindex (Fin.natAdd 300)).reindex (Fin.natAdd 80) = _
    rw [show run Q steps mid = _ from hchild]
  have hrun := congrArg (fun c ↦ run (peekDispatchProgram j f E Q) steps c) hfirst
  dsimp only at hrun
  rw [← run_add] at hrun
  change run (peekDispatchProgram j f E Q) _ _ =
    run (peekDispatchProgram j f E Q) steps
      ((mid.reindex (Fin.natAdd 300)).reindex (Fin.natAdd 80)) at hrun
  rw [hnext] at hrun
  have hcast := run_program_cast
    (show 80 + (300 + (statementSize q + n)) = (380 + statementSize q) + n by omega)
    (peekDispatchProgram j f E Q)
    ((((6 * (contentsCode (S j) / 5) + contentsCode (S j) % 5 + 1) +
      (2 * (contentsCode (S j) / 5) + 1)) +
      restoreSteps (S j).head? (contentsCode (S j).tail)) + steps)
    ⟨some (dispatchLabel (storeCode store) ((0 : Fin 16).castAdd (300 + (statementSize q + n)))),
      encodeStacks S⟩
  rw [hrun] at hcast
  have hlabels : (fun r : Fin n ↦
      (((r.natAdd (statementSize q)).natAdd 300).natAdd 80).cast
        (show 80 + (300 + (statementSize q + n)) = (380 + statementSize q) + n by omega)) =
      Fin.natAdd (380 + statementSize q) := by
    funext r
    apply Fin.ext
    simp
    omega
  simpa [compileStatement, statementEntry, statementSize, familyEntry, E, Q,
    Configuration.reindex, dispatchLabel, Option.map_map, Function.comp_def, hlabels] using hcast

private theorem statementOutput_map {a b : ℕ}
    (exit : Λ → Option Γ' → Option (Fin a)) (e : Fin a → Fin b)
    (out : Turing.TM2.Cfg (fun _ : K' ↦ Γ') Λ (Option Γ')) :
    statementOutput (fun l store ↦ (exit l store).map e) out =
      (statementOutput exit out).reindex e := by
  cases out with
  | mk label store S => cases label <;> rfl

set_option maxRecDepth 2048 in
/-- Every finite source statement executes in positive finite time to
exactly Mathlib's `stepAux` result. All stack registers match that result,
the shared scratch is zero, and external exit instructions have not run. -/
theorem run_compileStatement (q : StackStatement Λ) {n : ℕ}
    (exit : Λ → Option Γ' → Option (Fin n)) (continuation : Program 5 n)
    (store : Option Γ') (S : K' → List Γ') :
    ∃ steps : ℕ, 0 < steps ∧
      run (compileStatement q exit continuation) steps
        ⟨some ((statementEntry q store).castAdd n), encodeStacks S⟩ =
        (statementOutput exit (Turing.TM2.stepAux q store S)).reindex
          (Fin.natAdd (statementSize q)) := by
  induction q generalizing n store S with
  | goto f => exact ⟨1, by decide, run_compileStatement_goto f exit continuation store S⟩
  | halt => exact ⟨1, by decide, run_compileStatement_halt exit continuation store S⟩
  | push j f q ih =>
      obtain ⟨steps, hpos, hchild⟩ := ih exit continuation store
        (Function.update S j (f store :: S j))
      exact ⟨_, by omega, run_compileStatement_push j f q exit continuation store S steps hchild⟩
  | pop j f q ih =>
      obtain ⟨steps, hpos, hchild⟩ := ih exit continuation (f store (S j).head?)
        (Function.update S j (S j).tail)
      exact ⟨_, by omega, run_compileStatement_pop j f q exit continuation store S steps hchild⟩
  | peek j f q ih =>
      obtain ⟨steps, hpos, hchild⟩ := ih exit continuation (f store (S j).head?) S
      exact ⟨_, by omega, run_compileStatement_peek j f q exit continuation store S steps hchild⟩
  | load f q ih =>
      obtain ⟨steps, hpos, hchild⟩ := ih exit continuation (f store) S
      exact ⟨1 + steps, by omega,
        run_compileStatement_load f q exit continuation store S steps hchild⟩
  | branch f q₁ q₂ ih₁ ih₂ =>
      let tail := compileStatement q₂ exit continuation
      let E := fun l store ↦ (exit l store).map (Fin.natAdd (statementSize q₂))
      let branches := compileStatement q₁ E tail
      let entry := fun v ↦ if f v then
        (statementEntry q₁ v).castAdd (statementSize q₂ + n) else
        ((statementEntry q₂ v).castAdd n).natAdd (statementSize q₁)
      let out := statementOutput exit (Turing.TM2.stepAux (.branch f q₁ q₂) store S)
      have hbranch : ∃ steps : ℕ, 0 < steps ∧
          run branches steps ⟨some (entry store), encodeStacks S⟩ =
          (out.reindex (Fin.natAdd (statementSize q₂))).reindex
            (Fin.natAdd (statementSize q₁)) := by
        cases hf : f store with
        | true =>
            obtain ⟨steps, hpos, hchild⟩ := ih₁ E tail store S
            refine ⟨steps, hpos, ?_⟩
            simpa [branches, entry, out, hf, E, statementOutput_map] using hchild
        | false =>
            obtain ⟨steps, hpos, hchild⟩ := ih₂ exit continuation store S
            have h := run_compileStatement_continuation q₁ E tail steps
              ⟨some ((statementEntry q₂ store).castAdd n), encodeStacks S⟩
            change run branches steps _ =
              (run (compileStatement q₂ exit continuation) steps _).reindex
                (Fin.natAdd (statementSize q₁)) at h
            rw [hchild] at h
            refine ⟨steps, hpos, ?_⟩
            simpa [entry, out, hf, Configuration.reindex] using h
      obtain ⟨steps, hpos, hchild⟩ := hbranch
      have hfirst := run_controlDispatchProgram store S (fun v ↦ some (entry v)) branches
      have hrun := prefix_run (a := 5) _ branches 1 steps _
        ⟨some (entry store), encodeStacks S⟩ _ hfirst hchild
      change run (controlDispatchProgram (fun v ↦ some (entry v)) branches) _ _ = _ at hrun
      have hcast := run_program_cast
        (show 5 + (statementSize q₁ + (statementSize q₂ + n)) =
          (5 + (statementSize q₁ + statementSize q₂)) + n by omega)
        (controlDispatchProgram (fun v ↦ some (entry v)) branches) (1 + steps)
        ⟨some (dispatchLabel (storeCode store)
          ((0 : Fin 1).castAdd (statementSize q₁ + (statementSize q₂ + n)))), encodeStacks S⟩
      rw [hrun] at hcast
      have hlabels : (fun r : Fin n ↦
          (((r.natAdd (statementSize q₂)).natAdd (statementSize q₁)).natAdd 5).cast
            (show 5 + (statementSize q₁ + (statementSize q₂ + n)) =
              (5 + (statementSize q₁ + statementSize q₂)) + n by omega)) =
          Fin.natAdd (5 + (statementSize q₁ + statementSize q₂)) := by
        funext r
        apply Fin.ext
        simp [Nat.add_assoc]
      refine ⟨1 + steps, by omega, ?_⟩
      simpa [compileStatement, statementEntry, statementSize, entry, branches, tail, E, out,
        Configuration.reindex, dispatchLabel, Option.map_map, Function.comp_def,
        hlabels, finProdFinEquiv] using hcast

end TM2Encoding

end Stability.RegisterMachine
