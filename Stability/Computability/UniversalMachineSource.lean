import HGAS.Computability.SigmaOne
import Mathlib.Computability.TuringMachine.ToPartrec

/-!
# A fixed finite-support machine for universal halting

Mathlib's completeness theorem supplies one list-recursive program for
the universal partial-recursive evaluator. Its TM2 compilation therefore
has one fixed finite control support, independent of the encoded input.
The input map is primitive recursive, and its halting predicate agrees
exactly with `HGAS.UniversalHalts`.

This is a stack-machine source, not yet an increment/decrement register
machine. A register-machine universality proof still requires compiling
its finite-alphabet stack operations into arithmetic register macros.
-/

namespace Stability.UniversalMachineSource

open Nat.Partrec

/-- Encode the actual source program and its argument into one natural. -/
def inputCode (input : Code × ℕ) : ℕ := Encodable.encode input

theorem inputCode_primrec : Primrec inputCode := Primrec.encode

/-- The universal evaluator on a single encoded input. -/
def universalEval (n : ℕ) : Part ℕ :=
  let input := Denumerable.ofNat (Code × ℕ) n
  Code.eval input.1 input.2

theorem universalEval_partrec : Partrec universalEval := by
  exact Code.eval_part.comp
    (Computable.fst.comp (Computable.ofNat (Code × ℕ)))
    (Computable.snd.comp (Computable.ofNat (Code × ℕ)))

@[simp]
theorem universalEval_inputCode (input : Code × ℕ) :
    universalEval (inputCode input) = Code.eval input.1 input.2 := by
  unfold universalEval inputCode
  rw [Denumerable.ofNat_encode]

/-- One list-recursive code computes the universal evaluator on singleton
inputs. This code is fixed before the source program and argument vary. -/
theorem exists_interpreterCode :
    ∃ c : Turing.ToPartrec.Code, ∀ n : ℕ,
      c.eval [n] = (fun m ↦ [m]) <$> universalEval n := by
  obtain ⟨c, hc⟩ := Turing.ToPartrec.Code.exists_code
    (Nat.Partrec'.part_iff₁.mpr universalEval_partrec)
  refine ⟨c, fun n ↦ ?_⟩
  exact hc ⟨[n], rfl⟩

/-- A fixed interpreter chosen from Mathlib's proved completeness theorem. -/
noncomputable def interpreterCode : Turing.ToPartrec.Code :=
  Classical.choose exists_interpreterCode

theorem interpreterCode_eval (n : ℕ) :
    interpreterCode.eval [n] = (fun m ↦ [m]) <$> universalEval n :=
  Classical.choose_spec exists_interpreterCode n

/-- The actual initial stack-machine configuration, with no semantic
halting condition stored in it. -/
noncomputable def initial (n : ℕ) : Turing.PartrecToTM2.Cfg' :=
  Turing.PartrecToTM2.init interpreterCode [n]

/-- Halting of the one fixed stack-machine interpreter. -/
def Halts (n : ℕ) : Prop :=
  (StateTransition.eval (Turing.TM2.step Turing.PartrecToTM2.tr) (initial n)).Dom

theorem halts_iff_universalEval_dom (n : ℕ) :
    Halts n ↔ (universalEval n).Dom := by
  rw [Halts, initial, Turing.PartrecToTM2.tr_eval, interpreterCode_eval]
  rfl

/-- The computable input encoding preserves both halting and divergence. -/
theorem halts_inputCode_iff (input : Code × ℕ) :
    Halts (inputCode input) ↔ HGAS.UniversalHalts input := by
  rw [halts_iff_universalEval_dom, universalEval_inputCode]
  rfl

/-- Universal halting reduces to the actual fixed stack-machine run. -/
theorem universalHalts_manyOneReducible : HGAS.UniversalHalts ≤₀ Halts :=
  ⟨inputCode, inputCode_primrec.to_comp, fun input ↦ (halts_inputCode_iff input).symm⟩

theorem halts_re : REPred Halts :=
  universalEval_partrec.dom_re.of_eq fun n ↦ (halts_iff_universalEval_dom n).symm

/-- The actual fixed interpreter has a complete c.e. halting language. -/
theorem halts_sigmaOneComplete : HGAS.SigmaOneComplete Halts :=
  HGAS.sigmaOneComplete_of_universalHalts_reduction halts_re universalHalts_manyOneReducible

theorem halts_not_computable : ¬ ComputablePred Halts :=
  halts_sigmaOneComplete.not_computable

theorem halts_complement_not_re : ¬ REPred (fun n ↦ ¬ Halts n) :=
  halts_sigmaOneComplete.complement_not_re

/-- The same finite set of labels supports every input run. -/
noncomputable def controlSupport : Finset Turing.PartrecToTM2.Λ' :=
  Turing.PartrecToTM2.codeSupp interpreterCode .halt

/-- Finite support is proved by the compiler, not assumed as part of the
interpreter's specification. -/
theorem interpreter_supports :
    @Turing.TM2.Supports _ _ _ _
      ⟨Turing.PartrecToTM2.trNormal interpreterCode .halt⟩
      Turing.PartrecToTM2.tr controlSupport :=
  Turing.PartrecToTM2.tr_supports interpreterCode .halt

/-- Every reachable control label belongs to the fixed support (or is
the halting label), independently of the input. -/
theorem reachable_label_mem_support {n : ℕ} {c : Turing.PartrecToTM2.Cfg'}
    (h : StateTransition.Reaches (Turing.TM2.step Turing.PartrecToTM2.tr) (initial n) c) :
    c.l ∈ Finset.insertNone controlSupport := by
  letI : Inhabited Turing.PartrecToTM2.Λ' :=
    ⟨Turing.PartrecToTM2.trNormal interpreterCode .halt⟩
  induction h with
  | refl =>
      exact Finset.some_mem_insertNone.mpr interpreter_supports.1
  | tail _ hstep ih =>
      exact Turing.TM2.step_supports _ interpreter_supports hstep ih

end Stability.UniversalMachineSource
