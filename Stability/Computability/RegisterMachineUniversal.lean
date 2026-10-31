import Stability.Computability.RegisterMachineSupport
import Stability.Computability.RegisterMachineInput
import Stability.Computability.RegisterMachineComputability
import Stability.Computability.UniversalMachineSource

/-!
# One fixed universal INC/DEC register machine

The finite-support TM2 interpreter for the universal partial-recursive
evaluator is restricted to finite labels and compiled by the actual stack
compiler. The resulting INC/DEC program is fixed, has five registers,
and starts with input in register zero and all other registers zero.
The primitive-recursive input map encodes Mathlib's literal binary stack.
-/

noncomputable section

namespace Stability.UniversalRegisterMachine

open RegisterMachine RegisterMachine.TM2Encoding Turing.PartrecToTM2

local instance : Inhabited Λ' :=
  ⟨trNormal UniversalMachineSource.interpreterCode .halt⟩

/-- The single finite-control source machine, independent of the input. -/
def stackMachine : Fin UniversalMachineSource.controlSupport.card →
    StackStatement (Fin UniversalMachineSource.controlSupport.card) :=
  supportedMachine tr UniversalMachineSource.controlSupport
    UniversalMachineSource.interpreter_supports

/-- Number of labels in the single compiled register program. -/
def labelCount : ℕ :=
  UniversalMachineSource.controlSupport.card * finiteProgramWidth stackMachine

/-- The fixed ordinary INC/DEC program obtained from the universal evaluator. -/
def program : Program 5 labelCount := compileFiniteMachine stackMachine

/-- The fixed initial control label, carrying the empty finite store. -/
def entry : Fin labelCount :=
  rootEntry stackMachine (statementSize_le_finiteProgramWidth stackMachine)
    (supportLabelCode UniversalMachineSource.controlSupport
      UniversalMachineSource.interpreter_supports.1
      (trNormal UniversalMachineSource.interpreterCode .halt)) none

/-- Literal halting with the natural input in register zero. -/
def Halts (n : ℕ) : Prop := RegisterMachine.Halts program (initial entry 0 n)

/-- The compiled source initialization is exactly the ordinary register
initialization with the actual input-stack numeral in register zero. -/
theorem encode_initial (n : ℕ) :
    encodeConfiguration stackMachine (statementSize_le_finiteProgramWidth stackMachine)
      (mapConfigurationLabels
        (supportLabelCode UniversalMachineSource.controlSupport
          UniversalMachineSource.interpreter_supports.1) (UniversalMachineSource.initial n)) =
      initial entry 0 (inputNumeral n) := by
  apply Configuration.ext
  · rfl
  · funext j
    fin_cases j <;> rfl

/-- The actual fixed register program preserves both halting and
divergence of the fixed universal stack interpreter. -/
theorem halts_inputNumeral_iff (n : ℕ) :
    Halts (inputNumeral n) ↔ UniversalMachineSource.Halts n := by
  have hfinite := compileFiniteMachine_halts_iff stackMachine
    (mapConfigurationLabels
      (supportLabelCode UniversalMachineSource.controlSupport
        UniversalMachineSource.interpreter_supports.1) (UniversalMachineSource.initial n))
  rw [encode_initial] at hfinite
  exact hfinite.trans (supportedMachine_eval_dom_iff tr UniversalMachineSource.controlSupport
    UniversalMachineSource.interpreter_supports (UniversalMachineSource.initial n)
    (UniversalMachineSource.reachable_label_mem_support Relation.ReflTransGen.refl))

/-- Primitive-recursive many-one encoding from a source code and argument
to the single input register of the fixed INC/DEC program. -/
def inputCode (input : Nat.Partrec.Code × ℕ) : ℕ :=
  inputNumeral (UniversalMachineSource.inputCode input)

theorem inputCode_primrec : Primrec inputCode :=
  inputNumeral_primrec.comp UniversalMachineSource.inputCode_primrec

theorem halts_inputCode_iff (input : Nat.Partrec.Code × ℕ) :
    Halts (inputCode input) ↔ HGAS.UniversalHalts input :=
  (halts_inputNumeral_iff _).trans (UniversalMachineSource.halts_inputCode_iff input)

/-- Genuine universal-halting hardness of one fixed five-register finite
INC/DEC program. No universality or simulation condition is assumed. -/
theorem universalHalts_manyOneReducible : HGAS.UniversalHalts ≤₀ Halts :=
  ⟨inputCode, inputCode_primrec.to_comp, fun input ↦ (halts_inputCode_iff input).symm⟩

/-- Every raw input has a semidecidable literal machine run, regardless
of whether it belongs to the range of the source input encoding. -/
theorem halts_re : REPred Halts := RegisterMachine.halts_re program entry 0

/-- The standard input-register halting language of the fixed program is
computably enumerable complete. -/
theorem halts_sigmaOneComplete : HGAS.SigmaOneComplete Halts :=
  HGAS.sigmaOneComplete_of_universalHalts_reduction halts_re universalHalts_manyOneReducible

theorem halts_not_computable : ¬ ComputablePred Halts := by
  intro h
  exact HGAS.universalHalts_sigmaOneComplete.not_computable
    (ComputablePred.computable_of_manyOneReducible universalHalts_manyOneReducible h)

theorem halts_complement_not_re : ¬ REPred (fun n ↦ ¬ Halts n) := by
  intro h
  apply HGAS.universalHalts_sigmaOneComplete.complement_not_re
  exact REPred.of_eq (h.comp inputCode_primrec.to_comp) fun input ↦
    not_congr (halts_inputCode_iff input)

end Stability.UniversalRegisterMachine
