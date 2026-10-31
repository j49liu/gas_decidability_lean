import Stability.Computability.RegisterMachine
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.Halting

/-!
# Primitive-recursive finite runs and enumerable halting

Packed configurations use the existing product, option, and finite-vector
encodings. A fixed instruction is primitive recursive, finite control
dispatch is primitive recursive, and finite iteration is primitive
recursive. Searching for the literal halt label therefore semidecides
the ordinary register-input halting language of every finite program.
-/

namespace Stability.RegisterMachine

variable {k s : ℕ}

/-- Existing primitive-recursive encodings suffice for the complete state. -/
abbrev PackedConfiguration (k s : ℕ) := Option (Fin s) × (Fin k → ℕ)

def pack (c : Configuration k s) : PackedConfiguration k s := (c.label, c.registers)

def unpack (c : PackedConfiguration k s) : Configuration k s := ⟨c.1, c.2⟩

private theorem update_primrec {α : Type*} [Primcodable α]
    {r : α → Fin k → ℕ} {v : α → ℕ} (hr : Primrec r) (hv : Primrec v) (i : Fin k) :
    Primrec (fun a ↦ Function.update (r a) i (v a)) := by
  apply Primrec.fin_curry.mpr
  exact (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const i))
    (hv.comp Primrec.fst)
    (Primrec.fin_app.comp (hr.comp Primrec.fst) Primrec.snd)).of_eq
      (fun p ↦ by simp [Function.update_apply])

/-- Execute one literal instruction in the standard packed encoding. -/
def packedExecute (instruction : Instruction k s) (r : Fin k → ℕ) : PackedConfiguration k s :=
  pack (execute instruction r)

theorem packedExecute_primrec (instruction : Instruction k s) :
    Primrec (packedExecute instruction) := by
  cases instruction with
  | inc i next =>
      exact Primrec.pair (Primrec.const next)
        (update_primrec Primrec.id
          (Primrec.succ.comp (Primrec.fin_app.comp Primrec.id (Primrec.const i))) i)
  | dec i zero positive =>
      have hvalue : Primrec (fun r : Fin k → ℕ ↦ r i) :=
        Primrec.fin_app.comp Primrec.id (Primrec.const i)
      exact (Primrec.ite (Primrec.eq.comp hvalue (Primrec.const 0))
        (Primrec.pair (Primrec.const zero) Primrec.id)
        (Primrec.pair (Primrec.const positive)
          (update_primrec Primrec.id (Primrec.nat_sub.comp hvalue (Primrec.const 1)) i))).of_eq
            (fun r ↦ by by_cases h : r i = 0 <;> simp [packedExecute, pack, execute, h])

/-- The actual total transition, including its absorbing halted state. -/
def packedStep (P : Program k s) (c : PackedConfiguration k s) : PackedConfiguration k s :=
  pack (step P (unpack c))

theorem packedStep_primrec (P : Program k s) : Primrec (packedStep P) := by
  have hdispatch : Primrec₂ (fun q : Fin s ↦ packedExecute (P q)) :=
    Primrec.fin_curry₁.mpr fun q ↦ packedExecute_primrec (P q)
  exact (Primrec.option_casesOn Primrec.fst Primrec.id
    (hdispatch.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).to₂).of_eq
      (fun c ↦ by cases c with | mk label r => cases label <;> rfl)

/-- Exact finite iteration on packed states. -/
def packedRun (P : Program k s) (steps : ℕ) (c : PackedConfiguration k s) :
    PackedConfiguration k s := (packedStep P)^[steps] c

theorem packedRun_eq (P : Program k s) (steps : ℕ) (c : Configuration k s) :
    packedRun P steps (pack c) = pack (run P steps c) := by
  induction steps generalizing c with
  | zero => rfl
  | succ steps ih =>
      change (packedStep P)^[steps + 1] (pack c) = _
      rw [Function.iterate_succ_apply]
      exact ih (step P c)

theorem packedRun_primrec (P : Program k s) : Primrec₂ (packedRun P) :=
  Primrec.nat_iterate Primrec.fst Primrec.snd
    ((packedStep_primrec P).comp Primrec.snd).to₂

/-- A total Boolean check for halting within a specified finite run. -/
def checkHalts (P : Program k s) (entry : Fin s) (input : Fin k) (n steps : ℕ) : Bool :=
  (packedRun P steps (pack (initial entry input n))).1 == none

theorem checkHalts_primrec (P : Program k s) (entry : Fin s) (input : Fin k) :
    Primrec₂ (checkHalts P entry input) := by
  have hinitial : Primrec (fun n ↦ pack (initial entry input n)) :=
    Primrec.pair (Primrec.const (some entry))
      (update_primrec (Primrec.const (fun _ ↦ 0)) Primrec.id input)
  exact (Primrec.beq.comp
    (Primrec.fst.comp ((packedRun_primrec P).comp Primrec.snd (hinitial.comp Primrec.fst)))
    (Primrec.const none)).of_eq (fun p ↦ by
      unfold checkHalts
      cases (packedRun P p.2 (pack (initial entry input p.1))).1 <;> rfl)

/-- Semidecidability holds for every raw natural input, including numbers
which do not encode a valid source stack. -/
theorem halts_re (P : Program k s) (entry : Fin s) (input : Fin k) :
    REPred (fun n ↦ Halts P (initial entry input n)) := by
  have hsearch : Partrec (fun n ↦ Nat.rfind
      (fun steps ↦ Part.some (checkHalts P entry input n steps))) :=
    Partrec.rfind (checkHalts_primrec P entry input).to_comp.partrec
  apply REPred.of_eq hsearch.dom_re
  intro n
  rw [Nat.rfind_dom]
  simp only [checkHalts, packedRun_eq]
  simp [pack, Halts]

end Stability.RegisterMachine
