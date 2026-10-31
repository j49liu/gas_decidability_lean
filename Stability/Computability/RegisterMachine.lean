import Mathlib.Computability.StateTransition
import Mathlib.Tactic

/-!
# Finite increment/decrement register machines

Registers contain natural numbers. The only instructions increment one
register, or test one register for zero and decrement it in the positive
branch. There are finitely many registers and active labels; `none` is
the halting label. A halted configuration stays fixed under the total
step map. The partial transition map instead returns `none` there, as
required by Mathlib's `StateTransition` interface.

The clear and transfer lemmas below concern actual finite instruction
sequences, including their final zero test. They work inside any program
containing the stated instructions and preserve every other register.
This file does not assert the existence of a universal register machine.
-/

namespace Stability.RegisterMachine

open Function

/-- The two instructions of a finite register machine. -/
inductive Instruction (k s : ℕ) where
  /-- Increment register `r` and jump to `next`. -/
  | inc (r : Fin k) (next : Option (Fin s))
  /-- Test `r`; preserve zero or decrement a positive value, then jump. -/
  | dec (r : Fin k) (zero positive : Option (Fin s))
  deriving DecidableEq

/-- A program assigns an instruction to each active label. -/
abbrev Program (k s : ℕ) := Fin s → Instruction k s

/-- A register configuration, with `none` denoting the halting label. -/
@[ext]
structure Configuration (k s : ℕ) where
  /-- The current active label, or the halting label. -/
  label : Option (Fin s)
  /-- The current contents of the finite family of registers. -/
  registers : Fin k → ℕ
  deriving DecidableEq

variable {k s : ℕ}

/-- Execute one instruction. The zero branch does not change a register. -/
def execute (instruction : Instruction k s) (r : Fin k → ℕ) : Configuration k s :=
  match instruction with
  | .inc i next => ⟨next, update r i (r i + 1)⟩
  | .dec i zero positive =>
      if r i = 0 then ⟨zero, r⟩ else ⟨positive, update r i (r i - 1)⟩

/-- The total discrete dynamics, with an absorbing halting state. -/
def step (P : Program k s) (c : Configuration k s) : Configuration k s :=
  match c.label with
  | none => c
  | some q => execute (P q) c.registers

/-- The partial transition interface used by Mathlib machine simulations. -/
def transition (P : Program k s) (c : Configuration k s) : Option (Configuration k s) :=
  match c.label with
  | none => none
  | some q => some (execute (P q) c.registers)

/-- Execute exactly `n` total steps. -/
def run (P : Program k s) : ℕ → Configuration k s → Configuration k s
  | 0, c => c
  | n + 1, c => run P n (step P c)

/-- Start at `entry`, placing the input in one designated register. -/
def initial (entry : Fin s) (input : Fin k) (n : ℕ) : Configuration k s :=
  ⟨some entry, update (fun _ ↦ 0) input n⟩

/-- Halting means reaching the literal halting label after finitely many steps. -/
def Halts (P : Program k s) (c : Configuration k s) : Prop :=
  ∃ n, (run P n c).label = none

@[simp]
theorem step_halted (P : Program k s) (r : Fin k → ℕ) :
    step P ⟨none, r⟩ = ⟨none, r⟩ := rfl

@[simp]
theorem transition_eq_none_iff (P : Program k s) (c : Configuration k s) :
    transition P c = none ↔ c.label = none := by
  cases c with
  | mk label r => cases label <;> simp [transition]

@[simp]
theorem run_zero (P : Program k s) (c : Configuration k s) : run P 0 c = c := rfl

theorem run_succ (P : Program k s) (n : ℕ) (c : Configuration k s) :
    run P (n + 1) c = run P n (step P c) := rfl

theorem run_add (P : Program k s) (m n : ℕ) (c : Configuration k s) :
    run P (m + n) c = run P n (run P m c) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih => simpa only [Nat.succ_add, run] using ih (step P c)

@[simp]
theorem run_halted (P : Program k s) (n : ℕ) (r : Fin k → ℕ) :
    run P n ⟨none, r⟩ = ⟨none, r⟩ := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

/-- Reaching halt makes every later total step constant. -/
theorem run_eq_of_halted (P : Program k s) (m n : ℕ) (c : Configuration k s)
    (h : (run P m c).label = none) :
    run P (m + n) c = run P m c := by
  rw [run_add]
  generalize run P m c = d at h ⊢
  cases d with
  | mk label r =>
      change label = none at h
      subst label
      exact run_halted P n r

private theorem step_eq_of_mem_transition {P : Program k s}
    {c d : Configuration k s} (h : d ∈ transition P c) : step P c = d := by
  cases c with
  | mk label r => cases label <;> simp_all [transition, step]

/-- Total iteration reaches the same configuration through the partial
transition relation; extra halted iterations require no transition. -/
theorem reaches_run (P : Program k s) (n : ℕ) (c : Configuration k s) :
    StateTransition.Reaches (transition P) c (run P n c) := by
  induction n generalizing c with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih =>
      cases c with
      | mk label r =>
          cases label with
          | none => simpa only [run_halted] using
              (Relation.ReflTransGen.refl :
                StateTransition.Reaches (transition P) ⟨none, r⟩ ⟨none, r⟩)
          | some q => exact Relation.ReflTransGen.head rfl (ih (execute (P q) r))

/-- Partial reachability is exactly finite total iteration. -/
theorem reaches_iff_exists_run (P : Program k s) (c d : Configuration k s) :
    StateTransition.Reaches (transition P) c d ↔ ∃ n, run P n c = d := by
  constructor
  · intro h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨0, rfl⟩
    | @head a b hab _ ih =>
        obtain ⟨n, hn⟩ := ih
        exact ⟨n + 1, by rw [run_succ, step_eq_of_mem_transition hab, hn]⟩
  · rintro ⟨n, rfl⟩
    exact reaches_run P n c

/-- Literal register-machine halting agrees with Mathlib's partial
transition evaluator. No halting hypothesis is built into the machine. -/
theorem halts_iff_eval_dom (P : Program k s) (c : Configuration k s) :
    Halts P c ↔ (StateTransition.eval (transition P) c).Dom := by
  rw [Part.dom_iff_mem]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨run P n c, StateTransition.mem_eval.mpr
      ⟨reaches_run P n c, (transition_eq_none_iff P _).mpr hn⟩⟩
  · rintro ⟨d, hd⟩
    obtain ⟨hreach, hhalt⟩ := StateTransition.mem_eval.mp hd
    obtain ⟨n, hn⟩ := (reaches_iff_exists_run P c d).mp hreach
    exact ⟨n, hn ▸ (transition_eq_none_iff P d).mp hhalt⟩

theorem step_inc {P : Program k s} {q : Fin s} {i : Fin k}
    {next : Option (Fin s)} (h : P q = .inc i next) (r : Fin k → ℕ) :
    step P ⟨some q, r⟩ = ⟨next, update r i (r i + 1)⟩ := by
  simp [step, execute, h]

theorem step_dec_zero {P : Program k s} {q : Fin s} {i : Fin k}
    {zero positive : Option (Fin s)} (h : P q = .dec i zero positive)
    (r : Fin k → ℕ) (hr : r i = 0) :
    step P ⟨some q, r⟩ = ⟨zero, r⟩ := by
  simp [step, execute, h, hr]

theorem step_dec_positive {P : Program k s} {q : Fin s} {i : Fin k}
    {zero positive : Option (Fin s)} (h : P q = .dec i zero positive)
    (r : Fin k → ℕ) (hr : 0 < r i) :
    step P ⟨some q, r⟩ = ⟨positive, update r i (r i - 1)⟩ := by
  simp [step, execute, h, Nat.ne_of_gt hr]

/-- A single decrement loop clears one register in its initial value plus
one steps. The last step is the zero test and jump to `exit`. -/
theorem run_clear {P : Program k s} {loop : Fin s} {i : Fin k}
    {exit : Option (Fin s)} (hcode : P loop = .dec i exit (some loop))
    (r : Fin k → ℕ) :
    run P (r i + 1) ⟨some loop, r⟩ = ⟨exit, update r i 0⟩ := by
  generalize hn : r i = n
  induction n generalizing r with
  | zero =>
      rw [run_succ, step_dec_zero hcode r hn, run_zero]
      congr 1
      exact (update_eq_self i r).symm.trans (congrArg (update r i) hn)
  | succ n ih =>
      rw [run_succ, step_dec_positive hcode r (by omega)]
      simpa [hn] using ih (update r i (r i - 1)) (by simp [hn])

/-- The transfer loop tests/decrements `source`, increments `target`, and
returns to the test. Distinct registers are essential. It takes two steps
per transferred unit and one final zero test, with no scratch register. -/
theorem run_transfer {P : Program k s} {test add : Fin s} {source target : Fin k}
    {exit : Option (Fin s)} (hne : source ≠ target)
    (htest : P test = .dec source exit (some add))
    (hadd : P add = .inc target (some test)) (r : Fin k → ℕ) :
    run P (2 * r source + 1) ⟨some test, r⟩ =
      ⟨exit, update (update r source 0) target (r target + r source)⟩ := by
  generalize hn : r source = n
  induction n generalizing r with
  | zero =>
      rw [show 2 * 0 + 1 = 1 by omega, run_succ,
        step_dec_zero htest r hn, run_zero]
      congr 1
      ext j
      by_cases hjt : j = target
      · subst j; simp
      · by_cases hjs : j = source
        · subst j; simp [hne, hn]
        · simp [hjt, hjs]
  | succ n ih =>
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 by omega,
        run_succ, step_dec_positive htest r (by omega), run_succ, step_inc hadd]
      have hsource : (update (update r source (r source - 1)) target
          ((update r source (r source - 1)) target + 1)) source = n := by
        simp [hne, hn]
      rw [ih _ hsource]
      congr 1
      ext j
      by_cases hjt : j = target
      · subst j
        simp only [update_self, update_of_ne (Ne.symm hne)]
        omega
      · by_cases hjs : j = source
        · subst j; simp [hne]
        · simp [hjt, hjs]

/-- A closed one-instruction program implementing the clear macro. -/
def clearProgram (i : Fin k) : Program k 1 :=
  fun _ ↦ .dec i none (some 0)

/-- A closed two-instruction program implementing the transfer macro. -/
def transferProgram (source target : Fin k) : Program k 2 :=
  fun q ↦ if q = 0 then .dec source none (some 1) else .inc target (some 0)

theorem clearProgram_halts (i : Fin k) (r : Fin k → ℕ) :
    Halts (clearProgram i) ⟨some 0, r⟩ := by
  refine ⟨r i + 1, ?_⟩
  rw [run_clear (show clearProgram i 0 = .dec i none (some 0) from rfl)]

theorem transferProgram_halts {source target : Fin k} (hne : source ≠ target)
    (r : Fin k → ℕ) : Halts (transferProgram source target) ⟨some 0, r⟩ := by
  refine ⟨2 * r source + 1, ?_⟩
  rw [run_transfer (test := 0) (add := 1) (exit := none) hne
    (by simp [transferProgram]) (by simp [transferProgram])]

end Stability.RegisterMachine
