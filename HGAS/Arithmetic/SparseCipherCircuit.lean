import HGAS.Arithmetic.SparseCipherIndex
import HGAS.Arithmetic.PolynomialGateCompiler
import Mathlib.Tactic

/-!
# Finite arithmetic circuits evaluated in parallel by sparse ciphers

Each sparse cipher stores one finite sequence.  Consequently a finite
arithmetic circuit can be evaluated at every sequence position in
parallel: constants use `ConstCode`, addition uses `CodeAdd`, and
multiplication uses `CodeMul`.

This module packages that observation independently of any particular
polynomial.  Its main results are:

* `cipherGate_spec`, correctness for one gate;
* `cipherCircuit_spec`, correctness for an arbitrary finite circuit;
* `cipherCircuit_dioph`, unconditional Diophantineness of the complete
  parallel circuit relation.

The module is the reusable bridge from the number-theoretic cipher to
the existing natural arithmetic circuit compiler.
-/

namespace HGAS

namespace SparseCipherCircuit

open SparseCipherCode
open SparseCipherOperations
open Vector3
open scoped Vector3

/-! ## Finite conjunctions of Diophantine relations -/

/-- A fixed finite conjunction of Diophantine relations is
Diophantine. -/
theorem dioph_forall_fin
    {α : Type} {count : ℕ}
    {predicate : Fin count → (α → ℕ) → Prop}
    (hpredicate :
      ∀ i, Dioph {v : α → ℕ | predicate i v}) :
    Dioph {v : α → ℕ | ∀ i, predicate i v} := by
  induction count with
  | zero =>
      have htrivial :
          Dioph {v : α → ℕ | (0 : ℕ) = 0} :=
        Dioph.eq_dioph
          (Dioph.const_dioph 0)
          (Dioph.const_dioph 0)
      exact
        Dioph.ext htrivial fun v => by
          simp
  | succ count ih =>
      have hhead :
          Dioph {v : α → ℕ |
            predicate 0 v} :=
        hpredicate 0
      have htail :
          Dioph {v : α → ℕ |
            ∀ i : Fin count,
              predicate i.succ v} :=
        ih (fun i => hpredicate i.succ)
      exact
        Dioph.ext (hhead.inter htail) fun v => by
          simp only [Set.mem_inter_iff,
            Set.mem_setOf_eq]
          exact
            (@Fin.forall_fin_succ count
              (fun i => predicate i v)).symm

/-! ## One gate -/

/-- Natural-number semantics of one arithmetic gate. -/
def NatGateHolds
    {vars : ℕ} (gate : ArithmeticGate vars)
    (value : Fin vars → ℕ) : Prop :=
  match gate with
  | .zero x => value x = 0
  | .one x => value x = 1
  | .add x y z => value z = value x + value y
  | .mul x y z => value z = value x * value y

/-- The direct natural-number gate semantics used by sparse ciphers is
exactly the natural circuit semantics used by the arithmetic compiler. -/
theorem natGateHolds_iff_arithmeticGateHolds
    {vars : ℕ} (gate : ArithmeticGate vars)
    (value : Fin vars → ℕ) :
    NatGateHolds gate value ↔
      gate.Holds (fun i => (value i : ℤ)) := by
  cases gate <;>
    simp only [NatGateHolds, ArithmeticGate.Holds] <;>
    norm_cast <;> omega

/-- Pointwise `NatGateHolds` for every gate is the existing
`NaturalCircuitHolds` predicate. -/
theorem natGatesHold_iff_naturalCircuitHolds
    {vars : ℕ} (gates : List (ArithmeticGate vars))
    (value : Fin vars → ℕ) :
    (∀ gateIndex : Fin gates.length,
      NatGateHolds (gates.get gateIndex) value) ↔
      GateDQLCompiler.NaturalCircuitHolds gates value := by
  unfold GateDQLCompiler.NaturalCircuitHolds
    ArithmeticCircuitHolds
  exact forall_congr' fun gateIndex =>
    natGateHolds_iff_arithmeticGateHolds
      (gates.get gateIndex) value

/-- Sparse-cipher realization of one arithmetic gate. -/
def CipherGateHolds
    {vars : ℕ} (length q : ℕ)
    (code : Fin vars → ℕ)
    (gate : ArithmeticGate vars) : Prop :=
  match gate with
  | .zero x =>
      ConstCode length q 0 (code x)
  | .one x =>
      ConstCode length q 1 (code x)
  | .add x y z =>
      CodeAdd (code z) (code x) (code y)
  | .mul x y z =>
      CodeMul length q (code z) (code x) (code y)

/-- Correctness of one parallel cipher gate, assuming every register is
a valid cipher. -/
theorem cipherGate_spec
    {vars length q : ℕ}
    {code : Fin vars → ℕ}
    {entry : Fin vars → Fin length → ℕ}
    (hentry :
      ∀ register,
        CipherOf length q
          (entry register) (code register))
    (gate : ArithmeticGate vars) :
    CipherGateHolds length q code gate ↔
      ∀ position,
        NatGateHolds gate
          (fun register => entry register position) := by
  cases gate with
  | zero x =>
      exact constCode_spec (hentry x)
  | one x =>
      exact constCode_spec (hentry x)
  | add x y z =>
      exact codeAdd_spec
        (hentry z) (hentry x) (hentry y)
  | mul x y z =>
      exact codeMul_spec
        (hentry z) (hentry x) (hentry y)

/-! ## Diophantineness of one gate -/

theorem constCode_comp_dioph
    {α : Type}
    {length q coefficient value :
      (α → ℕ) → ℕ}
    (hlength : Dioph.DiophFn length)
    (hq : Dioph.DiophFn q)
    (hcoefficient : Dioph.DiophFn coefficient)
    (hvalue : Dioph.DiophFn value) :
    Dioph {v : α → ℕ |
      ConstCode (length v) (q v)
        (coefficient v) (value v)} := by
  have hbase :
      Dioph {v : Vector3 ℕ 4 |
        ConstCode
          (v (Fin2.ofFin 0)) (v (Fin2.ofFin 1))
          (v (Fin2.ofFin 2)) (v (Fin2.ofFin 3))} :=
    Dioph.reindex_dioph
      (Fin2 4) Fin2.ofFin constCode_dioph
  exact
    Dioph.dioph_comp hbase
      [length, q, coefficient, value]
      ⟨hlength, hq, hcoefficient, hvalue⟩

theorem codeAdd_comp_dioph
    {α : Type}
    {result left right : (α → ℕ) → ℕ}
    (hresult : Dioph.DiophFn result)
    (hleft : Dioph.DiophFn left)
    (hright : Dioph.DiophFn right) :
    Dioph {v : α → ℕ |
      CodeAdd (result v) (left v) (right v)} := by
  have hbase :
      Dioph {v : Vector3 ℕ 3 |
        CodeAdd
          (v (Fin2.ofFin 0)) (v (Fin2.ofFin 1))
          (v (Fin2.ofFin 2))} :=
    Dioph.reindex_dioph
      (Fin2 3) Fin2.ofFin codeAdd_dioph
  exact
    Dioph.dioph_comp hbase
      [result, left, right]
      ⟨hresult, hleft, hright⟩

theorem codeMul_comp_dioph
    {α : Type}
    {length q result left right :
      (α → ℕ) → ℕ}
    (hlength : Dioph.DiophFn length)
    (hq : Dioph.DiophFn q)
    (hresult : Dioph.DiophFn result)
    (hleft : Dioph.DiophFn left)
    (hright : Dioph.DiophFn right) :
    Dioph {v : α → ℕ |
      CodeMul (length v) (q v)
        (result v) (left v) (right v)} := by
  have hbase :
      Dioph {v : Vector3 ℕ 5 |
        CodeMul
          (v (Fin2.ofFin 0)) (v (Fin2.ofFin 1))
          (v (Fin2.ofFin 2)) (v (Fin2.ofFin 3))
          (v (Fin2.ofFin 4))} :=
    Dioph.reindex_dioph
      (Fin2 5) Fin2.ofFin codeMul_dioph
  exact
    Dioph.dioph_comp hbase
      [length, q, result, left, right]
      ⟨hlength, hq, hresult, hleft, hright⟩

/-- One fixed cipher gate is a Diophantine relation in the shared
parameters `(length,q)` and the register-code vector. -/
theorem cipherGate_dioph
    {vars : ℕ} (gate : ArithmeticGate vars) :
    Dioph {v : (Fin 2 ⊕ Fin vars) → ℕ |
      CipherGateHolds
        (v (Sum.inl 0)) (v (Sum.inl 1))
        (fun i => v (Sum.inr i)) gate} := by
  let lengthFn :
      (((Fin 2 ⊕ Fin vars) → ℕ) → ℕ) :=
    fun v => v (Sum.inl 0)
  let qFn :
      (((Fin 2 ⊕ Fin vars) → ℕ) → ℕ) :=
    fun v => v (Sum.inl 1)
  have hlength : Dioph.DiophFn lengthFn :=
    Dioph.proj_dioph (Sum.inl 0)
  have hq : Dioph.DiophFn qFn :=
    Dioph.proj_dioph (Sum.inl 1)
  have hzero :
      Dioph.DiophFn
        (fun _ : (Fin 2 ⊕ Fin vars) → ℕ => 0) :=
    Dioph.const_dioph 0
  have hone :
      Dioph.DiophFn
        (fun _ : (Fin 2 ⊕ Fin vars) → ℕ => 1) :=
    Dioph.const_dioph 1
  cases gate with
  | zero x =>
      simpa only [CipherGateHolds, lengthFn, qFn] using
        constCode_comp_dioph hlength hq hzero
          (Dioph.proj_dioph (Sum.inr x))
  | one x =>
      simpa only [CipherGateHolds, lengthFn, qFn] using
        constCode_comp_dioph hlength hq hone
          (Dioph.proj_dioph (Sum.inr x))
  | add x y z =>
      simpa only [CipherGateHolds] using
        codeAdd_comp_dioph
          (Dioph.proj_dioph (Sum.inr z))
          (Dioph.proj_dioph (Sum.inr x))
          (Dioph.proj_dioph (Sum.inr y))
  | mul x y z =>
      simpa only [CipherGateHolds, lengthFn, qFn] using
        codeMul_comp_dioph hlength hq
          (Dioph.proj_dioph (Sum.inr z))
          (Dioph.proj_dioph (Sum.inr x))
          (Dioph.proj_dioph (Sum.inr y))

/-! ## Complete finite circuits -/

/-- All registers are valid ciphers and every circuit gate holds in
parallel at every encoded position. -/
def CipherCircuitHolds
    {vars : ℕ} (gates : List (ArithmeticGate vars))
    (length q : ℕ) (code : Fin vars → ℕ) : Prop :=
  (∀ register, Code length q (code register)) ∧
  ∀ gateIndex : Fin gates.length,
    CipherGateHolds length q code (gates.get gateIndex)

/-- Exact tuple semantics of a finite parallel cipher circuit. -/
theorem cipherCircuit_spec
    {vars length q : ℕ}
    (gates : List (ArithmeticGate vars))
    (code : Fin vars → ℕ) :
    CipherCircuitHolds gates length q code ↔
      ∃ entry : Fin vars → Fin length → ℕ,
        (∀ register,
          CipherOf length q
            (entry register) (code register)) ∧
        ∀ gateIndex : Fin gates.length,
          ∀ position,
            NatGateHolds (gates.get gateIndex)
              (fun register =>
                entry register position) := by
  constructor
  · rintro ⟨hcodes, hgates⟩
    choose entry hentry using hcodes
    refine ⟨entry, hentry, ?_⟩
    intro gateIndex
    exact
      (cipherGate_spec hentry
        (gates.get gateIndex)).mp
        (hgates gateIndex)
  · rintro ⟨entry, hentry, hgates⟩
    constructor
    · intro register
      exact ⟨entry register, hentry register⟩
    · intro gateIndex
      exact
        (cipherGate_spec hentry
          (gates.get gateIndex)).mpr
          (hgates gateIndex)

/-- The complete parallel cipher relation for a fixed finite arithmetic
circuit is Diophantine. -/
theorem cipherCircuit_dioph
    {vars : ℕ} (gates : List (ArithmeticGate vars)) :
    Dioph {v : (Fin 2 ⊕ Fin vars) → ℕ |
      CipherCircuitHolds gates
        (v (Sum.inl 0)) (v (Sum.inl 1))
        (fun i => v (Sum.inr i))} := by
  have hCodes :
      Dioph {v : (Fin 2 ⊕ Fin vars) → ℕ |
        ∀ register,
          Code (v (Sum.inl 0)) (v (Sum.inl 1))
            (v (Sum.inr register))} := by
    apply dioph_forall_fin
    intro register
    exact
      Dioph.reindex_dioph
        (Fin 2 ⊕ Fin vars)
        ![Sum.inl 0, Sum.inl 1, Sum.inr register]
        code_dioph
  have hGates :
      Dioph {v : (Fin 2 ⊕ Fin vars) → ℕ |
        ∀ gateIndex : Fin gates.length,
          CipherGateHolds
            (v (Sum.inl 0)) (v (Sum.inl 1))
            (fun i => v (Sum.inr i))
            (gates.get gateIndex)} := by
    apply dioph_forall_fin
    intro gateIndex
    exact cipherGate_dioph (gates.get gateIndex)
  exact
    Dioph.ext (hCodes.inter hGates) fun v => by
      rfl

end SparseCipherCircuit

end HGAS
