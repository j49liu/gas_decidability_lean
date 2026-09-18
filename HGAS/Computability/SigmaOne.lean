import Mathlib.Computability.Reduce
import Mathlib.Tactic

/-!
# Computably enumerable completeness

This file fixes the recursion-theoretic vocabulary used by the formalized
main theorem.  A predicate on a primitively codable type is
`Σ⁰₁`-complete when it is recursively enumerable and every recursively
enumerable predicate on natural numbers many-one reduces to it.

For later hardness proofs we also package the universal halting problem for
Mathlib's codes of partial recursive functions.  Unlike an informal appeal
to "some c.e.-complete set", the proof below constructs the reduction:
an enumerator for a predicate has a code `c`, and the input `n` is sent to
the pair `(c,n)`.
-/

namespace HGAS

open Nat.Partrec
open Nat.Partrec.Code

/-- Many-one `Σ⁰₁`-completeness, with natural-number c.e. predicates as the
universal source class. -/
def SigmaOneComplete {α : Type*} [Primcodable α]
    (p : α → Prop) : Prop :=
  REPred p ∧
    ∀ q : ℕ → Prop, REPred q → q ≤₀ p

/-- The universal halting predicate for Mathlib partial-recursive codes. -/
def UniversalHalts (input : Code × ℕ) : Prop :=
  (eval input.1 input.2).Dom

/-- The universal halting predicate is recursively enumerable. -/
theorem universalHalts_re :
    REPred UniversalHalts := by
  exact
    (eval_part.comp Computable.fst Computable.snd).dom_re

/-- Every c.e. predicate on natural numbers reduces to universal halting. -/
theorem re_manyOneReducible_universalHalts
    (q : ℕ → Prop) (hq : REPred q) :
    q ≤₀ UniversalHalts := by
  let asserted : ℕ →. Unit :=
    fun n ↦ Part.assert (q n) fun _ ↦ Part.some ()
  have hasserted : Partrec asserted := by
    exact hq
  let witness : ℕ →. ℕ :=
    fun n ↦ (asserted n).map fun _ ↦ 0
  have hwitness : Nat.Partrec witness := by
    apply Partrec.nat_iff.mp
    exact
      (hasserted.map
        (Computable.const (α := ℕ × Unit) (0 : ℕ)).to₂).of_eq
          fun _ ↦ rfl
  obtain ⟨c, hc⟩ := exists_code.mp hwitness
  refine ⟨fun n ↦ (c, n), ?_, ?_⟩
  · exact Computable.pair (Computable.const c) Computable.id
  · intro n
    change q n ↔ (eval c n).Dom
    rw [hc]
    by_cases hn : q n <;>
      simp [witness, asserted, Part.dom_iff_mem, hn]

/-- Universal halting is `Σ⁰₁`-complete. -/
theorem universalHalts_sigmaOneComplete :
    SigmaOneComplete UniversalHalts :=
  ⟨universalHalts_re, re_manyOneReducible_universalHalts⟩

/-- Completeness can be proved by membership plus one reduction from
universal halting. -/
theorem sigmaOneComplete_of_universalHalts_reduction
    {α : Type*} [Primcodable α] {p : α → Prop}
    (hp : REPred p) (hhard : UniversalHalts ≤₀ p) :
    SigmaOneComplete p := by
  refine ⟨hp, ?_⟩
  intro q hq
  exact
    (re_manyOneReducible_universalHalts q hq).trans hhard

/-- A `Σ⁰₁`-complete predicate cannot be computable. -/
theorem SigmaOneComplete.not_computable
    {α : Type*} [Primcodable α] {p : α → Prop}
    (hp : SigmaOneComplete p) :
    ¬ ComputablePred p := by
  intro hcomputable
  let fixedHalts : Code → Prop :=
    fun c ↦ (eval c 0).Dom
  let decodeCode : ℕ → Code :=
    fun n ↦
      (@Encodable.decode Code
        (@Primcodable.toEncodable Code inferInstance) n).getD default
  have hdecode : Computable decodeCode := by
    exact Computable.option_getD Computable.decode
      (Computable.const default)
  have hsource :
      REPred (toNat (fixedHalts : Set Code)) := by
    exact
      (eval_part.comp hdecode (Computable.const 0)).dom_re
  have hreduce :
      fixedHalts ≤₀ p :=
    manyOneReducible_toNat.trans (hp.2 _ hsource)
  exact ComputablePred.halting_problem 0
    (ComputablePred.computable_of_manyOneReducible
      hreduce hcomputable)

/-- If a complete c.e. predicate had a c.e. complement, it would be
computable; hence its complement is not c.e. -/
theorem SigmaOneComplete.complement_not_re
    {α : Type*} [Primcodable α] {p : α → Prop}
    (hp : SigmaOneComplete p) :
    ¬ REPred (fun a ↦ ¬ p a) := by
  classical
  intro hcomplement
  apply hp.not_computable
  exact
    ComputablePred.computable_iff_re_compl_re.mpr
      ⟨hp.1, hcomplement⟩

end HGAS
