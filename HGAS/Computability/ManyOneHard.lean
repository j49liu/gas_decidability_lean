import HGAS.Computability.SigmaOne
import Mathlib.Tactic

/-!
# Many-one hardness

A predicate is many-one hard when every recursively enumerable predicate on
`ℕ` many-one reduces to it.  This is the hardness half of
`SigmaOneComplete`; it is the notion used for Lyapunov stability, where
membership in the class of recursively enumerable sets is not known.
-/

namespace HGAS

/-- Many-one hardness: every recursively enumerable predicate on `ℕ`
many-one reduces to `p`. -/
def ManyOneHard {α : Type*} [Primcodable α] (p : α → Prop) : Prop :=
  ∀ q : ℕ → Prop, REPred q → q ≤₀ p

theorem ManyOneHard.of_manyOneReducible
    {α β : Type*} [Primcodable α] [Primcodable β]
    {p : α → Prop} {r : β → Prop}
    (hp : ManyOneHard p) (hpr : p ≤₀ r) :
    ManyOneHard r :=
  fun q hq ↦ (hp q hq).trans hpr

open Nat.Partrec Nat.Partrec.Code in
/-- Halting on input `0` reduces to every many-one hard predicate. -/
theorem ManyOneHard.fixedHalts_reducible
    {α : Type*} [Primcodable α] {p : α → Prop}
    (hp : ManyOneHard p) :
    (fun c : Code ↦ (eval c 0).Dom) ≤₀ p := by
  let decodeCode : ℕ → Code :=
    fun n ↦
      (@Encodable.decode Code
        (@Primcodable.toEncodable Code inferInstance) n).getD default
  have hdecode : Computable decodeCode := by
    exact Computable.option_getD Computable.decode
      (Computable.const default)
  have hsource :
      REPred (toNat ((fun c : Code ↦ (eval c 0).Dom) : Set Code)) := by
    exact (eval_part.comp hdecode (Computable.const 0)).dom_re
  exact manyOneReducible_toNat.trans (hp _ hsource)

/-- A many-one hard predicate is not computable. -/
theorem ManyOneHard.not_computable
    {α : Type*} [Primcodable α] {p : α → Prop}
    (hp : ManyOneHard p) :
    ¬ ComputablePred p := fun hcomputable ↦
  ComputablePred.halting_problem 0
    (ComputablePred.computable_of_manyOneReducible
      hp.fixedHalts_reducible hcomputable)

open Nat.Partrec Nat.Partrec.Code in
/-- The complement of a many-one hard predicate is not recursively
enumerable. -/
theorem ManyOneHard.complement_not_re
    {α : Type*} [Primcodable α] {p : α → Prop}
    (hp : ManyOneHard p) :
    ¬ REPred (fun a ↦ ¬ p a) := by
  classical
  intro hcomplement
  obtain ⟨f, hf, hfp⟩ := hp.fixedHalts_reducible
  have hcompl : REPred (fun c : Code ↦ ¬ (eval c 0).Dom) :=
    REPred.of_eq (hcomplement.comp hf) fun c ↦ by
      simp only [hfp c]
  have hre : REPred (fun c : Code ↦ (eval c 0).Dom) :=
    (eval_part.comp Computable.id (Computable.const 0)).dom_re
  exact ComputablePred.halting_problem 0
    (ComputablePred.computable_iff_re_compl_re.mpr ⟨hre, hcompl⟩)

end HGAS
