import Stability.Computability.RegisterMachineStackBlocks
import Mathlib.Computability.Primrec.List

/-!
# Computable numeral input for the stack compiler

The universal stack interpreter starts with `trList [n]` on its main
stack and all other stacks empty. Its base-five numeral has the binary
recurrence `F(0) = 2` and `F(n) = 5 F(n/2) + 3 + n%2` for `n > 0`.
Strong primitive recursion therefore computes the exact register input.
-/

namespace Stability.RegisterMachine.TM2Encoding

open Turing.PartrecToTM2

/-- The literal main-register value encoding Mathlib's singleton input. -/
def inputNumeral (n : ℕ) : ℕ := contentsCode (trList [n])

theorem inputNumeral_rec (n : ℕ) :
    inputNumeral n = if n = 0 then 2 else 5 * inputNumeral (n / 2) + 3 + n % 2 := by
  have hnum (a : Num) : inputNumeral (a : ℕ) =
      if (a : ℕ) = 0 then 2 else 5 * inputNumeral ((a : ℕ) / 2) + 3 + (a : ℕ) % 2 := by
    cases a with
    | zero => rfl
    | pos p =>
        cases p with
        | one => rfl
        | bit0 p =>
            have hp : 0 < (p : ℕ) := PosNum.to_nat_pos p
            have hn : (p : ℕ) + p ≠ 0 := by omega
            have hd : ((p : ℕ) + p) / 2 = p := by omega
            have hm : ((p : ℕ) + p) % 2 = 0 := by omega
            simp only [inputNumeral, trList, trNat, Num.of_to_nat, trNum]
            simp only [Num.cast_pos, PosNum.cast_bit0, hn, ↓reduceIte, hd, hm,
              PosNum.of_to_nat, trPosNum, List.cons_append,
              contentsCode_cons, symbolCode, add_zero]
            rfl
        | bit1 p =>
            have hn : (p : ℕ) + p + 1 ≠ 0 := by omega
            have hd : ((p : ℕ) + p + 1) / 2 = p := by omega
            have hm : ((p : ℕ) + p + 1) % 2 = 1 := by omega
            simp only [inputNumeral, trList, trNat, Num.of_to_nat, trNum]
            simp only [Num.cast_pos, PosNum.cast_bit1, hn, ↓reduceIte, hd, hm,
              PosNum.of_to_nat, trPosNum, List.cons_append,
              contentsCode_cons, symbolCode]
            omega
  simpa only [Num.to_of_nat] using hnum (n : Num)

/-- The actual register numeral is primitive recursive, not merely a
set-theoretic encoding chosen from a halting equivalence. -/
theorem inputNumeral_primrec : Primrec inputNumeral := by
  let g : Unit → List ℕ → Option ℕ := fun _ L ↦ some
    (if L.length = 0 then 2 else 5 * L.getD (L.length / 2) 0 + 3 + L.length % 2)
  have hlen : Primrec (fun p : Unit × List ℕ ↦ p.2.length) :=
    Primrec.list_length.comp Primrec.snd
  have hget : Primrec (fun p : Unit × List ℕ ↦ p.2.getD (p.2.length / 2) 0) :=
    (Primrec.list_getD 0).comp Primrec.snd (Primrec.nat_div.comp hlen (Primrec.const 2))
  have hg : Primrec₂ g :=
    (Primrec.option_some.comp (Primrec.ite
      (Primrec.eq.comp hlen (Primrec.const 0)) (Primrec.const 2)
      (Primrec.nat_add.comp
        (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 5) hget) (Primrec.const 3))
        (Primrec.nat_mod.comp hlen (Primrec.const 2))))).to₂
  have hrec : Primrec₂ (fun _ : Unit ↦ inputNumeral) :=
    Primrec.nat_strong_rec (fun _ : Unit ↦ inputNumeral) hg (by
      intro _ n
      simp only [g, List.length_map, List.length_range]
      rw [inputNumeral_rec n]
      by_cases hn : n = 0
      · simp [hn]
      · have hdiv : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)
        simp [hn, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hdiv])
  exact hrec.comp (Primrec.const ()) Primrec.id

end Stability.RegisterMachine.TM2Encoding
