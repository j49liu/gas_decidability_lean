import HGAS.Arithmetic.RadixSequenceCode
import Mathlib.Data.List.Indexes
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-!
# Binomial coefficients and bitwise operations are Diophantine

Matiyasevich's sparse-cipher proof of closure under bounded universal
quantification uses binary masks to select designated digits of large
radix codes.  This file develops the first number-theoretic bridge needed
by that construction.

The key chain is:

1. `n.choose k` is the `k`-th digit of `(q + 1)^n` in the sufficiently
   large base `q = 2^(n+1)`;
2. therefore the binomial coefficient is a Diophantine function, using
   `Dioph.pow_dioph` and the already formalized radix decoder;
3. Lucas's theorem modulo two identifies bitwise inclusion with oddness
   of a binomial coefficient;
4. bitwise inclusion, and then bitwise `and`, are Diophantine.

All results are unconditional.  They isolate reusable arithmetic from
the later sparse-cipher implementation.
-/

namespace HGAS

namespace DiophantineBitwise

open scoped BigOperators

/-! ## Binomial coefficients as radix digits -/

/-- A radix large enough to contain every coefficient in the binomial
expansion of `(q + 1)^n`. -/
def chooseRadixBase (n : ℕ) : ℕ :=
  2 ^ (n + 1)

/-- The number whose base-`chooseRadixBase n` digits are the binomial
coefficients in row `n` of Pascal's triangle. -/
def chooseRadixCode (n : ℕ) : ℕ :=
  (chooseRadixBase n + 1) ^ n

theorem one_lt_chooseRadixBase (n : ℕ) :
    1 < chooseRadixBase n := by
  simp [chooseRadixBase, Nat.one_lt_pow_iff]

theorem choose_lt_chooseRadixBase (n k : ℕ) :
    n.choose k < chooseRadixBase n := by
  apply lt_of_le_of_lt (Nat.choose_le_two_pow n k)
  exact Nat.pow_lt_pow_succ (by norm_num)

/-- The radix encoding of a row of Pascal's triangle is exactly the
corresponding binomial power. -/
theorem encode_choose_row (n : ℕ) :
    RadixSequence.encode (chooseRadixBase n)
        (List.ofFn fun i : Fin (n + 1) => n.choose i) =
      chooseRadixCode n := by
  rw [RadixSequence.encode, Nat.ofDigits_eq_sum_mapIdx]
  simp only [List.mapIdx_eq_ofFn, List.get_ofFn, List.length_ofFn,
    Fin.val_cast, List.sum_ofFn]
  rw [chooseRadixCode, add_pow]
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_range] at hk
  rw [dif_pos hk]
  simp [Nat.mul_comm]

/-- Every binomial coefficient is recovered as a digit of the binomial
radix code, including the zero coefficients beyond the end of the row. -/
theorem digit_chooseRadixCode (n k : ℕ) :
    RadixSequence.digit
        (chooseRadixBase n) (chooseRadixCode n) k =
      n.choose k := by
  let entries :=
    List.ofFn fun i : Fin (n + 1) => n.choose i
  have hentries :
      ∀ entry ∈ entries, entry < chooseRadixBase n := by
    intro entry hentry
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hentry
    exact choose_lt_chooseRadixBase n i
  rw [← encode_choose_row n]
  by_cases hk : k < entries.length
  · have hdigit :=
      RadixSequence.digit_encode_eq_getElem
        (Nat.zero_lt_of_lt (one_lt_chooseRadixBase n))
        hentries k hk
    rw [hdigit]
    simp only [entries, List.getElem_ofFn]
  · have hk' : n < k := by
      simpa [entries] using Nat.le_of_not_gt hk
    have hcode :
        RadixSequence.encode (chooseRadixBase n) entries <
          chooseRadixBase n ^ entries.length := by
      exact Nat.ofDigits_lt_base_pow_length
        (one_lt_chooseRadixBase n) hentries
    have hpow :
        chooseRadixBase n ^ entries.length ≤
          chooseRadixBase n ^ k := by
      exact
        pow_le_pow_right' (one_lt_chooseRadixBase n).le
          (Nat.le_of_not_gt hk)
    rw [RadixSequence.digit, Nat.div_eq_of_lt (hcode.trans_le hpow)]
    simp [Nat.choose_eq_zero_of_lt hk']

/-- Binomial coefficients are Diophantine functions. -/
theorem choose_diophFn
    {α : Type}
    {n k : (α → ℕ) → ℕ}
    (hn : Dioph.DiophFn n)
    (hk : Dioph.DiophFn k) :
    Dioph.DiophFn fun input => (n input).choose (k input) := by
  have hbase :
      Dioph.DiophFn fun input => chooseRadixBase (n input) := by
    simpa [chooseRadixBase] using
      Dioph.pow_dioph
        (Dioph.const_dioph (α := α) 2)
        (Dioph.add_dioph hn (Dioph.const_dioph 1))
  have hcode :
      Dioph.DiophFn fun input => chooseRadixCode (n input) := by
    simpa [chooseRadixCode] using
      Dioph.pow_dioph
        (Dioph.add_dioph hbase (Dioph.const_dioph 1)) hn
  simpa only [digit_chooseRadixCode] using
    RadixSequence.digit_diophFn hbase hcode hk

/-! ## Binary inclusion -/

/-- `BinaryLE n m` says that every one-bit of `n` is also a one-bit of
`m`.  The constructors expose one binary digit at a time.  This form is
suited both to induction and to Lucas's theorem. -/
inductive BinaryLE : ℕ → ℕ → Prop
  | zero (m : ℕ) : BinaryLE 0 m
  | step {n m : ℕ} :
      n % 2 ≤ m % 2 →
      BinaryLE (n / 2) (m / 2) →
      BinaryLE n m

theorem binaryLE_iff_mod_div (n m : ℕ) :
    BinaryLE n m ↔
      n % 2 ≤ m % 2 ∧ BinaryLE (n / 2) (m / 2) := by
  constructor
  · intro h
    cases h with
    | zero m =>
        exact ⟨by simp, BinaryLE.zero _⟩
    | step hbit htail =>
        exact ⟨hbit, htail⟩
  · rintro ⟨hbit, htail⟩
    exact BinaryLE.step hbit htail

@[simp]
theorem binaryLE_zero_left (m : ℕ) : BinaryLE 0 m :=
  BinaryLE.zero m

private theorem bool_toNat_le_iff_and_eq_left (a b : Bool) :
    a.toNat ≤ b.toNat ↔ (a && b) = a := by
  cases a <;> cases b <;> decide

/-- Binary inclusion implies the familiar bitwise-AND equation. -/
theorem land_eq_left_of_binaryLE {n m : ℕ}
    (h : BinaryLE n m) :
    n &&& m = n := by
  induction h with
  | zero => simp
  | @step n m hbit htail ih =>
      change Nat.div2 n &&& Nat.div2 m = Nat.div2 n at ih
      rw [← Nat.bit_bodd_div2 n, ← Nat.bit_bodd_div2 m,
        Nat.land_bit, ih]
      congr
      rw [Nat.mod_two_of_bodd, Nat.mod_two_of_bodd] at hbit
      exact
        (bool_toNat_le_iff_and_eq_left (Nat.bodd n) (Nat.bodd m)).mp
          hbit

/-- The bitwise-AND equation implies binary inclusion. -/
theorem binaryLE_of_land_eq_left :
    ∀ {n m : ℕ}, n &&& m = n → BinaryLE n m := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro m hland
      by_cases hn : n = 0
      · subst n
        exact BinaryLE.zero m
      · have hdecomp :
            Nat.bit (Nat.bodd n && Nat.bodd m)
                (Nat.div2 n &&& Nat.div2 m) =
              Nat.bit (Nat.bodd n) (Nat.div2 n) := by
          calc
            _ =
                Nat.bit (Nat.bodd n) (Nat.div2 n) &&&
                  Nat.bit (Nat.bodd m) (Nat.div2 m) :=
              (Nat.land_bit _ _ _ _).symm
            _ = n &&& m := by
              rw [Nat.bit_bodd_div2, Nat.bit_bodd_div2]
            _ = n := hland
            _ = Nat.bit (Nat.bodd n) (Nat.div2 n) :=
              (Nat.bit_bodd_div2 n).symm
        have hbitBool :
            (Nat.bodd n && Nat.bodd m) = Nat.bodd n := by
          simpa only [Nat.bodd_bit] using congrArg Nat.bodd hdecomp
        have htail :
            Nat.div2 n &&& Nat.div2 m = Nat.div2 n := by
          simpa only [Nat.div2_bit] using congrArg Nat.div2 hdecomp
        apply BinaryLE.step
        · rw [Nat.mod_two_of_bodd, Nat.mod_two_of_bodd]
          exact
            (bool_toNat_le_iff_and_eq_left
              (Nat.bodd n) (Nat.bodd m)).mpr hbitBool
        · exact
            ih (Nat.div2 n) (Nat.binaryRec_decreasing hn)
              htail

theorem binaryLE_zero_right_iff (n : ℕ) :
    BinaryLE n 0 ↔ n = 0 := by
  constructor
  · intro h
    have hland := land_eq_left_of_binaryLE h
    simpa using hland.symm
  · rintro rfl
    exact BinaryLE.zero 0

/-- Binary inclusion is exactly absorption by bitwise AND. -/
theorem binaryLE_iff_land_eq_left (n m : ℕ) :
    BinaryLE n m ↔ n &&& m = n :=
  ⟨land_eq_left_of_binaryLE, binaryLE_of_land_eq_left⟩

/-! ## Lucas's theorem modulo two -/

/-- One binary digit of Lucas's theorem.  A binomial coefficient is
odd precisely when its low binary digits are ordered and the binomial
coefficient obtained by deleting those digits is odd. -/
theorem choose_mod_two_eq_one_iff (n k : ℕ) :
    n.choose k % 2 = 1 ↔
      k % 2 ≤ n % 2 ∧
        (n / 2).choose (k / 2) % 2 = 1 := by
  have hLucas :
      n.choose k % 2 =
        ((n % 2).choose (k % 2) *
          (n / 2).choose (k / 2)) % 2 := by
    exact
      (Choose.choose_modEq_choose_mod_mul_choose_div_nat
        (p := 2) (n := n) (k := k))
  rw [hLucas]
  by_cases hbit : k % 2 ≤ n % 2
  · have hsmall : (n % 2).choose (k % 2) = 1 := by
      rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;>
        rcases Nat.mod_two_eq_zero_or_one k with hk | hk <;>
          simp_all
    simp [hbit, hsmall]
  · have hlt : n % 2 < k % 2 := Nat.lt_of_not_ge hbit
    rw [Nat.choose_eq_zero_of_lt hlt]
    simp [hbit]

/-- Lucas's theorem iterated through all binary digits: the one-bits
of `k` are included in those of `n` iff `n.choose k` is odd. -/
theorem binaryLE_iff_choose_mod_two_eq_one :
    ∀ n k : ℕ, BinaryLE k n ↔ n.choose k % 2 = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro k
      by_cases hn : n = 0
      · subst n
        rw [binaryLE_zero_right_iff]
        cases k <;> simp
      · rw [binaryLE_iff_mod_div, choose_mod_two_eq_one_iff]
        rw [ih (n / 2) (Nat.div_lt_self (Nat.zero_lt_of_ne_zero hn)
          (by norm_num))]

/-- Binary inclusion is a Diophantine relation.  This is the first
Lucas-theoretic mask predicate required by Matiyasevich's sparse
cipher construction. -/
theorem binaryLE_dioph
    {α : Type}
    {n m : (α → ℕ) → ℕ}
    (hn : Dioph.DiophFn n)
    (hm : Dioph.DiophFn m) :
    Dioph {input | BinaryLE (n input) (m input)} := by
  have hchoose :
      Dioph.DiophFn fun input => (m input).choose (n input) :=
    choose_diophFn hm hn
  have hmod :
      Dioph.DiophFn fun input =>
        (m input).choose (n input) % 2 := by
    simpa using
      Dioph.mod_dioph hchoose (Dioph.const_dioph (α := α) 2)
  exact
    Dioph.ext
      (Dioph.eq_dioph hmod (Dioph.const_dioph (α := α) 1))
      fun input => by
        simp only [Set.mem_setOf_eq]
        exact (binaryLE_iff_choose_mod_two_eq_one _ _).symm

/-! ## Carry-free addition and bitwise AND -/

/-- Adding `x` preserves every one-bit of `a` exactly when the addition
is carry-free, equivalently when `a` and `x` have disjoint one-bits. -/
theorem binaryLE_add_iff_land_eq_zero :
    ∀ a x : ℕ, BinaryLE a (a + x) ↔ a &&& x = 0 := by
  intro a
  induction a using Nat.binaryRec' with
  | zero =>
      intro x
      simp
  | bit ba a hba ih =>
      intro x
      induction x using Nat.binaryRec' with
      | zero =>
          simp [binaryLE_iff_land_eq_left]
      | bit bx x hbx ix =>
          cases ba
          · cases bx
            · have hadd :
                  Nat.bit false a + Nat.bit false x =
                    Nat.bit false (a + x) := by
                simp [Nat.bit, Nat.mul_add]
              rw [binaryLE_iff_mod_div, hadd, Nat.land_bit]
              simp only [Nat.bit_mod_two, Nat.bit_div_two]
              simp [ih, Nat.bit]
            · have hadd :
                  Nat.bit false a + Nat.bit true x =
                    Nat.bit true (a + x) := by
                simp [Nat.bit, Nat.mul_add]
                omega
              rw [binaryLE_iff_mod_div, hadd, Nat.land_bit]
              simp only [Nat.bit_mod_two, Nat.bit_div_two]
              simp [ih, Nat.bit]
          · cases bx
            · have hadd :
                  Nat.bit true a + Nat.bit false x =
                    Nat.bit true (a + x) := by
                simp [Nat.bit, Nat.mul_add]
                omega
              rw [binaryLE_iff_mod_div, hadd, Nat.land_bit]
              simp only [Nat.bit_mod_two, Nat.bit_div_two]
              simp [ih, Nat.bit]
            · have hadd :
                  Nat.bit true a + Nat.bit true x =
                    Nat.bit false (a + x + 1) := by
                simp [Nat.bit, Nat.mul_add]
                omega
              rw [binaryLE_iff_mod_div, hadd, Nat.land_bit]
              simp only [Nat.bit_mod_two, Nat.bit_div_two]
              simp [Nat.bit]

/-- Bitwise OR agrees with ordinary addition when no binary carry is
possible. -/
theorem lor_eq_add_of_land_eq_zero :
    ∀ a x : ℕ, a &&& x = 0 → a ||| x = a + x := by
  intro a
  induction a using Nat.binaryRec' with
  | zero =>
      intro x h
      simp
  | bit ba a hba ih =>
      intro x hland
      induction x using Nat.binaryRec' with
      | zero =>
          simp
      | bit bx x hbx ix =>
          have hdecomp :
              Nat.bit (ba && bx) (a &&& x) = 0 := by
            simpa only [Nat.land_bit] using hland
          have htail : a &&& x = 0 := by
            simpa only [Nat.div2_bit, Nat.div2_zero] using
              congrArg Nat.div2 hdecomp
          have hlow : (ba && bx) = false := by
            simpa only [Nat.bodd_bit, Nat.bodd_zero] using
              congrArg Nat.bodd hdecomp
          have ih' := ih x htail
          cases ba <;> cases bx
          · simp only [Nat.lor_bit]
            simp [Nat.bit, Nat.mul_add, ih']
          · simp only [Nat.lor_bit]
            simp [Nat.bit, Nat.mul_add, ih']
            omega
          · simp only [Nat.lor_bit]
            simp [Nat.bit, Nat.mul_add, ih']
            omega
          · simp at hlow

/-- Removing the bits of `a` from any number leaves a number disjoint
from `a`. -/
theorem land_ldiff_eq_zero (a b : ℕ) :
    a &&& Nat.ldiff b a = 0 := by
  apply Nat.zero_of_testBit_eq_false
  intro i
  rw [Nat.testBit_land, Nat.testBit_ldiff]
  cases Nat.testBit a i <;> cases Nat.testBit b i <;> rfl

/-- If the bits of `a` are included in `b`, adjoining the bits of `b`
outside `a` recovers `b`. -/
theorem lor_ldiff_eq_of_binaryLE {a b : ℕ}
    (h : BinaryLE a b) :
    a ||| Nat.ldiff b a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hbit :=
    congrArg (fun z => Nat.testBit z i)
      (land_eq_left_of_binaryLE h)
  change (a &&& b).testBit i = a.testBit i at hbit
  rw [Nat.testBit_land] at hbit
  rw [Nat.testBit_lor, Nat.testBit_ldiff]
  generalize ha : Nat.testBit a i = ai at hbit ⊢
  generalize hb : Nat.testBit b i = bi at hbit ⊢
  cases ai <;> cases bi <;> simp_all

/-- If `a` is the meet of `b` and `c`, the parts of `b` and `c`
remaining after deleting `a` are disjoint. -/
theorem ldiff_land_ldiff_eq_zero_of_eq_land
    {a b c : ℕ}
    (h : a = b &&& c) :
    Nat.ldiff b a &&& Nat.ldiff c a = 0 := by
  apply Nat.zero_of_testBit_eq_false
  intro i
  have hbit := congrArg (fun z => Nat.testBit z i) h
  change a.testBit i = (b &&& c).testBit i at hbit
  rw [Nat.testBit_land] at hbit
  rw [Nat.testBit_land, Nat.testBit_ldiff, Nat.testBit_ldiff]
  generalize ha : Nat.testBit a i = ai at hbit ⊢
  generalize hb : Nat.testBit b i = bi at hbit ⊢
  generalize hc : Nat.testBit c i = ci at hbit ⊢
  clear h ha hb hc
  cases ai <;> cases bi <;> cases ci <;> simp_all

/-- The addition-and-inclusion characterization of bitwise AND used in
Matiyasevich's sparse-cipher construction.  Its importance is that the
right-hand side uses only addition, existential quantifiers, and
`BinaryLE`, all of which have Diophantine representations. -/
theorem eq_land_iff_exists_binaryLE (a b c : ℕ) :
    a = b &&& c ↔
      ∃ x y : ℕ,
        b = a + x ∧
        c = a + y ∧
        BinaryLE a (a + x) ∧
        BinaryLE a (a + y) ∧
        BinaryLE x (x + y) := by
  constructor
  · intro h
    let x := Nat.ldiff b a
    let y := Nat.ldiff c a
    have hab : BinaryLE a b := by
      apply binaryLE_of_land_eq_left
      simp [h, Nat.and_comm]
    have hac : BinaryLE a c := by
      apply binaryLE_of_land_eq_left
      simp [h, Nat.and_comm, Nat.and_left_comm]
    have hax : a &&& x = 0 := by
      exact land_ldiff_eq_zero a b
    have hay : a &&& y = 0 := by
      exact land_ldiff_eq_zero a c
    have hxy : x &&& y = 0 := by
      exact ldiff_land_ldiff_eq_zero_of_eq_land h
    have hlorx : a ||| x = b :=
      lor_ldiff_eq_of_binaryLE hab
    have hlory : a ||| y = c :=
      lor_ldiff_eq_of_binaryLE hac
    refine ⟨x, y, ?_, ?_, ?_, ?_, ?_⟩
    · exact hlorx.symm.trans (lor_eq_add_of_land_eq_zero a x hax)
    · exact hlory.symm.trans (lor_eq_add_of_land_eq_zero a y hay)
    · exact (binaryLE_add_iff_land_eq_zero a x).mpr hax
    · exact (binaryLE_add_iff_land_eq_zero a y).mpr hay
    · exact (binaryLE_add_iff_land_eq_zero x y).mpr hxy
  · rintro ⟨x, y, hb, hc, haxLE, hayLE, hxyLE⟩
    have hax :
        a &&& x = 0 :=
      (binaryLE_add_iff_land_eq_zero a x).mp haxLE
    have hay :
        a &&& y = 0 :=
      (binaryLE_add_iff_land_eq_zero a y).mp hayLE
    have hxy :
        x &&& y = 0 :=
      (binaryLE_add_iff_land_eq_zero x y).mp hxyLE
    have hbor : b = a ||| x :=
      hb.trans (lor_eq_add_of_land_eq_zero a x hax).symm
    have hcor : c = a ||| y :=
      hc.trans (lor_eq_add_of_land_eq_zero a y hay).symm
    have hmeet : (a ||| x) &&& (a ||| y) = a := by
      rw [Nat.and_or_distrib_right,
        Nat.and_or_distrib_left, Nat.and_or_distrib_left]
      simp [hax, hay, hxy, Nat.and_comm]
    calc
      a = (a ||| x) &&& (a ||| y) := hmeet.symm
      _ = b &&& c := by rw [hbor, hcor]

/-- Bitwise AND is a Diophantine function. -/
theorem land_diophFn
    {α : Type}
    {b c : (α → ℕ) → ℕ}
    (hb : Dioph.DiophFn b)
    (hc : Dioph.DiophFn c) :
    Dioph.DiophFn fun input => b input &&& c input := by
  let β := Option α ⊕ Fin 2
  let a : (β → ℕ) → ℕ :=
    fun v => v (Sum.inl none)
  let b' : (β → ℕ) → ℕ :=
    fun v => b (fun i => v (Sum.inl (some i)))
  let c' : (β → ℕ) → ℕ :=
    fun v => c (fun i => v (Sum.inl (some i)))
  let x : (β → ℕ) → ℕ :=
    fun v => v (Sum.inr 0)
  let y : (β → ℕ) → ℕ :=
    fun v => v (Sum.inr 1)
  have ha : Dioph.DiophFn a := by
    exact Dioph.proj_dioph (Sum.inl none)
  have hb' : Dioph.DiophFn b' := by
    simpa [b', Function.comp_def] using
      Dioph.reindex_diophFn
        (fun i : α => Sum.inl (some i) : α → β) hb
  have hc' : Dioph.DiophFn c' := by
    simpa [c', Function.comp_def] using
      Dioph.reindex_diophFn
        (fun i : α => Sum.inl (some i) : α → β) hc
  have hx : Dioph.DiophFn x := by
    exact Dioph.proj_dioph (Sum.inr 0)
  have hy : Dioph.DiophFn y := by
    exact Dioph.proj_dioph (Sum.inr 1)
  have hax : Dioph.DiophFn fun v => a v + x v :=
    Dioph.add_dioph ha hx
  have hay : Dioph.DiophFn fun v => a v + y v :=
    Dioph.add_dioph ha hy
  have hxy : Dioph.DiophFn fun v => x v + y v :=
    Dioph.add_dioph hx hy
  have hEqB : Dioph {v | b' v = a v + x v} :=
    Dioph.eq_dioph hb' hax
  have hEqC : Dioph {v | c' v = a v + y v} :=
    Dioph.eq_dioph hc' hay
  have hBinAX : Dioph {v | BinaryLE (a v) (a v + x v)} :=
    binaryLE_dioph ha hax
  have hBinAY : Dioph {v | BinaryLE (a v) (a v + y v)} :=
    binaryLE_dioph ha hay
  have hBinXY : Dioph {v | BinaryLE (x v) (x v + y v)} :=
    binaryLE_dioph hx hxy
  have hAll :
      Dioph
        {v |
          b' v = a v + x v ∧
          c' v = a v + y v ∧
          BinaryLE (a v) (a v + x v) ∧
          BinaryLE (a v) (a v + y v) ∧
          BinaryLE (x v) (x v + y v)} := by
    simpa only [Set.mem_inter_iff, Set.mem_setOf_eq] using
      hEqB.inter
        (hEqC.inter
          (hBinAX.inter
            (hBinAY.inter hBinXY)))
  refine
    Dioph.ext (Dioph.ex_dioph hAll) fun v => ?_
  simp only [Set.mem_setOf_eq]
  change
    (∃ w : Fin 2 → ℕ,
      b (fun i => v (some i)) = v none + w 0 ∧
      c (fun i => v (some i)) = v none + w 1 ∧
      BinaryLE (v none) (v none + w 0) ∧
      BinaryLE (v none) (v none + w 1) ∧
      BinaryLE (w 0) (w 0 + w 1)) ↔
      b (fun i => v (some i)) &&&
          c (fun i => v (some i)) =
        v none
  constructor
  · rintro ⟨w, hw⟩
    exact
      (eq_land_iff_exists_binaryLE
        (v none)
        (b (fun i => v (some i)))
        (c (fun i => v (some i)))).2
          ⟨w 0, w 1, hw⟩ |>.symm
  · intro h
    obtain ⟨x₀, y₀, hw⟩ :=
      (eq_land_iff_exists_binaryLE
        (v none)
        (b (fun i => v (some i)))
        (c (fun i => v (some i)))).1 h.symm
    exact ⟨![x₀, y₀], by simpa using hw⟩

end DiophantineBitwise

end HGAS
