import HGAS.Arithmetic.ExecutableMRDPBoundary
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic

/-!
# Finite sequences encoded by radix digits

This file isolates the elementary sequence-coding ingredient needed by an
effective MRDP compiler.  A finite list

```
[a₀, a₁, ..., aₙ₋₁]
```

whose entries are smaller than `base` is represented by

```
a₀ + base * a₁ + ... + base^(n-1) * aₙ₋₁.
```

The entry at position `i` is recovered by first dividing by `base^i` and
then taking the remainder modulo `base`.  This coding is simpler than the
traditional Gödel beta function for our purpose: exponentiation is already
known to be Diophantine in Mathlib, so the decoder is immediately a
Diophantine function.

The important limitation is explicit.  The theorem below encodes every
*given finite sequence*.  It does not turn a proposition
`∀ i < bound, R i` into a single Diophantine equation.  That
variable-bounded conjunction is the remaining primitive-recursion closure
step in the effective MRDP construction.
-/

namespace HGAS

namespace RadixSequence

/-- Encode a least-significant-digit-first list in the given base. -/
def encode (base : ℕ) (entries : List ℕ) : ℕ :=
  Nat.ofDigits base entries

/-- Read the `index`-th least-significant radix digit. -/
def digit (base code index : ℕ) : ℕ :=
  code / base ^ index % base

@[simp]
theorem encode_nil (base : ℕ) :
    encode base [] = 0 := rfl

@[simp]
theorem encode_cons (base entry : ℕ) (entries : List ℕ) :
    encode base (entry :: entries) =
      entry + base * encode base entries := rfl

/-- Dividing an encoded list by a power of the base drops that many
least-significant entries. -/
theorem encode_div_pow_eq_encode_drop
    {base : ℕ} (index : ℕ) (hbase : 0 < base)
    (entries : List ℕ)
    (hentries : ∀ entry ∈ entries, entry < base) :
    encode base entries / base ^ index =
      encode base (entries.drop index) := by
  exact Nat.ofDigits_div_pow_eq_ofDigits_drop
    index hbase entries hentries

/-- The radix decoder recovers every in-range entry of a bounded list. -/
theorem digit_encode_eq_getElem
    {base : ℕ} {entries : List ℕ}
    (hbase : 0 < base)
    (hentries : ∀ entry ∈ entries, entry < base)
    (index : ℕ) (hindex : index < entries.length) :
    digit base (encode base entries) index =
      entries[index] := by
  rw [digit, encode_div_pow_eq_encode_drop index hbase entries hentries,
    List.drop_eq_getElem_cons hindex]
  simp only [encode_cons, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (hentries entries[index] (List.getElem_mem hindex))

/-- A convenient uniform base for a list.  Every entry is strictly below
one plus the sum of all entries. -/
def boundingBase (entries : List ℕ) : ℕ :=
  entries.sum + 1

theorem entry_lt_boundingBase
    {entries : List ℕ} {entry : ℕ} (hentry : entry ∈ entries) :
    entry < boundingBase entries := by
  unfold boundingBase
  exact Nat.lt_succ_of_le (List.le_sum_of_mem hentry)

theorem boundingBase_pos (entries : List ℕ) :
    0 < boundingBase entries := by
  simp [boundingBase]

/-- Every finite list has a concrete radix code and a concrete base from
which all of its entries are recovered. -/
theorem exists_code_for_list (entries : List ℕ) :
    ∃ base code,
      0 < base ∧
      ∀ (index : ℕ) (hindex : index < entries.length),
        digit base code index = entries[index] := by
  refine ⟨boundingBase entries, encode (boundingBase entries) entries,
    boundingBase_pos entries, ?_⟩
  intro index hindex
  exact digit_encode_eq_getElem
    (boundingBase_pos entries)
    (fun entry hentry ↦ entry_lt_boundingBase hentry)
    index hindex

/-- Every finite family has a concrete two-number sequence certificate.
This is often the most convenient statement when the intended trace is a
function on `Fin length`. -/
theorem exists_code_for_fin_family
    {length : ℕ} (entry : Fin length → ℕ) :
    ∃ base code,
      0 < base ∧
      ∀ index : Fin length,
        digit base code index = entry index := by
  let entries := List.ofFn entry
  obtain ⟨base, code, hbase, hcode⟩ :=
    exists_code_for_list entries
  refine ⟨base, code, hbase, ?_⟩
  intro index
  have hindex : index.1 < entries.length := by
    simp [entries]
  simpa [entries] using hcode index.1 hindex

/-! ## The decoder is Diophantine -/

/-- Diophantine closure for the radix decoder with arbitrary
Diophantine base, code, and index functions. -/
theorem digit_diophFn
    {α : Type}
    {base code index : (α → ℕ) → ℕ}
    (hbase : Dioph.DiophFn base)
    (hcode : Dioph.DiophFn code)
    (hindex : Dioph.DiophFn index) :
    Dioph.DiophFn fun input ↦
      digit (base input) (code input) (index input) := by
  have hpower : Dioph.DiophFn fun input ↦
      base input ^ index input :=
    Dioph.pow_dioph hbase hindex
  have hquotient : Dioph.DiophFn fun input ↦
      code input / base input ^ index input :=
    Dioph.div_dioph hcode hpower
  simpa [digit] using Dioph.mod_dioph hquotient hbase

/-- In particular, the graph of the three-argument radix decoder is
Diophantine.  Coordinates are `(base, code, index)`. -/
theorem digit_three_variables_diophFn :
    Dioph.DiophFn fun input : Fin 3 → ℕ ↦
      digit (input 0) (input 1) (input 2) := by
  exact digit_diophFn
    (Dioph.proj_dioph (0 : Fin 3))
    (Dioph.proj_dioph (1 : Fin 3))
    (Dioph.proj_dioph (2 : Fin 3))

end RadixSequence

end HGAS
