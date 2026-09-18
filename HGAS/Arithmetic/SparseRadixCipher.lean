import HGAS.Arithmetic.DiophantineBitwise
import Mathlib.Data.List.Indexes
import Mathlib.Tactic

/-!
# Sparse radix ciphers

Matiyasevich's bounded-universal construction stores a finite tuple in
widely separated radix positions.  The separation makes products of two
codes distinguish diagonal terms from cross terms.  This file begins the
reusable semantic layer of that construction.

For the `i`-th tuple entry we use position `2^(i+1)`.  The present module
establishes the basic facts independently of the later multiplication
mask:

* positions are injective and fit in an explicit finite digit list;
* a sparse coefficient array has at most one nonzero summand at each
  position;
* every bounded tuple is recovered exactly by the ordinary radix decoder;
* consequently sparse encoding is injective.

The implementation deliberately reuses `RadixSequence`: a sparse cipher is
an ordinary finite radix word with zeroes in the unused positions.  This
avoids reproducing a separate theory of finite positional expansions.
-/

namespace HGAS

namespace SparseRadixCipher

open scoped BigOperators

/-- The sparse position reserved for tuple coordinate `i`. -/
def slot (i : ℕ) : ℕ :=
  2 ^ (i + 1)

/-- The reserved positions increase strictly. -/
theorem slot_strictMono : StrictMono slot := by
  intro i j hij
  exact Nat.pow_lt_pow_right (by norm_num) (Nat.add_lt_add_right hij 1)

theorem slot_injective : Function.Injective slot :=
  slot_strictMono.injective

/-- Length of the finite radix word used for a tuple of the given
length.  The extra successor includes its largest reserved position. -/
def wordLength (length : ℕ) : ℕ :=
  2 ^ (length + 1) + 1

theorem slot_lt_wordLength
    {length : ℕ} (i : Fin length) :
    slot i < wordLength length := by
  apply Nat.lt_succ_of_le
  exact
    Nat.pow_le_pow_right (by norm_num)
      (Nat.add_le_add_right (Nat.le_of_lt i.isLt) 1)

/-- Coefficient placed at one radix position.  Injectivity of `slot`
ensures that this finite sum contains at most one nonzero term. -/
def coefficientAt
    {length : ℕ} (entry : Fin length → ℕ) (position : ℕ) : ℕ :=
  ∑ i : Fin length, if position = slot i then entry i else 0

theorem coefficientAt_slot
    {length : ℕ} (entry : Fin length → ℕ) (i : Fin length) :
    coefficientAt entry (slot i) = entry i := by
  classical
  unfold coefficientAt
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp only [ite_eq_right_iff]
    intro hslot
    exact (hji (Fin.ext (slot_injective hslot.symm))).elim
  · simp

theorem coefficientAt_eq_zero_of_not_slot
    {length : ℕ} (entry : Fin length → ℕ) {position : ℕ}
    (hposition : ¬ ∃ i : Fin length, position = slot i) :
    coefficientAt entry position = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i hi
  simp only [ite_eq_right_iff]
  intro hslot
  exact (hposition ⟨i, hslot⟩).elim

theorem coefficientAt_lt
    {length base : ℕ} {entry : Fin length → ℕ}
    (hbase : 0 < base)
    (hentry : ∀ i, entry i < base)
    (position : ℕ) :
    coefficientAt entry position < base := by
  classical
  by_cases hposition : ∃ i : Fin length, position = slot i
  · obtain ⟨i, hi⟩ := hposition
    rw [hi, coefficientAt_slot]
    exact hentry i
  · rw [coefficientAt_eq_zero_of_not_slot entry hposition]
    exact hbase

/-- The full finite radix word underlying a sparse tuple code. -/
def entries
    {length : ℕ} (entry : Fin length → ℕ) : List ℕ :=
  List.ofFn fun position : Fin (wordLength length) =>
    coefficientAt entry position

theorem entries_length
    {length : ℕ} (entry : Fin length → ℕ) :
    (entries entry).length = wordLength length := by
  simp [entries]

theorem entries_get_slot
    {length : ℕ} (entry : Fin length → ℕ) (i : Fin length) :
    (entries entry)[slot i]'(by
      simpa [entries] using slot_lt_wordLength i) =
      entry i := by
  simp [entries, coefficientAt_slot]

/-- Sparse radix encoding of a bounded finite tuple. -/
def encode
    (base : ℕ) {length : ℕ} (entry : Fin length → ℕ) : ℕ :=
  RadixSequence.encode base (entries entry)

/-- Sparse encoding has the expected explicit positional sum. -/
theorem encode_eq_sum
    (base : ℕ) {length : ℕ} (entry : Fin length → ℕ) :
    encode base entry =
      ∑ i : Fin length, entry i * base ^ slot i := by
  classical
  rw [encode, RadixSequence.encode, Nat.ofDigits_eq_sum_mapIdx]
  simp only [entries, List.mapIdx_eq_ofFn, List.get_ofFn,
    List.length_ofFn, Fin.val_cast, List.sum_ofFn, coefficientAt]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  let position : Fin (wordLength length) :=
    ⟨slot i, slot_lt_wordLength i⟩
  rw [Finset.sum_eq_single position]
  · simp [position]
  · intro j hj hji
    have hslot : (j : ℕ) ≠ slot i := by
      intro h
      apply hji
      exact Fin.ext h
    simp [hslot]
  · simp

/-- Componentwise addition of tuples is represented by ordinary
addition of their sparse codes.  Bounds are needed only when decoding,
not for this algebraic identity. -/
theorem encode_add
    (base : ℕ) {length : ℕ}
    (left right : Fin length → ℕ) :
    encode base (fun i => left i + right i) =
      encode base left + encode base right := by
  simp only [encode_eq_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact Nat.add_mul _ _ _

/-- Appending one coordinate appends one final reserved sparse block. -/
theorem encode_snoc
    (base : ℕ) {length : ℕ}
    (entry : Fin length → ℕ) (last : ℕ) :
    encode base (Fin.snoc entry last) =
      encode base entry + last * base ^ slot length := by
  rw [encode_eq_sum, encode_eq_sum,
    Fin.sum_univ_castSucc]
  simp

/-- Multiplying two sparse codes expands into the pairwise products of
their coordinates.  Later masks isolate the diagonal `i = j` terms. -/
theorem encode_mul_eq_double_sum
    (base : ℕ) {length : ℕ}
    (left right : Fin length → ℕ) :
    encode base left * encode base right =
      ∑ i : Fin length, ∑ j : Fin length,
        (left i * right j) * base ^ (slot i + slot j) := by
  rw [encode_eq_sum, encode_eq_sum, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [pow_add]
  ring

/-- Every exponent occurring in the product of two length-`length`
sparse words fits in the same explicit product word. -/
theorem slot_add_slot_lt_wordLength
    {length : ℕ} (i j : Fin length) :
    slot i + slot j < wordLength length := by
  have hi :
      slot i ≤ 2 ^ length := by
    exact
      Nat.pow_le_pow_right (by norm_num)
        (by omega)
  have hj :
      slot j ≤ 2 ^ length := by
    exact
      Nat.pow_le_pow_right (by norm_num)
        (by omega)
  have hdouble :
      2 ^ length + 2 ^ length = 2 ^ (length + 1) := by
    rw [pow_succ]
    ring
  unfold wordLength
  omega

/-- Coefficient of a radix position in the product of two sparse
codes.  Several ordered pairs may contribute to one position. -/
def convolutionAt
    {length : ℕ}
    (left right : Fin length → ℕ)
    (position : ℕ) : ℕ :=
  ∑ i : Fin length, ∑ j : Fin length,
    if position = slot i + slot j then left i * right j else 0

/-- Finite radix word containing all coefficients of a sparse-code
product. -/
def convolutionEntries
    {length : ℕ}
    (left right : Fin length → ℕ) : List ℕ :=
  List.ofFn fun position : Fin (wordLength length) =>
    convolutionAt left right position

theorem convolutionEntries_length
    {length : ℕ}
    (left right : Fin length → ℕ) :
    (convolutionEntries left right).length = wordLength length := by
  simp [convolutionEntries]

/-- The ordinary product of sparse codes is exactly the radix encoding
of their convolution coefficients.  No size bound is required for this
pure algebraic identity. -/
theorem encode_convolutionEntries
    (base : ℕ) {length : ℕ}
    (left right : Fin length → ℕ) :
    RadixSequence.encode base (convolutionEntries left right) =
      encode base left * encode base right := by
  classical
  rw [encode_mul_eq_double_sum,
    RadixSequence.encode, Nat.ofDigits_eq_sum_mapIdx]
  simp only [convolutionEntries, List.mapIdx_eq_ofFn,
    List.get_ofFn, List.length_ofFn, Fin.val_cast,
    List.sum_ofFn, convolutionAt]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  let position : Fin (wordLength length) :=
    ⟨slot i + slot j, slot_add_slot_lt_wordLength i j⟩
  rw [Finset.sum_eq_single position]
  · simp [position]
  · intro other hother hne
    have hposition :
        (other : ℕ) ≠ slot i + slot j := by
      intro h
      apply hne
      exact Fin.ext h
    simp [hposition]
  · simp

/-- A diagonal product lands in the next sparse position. -/
theorem slot_add_self (i : ℕ) :
    slot i + slot i = slot (i + 1) := by
  simp [slot, pow_succ]
  ring

/-- Distinct powers of two have disjoint binary supports. -/
theorem pow_two_land_pow_two_eq_zero
    {i j : ℕ} (hij : i ≠ j) :
    2 ^ i &&& 2 ^ j = 0 := by
  apply Nat.zero_of_testBit_eq_false
  intro k
  rw [Nat.testBit_land, Nat.testBit_two_pow, Nat.testBit_two_pow]
  by_cases hi : i = k <;> by_cases hj : j = k <;>
    simp_all

/-- A sum of two powers of two can itself be a power of two only when
the two summands occupy the same binary position. -/
theorem eq_of_pow_add_pow_eq_pow
    {i j k : ℕ}
    (h : 2 ^ i + 2 ^ j = 2 ^ k) :
    i = j := by
  by_contra hij
  have hdisjoint : 2 ^ i &&& 2 ^ j = 0 :=
    pow_two_land_pow_two_eq_zero hij
  have hor :
      2 ^ i ||| 2 ^ j = 2 ^ k :=
    (DiophantineBitwise.lor_eq_add_of_land_eq_zero
      _ _ hdisjoint).trans h
  have hi :=
    congrArg (fun value => Nat.testBit value i) hor
  have hj :=
    congrArg (fun value => Nat.testBit value j) hor
  have hki : k = i := by
    simpa [Nat.testBit_lor, Nat.testBit_two_pow] using hi
  have hkj : k = j := by
    simpa [Nat.testBit_lor, Nat.testBit_two_pow] using hj
  exact hij (hki.symm.trans hkj)

/-- Diagonal terms are exactly the pairwise products whose exponent
sum is another reserved sparse position. -/
theorem slot_add_slot_eq_slot_iff (i j k : ℕ) :
    slot i + slot j = slot k ↔
      i = j ∧ k = i + 1 := by
  constructor
  · intro h
    have hij : i = j := by
      apply Nat.add_right_cancel
      exact eq_of_pow_add_pow_eq_pow h
    subst j
    have hk : slot (i + 1) = slot k := by
      rw [← slot_add_self]
      exact h
    exact ⟨rfl, (slot_injective hk).symm⟩
  · rintro ⟨rfl, rfl⟩
    exact slot_add_self i

/-- Binary uniqueness for a sum of two reserved positions.  The order
of the two summands is the only ambiguity. -/
theorem slot_add_slot_eq_slot_add_slot_iff
    (i j k l : ℕ) :
    slot i + slot j = slot k + slot l ↔
      (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  constructor
  · intro h
    by_cases hij : i = j
    · subst j
      have hkl : k = l := by
        rw [slot_add_self] at h
        have h' : slot k + slot l = slot (i + 1) := h.symm
        exact (slot_add_slot_eq_slot_iff k l (i + 1)).mp h' |>.1
      subst l
      rw [slot_add_self, slot_add_self] at h
      have hik : i = k := by
        have := slot_injective h
        omega
      exact Or.inl ⟨hik, hik⟩
    · have hkl : k ≠ l := by
        intro hkl
        subst l
        rw [slot_add_self] at h
        exact hij
          ((slot_add_slot_eq_slot_iff i j (k + 1)).mp h).1
      have hleftDisjoint :
          slot i &&& slot j = 0 := by
        exact pow_two_land_pow_two_eq_zero
          (by
            intro hexponent
            exact hij (by omega))
      have hrightDisjoint :
          slot k &&& slot l = 0 := by
        exact pow_two_land_pow_two_eq_zero
          (by
            intro hexponent
            exact hkl (by omega))
      have horEq :
          slot i ||| slot j = slot k ||| slot l := by
        rw [DiophantineBitwise.lor_eq_add_of_land_eq_zero
              _ _ hleftDisjoint,
            DiophantineBitwise.lor_eq_add_of_land_eq_zero
              _ _ hrightDisjoint]
        exact h
      have hiBit :
          (slot k ||| slot l).testBit (i + 1) = true := by
        rw [← horEq]
        simp [slot, Nat.testBit_two_pow]
      have hiCases : k = i ∨ l = i := by
        simpa [slot, Nat.testBit_lor, Nat.testBit_two_pow,
          Bool.or_eq_true] using hiBit
      rcases hiCases with hki | hli
      · subst k
        left
        exact ⟨rfl, slot_injective (Nat.add_left_cancel h)⟩
      · subst l
        right
        refine ⟨rfl, ?_⟩
        exact slot_injective
          (Nat.add_left_cancel (h.trans (Nat.add_comm _ _)))
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact Nat.add_comm _ _

/-- The diagonal block for coordinate `i` still fits in the finite
product word. -/
theorem slot_succ_lt_wordLength
    {length : ℕ} (i : Fin length) :
    slot (i + 1) < wordLength length := by
  rw [← slot_add_self]
  exact slot_add_slot_lt_wordLength i i

/-- Sparse coefficient array shifted to the diagonal product
positions. -/
def diagonalCoefficientAt
    {length : ℕ} (entry : Fin length → ℕ) (position : ℕ) : ℕ :=
  ∑ i : Fin length,
    if position = slot (i + 1) then entry i else 0

theorem diagonalCoefficientAt_slot
    {length : ℕ} (entry : Fin length → ℕ) (i : Fin length) :
    diagonalCoefficientAt entry (slot (i + 1)) = entry i := by
  classical
  unfold diagonalCoefficientAt
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    have hslot : slot (i + 1) ≠ slot (j + 1) := by
      intro h
      apply hji
      apply Fin.ext
      have := slot_injective h
      omega
    simp [hslot]
  · simp

theorem diagonalCoefficientAt_eq_zero_of_not_slot
    {length : ℕ} (entry : Fin length → ℕ) {position : ℕ}
    (hposition :
      ¬ ∃ i : Fin length, position = slot (i + 1)) :
    diagonalCoefficientAt entry position = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i hi
  have hne : position ≠ slot (i + 1) := by
    intro h
    exact hposition ⟨i, h⟩
  simp [hne]

theorem diagonalCoefficientAt_lt
    {length base : ℕ} {entry : Fin length → ℕ}
    (hbase : 0 < base)
    (hentry : ∀ i, entry i < base)
    (position : ℕ) :
    diagonalCoefficientAt entry position < base := by
  classical
  by_cases hposition :
      ∃ i : Fin length, position = slot (i + 1)
  · obtain ⟨i, hi⟩ := hposition
    rw [hi, diagonalCoefficientAt_slot]
    exact hentry i
  · rw [diagonalCoefficientAt_eq_zero_of_not_slot
      entry hposition]
    exact hbase

/-- Radix word whose nonzero blocks lie exactly at the diagonal
positions. -/
def diagonalEntries
    {length : ℕ} (entry : Fin length → ℕ) : List ℕ :=
  List.ofFn fun position : Fin (wordLength length) =>
    diagonalCoefficientAt entry position

theorem diagonalEntries_length
    {length : ℕ} (entry : Fin length → ℕ) :
    (diagonalEntries entry).length = wordLength length := by
  simp [diagonalEntries]

theorem diagonalEntries_get_slot
    {length : ℕ} (entry : Fin length → ℕ)
    (i : Fin length) :
    (diagonalEntries entry)[slot (i + 1)]'(by
      simpa [diagonalEntries] using
        slot_succ_lt_wordLength i) =
      entry i := by
  simp [diagonalEntries, diagonalCoefficientAt_slot]

/-- The convolution coefficient at a diagonal position is precisely
the corresponding coordinate product. -/
theorem convolutionAt_diagonal
    {length : ℕ}
    (left right : Fin length → ℕ) (i : Fin length) :
    convolutionAt left right (slot (i + 1)) =
      left i * right i := by
  classical
  unfold convolutionAt
  have hiff (j k : Fin length) :
      slot (i + 1) = slot j + slot k ↔
        j = k ∧ i = j := by
    rw [eq_comm, slot_add_slot_eq_slot_iff]
    constructor
    · rintro ⟨hjk, hik⟩
      exact ⟨Fin.ext hjk, Fin.ext (by omega)⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
  simp_rw [hiff]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      have hij : i ≠ j := fun h => hji h.symm
      simp [hij]
    · simp
  · intro j hj hji
    have hij : i ≠ j := fun h => hji h.symm
    simp [hij]
  · simp

theorem convolutionAt_land_diagonalMask
    {width length : ℕ}
    (left right : Fin length → ℕ)
    (hconvolution :
      ∀ position, convolutionAt left right position < 2 ^ width)
    (position : ℕ) :
    convolutionAt left right position &&&
        diagonalCoefficientAt
          (fun _ : Fin length => 2 ^ width - 1) position =
      diagonalCoefficientAt
        (fun i => left i * right i) position := by
  classical
  by_cases hposition :
      ∃ i : Fin length, position = slot (i + 1)
  · obtain ⟨i, hi⟩ := hposition
    subst position
    have hproduct :
        left i * right i < 2 ^ width := by
      simpa only [convolutionAt_diagonal] using
        hconvolution (slot (i + 1))
    rw [convolutionAt_diagonal,
      diagonalCoefficientAt_slot,
      diagonalCoefficientAt_slot]
    exact Nat.and_two_pow_sub_one_of_lt_two_pow hproduct
  · rw [diagonalCoefficientAt_eq_zero_of_not_slot
      _ hposition]
    simp [diagonalCoefficientAt_eq_zero_of_not_slot
      _ hposition]

/-! ## Binary block masks -/

/-- Bitwise AND commutes with multiplication by a power of two. -/
theorem land_mul_two_pow (left right shift : ℕ) :
    (left * 2 ^ shift) &&& (right * 2 ^ shift) =
      (left &&& right) * 2 ^ shift := by
  simpa only [Nat.shiftLeft_eq] using
    (Nat.shiftLeft_and_distrib
      (a := left) (b := right) (i := shift)).symm

/-- A radix block begins at this binary bit position when the radix is
`2^width`. -/
def blockShift (width position : ℕ) : ℕ :=
  width * position

theorem radixPower_eq_two_pow_blockShift (width position : ℕ) :
    (2 ^ width) ^ position = 2 ^ blockShift width position := by
  simp [blockShift, pow_mul]

/-- A block mask consists of `width` one-bits shifted to the selected
radix position. -/
def blockMask (width position : ℕ) : ℕ :=
  (2 ^ width - 1) * (2 ^ width) ^ position

/-- Applying the matching mask preserves a coefficient that fits in its
block. -/
theorem land_blockMask_eq_self
    {width position value : ℕ}
    (hvalue : value < 2 ^ width) :
    (value * (2 ^ width) ^ position) &&&
        blockMask width position =
      value * (2 ^ width) ^ position := by
  rw [blockMask,
    radixPower_eq_two_pow_blockShift,
    land_mul_two_pow,
    Nat.and_two_pow_sub_one_of_lt_two_pow hvalue]

/-- Blocks at distinct radix positions are bitwise disjoint.  Only the
coefficient in the lower block needs a size bound. -/
theorem land_radixBlocks_eq_zero
    {width lower upper left right : ℕ}
    (hpositions : lower < upper)
    (hleft : left < 2 ^ width) :
    (left * (2 ^ width) ^ lower) &&&
        (right * (2 ^ width) ^ upper) =
      0 := by
  rw [radixPower_eq_two_pow_blockShift,
    radixPower_eq_two_pow_blockShift]
  apply Nat.zero_of_testBit_eq_false
  intro bit
  rw [Nat.testBit_land,
    Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow]
  by_cases hbit : bit < blockShift width upper
  · simp [Nat.not_le_of_lt hbit]
  · have hupp : blockShift width upper ≤ bit :=
      Nat.le_of_not_gt hbit
    have hblocks :
        blockShift width lower + width ≤
          blockShift width upper := by
      calc
        blockShift width lower + width =
            width * (lower + 1) := by
          simp [blockShift, Nat.mul_add]
        _ ≤ width * upper :=
          Nat.mul_le_mul_left width
            (Nat.succ_le_of_lt hpositions)
        _ = blockShift width upper := by
          rfl
    have hlow : blockShift width lower ≤ bit :=
      le_trans (Nat.le_add_right _ _) (hblocks.trans hupp)
    have hindex :
        width ≤ bit - blockShift width lower := by
      omega
    have hxpow :
        left < 2 ^ (bit - blockShift width lower) :=
      hleft.trans_le
        (Nat.pow_le_pow_right (by norm_num) hindex)
    have hxbit :
        left.testBit (bit - blockShift width lower) = false :=
      Nat.testBit_eq_false_of_lt hxpow
    simp [hlow, hupp, hxbit]

/-- Splitting off the low digit of a power-of-two radix word is also a
bitwise-OR decomposition, because the low digit cannot overlap the
shifted tail. -/
theorem encode_cons_eq_or
    {width head : ℕ} (tail : List ℕ)
    (hhead : head < 2 ^ width) :
    RadixSequence.encode (2 ^ width) (head :: tail) =
      (2 ^ width * RadixSequence.encode (2 ^ width) tail) ||| head := by
  rw [RadixSequence.encode_cons, Nat.add_comm]
  exact
    Nat.two_pow_add_eq_or_of_lt hhead
      (RadixSequence.encode (2 ^ width) tail)

/-- Radix encoding is additive, coefficient by coefficient, for two
lists of equal length.  No digit bounds are needed because this is a
plain polynomial identity rather than a decoding statement. -/
theorem encode_zipWith_add (base : ℕ) :
    ∀ (left right : List ℕ),
      left.length = right.length →
      RadixSequence.encode base
          (List.zipWith (· + ·) left right) =
        RadixSequence.encode base left +
          RadixSequence.encode base right := by
  intro left
  induction left with
  | nil =>
      intro right hlength
      have : right = [] :=
        List.eq_nil_of_length_eq_zero (by simpa using hlength.symm)
      subst right
      simp
  | cons leftHead leftTail ih =>
      intro right hlength
      cases right with
      | nil =>
          simp at hlength
      | cons rightHead rightTail =>
          have htail :
              leftTail.length = rightTail.length := by
            simpa using Nat.succ.inj hlength
          simp only [List.zipWith_cons_cons,
            RadixSequence.encode_cons, ih rightTail htail]
          ring

/-- For a power-of-two radix, bitwise AND acts block by block on two
equally long bounded radix words. -/
theorem encode_zipWith_land
    {width : ℕ} :
    ∀ (left right : List ℕ),
      left.length = right.length →
      (∀ value ∈ left, value < 2 ^ width) →
      (∀ value ∈ right, value < 2 ^ width) →
      RadixSequence.encode (2 ^ width) left &&&
          RadixSequence.encode (2 ^ width) right =
        RadixSequence.encode (2 ^ width)
          (List.zipWith (· &&& ·) left right) := by
  intro left
  induction left with
  | nil =>
      intro right hlength hleft hright
      have : right = [] := by
        exact List.eq_nil_of_length_eq_zero (by simpa using hlength.symm)
      subst right
      simp
  | cons leftHead leftTail ih =>
      intro right hlength hleft hright
      cases right with
      | nil =>
          simp at hlength
      | cons rightHead rightTail =>
          have htailLength :
              leftTail.length = rightTail.length := by
            simpa using Nat.succ.inj hlength
          have hleftHead : leftHead < 2 ^ width :=
            hleft leftHead (by simp)
          have hrightHead : rightHead < 2 ^ width :=
            hright rightHead (by simp)
          have hleftTail :
              ∀ value ∈ leftTail, value < 2 ^ width := by
            intro value hvalue
            exact hleft value (by simp [hvalue])
          have hrightTail :
              ∀ value ∈ rightTail, value < 2 ^ width := by
            intro value hvalue
            exact hright value (by simp [hvalue])
          have ih' :=
            ih rightTail htailLength hleftTail hrightTail
          let leftCode :=
            RadixSequence.encode (2 ^ width) leftTail
          let rightCode :=
            RadixSequence.encode (2 ^ width) rightTail
          let resultCode :=
            RadixSequence.encode (2 ^ width)
              (List.zipWith (· &&& ·) leftTail rightTail)
          have hLeft :
              RadixSequence.encode (2 ^ width)
                  (leftHead :: leftTail) =
                (2 ^ width * leftCode) ||| leftHead :=
            encode_cons_eq_or leftTail hleftHead
          have hRight :
              RadixSequence.encode (2 ^ width)
                  (rightHead :: rightTail) =
                (2 ^ width * rightCode) ||| rightHead :=
            encode_cons_eq_or rightTail hrightHead
          have hHigh :
              (2 ^ width * leftCode) &&&
                  (2 ^ width * rightCode) =
                2 ^ width * resultCode := by
            calc
              (2 ^ width * leftCode) &&&
                    (2 ^ width * rightCode) =
                  (leftCode * 2 ^ width) &&&
                    (rightCode * 2 ^ width) := by
                rw [Nat.mul_comm (2 ^ width) leftCode,
                  Nat.mul_comm (2 ^ width) rightCode]
              _ = (leftCode &&& rightCode) * 2 ^ width :=
                land_mul_two_pow leftCode rightCode width
              _ = resultCode * 2 ^ width := by
                rw [ih']
              _ = 2 ^ width * resultCode := by
                rw [Nat.mul_comm]
          have hHighLow :
              (2 ^ width * leftCode) &&& rightHead = 0 := by
            rw [Nat.land_comm]
            simpa [Nat.mul_comm] using
              land_radixBlocks_eq_zero
                (width := width) (lower := 0) (upper := 1)
                (left := rightHead) (right := leftCode)
                (by omega) hrightHead
          have hLowHigh :
              leftHead &&& (2 ^ width * rightCode) = 0 := by
            simpa [Nat.mul_comm] using
              land_radixBlocks_eq_zero
                (width := width) (lower := 0) (upper := 1)
                (left := leftHead) (right := rightCode)
                (by omega) hleftHead
          have hLow :
              leftHead &&& rightHead < 2 ^ width :=
            Nat.and_lt_two_pow leftHead hrightHead
          have hResult :
              RadixSequence.encode (2 ^ width)
                  ((leftHead &&& rightHead) ::
                    List.zipWith (· &&& ·) leftTail rightTail) =
                (2 ^ width * resultCode) |||
                  (leftHead &&& rightHead) :=
            encode_cons_eq_or _ hLow
          rw [hLeft, hRight,
            Nat.and_or_distrib_right,
            Nat.and_or_distrib_left,
            Nat.and_or_distrib_left,
            hHigh, hHighLow, hLowHigh]
          simpa using hResult.symm

/-- At one sparse radix position, pointwise AND of two coefficient
arrays agrees with AND of the two coefficients stored there. -/
theorem coefficientAt_land
    {length : ℕ}
    (left right : Fin length → ℕ) (position : ℕ) :
    coefficientAt left position &&&
        coefficientAt right position =
      coefficientAt (fun i => left i &&& right i) position := by
  by_cases hposition :
      ∃ i : Fin length, position = slot i
  · obtain ⟨i, rfl⟩ := hposition
    simp only [coefficientAt_slot]
  · rw [coefficientAt_eq_zero_of_not_slot left hposition,
      coefficientAt_eq_zero_of_not_slot right hposition,
      coefficientAt_eq_zero_of_not_slot _ hposition]
    simp

/-- Bitwise AND of two bounded sparse words is their componentwise
bitwise AND.  This is a reusable power-of-two radix lemma; it does not
depend on the concrete all-ones cipher. -/
theorem encode_land
    {width length : ℕ}
    (left right : Fin length → ℕ)
    (hleft : ∀ i, left i < 2 ^ width)
    (hright : ∀ i, right i < 2 ^ width) :
    encode (2 ^ width) left &&&
        encode (2 ^ width) right =
      encode (2 ^ width)
        (fun i => left i &&& right i) := by
  have hleftEntries :
      ∀ value ∈ entries left, value < 2 ^ width := by
    intro value hvalue
    obtain ⟨position, rfl⟩ := List.mem_ofFn.mp hvalue
    exact
      coefficientAt_lt (Nat.two_pow_pos width)
        hleft position
  have hrightEntries :
      ∀ value ∈ entries right, value < 2 ^ width := by
    intro value hvalue
    obtain ⟨position, rfl⟩ := List.mem_ofFn.mp hvalue
    exact
      coefficientAt_lt (Nat.two_pow_pos width)
        hright position
  have hzip :
      List.zipWith (· &&& ·) (entries left) (entries right) =
        entries (fun i => left i &&& right i) := by
    apply List.ext_getElem
    · simp [entries]
    · intro index hleftIndex hrightIndex
      simp only [List.getElem_zipWith, entries,
        List.getElem_ofFn]
      exact coefficientAt_land left right index
  unfold encode
  rw [encode_zipWith_land
      (entries left) (entries right)
      (by simp [entries]) hleftEntries hrightEntries,
    hzip]

/-- Every submask of a bounded sparse radix word is itself a sparse
radix word, obtained by choosing a submask independently in each
reserved block.  This is the generic decoding principle behind the
`Code` predicate in Matiyasevich's cipher. -/
theorem exists_encode_of_land_encode_eq_self
    {width length value : ℕ}
    (hwidth : 0 < width)
    (mask : Fin length → ℕ)
    (hmask : ∀ i, mask i < 2 ^ width)
    (hland :
      value &&& encode (2 ^ width) mask = value) :
    ∃ entry : Fin length → ℕ,
      (∀ i, entry i &&& mask i = entry i) ∧
      value = encode (2 ^ width) entry := by
  let count := wordLength length
  let base := 2 ^ width
  have hbase : 1 < base := by
    exact Nat.one_lt_two_pow (Nat.ne_of_gt hwidth)
  have hmaskEntries :
      ∀ digit ∈ entries mask, digit < base := by
    intro digit hdigit
    obtain ⟨position, rfl⟩ := List.mem_ofFn.mp hdigit
    exact
      coefficientAt_lt (Nat.two_pow_pos width)
        hmask position
  have hmaskCodeLt :
      encode base mask < base ^ count := by
    unfold encode RadixSequence.encode
    simpa only [entries_length, count] using
      Nat.ofDigits_lt_base_pow_length
        hbase hmaskEntries
  have hvalueLe :
      value ≤ encode base mask := by
    rw [← hland]
    exact Nat.and_le_right
  have hvalueLt :
      value < base ^ count :=
    hvalueLe.trans_lt hmaskCodeLt
  let digits := Nat.digitsAppend base count value
  have hdigitsLength :
      digits.length = count := by
    exact Nat.length_digitsAppend hbase count hvalueLt
  have hdigitsBound :
      ∀ digit ∈ digits, digit < base := by
    intro digit hdigit
    exact
      Nat.lt_of_mem_digitsAppend hbase count digit hdigit
  have hencodeDigits :
      RadixSequence.encode base digits = value := by
    unfold RadixSequence.encode
    exact
      (Nat.setInvOn_digitsAppend_ofDigits hbase count).2
        hvalueLt
  let entry : Fin length → ℕ :=
    fun i =>
      digits[slot i]'(by
        rw [hdigitsLength]
        exact slot_lt_wordLength i) &&& mask i
  have hzip :
      List.zipWith (· &&& ·) digits (entries mask) =
        entries entry := by
    apply List.ext_getElem
    · simp [hdigitsLength, count, entries]
    · intro position hleft hright
      simp only [List.getElem_zipWith, entries,
        List.getElem_ofFn]
      by_cases hposition :
          ∃ i : Fin length, position = slot i
      · obtain ⟨i, rfl⟩ := hposition
        rw [coefficientAt_slot, coefficientAt_slot]
      · rw [coefficientAt_eq_zero_of_not_slot
          mask hposition,
          coefficientAt_eq_zero_of_not_slot
            entry hposition]
        simp
  refine ⟨entry, ?_, ?_⟩
  · intro i
    dsimp only [entry]
    simp
  · calc
      value =
          value &&& encode base mask :=
        hland.symm
      _ =
          RadixSequence.encode base digits &&&
            encode base mask := by
        rw [hencodeDigits]
      _ =
          RadixSequence.encode base
            (List.zipWith (· &&& ·) digits
              (entries mask)) := by
        unfold encode
        exact
          encode_zipWith_land digits (entries mask)
            (by simp [hdigitsLength, count, entries])
            hdigitsBound hmaskEntries
      _ =
          RadixSequence.encode base (entries entry) := by
        rw [hzip]
      _ = encode base entry := rfl

/-- Pointwise form of diagonal masking for the finite convolution and
mask words. -/
theorem zipWith_convolution_diagonalMask
    {width length : ℕ}
    (left right : Fin length → ℕ)
    (hconvolution :
      ∀ position, convolutionAt left right position < 2 ^ width) :
    List.zipWith (· &&& ·)
        (convolutionEntries left right)
        (diagonalEntries
          (fun _ : Fin length => 2 ^ width - 1)) =
      diagonalEntries (fun i => left i * right i) := by
  apply List.ext_getElem
  · simp [convolutionEntries, diagonalEntries]
  · intro index hleft hright
    simp only [List.getElem_zipWith]
    simp only [convolutionEntries, diagonalEntries,
      List.getElem_ofFn]
    exact
      convolutionAt_land_diagonalMask
        left right hconvolution index

/-- Numeric mask selecting exactly the diagonal product blocks. -/
def diagonalMaskCode (width length : ℕ) : ℕ :=
  RadixSequence.encode (2 ^ width)
    (diagonalEntries
      (fun _ : Fin length => 2 ^ width - 1))

/-- Sparse word containing the coordinatewise products in the shifted
diagonal positions. -/
def diagonalProductCode
    (width : ℕ) {length : ℕ}
    (left right : Fin length → ℕ) : ℕ :=
  RadixSequence.encode (2 ^ width)
    (diagonalEntries (fun i => left i * right i))

/-- The explicit positional-sum form of a diagonal product word. -/
theorem diagonalProductCode_eq_sum
    (width : ℕ) {length : ℕ}
    (left right : Fin length → ℕ) :
    diagonalProductCode width left right =
      ∑ i : Fin length,
        (left i * right i) *
          (2 ^ width) ^ slot (i + 1) := by
  rw [diagonalProductCode, RadixSequence.encode,
    Nat.ofDigits_eq_sum_mapIdx]
  simp only [diagonalEntries,
    List.mapIdx_eq_ofFn, List.get_ofFn, List.length_ofFn,
    Fin.val_cast, List.sum_ofFn, diagonalCoefficientAt]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  let position : Fin (wordLength length) :=
    ⟨slot (i + 1), slot_succ_lt_wordLength i⟩
  rw [Finset.sum_eq_single position]
  · simp [position]
  · intro other hother hne
    have hposition :
        (other : ℕ) ≠ slot (i + 1) := by
      intro h
      apply hne
      exact Fin.ext h
    simp [hposition]
  · simp

/-- Multiplying every diagonal coefficient by a scalar multiplies the
whole encoded word by that scalar. -/
theorem diagonalProductCode_constant_one
    (width length coefficient : ℕ) :
    diagonalProductCode width
        (fun _ : Fin length => coefficient)
        (fun _ : Fin length => 1) =
      coefficient *
        diagonalProductCode width
          (fun _ : Fin length => 1)
          (fun _ : Fin length => 1) := by
  rw [diagonalProductCode_eq_sum,
    diagonalProductCode_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp

/-- Shifting a sparse word to its diagonal positions is the same as
prepending one zero coordinate. -/
theorem diagonalProductCode_right_one_eq_encode_cons
    (width : ℕ) {length : ℕ}
    (entry : Fin length → ℕ) :
    diagonalProductCode width entry
        (fun _ : Fin length => 1) =
      encode (2 ^ width) (Fin.cons 0 entry) := by
  rw [diagonalProductCode_eq_sum, encode_eq_sum,
    Fin.sum_univ_succ]
  simp

/-- The diagonal mask is a scalar multiple of the shifted all-ones
word. -/
theorem diagonalMaskCode_eq_scale_ones
    (width length : ℕ) :
    diagonalMaskCode width length =
      (2 ^ width - 1) *
        diagonalProductCode width
          (fun _ : Fin length => 1)
          (fun _ : Fin length => 1) := by
  rw [← diagonalProductCode_constant_one]
  simp [diagonalMaskCode, diagonalProductCode]

/-- A reserved diagonal digit recovers the corresponding coordinate
product. -/
theorem digit_diagonalProductCode_slot
    {width length : ℕ}
    {left right : Fin length → ℕ}
    (hproduct :
      ∀ i, left i * right i < 2 ^ width)
    (i : Fin length) :
    RadixSequence.digit
        (2 ^ width)
        (diagonalProductCode width left right)
        (slot (i + 1)) =
      left i * right i := by
  have hall :
      ∀ value ∈
          diagonalEntries
            (fun i => left i * right i),
        value < 2 ^ width := by
    intro value hvalue
    obtain ⟨position, rfl⟩ :=
      List.mem_ofFn.mp hvalue
    exact
      diagonalCoefficientAt_lt
        (Nat.two_pow_pos width) hproduct position
  have hslot :
      slot (i + 1) <
        (diagonalEntries
          (fun i => left i * right i)).length := by
    simpa [diagonalEntries] using
      slot_succ_lt_wordLength i
  rw [diagonalProductCode,
    RadixSequence.digit_encode_eq_getElem
      (Nat.two_pow_pos width) hall
      (slot (i + 1)) hslot]
  exact diagonalEntries_get_slot _ i

/-- Diagonal product words are injective in their coordinate products
when those products fit in one block. -/
theorem diagonalProductCode_products_injective
    {width length : ℕ}
    {left₁ right₁ left₂ right₂ : Fin length → ℕ}
    (hproduct₁ :
      ∀ i, left₁ i * right₁ i < 2 ^ width)
    (hproduct₂ :
      ∀ i, left₂ i * right₂ i < 2 ^ width)
    (hcode :
      diagonalProductCode width left₁ right₁ =
        diagonalProductCode width left₂ right₂) :
    ∀ i, left₁ i * right₁ i =
      left₂ i * right₂ i := by
  intro i
  calc
    left₁ i * right₁ i =
        RadixSequence.digit
          (2 ^ width)
          (diagonalProductCode width left₁ right₁)
          (slot (i + 1)) :=
      (digit_diagonalProductCode_slot
        hproduct₁ i).symm
    _ =
        RadixSequence.digit
          (2 ^ width)
          (diagonalProductCode width left₂ right₂)
          (slot (i + 1)) := by
      rw [hcode]
    _ = left₂ i * right₂ i :=
      digit_diagonalProductCode_slot
        hproduct₂ i

/-- **Sparse multiplication mask.**  Provided all convolution
coefficients fit into one binary radix block, ANDing the ordinary
product of two sparse codes with the diagonal mask extracts exactly the
coordinatewise products. -/
theorem land_product_diagonalMask
    {width length : ℕ}
    (left right : Fin length → ℕ)
    (hconvolution :
      ∀ position, convolutionAt left right position < 2 ^ width) :
    (encode (2 ^ width) left * encode (2 ^ width) right) &&&
        diagonalMaskCode width length =
      diagonalProductCode width left right := by
  rw [← encode_convolutionEntries]
  have hconvEntries :
      ∀ value ∈ convolutionEntries left right,
        value < 2 ^ width := by
    intro value hvalue
    obtain ⟨position, rfl⟩ := List.mem_ofFn.mp hvalue
    exact hconvolution position
  have hmaskValue :
      2 ^ width - 1 < 2 ^ width :=
    Nat.sub_lt (Nat.two_pow_pos width) (by norm_num)
  have hmaskEntries :
      ∀ value ∈
          diagonalEntries
            (fun _ : Fin length => 2 ^ width - 1),
        value < 2 ^ width := by
    intro value hvalue
    obtain ⟨position, rfl⟩ := List.mem_ofFn.mp hvalue
    exact
      diagonalCoefficientAt_lt
        (Nat.two_pow_pos width)
        (fun _ => hmaskValue) position
  have hland :=
    encode_zipWith_land
      (convolutionEntries left right)
      (diagonalEntries
        (fun _ : Fin length => 2 ^ width - 1))
      (by simp [convolutionEntries, diagonalEntries])
      hconvEntries hmaskEntries
  rw [zipWith_convolution_diagonalMask
    left right hconvolution] at hland
  exact hland

/-! ## A uniform safe block width -/

/-- A deliberately generous binary block width.  It allows a direct
cardinality bound on every convolution coefficient, avoiding delicate
case analysis of collisions between cross-term exponents. -/
def safeWidth (entryWidth length : ℕ) : ℕ :=
  2 * length + 2 * entryWidth + 1

/-- If all tuple entries use fewer than `entryWidth` bits, every
convolution coefficient fits in a `safeWidth entryWidth length`-bit
block. -/
theorem convolutionAt_lt_safeWidth
    {entryWidth length : ℕ}
    {left right : Fin length → ℕ}
    (hleft : ∀ i, left i < 2 ^ entryWidth)
    (hright : ∀ i, right i < 2 ^ entryWidth)
    (position : ℕ) :
    convolutionAt left right position <
      2 ^ safeWidth entryWidth length := by
  have hproduct (i j : Fin length) :
      left i * right j < 2 ^ (2 * entryWidth) := by
    calc
      left i * right j <
          2 ^ entryWidth * 2 ^ entryWidth :=
        Nat.mul_lt_mul_of_lt_of_lt (hleft i) (hright j)
      _ = 2 ^ (2 * entryWidth) := by
        rw [← pow_add]
        congr 1
        omega
  have hinner (i : Fin length) :
      (∑ j : Fin length,
        if position = slot i + slot j
        then left i * right j else 0) ≤
          length * 2 ^ (2 * entryWidth) := by
    have h :=
      Finset.sum_le_card_nsmul
        (Finset.univ : Finset (Fin length))
        (fun j =>
          if position = slot i + slot j
          then left i * right j else 0)
        (2 ^ (2 * entryWidth))
        (by
          intro j hj
          dsimp only
          split_ifs
          · exact (hproduct i j).le
          · exact Nat.zero_le _)
    simpa using h
  have hsum :
      convolutionAt left right position ≤
        length * (length * 2 ^ (2 * entryWidth)) := by
    unfold convolutionAt
    have h :=
      Finset.sum_le_card_nsmul
        (Finset.univ : Finset (Fin length))
        (fun i =>
          ∑ j : Fin length,
            if position = slot i + slot j
            then left i * right j else 0)
        (length * 2 ^ (2 * entryWidth))
        (by
          intro i hi
          exact hinner i)
    simpa using h
  have hlengthSquare :
      length * length < 2 ^ (2 * length) := by
    calc
      length * length <
          2 ^ length * 2 ^ length :=
        Nat.mul_lt_mul_of_lt_of_lt
          Nat.lt_two_pow_self Nat.lt_two_pow_self
      _ = 2 ^ (2 * length) := by
        rw [← pow_add]
        congr 1
        omega
  have hcard :
      length * (length * 2 ^ (2 * entryWidth)) <
        2 ^ safeWidth entryWidth length := by
    calc
      length * (length * 2 ^ (2 * entryWidth)) =
          (length * length) * 2 ^ (2 * entryWidth) := by
        ring
      _ < 2 ^ (2 * length) * 2 ^ (2 * entryWidth) :=
        Nat.mul_lt_mul_of_pos_right
          hlengthSquare (Nat.two_pow_pos _)
      _ = 2 ^ (2 * length + 2 * entryWidth) := by
        rw [pow_add]
      _ < 2 ^ safeWidth entryWidth length := by
        apply Nat.pow_lt_pow_right (by norm_num)
        simp [safeWidth]
  exact hsum.trans_lt hcard

/-- Fully discharged multiplication-mask theorem using the uniform
safe width. -/
theorem land_product_diagonalMask_safe
    {entryWidth length : ℕ}
    (left right : Fin length → ℕ)
    (hleft : ∀ i, left i < 2 ^ entryWidth)
    (hright : ∀ i, right i < 2 ^ entryWidth) :
    (encode (2 ^ safeWidth entryWidth length) left *
        encode (2 ^ safeWidth entryWidth length) right) &&&
        diagonalMaskCode
          (safeWidth entryWidth length) length =
      diagonalProductCode
        (safeWidth entryWidth length) left right := by
  exact
    land_product_diagonalMask left right
      (convolutionAt_lt_safeWidth hleft hright)

/-- The reserved digit recovers the corresponding tuple entry. -/
theorem digit_encode_slot
    {base length : ℕ}
    (hbase : 0 < base)
    {entry : Fin length → ℕ}
    (hentry : ∀ i, entry i < base)
    (i : Fin length) :
    RadixSequence.digit base (encode base entry) (slot i) =
      entry i := by
  have hall :
      ∀ value ∈ entries entry, value < base := by
    intro value hvalue
    obtain ⟨position, rfl⟩ := List.mem_ofFn.mp hvalue
    exact coefficientAt_lt hbase hentry position
  have hslot :
      slot i < (entries entry).length := by
    simpa [entries] using slot_lt_wordLength i
  rw [encode,
    RadixSequence.digit_encode_eq_getElem hbase hall (slot i) hslot]
  exact entries_get_slot entry i

/-- Sparse encoding is injective on tuples whose entries fit in the
base. -/
theorem encode_injective
    {base length : ℕ}
    (hbase : 0 < base)
    {left right : Fin length → ℕ}
    (hleft : ∀ i, left i < base)
    (hright : ∀ i, right i < base)
    (hcode : encode base left = encode base right) :
    left = right := by
  funext i
  calc
    left i =
        RadixSequence.digit base (encode base left) (slot i) :=
      (digit_encode_slot hbase hleft i).symm
    _ =
        RadixSequence.digit base (encode base right) (slot i) := by
      rw [hcode]
    _ = right i :=
      digit_encode_slot hbase hright i

end SparseRadixCipher

end HGAS
