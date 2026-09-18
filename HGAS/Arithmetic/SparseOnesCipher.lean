import HGAS.Arithmetic.SparseRadixCipher
import Mathlib.Tactic

/-!
# The sparse all-ones cipher

This file specializes the reusable sparse-radix machinery to the
all-ones word used in Matiyasevich's bounded-sequence construction.

For a parameter `q` put

```
R = 2^(4q).
```

The length-`l` sparse word has a `1` in the radix positions
`2, 4, 8, ..., 2^l`:

```
U(l,q) = R^2 + R^4 + ... + R^(2^l).
```

Its shifted companion has a `1` in positions
`4, 8, ..., 2^(l+1)`.  Squaring the first word places precisely those
terms on the diagonal.  A dense radix word of ones is then used as a
binary mask to separate the diagonal terms from the off-diagonal terms.

The definitions below deliberately distinguish the generic radix objects
(`denseOnes`) from this concrete choice of sparse exponents
(`sparseOnes` and `shiftedSparseOnes`).  This separation makes the
radix lemmas reusable in later cipher constructions.
-/

namespace HGAS

namespace SparseOnesCipher

open scoped BigOperators

open SparseRadixCipher

/-- The power-of-two radix in Matiyasevich's cipher. -/
def cipherBase (q : ℕ) : ℕ :=
  2 ^ (4 * q)

/-- A dense radix word with `count` consecutive coefficients equal to
one, starting at the units position. -/
def denseOnes (base count : ℕ) : ℕ :=
  ∑ position ∈ Finset.range count, base ^ position

/-- The sparse word with coefficients one in positions `slot i`,
for `i < length`. -/
def sparseOnes (length q : ℕ) : ℕ :=
  SparseRadixCipher.encode (cipherBase q)
    (fun _ : Fin length => 1)

/-- The shifted sparse word in the diagonal positions `slot (i+1)`. -/
def shiftedSparseOnes (length q : ℕ) : ℕ :=
  SparseRadixCipher.diagonalProductCode (4 * q)
    (fun _ : Fin length => 1)
    (fun _ : Fin length => 1)

/-- The intended semantic relation between the two sparse all-ones
words. -/
def SeqsOfOnes (length q u u₁ : ℕ) : Prop :=
  length + 1 < q ∧
    u = sparseOnes length q ∧
    u₁ = shiftedSparseOnes length q

@[simp]
theorem cipherBase_eq (q : ℕ) :
    cipherBase q = 2 ^ (4 * q) := rfl

theorem cipherBase_pos (q : ℕ) :
    0 < cipherBase q := by
  simp [cipherBase]

theorem cipherBase_ge_two {q : ℕ} (hq : 0 < q) :
    2 ≤ cipherBase q := by
  rw [cipherBase]
  have hfour : 1 ≤ 4 * q := by omega
  exact (Nat.pow_le_pow_right (by omega) hfour : 2 ^ 1 ≤ 2 ^ (4 * q))

/-- The explicit finite-sum form of the first sparse word. -/
theorem sparseOnes_eq_sum (length q : ℕ) :
    sparseOnes length q =
      ∑ i : Fin length, cipherBase q ^ slot i := by
  simp [sparseOnes, SparseRadixCipher.encode_eq_sum]

/-- The explicit finite-sum form of the shifted sparse word. -/
theorem shiftedSparseOnes_eq_sum (length q : ℕ) :
    shiftedSparseOnes length q =
      ∑ i : Fin length, cipherBase q ^ slot (i + 1) := by
  rw [shiftedSparseOnes, SparseRadixCipher.diagonalProductCode,
    RadixSequence.encode, Nat.ofDigits_eq_sum_mapIdx]
  simp only [SparseRadixCipher.diagonalEntries,
    List.mapIdx_eq_ofFn, List.get_ofFn, List.length_ofFn,
    Fin.val_cast, List.sum_ofFn,
    SparseRadixCipher.diagonalCoefficientAt]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  let position : Fin (SparseRadixCipher.wordLength length) :=
    ⟨slot (i + 1),
      SparseRadixCipher.slot_succ_lt_wordLength i⟩
  rw [Finset.sum_eq_single position]
  · simp [position, cipherBase]
  · intro other hother hne
    have hposition :
        (other : ℕ) ≠ slot (i + 1) := by
      intro h
      apply hne
      exact Fin.ext h
    simp [hposition]
  · simp

@[simp]
theorem sparseOnes_zero (q : ℕ) :
    sparseOnes 0 q = 0 := by
  simp [sparseOnes_eq_sum]

@[simp]
theorem shiftedSparseOnes_zero (q : ℕ) :
    shiftedSparseOnes 0 q = 0 := by
  simp [shiftedSparseOnes_eq_sum]

/-- The elementary geometric identity behind the dense mask. -/
theorem denseOnes_equation
    {base count : ℕ} (hbase : 1 ≤ base) :
    1 + (base - 1) * denseOnes base count = base ^ count := by
  induction count with
  | zero =>
      simp [denseOnes]
  | succ count ih =>
      rw [denseOnes, Finset.sum_range_succ]
      rw [Nat.mul_add, ← denseOnes]
      calc
        1 +
              ((base - 1) * denseOnes base count +
                (base - 1) * base ^ count) =
            (1 + (base - 1) * denseOnes base count) +
              (base - 1) * base ^ count := by
                rw [Nat.add_assoc]
        _ = base ^ count + (base - 1) * base ^ count := by
              rw [ih]
        _ = (1 + (base - 1)) * base ^ count := by
              rw [Nat.add_mul, one_mul]
        _ = base * base ^ count := by
              congr 1
              omega
        _ = base ^ (count + 1) := by
              rw [pow_succ, Nat.mul_comm]

/-- Conversely, the geometric equation uniquely determines the dense
all-ones word as soon as the radix is at least two. -/
theorem denseOnes_iff_equation
    {base count w : ℕ} (hbase : 2 ≤ base) :
    w = denseOnes base count ↔
      1 + (base - 1) * w = base ^ count := by
  constructor
  · rintro rfl
    exact denseOnes_equation (by omega)
  · intro hw
    have hdense := denseOnes_equation
      (base := base) (count := count) (by omega)
    have hpositive : 0 < base - 1 := by omega
    have hmul :
        (base - 1) * w =
          (base - 1) * denseOnes base count := by
      omega
    exact Nat.eq_of_mul_eq_mul_left hpositive hmul

/-- A dense all-ones radix word fits strictly below the next radix
power. -/
theorem denseOnes_lt_pow
    {base count : ℕ} (hbase : 2 ≤ base) :
    denseOnes base count < base ^ count := by
  have hgeom :=
    denseOnes_equation
      (base := base) (count := count) (by omega)
  have hfactor : 1 ≤ base - 1 := by omega
  have hle :
      denseOnes base count ≤
        (base - 1) * denseOnes base count := by
    simpa only [one_mul] using
      Nat.mul_le_mul_right (denseOnes base count) hfactor
  omega

/-- Exact binary support of a dense word in radix `2^width`: there is
one bit at the beginning of each radix block and no others. -/
theorem testBit_denseOnes_iff
    {width : ℕ} (hwidth : 0 < width) :
    ∀ count bit : ℕ,
      (denseOnes (2 ^ width) count).testBit bit = true ↔
        ∃ position < count, bit = width * position := by
  intro count
  induction count with
  | zero =>
      intro bit
      simp [denseOnes]
  | succ count ih =>
      intro bit
      have hbase : 2 ≤ 2 ^ width := by
        exact
          (Nat.pow_le_pow_right (by norm_num)
            hwidth : 2 ^ 1 ≤ 2 ^ width)
      have hlow :
          denseOnes (2 ^ width) count <
            2 ^ (width * count) := by
        simpa [pow_mul] using
          denseOnes_lt_pow
            (base := 2 ^ width) (count := count) hbase
      have hdecomp :
          denseOnes (2 ^ width) (count + 1) =
            2 ^ (width * count) |||
              denseOnes (2 ^ width) count := by
        rw [denseOnes, Finset.sum_range_succ]
        rw [← denseOnes]
        have hpow :
            (2 ^ width) ^ count =
              2 ^ (width * count) := by
          rw [← pow_mul]
        rw [hpow]
        simpa [Nat.add_comm] using
          (Nat.two_pow_add_eq_or_of_lt hlow 1)
      rw [hdecomp, Nat.testBit_or, Bool.or_eq_true, ih]
      rw [Nat.testBit_two_pow]
      constructor
      · rintro (hbit | ⟨position, hposition, rfl⟩)
        · have heq : width * count = bit :=
            of_decide_eq_true hbit
          exact ⟨count, by omega, heq.symm⟩
        · exact ⟨position, by omega, rfl⟩
      · rintro ⟨position, hposition, hbit⟩
        by_cases hp : position = count
        · left
          subst position
          simp [hbit]
        · right
          exact ⟨position, by omega, hbit⟩

/-- Splitting off the final block of a dense word. -/
theorem denseOnes_succ (base count : ℕ) :
    denseOnes base (count + 1) =
      denseOnes base count + base ^ count := by
  rw [denseOnes, Finset.sum_range_succ]
  rw [← denseOnes]

/-- A coarse but useful gap estimate.  Once the endpoint is at least
the fourth radix block and the radix is at least four, inserting one
extra `base^2` term below a dense prefix still does not reach the
endpoint block. -/
theorem pow_two_add_denseOnes_lt
    {base endpoint : ℕ}
    (hbase : 4 ≤ base) (hendpoint : 4 ≤ endpoint) :
    base ^ 2 + denseOnes base endpoint <
      base ^ endpoint := by
  have htwoMem : 2 ∈ Finset.range endpoint := by
    simp only [Finset.mem_range]
    omega
  have hterm :
      base ^ 2 ≤ denseOnes base endpoint := by
    rw [denseOnes]
    exact Finset.single_le_sum
      (fun i hi => Nat.zero_le (base ^ i)) htwoMem
  have hfactor : 2 ≤ base - 1 := by omega
  have hdouble :
      2 * denseOnes base endpoint ≤
        (base - 1) * denseOnes base endpoint :=
    Nat.mul_le_mul_right
      (denseOnes base endpoint) hfactor
  have hleft :
      base ^ 2 + denseOnes base endpoint ≤
        2 * denseOnes base endpoint := by
    omega
  have hgeom :=
    denseOnes_equation
      (base := base) (count := endpoint) (by omega)
  omega

/-- Absorption by a dense mask forces every one-bit to lie at the
beginning of one of its radix blocks. -/
theorem testBit_position_of_land_denseOnes_eq_self
    {width count value bit : ℕ}
    (hwidth : 0 < width)
    (hland :
      value &&& denseOnes (2 ^ width) count = value)
    (hbit : value.testBit bit = true) :
    ∃ position < count, bit = width * position := by
  have htest := congrArg
    (fun n => n.testBit bit) hland
  change
    (value &&& denseOnes (2 ^ width) count).testBit bit =
      value.testBit bit at htest
  rw [Nat.testBit_land, hbit] at htest
  have hdense :
      (denseOnes (2 ^ width) count).testBit bit = true := by
    simpa using htest
  exact
    (testBit_denseOnes_iff hwidth count bit).mp hdense

/-- In particular, a number absorbed by the dense mask lies below the
next radix power. -/
theorem lt_pow_of_land_denseOnes_eq_self
    {width count value : ℕ}
    (hwidth : 0 < width)
    (hland :
      value &&& denseOnes (2 ^ width) count = value) :
    value < (2 ^ width) ^ count := by
  have hle :
      value ≤ denseOnes (2 ^ width) count := by
    rw [← hland]
    exact Nat.and_le_right
  exact hle.trans_lt
    (denseOnes_lt_pow
      (base := 2 ^ width) (count := count)
      (by
        exact
          (Nat.pow_le_pow_right (by norm_num)
            hwidth : 2 ^ 1 ≤ 2 ^ width)))

/-- Divisibility by the fourth radix block makes a number bitwise
disjoint from the second radix block. -/
theorem radixSquare_land_eq_zero_of_fourth_dvd
    {width value : ℕ}
    (hwidth : 0 < width)
    (hdvd : (2 ^ width) ^ 4 ∣ value) :
    ((2 ^ width) * (2 ^ width)) &&& value = 0 := by
  rcases hdvd with ⟨factor, hfactor⟩
  have hone : 1 < 2 ^ width :=
    Nat.one_lt_two_pow (Nat.ne_of_gt hwidth)
  have hblocks :=
    SparseRadixCipher.land_radixBlocks_eq_zero
      (width := width) (lower := 2) (upper := 4)
      (left := 1) (right := factor)
      (by omega) hone
  rw [hfactor]
  simpa only [one_mul, pow_two, Nat.mul_comm] using hblocks

/-- Multiples of `2^threshold` have no one-bits below `threshold`. -/
theorem testBit_eq_false_of_two_pow_dvd
    {threshold value bit : ℕ}
    (hdvd : 2 ^ threshold ∣ value)
    (hbit : bit < threshold) :
    value.testBit bit = false := by
  rcases hdvd with ⟨factor, hfactor⟩
  rw [hfactor, Nat.mul_comm,
    Nat.testBit_mul_two_pow]
  simp [Nat.not_le_of_gt hbit]

/-! ### Decoding an arbitrary submask of a dense word -/

/-- Keep precisely those block-starting powers selected by the
corresponding bits of `value`. -/
def selectedBits (width count value : ℕ) : ℕ :=
  ∑ position ∈ Finset.range count,
    if value.testBit (width * position) = true
    then 2 ^ (width * position)
    else 0

/-- A selected-bit word is bounded by the full dense mask. -/
theorem selectedBits_le_denseOnes
    (width count value : ℕ) :
    selectedBits width count value ≤
      denseOnes (2 ^ width) count := by
  rw [selectedBits, denseOnes]
  rw [show
      (fun position => (2 ^ width) ^ position) =
        (fun position => 2 ^ (width * position)) by
      funext position
      rw [← pow_mul]]
  apply Finset.sum_le_sum
  intro position hposition
  split_ifs
  · exact Nat.le_refl _
  · exact Nat.zero_le _

/-- Exact bit support of a selected submask. -/
theorem testBit_selectedBits_iff
    {width : ℕ} (hwidth : 0 < width) :
    ∀ count value bit : ℕ,
      (selectedBits width count value).testBit bit = true ↔
        ∃ position < count,
          value.testBit (width * position) = true ∧
          bit = width * position := by
  intro count
  induction count with
  | zero =>
      intro value bit
      simp [selectedBits]
  | succ count ih =>
      intro value bit
      by_cases hselected :
          value.testBit (width * count) = true
      · have hbase : 2 ≤ 2 ^ width := by
          exact
            (Nat.pow_le_pow_right (by norm_num)
              hwidth : 2 ^ 1 ≤ 2 ^ width)
        have hlow :
            selectedBits width count value <
              2 ^ (width * count) := by
          exact
            (selectedBits_le_denseOnes
              width count value).trans_lt
              (by
                simpa [pow_mul] using
                  denseOnes_lt_pow
                    (base := 2 ^ width)
                    (count := count) hbase)
        have hdecomp :
            selectedBits width (count + 1) value =
              2 ^ (width * count) |||
                selectedBits width count value := by
          rw [selectedBits, Finset.sum_range_succ,
            if_pos hselected, ← selectedBits]
          simpa [Nat.add_comm] using
            (Nat.two_pow_add_eq_or_of_lt hlow 1)
        rw [hdecomp, Nat.testBit_or,
          Bool.or_eq_true, Nat.testBit_two_pow, ih]
        constructor
        · rintro (hbit | ⟨position, hposition,
              hvalue, rfl⟩)
          · have heq : width * count = bit :=
              of_decide_eq_true hbit
            exact
              ⟨count, by omega, hselected, heq.symm⟩
          · exact
              ⟨position, by omega, hvalue, rfl⟩
        · rintro
            ⟨position, hposition, hvalue,
              hbitPosition⟩
          by_cases hp : position = count
          · left
            subst position
            simp [hbitPosition]
          · right
            exact
              ⟨position, by omega, hvalue,
                hbitPosition⟩
      · have hdecomp :
            selectedBits width (count + 1) value =
              selectedBits width count value := by
          rw [selectedBits, Finset.sum_range_succ,
            if_neg hselected, Nat.add_zero,
            ← selectedBits]
        rw [hdecomp, ih]
        constructor
        · rintro
            ⟨position, hposition, hvalue,
              hbitPosition⟩
          exact
            ⟨position, by omega, hvalue,
              hbitPosition⟩
        · rintro
            ⟨position, hposition, hvalue,
              hbitPosition⟩
          have hp : position ≠ count := by
            intro hp
            subst position
            exact hselected hvalue
          exact
            ⟨position, by omega, hvalue,
              hbitPosition⟩

/-- Every number absorbed by a dense mask is exactly the sum of the
block-starting powers selected by its own bits. -/
theorem selectedBits_eq_of_land_denseOnes_eq_self
    {width count value : ℕ}
    (hwidth : 0 < width)
    (hland :
      value &&& denseOnes (2 ^ width) count = value) :
    selectedBits width count value = value := by
  apply Nat.eq_of_testBit_eq
  intro bit
  by_cases hvalue : value.testBit bit = true
  · obtain ⟨position, hposition, hbitPosition⟩ :=
      testBit_position_of_land_denseOnes_eq_self
        hwidth hland hvalue
    have hselected :
        (selectedBits width count value).testBit bit =
          true :=
      (testBit_selectedBits_iff
        hwidth count value bit).mpr
        ⟨position, hposition,
          by simpa [hbitPosition] using hvalue,
          hbitPosition⟩
    rw [hselected, hvalue]
  · have hvalueFalse : value.testBit bit = false := by
      cases h : value.testBit bit <;> simp_all
    have hselectedFalse :
        (selectedBits width count value).testBit bit =
          false := by
      by_contra hnot
      have hselectedTrue :
          (selectedBits width count value).testBit bit =
            true := by
        cases h :
            (selectedBits width count value).testBit bit <;>
          simp_all
      obtain ⟨position, hposition, hsource,
          hbitPosition⟩ :=
        (testBit_selectedBits_iff
          hwidth count value bit).mp hselectedTrue
      rw [hbitPosition] at hvalueFalse
      exact Bool.false_ne_true
        (hvalueFalse.symm.trans hsource)
    rw [hselectedFalse, hvalueFalse]

/-- Ordinary radix digits corresponding to `selectedBits`. -/
def selectedEntries (width count value : ℕ) : List ℕ :=
  List.ofFn fun position : Fin count =>
    if value.testBit (width * position) = true
    then 1
    else 0

@[simp]
theorem selectedEntries_length
    (width count value : ℕ) :
    (selectedEntries width count value).length = count := by
  simp [selectedEntries]

theorem selectedEntries_lt_base
    {width : ℕ} (hwidth : 0 < width)
    (count value : ℕ) :
    ∀ digit ∈ selectedEntries width count value,
      digit < 2 ^ width := by
  intro digit hdigit
  obtain ⟨position, rfl⟩ := List.mem_ofFn.mp hdigit
  split_ifs
  · exact Nat.one_lt_two_pow (Nat.ne_of_gt hwidth)
  · exact Nat.two_pow_pos width

/-- The selected digit list encodes the selected-bit sum. -/
theorem encode_selectedEntries
    (width count value : ℕ) :
    RadixSequence.encode (2 ^ width)
        (selectedEntries width count value) =
      selectedBits width count value := by
  rw [RadixSequence.encode, Nat.ofDigits_eq_sum_mapIdx]
  simp only [selectedEntries, List.mapIdx_eq_ofFn,
    List.get_ofFn, List.length_ofFn, Fin.val_cast]
  rw [List.sum_ofFn]
  rw [selectedBits]
  rw [← Fin.sum_univ_eq_sum_range
      (fun position : ℕ =>
        if value.testBit (width * position) = true
        then 2 ^ (width * position)
        else 0)]
  apply Finset.sum_congr rfl
  intro position hposition
  by_cases hbit :
      value.testBit (width * position) = true
  · rw [if_pos hbit, if_pos hbit, one_mul, ← pow_mul]
  · rw [if_neg hbit, if_neg hbit, zero_mul]

/-- Radix reconstruction of a number absorbed by a dense mask. -/
theorem encode_selectedEntries_eq_of_land
    {width count value : ℕ}
    (hwidth : 0 < width)
    (hland :
      value &&& denseOnes (2 ^ width) count = value) :
    RadixSequence.encode (2 ^ width)
        (selectedEntries width count value) =
      value := by
  rw [encode_selectedEntries]
  exact
    selectedBits_eq_of_land_denseOnes_eq_self
      hwidth hland

/-! ### Ordinary radix convolution -/

/-- Coefficient of an ordinary (not sparse) radix-word product. -/
def linearConvolutionAt
    {count : ℕ} (left right : Fin count → ℕ)
    (position : ℕ) : ℕ :=
  ∑ i : Fin count, ∑ j : Fin count,
    if position = i + j then left i * right j else 0

/-- All coefficients of an ordinary radix-word product. -/
def linearConvolutionEntries
    {count : ℕ} (left right : Fin count → ℕ) : List ℕ :=
  List.ofFn fun position : Fin (2 * count) =>
    linearConvolutionAt left right position

@[simp]
theorem linearConvolutionEntries_length
    {count : ℕ} (left right : Fin count → ℕ) :
    (linearConvolutionEntries left right).length =
      2 * count := by
  simp [linearConvolutionEntries]

/-- Explicit sum for the radix encoding of a finite family. -/
theorem encode_ofFn_eq_sum
    (base : ℕ) {count : ℕ}
    (entry : Fin count → ℕ) :
    RadixSequence.encode base (List.ofFn entry) =
      ∑ i : Fin count, entry i * base ^ (i : ℕ) := by
  rw [RadixSequence.encode, Nat.ofDigits_eq_sum_mapIdx]
  simp only [List.mapIdx_eq_ofFn, List.get_ofFn,
    List.length_ofFn, Fin.val_cast]
  rw [List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i hi
  congr 2

/-- Multiplication of two ordinary radix words expands into the expected
double sum. -/
theorem encode_ofFn_mul_eq_double_sum
    (base : ℕ) {count : ℕ}
    (left right : Fin count → ℕ) :
    RadixSequence.encode base (List.ofFn left) *
        RadixSequence.encode base (List.ofFn right) =
      ∑ i : Fin count, ∑ j : Fin count,
        (left i * right j) *
          base ^ ((i : ℕ) + (j : ℕ)) := by
  rw [encode_ofFn_eq_sum, encode_ofFn_eq_sum,
    Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [pow_add]
  ring

/-- The product of two ordinary radix words is the encoding of their
convolution coefficients. -/
theorem encode_linearConvolutionEntries
    (base : ℕ) {count : ℕ}
    (left right : Fin count → ℕ) :
    RadixSequence.encode base
        (linearConvolutionEntries left right) =
      RadixSequence.encode base (List.ofFn left) *
        RadixSequence.encode base (List.ofFn right) := by
  classical
  rw [encode_ofFn_mul_eq_double_sum]
  rw [linearConvolutionEntries, encode_ofFn_eq_sum]
  unfold linearConvolutionAt
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  have hposition :
      (i : ℕ) + (j : ℕ) < 2 * count := by
    have hi' := i.isLt
    have hj' := j.isLt
    omega
  let position : Fin (2 * count) :=
    ⟨(i : ℕ) + (j : ℕ), hposition⟩
  rw [Finset.sum_eq_single position]
  · simp [position]
  · intro other hother hne
    have hpositionNe :
        (other : ℕ) ≠ (i : ℕ) + (j : ℕ) := by
      intro h
      apply hne
      exact Fin.ext h
    simp [hpositionNe]
  · simp

/-- A crude uniform bound for ordinary convolution coefficients. -/
theorem linearConvolutionAt_le_square
    {count : ℕ} {left right : Fin count → ℕ}
    (hleft : ∀ i, left i ≤ 1)
    (hright : ∀ i, right i ≤ 1)
    (position : ℕ) :
    linearConvolutionAt left right position ≤
      count * count := by
  have hterm (i j : Fin count) :
      (if position = (i : ℕ) + (j : ℕ)
        then left i * right j else 0) ≤ 1 := by
    split_ifs
    · simpa using
        Nat.mul_le_mul (hleft i) (hright j)
    · exact Nat.zero_le _
  have hinner (i : Fin count) :
      (∑ j : Fin count,
        if position = (i : ℕ) + (j : ℕ)
        then left i * right j else 0) ≤ count := by
    have h :=
      Finset.sum_le_card_nsmul
        (Finset.univ : Finset (Fin count))
        (fun j =>
          if position = (i : ℕ) + (j : ℕ)
          then left i * right j else 0)
        1 (by
          intro j hj
          exact hterm i j)
    simpa using h
  unfold linearConvolutionAt
  have h :=
    Finset.sum_le_card_nsmul
      (Finset.univ : Finset (Fin count))
      (fun i =>
        ∑ j : Fin count,
          if position = (i : ℕ) + (j : ℕ)
          then left i * right j else 0)
      count (by
        intro i hi
        exact hinner i)
  simpa [Nat.mul_comm] using h

/-- In characteristic two, every off-diagonal pair in a symmetric
convolution cancels with its transpose. -/
theorem linearConvolutionAt_cast_zmod_two
    {count : ℕ} (entry : Fin count → ℕ)
    (position : ℕ) :
    (linearConvolutionAt entry entry position : ZMod 2) =
      ∑ i : Fin count,
        if position = (i : ℕ) + (i : ℕ)
        then (entry i : ZMod 2) * entry i
        else 0 := by
  classical
  let pairs : Finset (Fin count × Fin count) :=
    Finset.univ ×ˢ Finset.univ
  let term : (Fin count × Fin count) → ZMod 2 :=
    fun pair =>
      if position =
          (pair.1 : ℕ) + (pair.2 : ℕ)
      then (entry pair.1 : ZMod 2) * entry pair.2
      else 0
  let diagonal : (Fin count × Fin count) → ZMod 2 :=
    fun pair =>
      if pair.1 = pair.2 then term pair else 0
  let offDiagonal :
      (Fin count × Fin count) → ZMod 2 :=
    fun pair =>
      if pair.1 = pair.2 then 0 else term pair
  have hsplit (pair : Fin count × Fin count) :
      term pair =
        diagonal pair + offDiagonal pair := by
    by_cases hpair : pair.1 = pair.2 <;>
      simp [diagonal, offDiagonal, hpair]
  have hoff :
      ∑ pair ∈ pairs, offDiagonal pair = 0 := by
    refine Finset.sum_involution
      (s := pairs) (f := offDiagonal)
      (fun pair _ => (pair.2, pair.1))
      ?_ ?_ ?_ ?_
    · intro pair hpair
      by_cases heq : pair.1 = pair.2
      · simp [offDiagonal, heq]
      · have hswap : pair.2 ≠ pair.1 := Ne.symm heq
        have hterm :
            term (pair.2, pair.1) = term pair := by
          unfold term
          rw [Nat.add_comm, mul_comm]
        simp only [offDiagonal, if_neg heq,
          if_neg hswap, hterm]
        exact CharTwo.add_self_eq_zero _
    · intro pair hpair hoffNonzero hfixed
      have heq : pair.1 = pair.2 := by
        exact (congrArg Prod.fst hfixed).symm
      exact hoffNonzero (by simp [offDiagonal, heq])
    · intro pair hpair
      simp [pairs]
    · intro pair hpair
      rfl
  have hcast :
      (linearConvolutionAt entry entry position :
          ZMod 2) =
        ∑ pair ∈ pairs, term pair := by
    unfold linearConvolutionAt
    simp only [Nat.cast_sum, Nat.cast_ite,
      Nat.cast_mul, Nat.cast_zero]
    change
      (∑ i : Fin count, ∑ j : Fin count,
        if position = (i : ℕ) + (j : ℕ)
        then (entry i : ZMod 2) * entry j
        else 0) =
      ∑ pair ∈
        ((Finset.univ : Finset (Fin count)) ×ˢ
          (Finset.univ : Finset (Fin count))),
        term pair
    rw [Finset.sum_product]
  rw [hcast]
  calc
    (∑ pair ∈ pairs, term pair) =
        (∑ pair ∈ pairs, diagonal pair) +
          ∑ pair ∈ pairs, offDiagonal pair := by
      simp_rw [hsplit, Finset.sum_add_distrib]
    _ = ∑ pair ∈ pairs, diagonal pair := by
      rw [hoff, add_zero]
    _ = ∑ i : Fin count,
          if position = (i : ℕ) + (i : ℕ)
          then (entry i : ZMod 2) * entry i
          else 0 := by
      change
        (∑ pair ∈
          ((Finset.univ : Finset (Fin count)) ×ˢ
            (Finset.univ : Finset (Fin count))),
          diagonal pair) = _
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_eq_single i]
      · simp [diagonal, term]
      · intro j hj hji
        have hij : i ≠ j := fun h => hji h.symm
        simp [diagonal, hij]
      · simp

/-- The selected `0/1` entries, viewed as a finite family. -/
def selectedEntry
    (width value : ℕ) {count : ℕ}
    (position : Fin count) : ℕ :=
  if value.testBit (width * position) = true
  then 1
  else 0

theorem selectedEntries_eq_ofFn
    (width count value : ℕ) :
    selectedEntries width count value =
      List.ofFn
        (fun position : Fin count =>
          selectedEntry width value position) := by
  rfl

theorem selectedEntry_le_one
    (width value : ℕ) {count : ℕ}
    (position : Fin count) :
    selectedEntry width value position ≤ 1 := by
  unfold selectedEntry
  split_ifs <;> omega

/-- Parity of a selected-entry convolution: all off-diagonal terms
cancel, so the coefficient is odd exactly when a selected diagonal
contributes. -/
theorem selectedConvolution_cast_eq_one_iff
    {width count value position : ℕ} :
    (linearConvolutionAt
        (fun i : Fin count =>
          selectedEntry width value i)
        (fun i : Fin count =>
          selectedEntry width value i)
        position : ZMod 2) = 1 ↔
      ∃ i : Fin count,
        position = (i : ℕ) + (i : ℕ) ∧
        value.testBit (width * (i : ℕ)) = true := by
  classical
  let entry : Fin count → ℕ :=
    fun i => selectedEntry width value i
  rw [linearConvolutionAt_cast_zmod_two]
  constructor
  · intro hsum
    by_contra hnone
    push Not at hnone
    have hzero :
        (∑ i : Fin count,
          if position = (i : ℕ) + (i : ℕ)
          then (entry i : ZMod 2) * entry i
          else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      by_cases hposition :
          position = (i : ℕ) + (i : ℕ)
      · have hbit :
            value.testBit (width * (i : ℕ)) ≠ true :=
          hnone i hposition
        have hentry : entry i = 0 := by
          simp [entry, selectedEntry, hbit]
        simp [hposition, hentry]
      · simp [hposition]
    rw [hzero] at hsum
    exact zero_ne_one hsum
  · rintro ⟨i, hposition, hbit⟩
    rw [Finset.sum_eq_single i]
    · simp [hposition, selectedEntry, hbit]
    · intro j hj hji
      have hpositionNe :
          position ≠ (j : ℕ) + (j : ℕ) := by
        intro hjPosition
        apply hji
        apply Fin.ext
        omega
      simp [hpositionNe]
    · simp

/-- Boolean low-bit form of
`selectedConvolution_cast_eq_one_iff`. -/
theorem selectedConvolution_testBit_zero_iff
    {width count value position : ℕ} :
    (linearConvolutionAt
        (fun i : Fin count =>
          selectedEntry width value i)
        (fun i : Fin count =>
          selectedEntry width value i)
        position).testBit 0 = true ↔
      ∃ i : Fin count,
        position = (i : ℕ) + (i : ℕ) ∧
        value.testBit (width * (i : ℕ)) = true := by
  rw [← Nat.mod_two_eq_one_iff_testBit_zero]
  change
    (linearConvolutionAt
        (fun i : Fin count =>
          selectedEntry width value i)
        (fun i : Fin count =>
          selectedEntry width value i)
        position) % 2 = 1 % 2 ↔ _
  rw [← ZMod.natCast_eq_natCast_iff']
  exact selectedConvolution_cast_eq_one_iff

/-- Under the cipher separation inequality, every convolution
coefficient of a selected `0/1` word fits in one `2^(4q)` block. -/
theorem selectedConvolution_lt_cipherBase
    {length q value position : ℕ}
    (hlq : length + 1 < q) :
    linearConvolutionAt
        (fun i : Fin (slot length) =>
          selectedEntry (4 * q) value i)
        (fun i : Fin (slot length) =>
          selectedEntry (4 * q) value i)
        position <
      cipherBase q := by
  have hcoeff :=
    linearConvolutionAt_le_square
      (left := fun i : Fin (slot length) =>
        selectedEntry (4 * q) value i)
      (right := fun i : Fin (slot length) =>
        selectedEntry (4 * q) value i)
      (selectedEntry_le_one _ _)
      (selectedEntry_le_one _ _)
      position
  have hslot :
      slot length < 2 ^ q := by
    exact Nat.pow_lt_pow_right
      (by norm_num) hlq
  have hsquare :
      slot length * slot length <
        2 ^ q * 2 ^ q :=
    Nat.mul_lt_mul_of_lt_of_lt hslot hslot
  have hpow :
      2 ^ q * 2 ^ q ≤ 2 ^ (4 * q) := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  exact hcoeff.trans_lt (hsquare.trans_le
    (by simpa [cipherBase] using hpow))

/-- The low bit of the radix digit at `position` is the bit of the
whole code at the beginning of that block. -/
theorem testBit_blockStart_eq_digit_testBit_zero
    {width : ℕ} (hwidth : 0 < width)
    (code position : ℕ) :
    code.testBit (width * position) =
      (RadixSequence.digit
        (2 ^ width) code position).testBit 0 := by
  rw [RadixSequence.digit]
  rw [show
      (2 ^ width) ^ position =
        2 ^ (width * position) by
      rw [← pow_mul]]
  rw [Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow]
  simp [hwidth]

/-- Appending one sparse entry gives the expected endpoint recurrence.
This is the identity later used to recover the sparse exponent chain
from an algebraic certificate. -/
theorem shifted_add_endpoint
    (length q : ℕ) :
    cipherBase q ^ 2 + shiftedSparseOnes length q =
      sparseOnes length q + cipherBase q ^ slot length := by
  rw [sparseOnes_eq_sum, shiftedSparseOnes_eq_sum]
  rw [Fin.sum_univ_eq_sum_range
      (fun i : ℕ =>
        cipherBase q ^ slot (i + 1))]
  rw [Fin.sum_univ_eq_sum_range
      (fun i : ℕ =>
        cipherBase q ^ slot i)]
  have hshift :
      cipherBase q ^ 2 +
          ∑ i ∈ Finset.range length,
            cipherBase q ^ slot (i + 1) =
        ∑ i ∈ Finset.range (length + 1),
          cipherBase q ^ slot i := by
    rw [Finset.sum_range_succ']
    simp [slot, Nat.add_comm]
  have hend :
      (∑ i ∈ Finset.range (length + 1),
          cipherBase q ^ slot i) =
        (∑ i ∈ Finset.range length,
          cipherBase q ^ slot i) +
          cipherBase q ^ slot length := by
    rw [Finset.sum_range_succ]
  exact hshift.trans hend

/-- Every term of the shifted sparse word is divisible by the fourth
power of the radix. -/
theorem fourth_power_dvd_shiftedSparseOnes
    (length q : ℕ) :
    cipherBase q ^ 4 ∣ shiftedSparseOnes length q := by
  rw [shiftedSparseOnes_eq_sum]
  apply Finset.dvd_sum
  intro i hi
  exact pow_dvd_pow (cipherBase q)
    (by
      simpa [slot] using
        (Nat.pow_le_pow_right (by norm_num : 0 < 2)
          (show 2 ≤ (i : ℕ) + 2 by omega) :
          2 ^ 2 ≤ 2 ^ ((i : ℕ) + 2)))

/-! ## The square and its two binary masks -/

/-- If a radix position is contributed by a fixed off-diagonal pair,
then the all-ones convolution coefficient there is exactly two: the
pair and its transpose.  Binary uniqueness of two powers of two rules
out every other contribution. -/
theorem convolutionAt_ones_eq_two
    {length position : ℕ} {i j : Fin length}
    (hposition : position = slot i + slot j)
    (hdiagonal :
      ¬ ∃ k : Fin length, position = slot (k + 1)) :
    SparseRadixCipher.convolutionAt
        (fun _ : Fin length => 1)
        (fun _ : Fin length => 1) position = 2 := by
  have hij : i ≠ j := by
    intro hij
    subst j
    exact hdiagonal ⟨i, hposition.trans (slot_add_self i)⟩
  have hiff (k l : Fin length) :
      position = slot k + slot l ↔
        (k = i ∧ l = j) ∨ (k = j ∧ l = i) := by
    constructor
    · intro hkl
      have hpairs :=
        (slot_add_slot_eq_slot_add_slot_iff
          (i : ℕ) (j : ℕ) (k : ℕ) (l : ℕ)).mp
          (hposition.symm.trans hkl)
      rcases hpairs with hpairs | hpairs
      · left
        exact
          ⟨Fin.ext hpairs.1.symm,
            Fin.ext hpairs.2.symm⟩
      · right
        exact
          ⟨Fin.ext hpairs.2.symm,
            Fin.ext hpairs.1.symm⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact hposition
      · simpa [Nat.add_comm] using hposition
  unfold SparseRadixCipher.convolutionAt
  have hinner (k : Fin length) :
      (∑ l : Fin length,
          if position = slot k + slot l
          then 1 * 1 else 0) =
        if k = i then 1 else if k = j then 1 else 0 := by
    by_cases hki : k = i
    · subst k
      simp [hiff, hij]
    · by_cases hkj : k = j
      · subst k
        simp [hiff, hki]
      · simp [hiff, hki, hkj]
  simp_rw [hinner]
  have hsplit (k : Fin length) :
      (if k = i then 1 else if k = j then 1 else 0) =
        (if k = i then 1 else 0) +
          (if k = j then 1 else 0) := by
    by_cases hki : k = i <;>
      by_cases hkj : k = j <;>
      simp_all
  simp_rw [hsplit, Finset.sum_add_distrib]
  simp

/-- A position to which no pair contributes has zero convolution
coefficient. -/
theorem convolutionAt_ones_eq_zero
    {length position : ℕ}
    (hposition :
      ¬ ∃ i j : Fin length,
        position = slot i + slot j) :
    SparseRadixCipher.convolutionAt
        (fun _ : Fin length => 1)
        (fun _ : Fin length => 1) position = 0 := by
  unfold SparseRadixCipher.convolutionAt
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  have hne : position ≠ slot i + slot j := by
    intro h
    exact hposition ⟨i, j, h⟩
  simp [hne]

/-- The low binary bit of every all-ones convolution block is one
exactly at a diagonal sparse position. -/
theorem convolutionAt_ones_land_one
    {length position : ℕ} :
    SparseRadixCipher.convolutionAt
        (fun _ : Fin length => 1)
        (fun _ : Fin length => 1) position &&& 1 =
      SparseRadixCipher.diagonalCoefficientAt
        (fun _ : Fin length => 1) position := by
  classical
  by_cases hdiagonal :
      ∃ i : Fin length, position = slot (i + 1)
  · obtain ⟨i, rfl⟩ := hdiagonal
    rw [SparseRadixCipher.convolutionAt_diagonal,
      SparseRadixCipher.diagonalCoefficientAt_slot]
    decide
  · rw [SparseRadixCipher.diagonalCoefficientAt_eq_zero_of_not_slot
      _ hdiagonal]
    by_cases hpair :
        ∃ i j : Fin length, position = slot i + slot j
    · obtain ⟨i, j, hij⟩ := hpair
      rw [convolutionAt_ones_eq_two hij hdiagonal]
      decide
    · rw [convolutionAt_ones_eq_zero hpair]
      decide

/-- Pointwise low-bit masking of the complete convolution word. -/
theorem zipWith_convolution_ones :
    ∀ length : ℕ,
      List.zipWith (· &&& ·)
          (SparseRadixCipher.convolutionEntries
            (fun _ : Fin length => 1)
            (fun _ : Fin length => 1))
          (List.replicate
            (SparseRadixCipher.wordLength length) 1) =
        SparseRadixCipher.diagonalEntries
          (fun _ : Fin length => 1) := by
  intro length
  apply List.ext_getElem
  · simp [SparseRadixCipher.convolutionEntries,
      SparseRadixCipher.diagonalEntries]
  · intro index hleft hright
    simp only [List.getElem_zipWith,
      SparseRadixCipher.convolutionEntries,
      SparseRadixCipher.diagonalEntries,
      List.getElem_ofFn, List.getElem_replicate]
    exact convolutionAt_ones_land_one

/-- A dense all-ones number is the radix encoding of a replicated
all-ones list. -/
theorem encode_replicate_one
    (base count : ℕ) :
    RadixSequence.encode base (List.replicate count 1) =
      denseOnes base count := by
  rw [RadixSequence.encode, Nat.ofDigits_eq_sum_mapIdx]
  simp only [List.mapIdx_eq_ofFn]
  rw [denseOnes]
  simp only [List.length_replicate, List.get_eq_getElem,
    Fin.val_cast, List.getElem_replicate, one_mul]
  rw [List.sum_ofFn,
    Fin.sum_univ_eq_sum_range
      (fun position : ℕ => base ^ position)]

/-- Under the standard cipher separation hypothesis, every coefficient
of the square fits in a radix block of width `4q`. -/
theorem convolutionAt_ones_lt_cipherBase
    {length q : ℕ} (hlq : length + 1 < q) :
    ∀ position,
      SparseRadixCipher.convolutionAt
          (fun _ : Fin length => 1)
          (fun _ : Fin length => 1) position <
        cipherBase q := by
  intro position
  have hq : 0 < q := by omega
  have hone : ∀ _ : Fin length, 1 < 2 ^ q := by
    intro i
    exact Nat.one_lt_two_pow (by omega)
  have hsafe :=
    SparseRadixCipher.convolutionAt_lt_safeWidth
      (entryWidth := q)
      (left := fun _ : Fin length => 1)
      (right := fun _ : Fin length => 1)
      hone hone position
  have hwidth :
      SparseRadixCipher.safeWidth q length ≤ 4 * q := by
    simp [SparseRadixCipher.safeWidth]
    omega
  exact hsafe.trans_le
    (by
      simpa [cipherBase] using
        (Nat.pow_le_pow_right (by norm_num : 0 < 2) hwidth :
          2 ^ SparseRadixCipher.safeWidth q length ≤
            2 ^ (4 * q)))

/-- The dense low-bit mask extracts precisely the diagonal of the square
of the sparse all-ones word. -/
theorem square_land_denseOnes
    {length q : ℕ} (hlq : length + 1 < q) :
    (sparseOnes length q * sparseOnes length q) &&&
        denseOnes (cipherBase q)
          (SparseRadixCipher.wordLength length) =
      shiftedSparseOnes length q := by
  rw [sparseOnes,
    ← SparseRadixCipher.encode_convolutionEntries]
  rw [← encode_replicate_one]
  simp only [cipherBase]
  rw [SparseRadixCipher.encode_zipWith_land]
  · rw [zipWith_convolution_ones]
    rfl
  · simp [SparseRadixCipher.convolutionEntries]
  · intro value hvalue
    obtain ⟨position, rfl⟩ := List.mem_ofFn.mp hvalue
    simpa [cipherBase] using
      convolutionAt_ones_lt_cipherBase hlq position
  · intro value hvalue
    simp only [List.mem_replicate] at hvalue
    rcases hvalue with ⟨hword, rfl⟩
    have hq : 0 < q := by omega
    simpa [cipherBase] using
      (Nat.one_lt_two_pow (by omega) : 1 < 2 ^ (4 * q))

/-- The word of off-diagonal coefficients in the square.  Each entry is
obtained by selecting the second-lowest bit of its convolution block. -/
def offDiagonalEntries (length : ℕ) : List ℕ :=
  List.ofFn fun position : Fin (SparseRadixCipher.wordLength length) =>
    SparseRadixCipher.convolutionAt
        (fun _ : Fin length => 1)
        (fun _ : Fin length => 1) position &&& 2

/-- Numeric code of the off-diagonal part of the all-ones square. -/
def offDiagonalCode (length q : ℕ) : ℕ :=
  RadixSequence.encode (cipherBase q)
    (offDiagonalEntries length)

theorem offDiagonalEntries_length (length : ℕ) :
    (offDiagonalEntries length).length =
      SparseRadixCipher.wordLength length := by
  simp [offDiagonalEntries]

/-- Every convolution coefficient splits into its diagonal low bit and
its off-diagonal second bit. -/
theorem convolutionAt_ones_decomposition
    {length position : ℕ} :
    SparseRadixCipher.convolutionAt
        (fun _ : Fin length => 1)
        (fun _ : Fin length => 1) position =
      SparseRadixCipher.diagonalCoefficientAt
          (fun _ : Fin length => 1) position +
        (SparseRadixCipher.convolutionAt
            (fun _ : Fin length => 1)
            (fun _ : Fin length => 1) position &&& 2) := by
  classical
  by_cases hdiagonal :
      ∃ i : Fin length, position = slot (i + 1)
  · obtain ⟨i, rfl⟩ := hdiagonal
    rw [SparseRadixCipher.convolutionAt_diagonal,
      SparseRadixCipher.diagonalCoefficientAt_slot]
    decide
  · rw [SparseRadixCipher.diagonalCoefficientAt_eq_zero_of_not_slot
      _ hdiagonal]
    by_cases hpair :
        ∃ i j : Fin length, position = slot i + slot j
    · obtain ⟨i, j, hij⟩ := hpair
      rw [convolutionAt_ones_eq_two hij hdiagonal]
      decide
    · rw [convolutionAt_ones_eq_zero hpair]
      decide

/-- The complete convolution list is the pointwise sum of its diagonal
and off-diagonal lists. -/
theorem convolutionEntries_ones_eq_zipWith :
    ∀ length : ℕ,
      SparseRadixCipher.convolutionEntries
          (fun _ : Fin length => 1)
          (fun _ : Fin length => 1) =
        List.zipWith (· + ·)
          (SparseRadixCipher.diagonalEntries
            (fun _ : Fin length => 1))
          (offDiagonalEntries length) := by
  intro length
  apply List.ext_getElem
  · simp [SparseRadixCipher.convolutionEntries,
      SparseRadixCipher.diagonalEntries,
      offDiagonalEntries]
  · intro index hleft hright
    simp only [List.getElem_zipWith,
      SparseRadixCipher.convolutionEntries,
      SparseRadixCipher.diagonalEntries,
      offDiagonalEntries, List.getElem_ofFn]
    exact convolutionAt_ones_decomposition

/-- Encoding a constant radix word multiplies the dense all-ones word
by that constant. -/
theorem encode_replicate_constant
    (base coefficient count : ℕ) :
    RadixSequence.encode base
        (List.replicate count coefficient) =
      coefficient * denseOnes base count := by
  rw [RadixSequence.encode, Nat.ofDigits_eq_sum_mapIdx]
  simp only [List.mapIdx_eq_ofFn]
  rw [denseOnes, Finset.mul_sum]
  simp only [List.length_replicate, List.get_eq_getElem,
    Fin.val_cast, List.getElem_replicate]
  rw [List.sum_ofFn,
    Fin.sum_univ_eq_sum_range
      (fun position : ℕ =>
        coefficient * base ^ position)]

/-- Pointwise masking by the coefficient `2` produces exactly the
off-diagonal list. -/
theorem zipWith_convolution_twos :
    ∀ length : ℕ,
      List.zipWith (· &&& ·)
          (SparseRadixCipher.convolutionEntries
            (fun _ : Fin length => 1)
            (fun _ : Fin length => 1))
          (List.replicate
            (SparseRadixCipher.wordLength length) 2) =
        offDiagonalEntries length := by
  intro length
  apply List.ext_getElem
  · simp [SparseRadixCipher.convolutionEntries,
      offDiagonalEntries]
  · intro index hleft hright
    simp only [List.getElem_zipWith,
      SparseRadixCipher.convolutionEntries,
      offDiagonalEntries, List.getElem_ofFn,
      List.getElem_replicate]

/-- The shifted dense mask extracts precisely the off-diagonal part of
the square. -/
theorem square_land_two_mul_denseOnes
    {length q : ℕ} (hlq : length + 1 < q) :
    (sparseOnes length q * sparseOnes length q) &&&
        (2 * denseOnes (cipherBase q)
          (SparseRadixCipher.wordLength length)) =
      offDiagonalCode length q := by
  rw [sparseOnes,
    ← SparseRadixCipher.encode_convolutionEntries]
  rw [← encode_replicate_constant]
  simp only [cipherBase]
  rw [SparseRadixCipher.encode_zipWith_land]
  · rw [zipWith_convolution_twos]
    rfl
  · simp [SparseRadixCipher.convolutionEntries]
  · intro value hvalue
    obtain ⟨position, rfl⟩ := List.mem_ofFn.mp hvalue
    simpa [cipherBase] using
      convolutionAt_ones_lt_cipherBase hlq position
  · intro value hvalue
    simp only [List.mem_replicate] at hvalue
    rcases hvalue with ⟨hword, rfl⟩
    have : 2 < 2 ^ (4 * q) := by
      have hq : 1 < q := by omega
      exact (by
        calc
          2 < 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (4 * q) :=
            Nat.pow_le_pow_right (by norm_num) (by omega))
    exact this

/-- The diagonal and off-diagonal masks partition the square. -/
theorem square_eq_shifted_add_offDiagonal
    (length q : ℕ) :
    sparseOnes length q * sparseOnes length q =
      shiftedSparseOnes length q +
        offDiagonalCode length q := by
  calc
    sparseOnes length q * sparseOnes length q =
        RadixSequence.encode (cipherBase q)
          (SparseRadixCipher.convolutionEntries
            (fun _ : Fin length => 1)
            (fun _ : Fin length => 1)) := by
      rw [sparseOnes,
        SparseRadixCipher.encode_convolutionEntries]
    _ = RadixSequence.encode (cipherBase q)
          (List.zipWith (· + ·)
            (SparseRadixCipher.diagonalEntries
              (fun _ : Fin length => 1))
            (offDiagonalEntries length)) := by
      rw [← convolutionEntries_ones_eq_zipWith]
    _ = RadixSequence.encode (cipherBase q)
          (SparseRadixCipher.diagonalEntries
            (fun _ : Fin length => 1)) +
        RadixSequence.encode (cipherBase q)
          (offDiagonalEntries length) := by
      apply SparseRadixCipher.encode_zipWith_add
      simp [SparseRadixCipher.diagonalEntries,
        offDiagonalEntries]
    _ = shiftedSparseOnes length q +
        offDiagonalCode length q := by
      rfl

/-! ## The finite algebraic certificate -/

/-- The quantifier-free/existential certificate used to recognize the
sparse all-ones words.

The first disjunct isolates the empty word.  In the nonempty case:

* `w` is forced by a geometric-series equation to be the dense mask;
* `u₁` and `u₂` are the low-bit and second-bit masks of `u²`;
* the endpoint recurrence aligns the sparse supports;
* divisibility by `r₀^4` fixes the first shifted exponent.

This is the exact arithmetic shape used in the traditional
Matiyasevich cipher proof. -/
def Certificate (length q u u₁ : ℕ) : Prop :=
  (length = 0 ∧ u = 0 ∧ u₁ = 0 ∧ 2 ≤ q) ∨
    (0 < length ∧ length + 1 < q ∧
      ∃ u₂ w r₀ r₁ p₁ p₂ : ℕ,
        r₀ = cipherBase q ∧
        r₁ + 1 = r₀ ∧
        p₁ = slot length ∧
        p₂ = r₀ ^ p₁ ∧
        1 + r₁ * w = r₀ * p₂ ∧
        u * u = u₁ + u₂ ∧
        u₁ = (u * u) &&& w ∧
        u₂ = (u * u) &&& (2 * w) ∧
        r₀ * r₀ + u₁ = u + p₂ ∧
        r₀ ^ 4 ∣ u₁)

/-- The nonempty certificate with its six witnesses exposed as a single
finite vector.  External coordinates are `(length,q,u,u₁)` and witness
coordinates are `(u₂,w,r₀,r₁,p₁,p₂)`.  This form is designed for one
application of `Dioph.ex_dioph`. -/
def CertificateCore
    (v : (Fin 4 ⊕ Fin 6) → ℕ) : Prop :=
  0 < v (Sum.inl 0) ∧
  v (Sum.inl 0) + 1 < v (Sum.inl 1) ∧
  v (Sum.inr 2) =
    cipherBase (v (Sum.inl 1)) ∧
  v (Sum.inr 3) + 1 = v (Sum.inr 2) ∧
  v (Sum.inr 4) = slot (v (Sum.inl 0)) ∧
  v (Sum.inr 5) =
    v (Sum.inr 2) ^ v (Sum.inr 4) ∧
  1 + v (Sum.inr 3) * v (Sum.inr 1) =
    v (Sum.inr 2) * v (Sum.inr 5) ∧
  v (Sum.inl 2) * v (Sum.inl 2) =
    v (Sum.inl 3) + v (Sum.inr 0) ∧
  v (Sum.inl 3) =
    (v (Sum.inl 2) * v (Sum.inl 2)) &&&
      v (Sum.inr 1) ∧
  v (Sum.inr 0) =
    (v (Sum.inl 2) * v (Sum.inl 2)) &&&
      (2 * v (Sum.inr 1)) ∧
  v (Sum.inr 2) * v (Sum.inr 2) +
      v (Sum.inl 3) =
    v (Sum.inl 2) + v (Sum.inr 5) ∧
  v (Sum.inr 2) ^ 4 ∣ v (Sum.inl 3)

/-- Bundling and unbundling the six witnesses does not change the
nonempty certificate. -/
theorem exists_certificateCore_iff
    (v : Fin 4 → ℕ) :
    (∃ witness : Fin 6 → ℕ,
      CertificateCore (Sum.elim v witness)) ↔
      (0 < v 0 ∧ v 0 + 1 < v 1 ∧
        ∃ u₂ w r₀ r₁ p₁ p₂ : ℕ,
          r₀ = cipherBase (v 1) ∧
          r₁ + 1 = r₀ ∧
          p₁ = slot (v 0) ∧
          p₂ = r₀ ^ p₁ ∧
          1 + r₁ * w = r₀ * p₂ ∧
          v 2 * v 2 = v 3 + u₂ ∧
          v 3 = (v 2 * v 2) &&& w ∧
          u₂ = (v 2 * v 2) &&& (2 * w) ∧
          r₀ * r₀ + v 3 = v 2 + p₂ ∧
          r₀ ^ 4 ∣ v 3) := by
  constructor
  · rintro ⟨witness, h⟩
    refine
      ⟨h.1, h.2.1,
        witness 0, witness 1, witness 2,
        witness 3, witness 4, witness 5, ?_⟩
    exact h.2.2
  · rintro
      ⟨hlength, hlq, u₂, w, r₀, r₁, p₁, p₂,
        hr₀, hr₁, hp₁, hp₂, hgeom, hsquare,
        hlow, hhigh, hshift, hdvd⟩
    refine ⟨![u₂, w, r₀, r₁, p₁, p₂], ?_⟩
    exact
      ⟨hlength, hlq, hr₀, hr₁, hp₁, hp₂,
        hgeom, hsquare, hlow, hhigh, hshift, hdvd⟩

/-- The exposed nonempty certificate is Diophantine.  This theorem is
pure closure bookkeeping: exponentiation is supplied by
`Dioph.pow_dioph`, and the two bit masks use the independently proved
`DiophantineBitwise.land_diophFn`. -/
theorem certificateCore_dioph :
    Dioph {v : (Fin 4 ⊕ Fin 6) → ℕ |
      CertificateCore v} := by
  let lengthFn : ((Fin 4 ⊕ Fin 6) → ℕ) → ℕ :=
    fun v => v (Sum.inl 0)
  let qFn : ((Fin 4 ⊕ Fin 6) → ℕ) → ℕ :=
    fun v => v (Sum.inl 1)
  let uFn : ((Fin 4 ⊕ Fin 6) → ℕ) → ℕ :=
    fun v => v (Sum.inl 2)
  let u₁Fn : ((Fin 4 ⊕ Fin 6) → ℕ) → ℕ :=
    fun v => v (Sum.inl 3)
  let u₂Fn : ((Fin 4 ⊕ Fin 6) → ℕ) → ℕ :=
    fun v => v (Sum.inr 0)
  let wFn : ((Fin 4 ⊕ Fin 6) → ℕ) → ℕ :=
    fun v => v (Sum.inr 1)
  let r₀Fn : ((Fin 4 ⊕ Fin 6) → ℕ) → ℕ :=
    fun v => v (Sum.inr 2)
  let r₁Fn : ((Fin 4 ⊕ Fin 6) → ℕ) → ℕ :=
    fun v => v (Sum.inr 3)
  let p₁Fn : ((Fin 4 ⊕ Fin 6) → ℕ) → ℕ :=
    fun v => v (Sum.inr 4)
  let p₂Fn : ((Fin 4 ⊕ Fin 6) → ℕ) → ℕ :=
    fun v => v (Sum.inr 5)
  have hlength : Dioph.DiophFn lengthFn :=
    Dioph.proj_dioph (Sum.inl 0)
  have hq : Dioph.DiophFn qFn :=
    Dioph.proj_dioph (Sum.inl 1)
  have hu : Dioph.DiophFn uFn :=
    Dioph.proj_dioph (Sum.inl 2)
  have hu₁ : Dioph.DiophFn u₁Fn :=
    Dioph.proj_dioph (Sum.inl 3)
  have hu₂ : Dioph.DiophFn u₂Fn :=
    Dioph.proj_dioph (Sum.inr 0)
  have hw : Dioph.DiophFn wFn :=
    Dioph.proj_dioph (Sum.inr 1)
  have hr₀ : Dioph.DiophFn r₀Fn :=
    Dioph.proj_dioph (Sum.inr 2)
  have hr₁ : Dioph.DiophFn r₁Fn :=
    Dioph.proj_dioph (Sum.inr 3)
  have hp₁ : Dioph.DiophFn p₁Fn :=
    Dioph.proj_dioph (Sum.inr 4)
  have hp₂ : Dioph.DiophFn p₂Fn :=
    Dioph.proj_dioph (Sum.inr 5)
  have hzero :
      Dioph.DiophFn
        (fun _ : (Fin 4 ⊕ Fin 6) → ℕ => 0) :=
    Dioph.const_dioph 0
  have hone :
      Dioph.DiophFn
        (fun _ : (Fin 4 ⊕ Fin 6) → ℕ => 1) :=
    Dioph.const_dioph 1
  have htwo :
      Dioph.DiophFn
        (fun _ : (Fin 4 ⊕ Fin 6) → ℕ => 2) :=
    Dioph.const_dioph 2
  have hfour :
      Dioph.DiophFn
        (fun _ : (Fin 4 ⊕ Fin 6) → ℕ => 4) :=
    Dioph.const_dioph 4
  let lengthPlusOne := fun v => lengthFn v + 1
  have hlengthPlusOne : Dioph.DiophFn lengthPlusOne :=
    Dioph.add_dioph hlength hone
  let fourQ := fun v => 4 * qFn v
  have hfourQ : Dioph.DiophFn fourQ :=
    Dioph.mul_dioph hfour hq
  let baseFn := fun v => 2 ^ fourQ v
  have hbase : Dioph.DiophFn baseFn :=
    Dioph.pow_dioph htwo hfourQ
  let slotFn := fun v => 2 ^ lengthPlusOne v
  have hslot : Dioph.DiophFn slotFn :=
    Dioph.pow_dioph htwo hlengthPlusOne
  let r₁PlusOne := fun v => r₁Fn v + 1
  have hr₁PlusOne : Dioph.DiophFn r₁PlusOne :=
    Dioph.add_dioph hr₁ hone
  let r₀PowP₁ := fun v => r₀Fn v ^ p₁Fn v
  have hr₀PowP₁ : Dioph.DiophFn r₀PowP₁ :=
    Dioph.pow_dioph hr₀ hp₁
  let r₁MulW := fun v => r₁Fn v * wFn v
  have hr₁MulW : Dioph.DiophFn r₁MulW :=
    Dioph.mul_dioph hr₁ hw
  let geomLeft := fun v => 1 + r₁MulW v
  have hgeomLeft : Dioph.DiophFn geomLeft :=
    Dioph.add_dioph hone hr₁MulW
  let geomRight := fun v => r₀Fn v * p₂Fn v
  have hgeomRight : Dioph.DiophFn geomRight :=
    Dioph.mul_dioph hr₀ hp₂
  let uSquare := fun v => uFn v * uFn v
  have huSquare : Dioph.DiophFn uSquare :=
    Dioph.mul_dioph hu hu
  let u₁PlusU₂ := fun v => u₁Fn v + u₂Fn v
  have hu₁PlusU₂ : Dioph.DiophFn u₁PlusU₂ :=
    Dioph.add_dioph hu₁ hu₂
  let lowMask := fun v => uSquare v &&& wFn v
  have hlowMask : Dioph.DiophFn lowMask :=
    DiophantineBitwise.land_diophFn huSquare hw
  let twoW := fun v => 2 * wFn v
  have htwoW : Dioph.DiophFn twoW :=
    Dioph.mul_dioph htwo hw
  let highMask := fun v => uSquare v &&& twoW v
  have hhighMask : Dioph.DiophFn highMask :=
    DiophantineBitwise.land_diophFn huSquare htwoW
  let r₀Square := fun v => r₀Fn v * r₀Fn v
  have hr₀Square : Dioph.DiophFn r₀Square :=
    Dioph.mul_dioph hr₀ hr₀
  let shiftLeft := fun v => r₀Square v + u₁Fn v
  have hshiftLeft : Dioph.DiophFn shiftLeft :=
    Dioph.add_dioph hr₀Square hu₁
  let shiftRight := fun v => uFn v + p₂Fn v
  have hshiftRight : Dioph.DiophFn shiftRight :=
    Dioph.add_dioph hu hp₂
  let r₀Fourth := fun v => r₀Fn v ^ 4
  have hr₀Fourth : Dioph.DiophFn r₀Fourth :=
    Dioph.pow_dioph hr₀ hfour
  have hPos : Dioph {v | 0 < lengthFn v} :=
    Dioph.lt_dioph hzero hlength
  have hLengthBound :
      Dioph {v | lengthPlusOne v < qFn v} :=
    Dioph.lt_dioph hlengthPlusOne hq
  have hBaseEq : Dioph {v | r₀Fn v = baseFn v} :=
    Dioph.eq_dioph hr₀ hbase
  have hPredEq : Dioph {v | r₁PlusOne v = r₀Fn v} :=
    Dioph.eq_dioph hr₁PlusOne hr₀
  have hSlotEq : Dioph {v | p₁Fn v = slotFn v} :=
    Dioph.eq_dioph hp₁ hslot
  have hPowerEq : Dioph {v | p₂Fn v = r₀PowP₁ v} :=
    Dioph.eq_dioph hp₂ hr₀PowP₁
  have hGeom : Dioph {v | geomLeft v = geomRight v} :=
    Dioph.eq_dioph hgeomLeft hgeomRight
  have hSquare : Dioph {v | uSquare v = u₁PlusU₂ v} :=
    Dioph.eq_dioph huSquare hu₁PlusU₂
  have hLow : Dioph {v | u₁Fn v = lowMask v} :=
    Dioph.eq_dioph hu₁ hlowMask
  have hHigh : Dioph {v | u₂Fn v = highMask v} :=
    Dioph.eq_dioph hu₂ hhighMask
  have hShift : Dioph {v | shiftLeft v = shiftRight v} :=
    Dioph.eq_dioph hshiftLeft hshiftRight
  have hDvd : Dioph {v | r₀Fourth v ∣ u₁Fn v} :=
    Dioph.dvd_dioph hr₀Fourth hu₁
  have hAll :=
    hPos.inter
      (hLengthBound.inter
        (hBaseEq.inter
          (hPredEq.inter
            (hSlotEq.inter
              (hPowerEq.inter
                (hGeom.inter
                  (hSquare.inter
                    (hLow.inter
                      (hHigh.inter
                        (hShift.inter hDvd))))))))))
  simpa only [CertificateCore, Set.mem_inter_iff,
    Set.mem_setOf_eq, lengthFn, qFn, uFn, u₁Fn, u₂Fn,
    wFn, r₀Fn, r₁Fn, p₁Fn, p₂Fn, lengthPlusOne,
    fourQ, baseFn, cipherBase, slotFn, slot,
    r₁PlusOne, r₀PowP₁, r₁MulW, geomLeft, geomRight,
    uSquare, u₁PlusU₂, lowMask, twoW, highMask,
    r₀Square, shiftLeft, shiftRight, r₀Fourth] using hAll

/-- The complete certificate, including the empty-word branch, is a
Diophantine relation in its four visible parameters. -/
theorem certificate_dioph :
    Dioph {v : Fin 4 → ℕ |
      Certificate (v 0) (v 1) (v 2) (v 3)} := by
  let lengthFn : (Fin 4 → ℕ) → ℕ := fun v => v 0
  let qFn : (Fin 4 → ℕ) → ℕ := fun v => v 1
  let uFn : (Fin 4 → ℕ) → ℕ := fun v => v 2
  let u₁Fn : (Fin 4 → ℕ) → ℕ := fun v => v 3
  have hlength : Dioph.DiophFn lengthFn :=
    Dioph.proj_dioph 0
  have hq : Dioph.DiophFn qFn :=
    Dioph.proj_dioph 1
  have hu : Dioph.DiophFn uFn :=
    Dioph.proj_dioph 2
  have hu₁ : Dioph.DiophFn u₁Fn :=
    Dioph.proj_dioph 3
  have hzero :
      Dioph.DiophFn (fun _ : Fin 4 → ℕ => 0) :=
    Dioph.const_dioph 0
  have htwo :
      Dioph.DiophFn (fun _ : Fin 4 → ℕ => 2) :=
    Dioph.const_dioph 2
  have hEmpty :
      Dioph {v : Fin 4 → ℕ |
        lengthFn v = 0 ∧ uFn v = 0 ∧
          u₁Fn v = 0 ∧ 2 ≤ qFn v} :=
    (Dioph.eq_dioph hlength hzero).inter
      ((Dioph.eq_dioph hu hzero).inter
        ((Dioph.eq_dioph hu₁ hzero).inter
          (Dioph.le_dioph htwo hq)))
  have hNonempty :
      Dioph {v : Fin 4 → ℕ |
        ∃ witness : Fin 6 → ℕ,
          CertificateCore (Sum.elim v witness)} := by
    simpa only using
      (Dioph.ex_dioph certificateCore_dioph)
  refine
    Dioph.ext (Dioph.union hEmpty hNonempty) fun v => ?_
  simp only [Set.mem_union, Set.mem_setOf_eq,
    lengthFn, qFn, uFn, u₁Fn]
  rw [exists_certificateCore_iff]
  rfl

theorem wordLength_eq_slot_add_one (length : ℕ) :
    SparseRadixCipher.wordLength length =
      slot length + 1 := by
  rfl

/-- Every intended pair of sparse words supplies the finite algebraic
certificate.  This is the constructive (forward) half of
`seqs_of_ones_dio` in Matiyasevich's cipher argument. -/
theorem SeqsOfOnes.toCertificate
    {length q u u₁ : ℕ}
    (hseq : SeqsOfOnes length q u u₁) :
    Certificate length q u u₁ := by
  rcases hseq with ⟨hlq, rfl, rfl⟩
  by_cases hzero : length = 0
  · left
    subst length
    refine
      ⟨rfl, sparseOnes_zero q,
        shiftedSparseOnes_zero q, by omega⟩
  · right
    have hlength : 0 < length := Nat.pos_of_ne_zero hzero
    let w :=
      denseOnes (cipherBase q)
        (SparseRadixCipher.wordLength length)
    let u₂ := offDiagonalCode length q
    refine ⟨hlength, hlq,
      u₂, w, cipherBase q, cipherBase q - 1,
      slot length, cipherBase q ^ slot length,
      rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hbase : 0 < cipherBase q := cipherBase_pos q
      omega
    · have hgeom :=
        denseOnes_equation
          (base := cipherBase q)
          (count := SparseRadixCipher.wordLength length)
          (by
            have := cipherBase_ge_two (q := q) (by omega)
            omega)
      change
        1 + (cipherBase q - 1) * w =
          cipherBase q * cipherBase q ^ slot length
      rw [hgeom]
      rw [wordLength_eq_slot_add_one, pow_succ,
        Nat.mul_comm]
    · exact square_eq_shifted_add_offDiagonal length q
    · change shiftedSparseOnes length q =
        (sparseOnes length q * sparseOnes length q) &&& w
      exact (square_land_denseOnes hlq).symm
    · change offDiagonalCode length q =
        (sparseOnes length q * sparseOnes length q) &&&
          (2 * w)
      exact (square_land_two_mul_denseOnes hlq).symm
    · simpa [pow_two] using shifted_add_endpoint length q
    · exact fourth_power_dvd_shiftedSparseOnes length q

/-- In a nonempty certificate all six auxiliary parameters except the
off-diagonal part are forced.  In particular the geometric equation
really does identify `w` with the dense all-ones mask; it is not an
additional semantic assumption. -/
theorem Certificate.nonempty_normalForm
    {length q u u₁ : ℕ}
    (hcertificate : Certificate length q u u₁)
    (hlength : 0 < length) :
    length + 1 < q ∧
      ∃ u₂ : ℕ,
        u * u = u₁ + u₂ ∧
        u₁ =
          (u * u) &&&
            denseOnes (cipherBase q)
              (SparseRadixCipher.wordLength length) ∧
        u₂ =
          (u * u) &&&
            (2 * denseOnes (cipherBase q)
              (SparseRadixCipher.wordLength length)) ∧
        cipherBase q * cipherBase q + u₁ =
          u + cipherBase q ^ slot length ∧
        cipherBase q ^ 4 ∣ u₁ := by
  rcases hcertificate with hempty | hnonempty
  · omega
  · rcases hnonempty with
      ⟨hlength', hlq, u₂, w, r₀, r₁, p₁, p₂,
        hr₀, hr₁, hp₁, hp₂, hgeom, hsquare,
        hlow, hhigh, hshift, hdvd⟩
    have hq : 0 < q := by omega
    have hr₁Value : r₁ = cipherBase q - 1 := by
      have hbase := cipherBase_pos q
      omega
    have hgeom' :
        1 + (cipherBase q - 1) * w =
          cipherBase q ^
            SparseRadixCipher.wordLength length := by
      calc
        1 + (cipherBase q - 1) * w =
            1 + r₁ * w := by rw [hr₁Value]
        _ = r₀ * p₂ := hgeom
        _ = cipherBase q *
              cipherBase q ^ slot length := by
            rw [hr₀, hp₂, hp₁, hr₀]
        _ = cipherBase q ^
              SparseRadixCipher.wordLength length := by
            rw [wordLength_eq_slot_add_one, pow_succ,
              Nat.mul_comm]
    have hw :
        w =
          denseOnes (cipherBase q)
            (SparseRadixCipher.wordLength length) :=
      (denseOnes_iff_equation
        (cipherBase_ge_two hq)).mpr hgeom'
    refine ⟨hlq, u₂, hsquare, ?_, ?_, ?_, ?_⟩
    · simpa [hw] using hlow
    · simpa [hw] using hhigh
    · simpa [hr₀, hp₂, hp₁] using hshift
    · simpa [hr₀] using hdvd

/-- The endpoint recurrence and low-bit mask force `u` below the final
radix block.  This quantitative fact is the first key step in the
reverse reconstruction. -/
theorem u_lt_endpoint_of_normalForm
    {length q u u₁ : ℕ}
    (hlength : 0 < length)
    (hlq : length + 1 < q)
    (hlow :
      u₁ =
        (u * u) &&&
          denseOnes (cipherBase q)
            (SparseRadixCipher.wordLength length))
    (hshift :
      cipherBase q * cipherBase q + u₁ =
        u + cipherBase q ^ slot length) :
    u < cipherBase q ^ slot length := by
  let base := cipherBase q
  let endpoint := slot length
  let mask :=
    denseOnes base
      (SparseRadixCipher.wordLength length)
  change u₁ = (u * u) &&& mask at hlow
  change
    base * base + u₁ =
      u + base ^ endpoint at hshift
  change u < base ^ endpoint
  have hbase : 4 ≤ base := by
    change 4 ≤ 2 ^ (4 * q)
    have hq : 1 ≤ q := by omega
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (4 * q) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
  have hendpoint : 4 ≤ endpoint := by
    change 4 ≤ 2 ^ (length + 1)
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (length + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
  have hu₁le : u₁ ≤ mask := by
    calc
      u₁ = (u * u) &&& mask := hlow
      _ ≤ mask := Nat.and_le_right
  have hgap :
      base ^ 2 + denseOnes base endpoint <
        base ^ endpoint :=
    pow_two_add_denseOnes_lt hbase hendpoint
  have hmask :
      mask =
        denseOnes base endpoint + base ^ endpoint := by
    change
      denseOnes base
          (SparseRadixCipher.wordLength length) =
        denseOnes base endpoint + base ^ endpoint
    rw [wordLength_eq_slot_add_one,
      denseOnes_succ]
  have hleft :
      base * base + mask <
        base ^ endpoint + base ^ endpoint := by
    rw [hmask]
    simpa [pow_two, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using
      Nat.add_lt_add_right hgap (base ^ endpoint)
  have hsum :
      u + base ^ endpoint <
        base ^ endpoint + base ^ endpoint := by
    calc
      u + base ^ endpoint =
          base * base + u₁ := hshift.symm
      _ ≤ base * base + mask :=
        Nat.add_le_add_left hu₁le _
      _ < base ^ endpoint + base ^ endpoint := hleft
  omega

/-- Bitwise form of the endpoint recurrence.  Both additions are
carry-free: divisibility separates `base^2` from `u₁`, and the endpoint
bound separates `u` from `base^endpoint`. -/
theorem or_recurrence_of_normalForm
    {length q u u₁ : ℕ}
    (hlength : 0 < length)
    (hlq : length + 1 < q)
    (hlow :
      u₁ =
        (u * u) &&&
          denseOnes (cipherBase q)
            (SparseRadixCipher.wordLength length))
    (hshift :
      cipherBase q * cipherBase q + u₁ =
        u + cipherBase q ^ slot length)
    (hdvd : cipherBase q ^ 4 ∣ u₁) :
    (cipherBase q * cipherBase q) ||| u₁ =
      (cipherBase q ^ slot length) ||| u := by
  let width := 4 * q
  let base := cipherBase q
  let endpoint := slot length
  have hwidth : 0 < width := by omega
  have hbaseEq : base = 2 ^ width := by
    rfl
  have hu :
      u < base ^ endpoint :=
    u_lt_endpoint_of_normalForm
      hlength hlq hlow hshift
  have hdisjoint :
      (base * base) &&& u₁ = 0 := by
    rw [hbaseEq]
    apply radixSquare_land_eq_zero_of_fourth_dvd hwidth
    simpa only [hbaseEq] using hdvd
  have hbasePow :
      base ^ endpoint =
        2 ^ (width * endpoint) := by
    rw [hbaseEq, ← pow_mul]
  have huPow :
      u < 2 ^ (width * endpoint) := by
    simpa only [hbasePow] using hu
  change (base * base) ||| u₁ =
    (base ^ endpoint) ||| u
  calc
    (base * base) ||| u₁ =
        base * base + u₁ :=
      DiophantineBitwise.lor_eq_add_of_land_eq_zero
        _ _ hdisjoint
    _ = u + base ^ endpoint := hshift
    _ = base ^ endpoint + u := Nat.add_comm _ _
    _ = (base ^ endpoint) ||| u := by
      have hor :=
        Nat.two_pow_add_eq_or_of_lt huPow 1
      simpa only [mul_one, hbasePow] using hor

/-- The recurrence also shows that `u` is itself a sparse low-bit radix
word, now supported strictly below the endpoint block. -/
theorem u_land_densePrefix_eq_self
    {length q u u₁ : ℕ}
    (hlength : 0 < length)
    (hlq : length + 1 < q)
    (hlow :
      u₁ =
        (u * u) &&&
          denseOnes (cipherBase q)
            (SparseRadixCipher.wordLength length))
    (hshift :
      cipherBase q * cipherBase q + u₁ =
        u + cipherBase q ^ slot length)
    (hdvd : cipherBase q ^ 4 ∣ u₁) :
    u &&&
        denseOnes (cipherBase q) (slot length) =
      u := by
  let width := 4 * q
  let base := cipherBase q
  let endpoint := slot length
  let fullMask :=
    denseOnes base
      (SparseRadixCipher.wordLength length)
  let prefixMask := denseOnes base endpoint
  have hwidth : 0 < width := by omega
  have hbaseEq : base = 2 ^ width := by
    rfl
  have hendpoint : 4 ≤ endpoint := by
    change 4 ≤ 2 ^ (length + 1)
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (length + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
  change
    u₁ = (u * u) &&& fullMask at hlow
  have hu₁Absorbed :
      u₁ &&& fullMask = u₁ := by
    rw [hlow, Nat.and_assoc, Nat.and_self]
  have hu :
      u < base ^ endpoint :=
    u_lt_endpoint_of_normalForm
      hlength hlq hlow hshift
  have hbasePow :
      base ^ endpoint =
        2 ^ (width * endpoint) := by
    rw [hbaseEq, ← pow_mul]
  have huPow :
      u < 2 ^ (width * endpoint) := by
    simpa only [hbasePow] using hu
  have hOr :=
    or_recurrence_of_normalForm
      hlength hlq hlow hshift hdvd
  change
    (base * base) ||| u₁ =
      (base ^ endpoint) ||| u at hOr
  change u &&& prefixMask = u
  apply Nat.eq_of_testBit_eq
  intro bit
  rw [Nat.testBit_land]
  by_cases huBit : u.testBit bit = true
  · have hbitLt :
        bit < width * endpoint := by
      by_contra hnot
      have hle : width * endpoint ≤ bit :=
        Nat.le_of_not_gt hnot
      have hpowLe :
          2 ^ (width * endpoint) ≤ 2 ^ bit :=
        Nat.pow_le_pow_right (by norm_num) hle
      have hfalse :=
        Nat.testBit_eq_false_of_lt
          (huPow.trans_le hpowLe)
      rw [huBit] at hfalse
      contradiction
    have hleftBit :
        ((base * base) ||| u₁).testBit bit = true := by
      rw [hOr, Nat.testBit_or, huBit]
      simp
    rw [Nat.testBit_or, Bool.or_eq_true] at hleftBit
    rcases hleftBit with hbaseBit | hu₁Bit
    · have hbaseSquarePow :
          base * base = 2 ^ (width * 2) := by
        rw [← pow_two, hbaseEq, ← pow_mul]
      rw [hbaseSquarePow, Nat.testBit_two_pow] at hbaseBit
      have hbitPosition :
          bit = width * 2 :=
        (of_decide_eq_true hbaseBit).symm
      have hprefixBit :
          prefixMask.testBit bit = true := by
        change
          (denseOnes (2 ^ width) endpoint).testBit bit =
            true
        apply
          (testBit_denseOnes_iff hwidth endpoint bit).mpr
        exact ⟨2, by omega, hbitPosition⟩
      rw [huBit, hprefixBit]
      rfl
    · have hu₁Position :=
        testBit_position_of_land_denseOnes_eq_self
          (width := width)
          (count :=
            SparseRadixCipher.wordLength length)
          (value := u₁) (bit := bit)
          hwidth
          (by
            simpa only [hbaseEq] using hu₁Absorbed)
          hu₁Bit
      rcases hu₁Position with
        ⟨position, hposition, hbitPosition⟩
      have hpositionLe :
          position < endpoint + 1 := by
        simpa only [wordLength_eq_slot_add_one] using
          hposition
      have hpositionLt : position < endpoint := by
        have hmulLt :
            width * position < width * endpoint := by
          rw [← hbitPosition]
          exact hbitLt
        exact (Nat.mul_lt_mul_left hwidth).mp hmulLt
      have hprefixBit :
          prefixMask.testBit bit = true := by
        change
          (denseOnes (2 ^ width) endpoint).testBit bit =
            true
        apply
          (testBit_denseOnes_iff hwidth endpoint bit).mpr
        exact ⟨position, hpositionLt, hbitPosition⟩
      rw [huBit, hprefixBit]
      rfl
  · have huBitFalse : u.testBit bit = false := by
      cases h : u.testBit bit <;> simp_all
    rw [huBitFalse]
    simp

/-- The radix digit of `u²` is its selected-entry convolution
coefficient. -/
theorem digit_square_eq_selectedConvolution
    {length q u u₁ position : ℕ}
    (hlength : 0 < length)
    (hlq : length + 1 < q)
    (hlow :
      u₁ =
        (u * u) &&&
          denseOnes (cipherBase q)
            (SparseRadixCipher.wordLength length))
    (hshift :
      cipherBase q * cipherBase q + u₁ =
        u + cipherBase q ^ slot length)
    (hdvd : cipherBase q ^ 4 ∣ u₁)
    (hposition : position < 2 * slot length) :
    RadixSequence.digit (cipherBase q)
        (u * u) position =
      linearConvolutionAt
        (fun i : Fin (slot length) =>
          selectedEntry (4 * q) u i)
        (fun i : Fin (slot length) =>
          selectedEntry (4 * q) u i)
        position := by
  let width := 4 * q
  let count := slot length
  let entry : Fin count → ℕ :=
    fun i => selectedEntry width u i
  have hwidth : 0 < width := by omega
  have hbaseEq : cipherBase q = 2 ^ width := by
    rfl
  have huLand :
      u &&& denseOnes (cipherBase q) count = u :=
    u_land_densePrefix_eq_self
      hlength hlq hlow hshift hdvd
  have hencode :
      RadixSequence.encode (cipherBase q)
          (List.ofFn entry) = u := by
    rw [hbaseEq]
    rw [← selectedEntries_eq_ofFn
      width count u]
    exact
      encode_selectedEntries_eq_of_land
        hwidth (by simpa only [hbaseEq] using huLand)
  have hproduct :
      RadixSequence.encode (cipherBase q)
          (linearConvolutionEntries entry entry) =
        u * u := by
    rw [encode_linearConvolutionEntries,
      hencode]
  have hentries :
      ∀ coefficient ∈
          linearConvolutionEntries entry entry,
        coefficient < cipherBase q := by
    intro coefficient hcoefficient
    obtain ⟨index, rfl⟩ :=
      List.mem_ofFn.mp hcoefficient
    exact
      selectedConvolution_lt_cipherBase
        (value := u) (position := index) hlq
  have hbasePos : 0 < cipherBase q :=
    cipherBase_pos q
  rw [← hproduct]
  rw [RadixSequence.digit_encode_eq_getElem
    hbasePos hentries position (by
      simpa [linearConvolutionEntries] using hposition)]
  simp [linearConvolutionEntries, entry, count, width]

/-- The low-bit square mask turns support into doubled support.  This is
the central parity step of the reverse cipher argument: off-diagonal
products occur in transposed pairs, so only diagonal squares survive
modulo two. -/
theorem testBit_u₁_iff_doubled_u
    {length q u u₁ position : ℕ}
    (hlength : 0 < length)
    (hlq : length + 1 < q)
    (hlow :
      u₁ =
        (u * u) &&&
          denseOnes (cipherBase q)
            (SparseRadixCipher.wordLength length))
    (hshift :
      cipherBase q * cipherBase q + u₁ =
        u + cipherBase q ^ slot length)
    (hdvd : cipherBase q ^ 4 ∣ u₁)
    (hposition : position ≤ slot length) :
    u₁.testBit ((4 * q) * position) = true ↔
      ∃ i : Fin (slot length),
        position = (i : ℕ) + (i : ℕ) ∧
        u.testBit ((4 * q) * (i : ℕ)) = true := by
  let width := 4 * q
  let base := cipherBase q
  let endpoint := slot length
  let mask :=
    denseOnes base
      (SparseRadixCipher.wordLength length)
  have hwidth : 0 < width := by omega
  have hbaseEq : base = 2 ^ width := by
    rfl
  have hendpoint : 0 < endpoint := by
    exact Nat.zero_lt_of_lt
      (show 4 ≤ endpoint by
        change 4 ≤ 2 ^ (length + 1)
        calc
          4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (length + 1) :=
            Nat.pow_le_pow_right (by norm_num) (by omega))
  have hpositionWord :
      position <
        SparseRadixCipher.wordLength length := by
    rw [wordLength_eq_slot_add_one]
    exact Nat.lt_succ_of_le hposition
  have hmaskBit :
      mask.testBit (width * position) = true := by
    change
      (denseOnes (2 ^ width)
        (SparseRadixCipher.wordLength length)).testBit
          (width * position) = true
    exact
      (testBit_denseOnes_iff hwidth
        (SparseRadixCipher.wordLength length)
        (width * position)).mpr
        ⟨position, hpositionWord, rfl⟩
  have hlowBit :
      u₁.testBit (width * position) =
        (u * u).testBit (width * position) := by
    have h :=
      congrArg
        (fun n => n.testBit (width * position)) hlow
    change
      u₁.testBit (width * position) =
        ((u * u) &&& mask).testBit
          (width * position) at h
    rw [Nat.testBit_land, hmaskBit] at h
    simpa using h
  have hblock :=
    testBit_blockStart_eq_digit_testBit_zero
      hwidth (u * u) position
  have hdigit :=
    digit_square_eq_selectedConvolution
      hlength hlq hlow hshift hdvd
      (position := position) (by omega)
  change
    u₁.testBit (width * position) = true ↔ _
  have hbaseWidth :
      2 ^ width = cipherBase q := by
    rfl
  rw [hlowBit, hblock, hbaseWidth, hdigit]
  exact selectedConvolution_testBit_zero_iff

/-- At every block below the endpoint, the support of `u` is exactly
the inserted block `2`, together with the non-endpoint support of
`u₁`. -/
theorem testBit_u_iff_two_or_u₁
    {length q u u₁ position : ℕ}
    (hlength : 0 < length)
    (hlq : length + 1 < q)
    (hlow :
      u₁ =
        (u * u) &&&
          denseOnes (cipherBase q)
            (SparseRadixCipher.wordLength length))
    (hshift :
      cipherBase q * cipherBase q + u₁ =
        u + cipherBase q ^ slot length)
    (hdvd : cipherBase q ^ 4 ∣ u₁)
    (hposition : position < slot length) :
    u.testBit ((4 * q) * position) = true ↔
      position = 2 ∨
        u₁.testBit ((4 * q) * position) = true := by
  let width := 4 * q
  let base := cipherBase q
  let endpoint := slot length
  have hwidth : 0 < width := by omega
  have hbaseEq : base = 2 ^ width := by
    rfl
  have hbaseSquare :
      base * base = 2 ^ (width * 2) := by
    rw [← pow_two, hbaseEq, ← pow_mul]
  have hbaseEndpoint :
      base ^ endpoint =
        2 ^ (width * endpoint) := by
    rw [hbaseEq, ← pow_mul]
  have hOr :=
    or_recurrence_of_normalForm
      hlength hlq hlow hshift hdvd
  change
    (base * base) ||| u₁ =
      (base ^ endpoint) ||| u at hOr
  have hbitEq :=
    congrArg
      (fun n => n.testBit (width * position)) hOr
  change
    ((base * base) ||| u₁).testBit
        (width * position) =
      ((base ^ endpoint) ||| u).testBit
        (width * position) at hbitEq
  rw [Nat.testBit_or, Nat.testBit_or,
    hbaseSquare, hbaseEndpoint,
    Nat.testBit_two_pow, Nat.testBit_two_pow] at hbitEq
  simp only [Nat.mul_left_cancel_iff hwidth] at hbitEq
  have hne : endpoint ≠ position := by
    omega
  rw [show decide (endpoint = position) = false by
      exact decide_eq_false hne] at hbitEq
  simp only [Bool.false_or] at hbitEq
  change
    u.testBit (width * position) = true ↔
      position = 2 ∨
        u₁.testBit (width * position) = true
  rw [← hbitEq, Bool.or_eq_true, decide_eq_true_eq]
  exact or_congr eq_comm Iff.rfl

/-- Closed recurrence for the support of `u₁`: it starts at block four,
and every later occupied block is twice an earlier occupied block. -/
theorem u₁_support_recurrence
    {length q u u₁ position : ℕ}
    (hlength : 0 < length)
    (hlq : length + 1 < q)
    (hlow :
      u₁ =
        (u * u) &&&
          denseOnes (cipherBase q)
            (SparseRadixCipher.wordLength length))
    (hshift :
      cipherBase q * cipherBase q + u₁ =
        u + cipherBase q ^ slot length)
    (hdvd : cipherBase q ^ 4 ∣ u₁)
    (hposition : position ≤ slot length) :
    u₁.testBit ((4 * q) * position) = true ↔
      position = 4 ∨
        ∃ previous < slot length,
          position = previous + previous ∧
          u₁.testBit ((4 * q) * previous) = true := by
  have hendpoint : 4 ≤ slot length := by
    change 4 ≤ 2 ^ (length + 1)
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (length + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [testBit_u₁_iff_doubled_u
    hlength hlq hlow hshift hdvd hposition]
  constructor
  · rintro ⟨i, hdouble, huBit⟩
    have huSupport :=
      (testBit_u_iff_two_or_u₁
        hlength hlq hlow hshift hdvd i.isLt).mp
        huBit
    rcases huSupport with hi | hi
    · left
      omega
    · right
      exact ⟨i, i.isLt, hdouble, hi⟩
  · rintro (hfour | ⟨previous, hprevious,
      hdouble, hu₁Bit⟩)
    · let i : Fin (slot length) :=
        ⟨2, by omega⟩
      refine ⟨i, by
        dsimp [i]
        omega, ?_⟩
      apply
        (testBit_u_iff_two_or_u₁
          hlength hlq hlow hshift hdvd i.isLt).mpr
      left
      rfl
    · let i : Fin (slot length) :=
        ⟨previous, hprevious⟩
      refine ⟨i, by
        simpa [i] using hdouble, ?_⟩
      apply
        (testBit_u_iff_two_or_u₁
          hlength hlq hlow hshift hdvd i.isLt).mpr
      right
      simpa [i] using hu₁Bit

/-- Divisibility fixes the lower endpoint of the support at block four. -/
theorem four_le_of_u₁_testBit
    {q u₁ position : ℕ}
    (hq : 0 < q)
    (hdvd : cipherBase q ^ 4 ∣ u₁)
    (hbit :
      u₁.testBit ((4 * q) * position) = true) :
    4 ≤ position := by
  let width := 4 * q
  have hwidth : 0 < width := by omega
  have hdvd' :
      2 ^ (width * 4) ∣ u₁ := by
    simpa [width, cipherBase, ← pow_mul] using hdvd
  by_contra hnot
  have hposition : position < 4 := by omega
  have hmul :
      width * position < width * 4 :=
    (Nat.mul_lt_mul_left hwidth).mpr hposition
  have hfalse :=
    testBit_eq_false_of_two_pow_dvd hdvd' hmul
  rw [hbit] at hfalse
  contradiction

/-- No spurious support positions can satisfy the recurrence: every
occupied block is one of `4,8,...,2^(length+1)`. -/
theorem u₁_testBit_only_at_shiftedSlots
    {length q u u₁ position : ℕ}
    (hlength : 0 < length)
    (hlq : length + 1 < q)
    (hlow :
      u₁ =
        (u * u) &&&
          denseOnes (cipherBase q)
            (SparseRadixCipher.wordLength length))
    (hshift :
      cipherBase q * cipherBase q + u₁ =
        u + cipherBase q ^ slot length)
    (hdvd : cipherBase q ^ 4 ∣ u₁)
    (hposition : position ≤ slot length)
    (hbit :
      u₁.testBit ((4 * q) * position) = true) :
    ∃ i < length, position = slot (i + 1) := by
  have hq : 0 < q := by omega
  induction position using Nat.strong_induction_on with
  | h position ih =>
      have hrec :=
        (u₁_support_recurrence
          hlength hlq hlow hshift hdvd hposition).mp hbit
      rcases hrec with hfour |
          ⟨previous, hprevious, hdouble, hpreviousBit⟩
      · refine ⟨0, hlength, ?_⟩
        simpa [slot] using hfour
      · have hpreviousFour :
            4 ≤ previous :=
          four_le_of_u₁_testBit hq hdvd hpreviousBit
        have hpreviousLt : previous < position := by
          omega
        have hpreviousLe :
            previous ≤ slot length := by
          omega
        obtain ⟨i, hi, hiPosition⟩ :=
          ih previous hpreviousLt
            hpreviousLe hpreviousBit
        have hpositionSlot :
            position = slot (i + 2) := by
          calc
            position = previous + previous := hdouble
            _ = slot (i + 1) + slot (i + 1) := by
              rw [hiPosition]
            _ = slot ((i + 1) + 1) :=
              slot_add_self (i + 1)
            _ = slot (i + 2) := by
              congr 1
        have hiSucc : i + 1 < length := by
          by_contra hnot
          have hiLast : i + 1 = length := by
            omega
          have hstrict :
              slot length < slot (length + 1) :=
            slot_strictMono (Nat.lt_succ_self length)
          have hiIndex : i + 2 = length + 1 := by
            omega
          have hslotLe :
              slot (i + 2) ≤ slot length := by
            rw [← hpositionSlot]
            exact hposition
          rw [hiIndex] at hslotLe
          omega
        exact
          ⟨i + 1, hiSucc, by
            simpa [Nat.add_assoc] using hpositionSlot⟩

/-- Conversely, every intended shifted slot is generated by the support
recurrence. -/
theorem u₁_testBit_at_shiftedSlot
    {length q u u₁ : ℕ}
    (hlength : 0 < length)
    (hlq : length + 1 < q)
    (hlow :
      u₁ =
        (u * u) &&&
          denseOnes (cipherBase q)
            (SparseRadixCipher.wordLength length))
    (hshift :
      cipherBase q * cipherBase q + u₁ =
        u + cipherBase q ^ slot length)
    (hdvd : cipherBase q ^ 4 ∣ u₁) :
    ∀ i < length,
      u₁.testBit ((4 * q) * slot (i + 1)) = true := by
  intro i
  induction i with
  | zero =>
      intro hi
      apply
        (u₁_support_recurrence
          hlength hlq hlow hshift hdvd
          (by
            have :=
              slot_strictMono.monotone
                (show 1 ≤ length by omega)
            simpa using this)).mpr
      left
      simp [slot]
  | succ i ih =>
      intro hi
      have hiPrev : i < length := by omega
      have hprevious :=
        ih hiPrev
      have hpreviousLt :
          slot (i + 1) < slot length :=
        slot_strictMono (by omega)
      have hcurrentLe :
          slot (i + 2) ≤ slot length :=
        slot_strictMono.monotone (by omega)
      apply
        (u₁_support_recurrence
          hlength hlq hlow hshift hdvd
          hcurrentLe).mpr
      right
      refine
        ⟨slot (i + 1), hpreviousLt, ?_, hprevious⟩
      exact (slot_add_self (i + 1)).symm

/-- Exact block support of `u₁`. -/
theorem u₁_testBit_iff_shiftedSlot
    {length q u u₁ position : ℕ}
    (hlength : 0 < length)
    (hlq : length + 1 < q)
    (hlow :
      u₁ =
        (u * u) &&&
          denseOnes (cipherBase q)
            (SparseRadixCipher.wordLength length))
    (hshift :
      cipherBase q * cipherBase q + u₁ =
        u + cipherBase q ^ slot length)
    (hdvd : cipherBase q ^ 4 ∣ u₁)
    (hposition : position ≤ slot length) :
    u₁.testBit ((4 * q) * position) = true ↔
      ∃ i < length, position = slot (i + 1) := by
  constructor
  · exact
      u₁_testBit_only_at_shiftedSlots
        hlength hlq hlow hshift hdvd
          hposition
  · rintro ⟨i, hi, rfl⟩
    exact
      u₁_testBit_at_shiftedSlot
        hlength hlq hlow hshift hdvd i hi

/-- Reassembling the exact support gives the intended shifted sparse
word. -/
theorem u₁_eq_shiftedSparseOnes_of_normalForm
    {length q u u₁ : ℕ}
    (hlength : 0 < length)
    (hlq : length + 1 < q)
    (hlow :
      u₁ =
        (u * u) &&&
          denseOnes (cipherBase q)
            (SparseRadixCipher.wordLength length))
    (hshift :
      cipherBase q * cipherBase q + u₁ =
        u + cipherBase q ^ slot length)
    (hdvd : cipherBase q ^ 4 ∣ u₁) :
    u₁ = shiftedSparseOnes length q := by
  classical
  let width := 4 * q
  let endpoint := slot length
  let count := SparseRadixCipher.wordLength length
  let mask := denseOnes (cipherBase q) count
  let supportPositions : Finset ℕ :=
    (Finset.range count).filter fun position =>
      u₁.testBit (width * position) = true
  have hwidth : 0 < width := by omega
  have hbaseEq : cipherBase q = 2 ^ width := by
    rfl
  change u₁ = (u * u) &&& mask at hlow
  have habsorbed :
      u₁ &&& mask = u₁ := by
    rw [hlow, Nat.and_assoc, Nat.and_self]
  have hselected :
      selectedBits width count u₁ = u₁ := by
    apply
      selectedBits_eq_of_land_denseOnes_eq_self
        hwidth
    simpa only [hbaseEq] using habsorbed
  have hsupportSum :
      selectedBits width count u₁ =
        ∑ position ∈ supportPositions,
          2 ^ (width * position) := by
    rw [selectedBits]
    rw [← Finset.sum_filter]
  have hbij :
      (∑ i ∈ Finset.range length,
          (2 ^ width) ^ slot (i + 1)) =
        ∑ position ∈ supportPositions,
          2 ^ (width * position) := by
    apply Finset.sum_bij
      (fun i hi => slot (i + 1))
    · intro i hi
      have hiLength : i < length := by
        simpa only [Finset.mem_range] using hi
      have hslotLe :
          slot (i + 1) ≤ endpoint :=
        slot_strictMono.monotone (by omega)
      have hslotCount :
          slot (i + 1) < count := by
        change
          slot (i + 1) <
            SparseRadixCipher.wordLength length
        rw [wordLength_eq_slot_add_one]
        exact Nat.lt_succ_of_le hslotLe
      have hbit :=
        u₁_testBit_at_shiftedSlot
          hlength hlq hlow hshift hdvd
          i hiLength
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr hslotCount, hbit⟩
    · intro i₁ hi₁ i₂ hi₂ heq
      have hindices :
          i₁ + 1 = i₂ + 1 :=
        slot_injective heq
      omega
    · intro position hposition
      have hpositionData :=
        Finset.mem_filter.mp hposition
      have hpositionLt :
          position < count :=
        Finset.mem_range.mp hpositionData.1
      have hpositionLe :
          position ≤ endpoint := by
        change
          position <
            SparseRadixCipher.wordLength length at hpositionLt
        change
          position ≤ slot length
        rw [wordLength_eq_slot_add_one] at hpositionLt
        omega
      obtain ⟨i, hi, hiPosition⟩ :=
        (u₁_testBit_iff_shiftedSlot
          hlength hlq hlow hshift hdvd
          hpositionLe).mp hpositionData.2
      refine ⟨i, Finset.mem_range.mpr hi, ?_⟩
      exact hiPosition.symm
    · intro i hi
      rw [← pow_mul]
  calc
    u₁ = selectedBits width count u₁ :=
      hselected.symm
    _ = ∑ position ∈ supportPositions,
          2 ^ (width * position) :=
      hsupportSum
    _ = ∑ i ∈ Finset.range length,
          (2 ^ width) ^ slot (i + 1) :=
      hbij.symm
    _ = shiftedSparseOnes length q := by
      rw [shiftedSparseOnes_eq_sum]
      rw [Fin.sum_univ_eq_sum_range
        (fun i : ℕ =>
          cipherBase q ^ slot (i + 1))]
      simp only [hbaseEq]

/-- Once `u₁` has been reconstructed, the endpoint recurrence determines
`u` by cancellation. -/
theorem u_eq_sparseOnes_of_normalForm
    {length q u u₁ : ℕ}
    (hlength : 0 < length)
    (hlq : length + 1 < q)
    (hlow :
      u₁ =
        (u * u) &&&
          denseOnes (cipherBase q)
            (SparseRadixCipher.wordLength length))
    (hshift :
      cipherBase q * cipherBase q + u₁ =
        u + cipherBase q ^ slot length)
    (hdvd : cipherBase q ^ 4 ∣ u₁) :
    u = sparseOnes length q := by
  have hu₁ :
      u₁ = shiftedSparseOnes length q :=
    u₁_eq_shiftedSparseOnes_of_normalForm
      hlength hlq hlow hshift hdvd
  apply Nat.add_right_cancel
  calc
    u + cipherBase q ^ slot length =
        cipherBase q * cipherBase q + u₁ :=
      hshift.symm
    _ = cipherBase q ^ 2 +
        shiftedSparseOnes length q := by
      rw [hu₁, pow_two]
    _ = sparseOnes length q +
        cipherBase q ^ slot length :=
      shifted_add_endpoint length q

/-- The endpoint block must actually occur in `u₁`.  Divisibility keeps
the inserted `base^2` bit disjoint from `u₁`, while the preceding bound
keeps `u` strictly below the endpoint; comparing the endpoint bit in the
recurrence then forces it to be present on the left. -/
theorem endpoint_testBit_of_normalForm
    {length q u u₁ : ℕ}
    (hlength : 0 < length)
    (hlq : length + 1 < q)
    (hlow :
      u₁ =
        (u * u) &&&
          denseOnes (cipherBase q)
            (SparseRadixCipher.wordLength length))
    (hshift :
      cipherBase q * cipherBase q + u₁ =
        u + cipherBase q ^ slot length)
    (hdvd : cipherBase q ^ 4 ∣ u₁) :
    u₁.testBit ((4 * q) * slot length) = true := by
  let width := 4 * q
  let base := cipherBase q
  let endpoint := slot length
  have hwidth : 0 < width := by omega
  have hendpoint : 4 ≤ endpoint := by
    change 4 ≤ 2 ^ (length + 1)
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (length + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
  have hbasePow (exponent : ℕ) :
      base ^ exponent =
        2 ^ (width * exponent) := by
    dsimp [base, width, cipherBase]
    rw [← pow_mul]
  have hu :
      u < base ^ endpoint := by
    exact
      u_lt_endpoint_of_normalForm
        hlength hlq hlow hshift
  have huPow :
      u < 2 ^ (width * endpoint) := by
    simpa only [hbasePow] using hu
  have huBit :
      u.testBit (width * endpoint) = false :=
    Nat.testBit_eq_false_of_lt huPow
  have hbaseSquareBit :
      (base * base).testBit (width * endpoint) = false := by
    rw [← pow_two, hbasePow, Nat.testBit_two_pow]
    rw [decide_eq_false_iff_not]
    intro heq
    have : 2 = endpoint := by
      exact Nat.eq_of_mul_eq_mul_left hwidth heq
    omega
  have hendpointBit :
      (base ^ endpoint).testBit
          (width * endpoint) = true := by
    rw [hbasePow, Nat.testBit_two_pow]
    simp
  have hdisjoint :
      (base * base) &&& u₁ = 0 := by
    rcases hdvd with ⟨factor, hfactor⟩
    have hone : 1 < 2 ^ width :=
      Nat.one_lt_two_pow (Nat.ne_of_gt hwidth)
    have hblocks :=
      SparseRadixCipher.land_radixBlocks_eq_zero
        (width := width) (lower := 2) (upper := 4)
        (left := 1) (right := factor)
        (by omega) hone
    rw [hfactor]
    simpa only [one_mul, base, width, cipherBase,
      pow_two, Nat.mul_comm] using hblocks
  have hOrEq :
      (base * base) ||| u₁ =
        (base ^ endpoint) ||| u := by
    calc
      (base * base) ||| u₁ =
          base * base + u₁ :=
        DiophantineBitwise.lor_eq_add_of_land_eq_zero
          _ _ hdisjoint
      _ = u + base ^ endpoint := hshift
      _ = base ^ endpoint + u := Nat.add_comm _ _
      _ = (base ^ endpoint) ||| u := by
        have hor :=
          Nat.two_pow_add_eq_or_of_lt huPow 1
        simpa only [one_mul, mul_one, hbasePow] using hor
  have hbitEq :=
    congrArg
      (fun n => n.testBit (width * endpoint)) hOrEq
  change
    ((base * base) ||| u₁).testBit
        (width * endpoint) =
      ((base ^ endpoint) ||| u).testBit
        (width * endpoint) at hbitEq
  rw [Nat.testBit_or, Nat.testBit_or,
    hbaseSquareBit, hendpointBit, huBit] at hbitEq
  simpa using hbitEq

/-- Conversely, every finite algebraic certificate reconstructs the
intended pair of sparse all-ones words.  The empty branch is immediate.
In the nonempty branch, `Certificate.nonempty_normalForm` first removes
all auxiliary parameters; the support reconstruction above then forces
`u₁`, and the endpoint recurrence forces `u`. -/
theorem Certificate.toSeqsOfOnes
    {length q u u₁ : ℕ}
    (hcertificate : Certificate length q u u₁) :
    SeqsOfOnes length q u u₁ := by
  by_cases hzero : length = 0
  · rcases hcertificate with hempty | hnonempty
    · rcases hempty with
        ⟨hlength, hu, hu₁, hq⟩
      subst length
      exact
        ⟨by omega,
          hu.trans (sparseOnes_zero q).symm,
          hu₁.trans (shiftedSparseOnes_zero q).symm⟩
    · omega
  · have hlength : 0 < length :=
      Nat.pos_of_ne_zero hzero
    obtain
      ⟨hlq, u₂, hsquare, hlow, hhigh, hshift, hdvd⟩ :=
        Certificate.nonempty_normalForm
          hcertificate hlength
    have hu₁ :
        u₁ = shiftedSparseOnes length q :=
      u₁_eq_shiftedSparseOnes_of_normalForm
        hlength hlq hlow hshift hdvd
    have hu :
        u = sparseOnes length q :=
      u_eq_sparseOnes_of_normalForm
        hlength hlq hlow hshift hdvd
    exact ⟨hlq, hu, hu₁⟩

/-- Exact correctness of the finite certificate. -/
theorem seqsOfOnes_iff_certificate
    {length q u u₁ : ℕ} :
    SeqsOfOnes length q u u₁ ↔
      Certificate length q u u₁ :=
  ⟨SeqsOfOnes.toCertificate,
    Certificate.toSeqsOfOnes⟩

/-- The sparse all-ones relation is Diophantine.  This is the complete,
unconditional formal counterpart of the `seqs_of_ones_dio` lemma in
Matiyasevich's radix-cipher construction. -/
theorem seqsOfOnes_dioph :
    Dioph {v : Fin 4 → ℕ |
      SeqsOfOnes (v 0) (v 1) (v 2) (v 3)} := by
  exact
    Dioph.ext certificate_dioph fun v =>
      (seqsOfOnes_iff_certificate
        (length := v 0) (q := v 1)
        (u := v 2) (u₁ := v 3)).symm

end SparseOnesCipher

end HGAS
