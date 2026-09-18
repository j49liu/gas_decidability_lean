import HGAS.Arithmetic.SparseOnesCipher
import Mathlib.Tactic

/-!
# Diophantine recognition of sparse cipher words

This file is the next layer of Matiyasevich's bounded-universal
construction.  A length-`length` tuple `entry` is stored at the sparse
radix positions

```
2^(i+1),   i = 0, ..., length-1
```

in radix `2^(4q)`.  Every tuple entry is required to be below `2^q`.

The semantic predicate `CipherOf` still quantifies over a finite
function.  The point of the construction is to eliminate that
higher-level witness.  A number is such a cipher exactly when it is a
binary submask of

```
(2^q - 1) * sparseOnes length q.
```

The preceding generic sparse-radix decoder proves the reverse
implication: every submask splits independently into the reserved
blocks.  Combining this characterization with
`SparseOnesCipher.seqsOfOnes_dioph` gives an unconditional
Diophantine definition of the existential `Code` predicate.

The theorem `code_iff_certificate` is the formal counterpart of
`Code_dio` in the Coq/Undecidability development of the DPRM theorem.
-/

namespace HGAS

namespace SparseCipherCode

open SparseRadixCipher
open SparseOnesCipher

/-- The bound imposed on every tuple coordinate. -/
def entryBase (q : ℕ) : ℕ :=
  2 ^ q

/-- The binary word with its lowest `q` bits equal to one. -/
def maxEntry (q : ℕ) : ℕ :=
  entryBase q - 1

/-- `a` is the sparse `q`-cipher of the finite tuple `entry`. -/
def CipherOf
    (length q : ℕ) (entry : Fin length → ℕ) (a : ℕ) : Prop :=
  length + 1 < q ∧
    (∀ i, entry i < entryBase q) ∧
    a = encode (cipherBase q) entry

/-- `a` is the cipher of some bounded tuple of the prescribed length. -/
def Code (length q a : ℕ) : Prop :=
  ∃ entry : Fin length → ℕ,
    CipherOf length q entry a

/-- The universal block mask for all bounded length-`length` tuple
codes. -/
def maskCode (length q : ℕ) : ℕ :=
  maxEntry q * sparseOnes length q

theorem maxEntry_lt_entryBase (q : ℕ) :
    maxEntry q < entryBase q := by
  have hpositive : 0 < entryBase q := by
    simp [entryBase]
  simp only [maxEntry]
  omega

theorem entryBase_le_cipherBase (q : ℕ) :
    entryBase q ≤ cipherBase q := by
  rw [entryBase, cipherBase]
  exact
    Nat.pow_le_pow_right (by norm_num)
      (by omega)

/-- A sparse cipher word has at most one decoded tuple.  This is the
basic extensionality principle used whenever two semantic descriptions
refer to the same numeric code. -/
theorem CipherOf.entry_eq
    {length q value : ℕ}
    {left right : Fin length → ℕ}
    (hleft : CipherOf length q left value)
    (hright : CipherOf length q right value) :
    left = right := by
  apply
    SparseRadixCipher.encode_injective
      (cipherBase_pos q)
      (fun i =>
        (hleft.2.1 i).trans_le
          (entryBase_le_cipherBase q))
      (fun i =>
        (hright.2.1 i).trans_le
          (entryBase_le_cipherBase q))
  exact hleft.2.2.symm.trans hright.2.2

theorem maxEntry_lt_cipherBase (q : ℕ) :
    maxEntry q < cipherBase q :=
  (maxEntry_lt_entryBase q).trans_le
    (entryBase_le_cipherBase q)

/-- Encoding a constant sparse tuple is scalar multiplication of the
sparse all-ones word. -/
theorem encode_constant
    (length q coefficient : ℕ) :
    encode (cipherBase q)
        (fun _ : Fin length => coefficient) =
      coefficient * sparseOnes length q := by
  rw [SparseRadixCipher.encode_eq_sum,
    sparseOnes, SparseRadixCipher.encode_eq_sum,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp

theorem encode_maxEntry (length q : ℕ) :
    encode (cipherBase q)
        (fun _ : Fin length => maxEntry q) =
      maskCode length q := by
  exact encode_constant length q (maxEntry q)

/-- A semantic cipher is absorbed by the universal binary block mask. -/
theorem land_maskCode_eq_of_cipherOf
    {length q a : ℕ} {entry : Fin length → ℕ}
    (hcipher : CipherOf length q entry a) :
    a &&& maskCode length q = a := by
  rcases hcipher with ⟨hlq, hentry, rfl⟩
  rw [← encode_maxEntry]
  calc
    encode (cipherBase q) entry &&&
          encode (cipherBase q)
            (fun _ : Fin length => maxEntry q) =
        encode (cipherBase q)
          (fun i => entry i &&& maxEntry q) := by
      change
        encode (2 ^ (4 * q)) entry &&&
            encode (2 ^ (4 * q))
              (fun _ : Fin length => maxEntry q) =
          encode (2 ^ (4 * q))
            (fun i => entry i &&& maxEntry q)
      exact
        SparseRadixCipher.encode_land entry
          (fun _ : Fin length => maxEntry q)
          (fun i =>
            (hentry i).trans_le
              (entryBase_le_cipherBase q))
          (fun _ => maxEntry_lt_cipherBase q)
    _ = encode (cipherBase q) entry := by
      congr 1
      funext i
      exact
        Nat.and_two_pow_sub_one_of_lt_two_pow
          (hentry i)

/-- Equivalently, every semantic cipher is a binary submask of the
universal word. -/
theorem binaryLE_maskCode_of_cipherOf
    {length q a : ℕ} {entry : Fin length → ℕ}
    (hcipher : CipherOf length q entry a) :
    DiophantineBitwise.BinaryLE a (maskCode length q) :=
  (DiophantineBitwise.binaryLE_iff_land_eq_left
    a (maskCode length q)).mpr
      (land_maskCode_eq_of_cipherOf hcipher)

/-- The generic submask decoder specializes to bounded cipher entries:
absorption by the universal mask reconstructs an actual tuple. -/
theorem exists_cipherOf_of_land_maskCode_eq
    {length q a : ℕ}
    (hlq : length + 1 < q)
    (hland : a &&& maskCode length q = a) :
    ∃ entry : Fin length → ℕ,
      CipherOf length q entry a := by
  have hq : 0 < q := by omega
  have hwidth : 0 < 4 * q := by omega
  have hland' :
      a &&&
          encode (2 ^ (4 * q))
            (fun _ : Fin length => maxEntry q) =
        a := by
    change
      a &&&
          encode (cipherBase q)
            (fun _ : Fin length => maxEntry q) =
        a
    rw [encode_maxEntry]
    exact hland
  obtain ⟨entry, hsubmask, hcode⟩ :=
    SparseRadixCipher.exists_encode_of_land_encode_eq_self
      hwidth
      (fun _ : Fin length => maxEntry q)
      (fun _ => by
        simpa only [cipherBase] using
          maxEntry_lt_cipherBase q)
      hland'
  refine ⟨entry, hlq, ?_, ?_⟩
  · intro i
    have hle :
        entry i ≤ maxEntry q := by
      rw [← hsubmask i]
      exact Nat.and_le_right
    exact hle.trans_lt (maxEntry_lt_entryBase q)
  · simpa only [cipherBase] using hcode

/-- Binary inclusion in the universal mask also reconstructs a semantic
cipher. -/
theorem exists_cipherOf_of_binaryLE_maskCode
    {length q a : ℕ}
    (hlq : length + 1 < q)
    (hbinary :
      DiophantineBitwise.BinaryLE a (maskCode length q)) :
    ∃ entry : Fin length → ℕ,
      CipherOf length q entry a := by
  apply exists_cipherOf_of_land_maskCode_eq hlq
  exact
    (DiophantineBitwise.binaryLE_iff_land_eq_left
      a (maskCode length q)).mp hbinary

/-- For fixed admissible parameters, the higher-order existential
definition of `Code` is exactly binary inclusion in one explicit mask. -/
theorem code_iff_binaryLE_maskCode
    {length q a : ℕ}
    (hlq : length + 1 < q) :
    Code length q a ↔
      DiophantineBitwise.BinaryLE a (maskCode length q) := by
  constructor
  · rintro ⟨entry, hcipher⟩
    exact binaryLE_maskCode_of_cipherOf hcipher
  · intro hbinary
    exact
      exists_cipherOf_of_binaryLE_maskCode
        hlq hbinary

/-! ## A finite Diophantine certificate for `Code` -/

/-- The purely arithmetic certificate for membership in `Code`.
The `u₁` coordinate is retained because it is what makes the sparse
all-ones word Diophantine. -/
def CodeCertificate (length q a : ℕ) : Prop :=
  (length = 0 ∧ 1 < q ∧ a = 0) ∨
    (0 < length ∧ length + 1 < q ∧
      ∃ p u u₁ : ℕ,
        p + 1 = entryBase q ∧
        SeqsOfOnes length q u u₁ ∧
        DiophantineBitwise.BinaryLE a (p * u))

/-- Correctness of the finite `Code` certificate. -/
theorem code_iff_certificate
    {length q a : ℕ} :
    Code length q a ↔
      CodeCertificate length q a := by
  constructor
  · rintro ⟨entry, hcipher⟩
    rcases hcipher with ⟨hlq, hentry, hcode⟩
    by_cases hzero : length = 0
    · left
      subst length
      have ha : a = 0 := by
        simpa [SparseRadixCipher.encode] using hcode
      exact ⟨rfl, by omega, ha⟩
    · right
      have hlength : 0 < length :=
        Nat.pos_of_ne_zero hzero
      refine
        ⟨hlength, hlq, maxEntry q,
          sparseOnes length q,
          shiftedSparseOnes length q, ?_, ?_, ?_⟩
      · have hpositive : 0 < entryBase q := by
          simp [entryBase]
        simp only [maxEntry]
        omega
      · exact ⟨hlq, rfl, rfl⟩
      · have hmask :
            maskCode length q =
              maxEntry q * sparseOnes length q :=
          rfl
        rw [← hmask]
        exact
          binaryLE_maskCode_of_cipherOf
            ⟨hlq, hentry, hcode⟩
  · intro hcertificate
    rcases hcertificate with hempty | hnonempty
    · rcases hempty with ⟨rfl, hq, rfl⟩
      refine ⟨Fin.elim0, ?_⟩
      refine ⟨by omega, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · rw [SparseRadixCipher.encode_eq_sum]
        simp
    · rcases hnonempty with
        ⟨hlength, hlq, p, u, u₁,
          hp, hseq, hbinary⟩
      rcases hseq with ⟨hlq', hu, hu₁⟩
      have hpValue : p = maxEntry q := by
        have hpositive : 0 < entryBase q := by
          simp [entryBase]
        simp only [maxEntry]
        omega
      have hbinary' :
          DiophantineBitwise.BinaryLE
            a (maskCode length q) := by
        simpa only [maskCode, hpValue, hu] using hbinary
      exact
        exists_cipherOf_of_binaryLE_maskCode
          hlq hbinary'

/-- The nonempty certificate with witnesses `(p,u,u₁)` exposed as a
single finite vector. -/
def CodeCore
    (v : (Fin 3 ⊕ Fin 3) → ℕ) : Prop :=
  0 < v (Sum.inl 0) ∧
  v (Sum.inl 0) + 1 < v (Sum.inl 1) ∧
  v (Sum.inr 0) + 1 =
    entryBase (v (Sum.inl 1)) ∧
  SeqsOfOnes
    (v (Sum.inl 0)) (v (Sum.inl 1))
    (v (Sum.inr 1)) (v (Sum.inr 2)) ∧
  DiophantineBitwise.BinaryLE
    (v (Sum.inl 2))
    (v (Sum.inr 0) * v (Sum.inr 1))

theorem exists_codeCore_iff
    (v : Fin 3 → ℕ) :
    (∃ witness : Fin 3 → ℕ,
      CodeCore (Sum.elim v witness)) ↔
      (0 < v 0 ∧ v 0 + 1 < v 1 ∧
        ∃ p u u₁ : ℕ,
          p + 1 = entryBase (v 1) ∧
          SeqsOfOnes (v 0) (v 1) u u₁ ∧
          DiophantineBitwise.BinaryLE
            (v 2) (p * u)) := by
  constructor
  · rintro ⟨witness, h⟩
    exact
      ⟨h.1, h.2.1,
        witness 0, witness 1, witness 2,
        h.2.2⟩
  · rintro
      ⟨hlength, hlq, p, u, u₁,
        hp, hseq, hbinary⟩
    exact
      ⟨![p, u, u₁],
        hlength, hlq, hp, hseq, hbinary⟩

/-- The exposed nonempty `Code` certificate is Diophantine. -/
theorem codeCore_dioph :
    Dioph {v : (Fin 3 ⊕ Fin 3) → ℕ |
      CodeCore v} := by
  let lengthFn : ((Fin 3 ⊕ Fin 3) → ℕ) → ℕ :=
    fun v => v (Sum.inl 0)
  let qFn : ((Fin 3 ⊕ Fin 3) → ℕ) → ℕ :=
    fun v => v (Sum.inl 1)
  let aFn : ((Fin 3 ⊕ Fin 3) → ℕ) → ℕ :=
    fun v => v (Sum.inl 2)
  let pFn : ((Fin 3 ⊕ Fin 3) → ℕ) → ℕ :=
    fun v => v (Sum.inr 0)
  let uFn : ((Fin 3 ⊕ Fin 3) → ℕ) → ℕ :=
    fun v => v (Sum.inr 1)
  have hlength : Dioph.DiophFn lengthFn :=
    Dioph.proj_dioph (Sum.inl 0)
  have hq : Dioph.DiophFn qFn :=
    Dioph.proj_dioph (Sum.inl 1)
  have ha : Dioph.DiophFn aFn :=
    Dioph.proj_dioph (Sum.inl 2)
  have hp : Dioph.DiophFn pFn :=
    Dioph.proj_dioph (Sum.inr 0)
  have hu : Dioph.DiophFn uFn :=
    Dioph.proj_dioph (Sum.inr 1)
  have hzero :
      Dioph.DiophFn
        (fun _ : (Fin 3 ⊕ Fin 3) → ℕ => 0) :=
    Dioph.const_dioph 0
  have hone :
      Dioph.DiophFn
        (fun _ : (Fin 3 ⊕ Fin 3) → ℕ => 1) :=
    Dioph.const_dioph 1
  have htwo :
      Dioph.DiophFn
        (fun _ : (Fin 3 ⊕ Fin 3) → ℕ => 2) :=
    Dioph.const_dioph 2
  let lengthPlusOne := fun v => lengthFn v + 1
  have hlengthPlusOne : Dioph.DiophFn lengthPlusOne :=
    Dioph.add_dioph hlength hone
  let pPlusOne := fun v => pFn v + 1
  have hpPlusOne : Dioph.DiophFn pPlusOne :=
    Dioph.add_dioph hp hone
  let entryBaseFn := fun v => 2 ^ qFn v
  have hentryBase : Dioph.DiophFn entryBaseFn :=
    Dioph.pow_dioph htwo hq
  let pMulU := fun v => pFn v * uFn v
  have hpMulU : Dioph.DiophFn pMulU :=
    Dioph.mul_dioph hp hu
  have hPos :
      Dioph {v | 0 < lengthFn v} :=
    Dioph.lt_dioph hzero hlength
  have hLengthBound :
      Dioph {v | lengthPlusOne v < qFn v} :=
    Dioph.lt_dioph hlengthPlusOne hq
  have hMax :
      Dioph {v | pPlusOne v = entryBaseFn v} :=
    Dioph.eq_dioph hpPlusOne hentryBase
  have hSeq :
      Dioph {v : (Fin 3 ⊕ Fin 3) → ℕ |
        SeqsOfOnes
          (lengthFn v) (qFn v)
          (uFn v) (v (Sum.inr 2))} := by
    simpa only [lengthFn, qFn, uFn] using
      (Dioph.reindex_dioph
        (Fin 3 ⊕ Fin 3)
        ![Sum.inl 0, Sum.inl 1,
          Sum.inr 1, Sum.inr 2]
        seqsOfOnes_dioph)
  have hBinary :
      Dioph {v |
        DiophantineBitwise.BinaryLE
          (aFn v) (pMulU v)} :=
    DiophantineBitwise.binaryLE_dioph
      ha hpMulU
  have hAll :=
    hPos.inter
      (hLengthBound.inter
        (hMax.inter
          (hSeq.inter hBinary)))
  simpa only [CodeCore, Set.mem_inter_iff,
    Set.mem_setOf_eq, lengthFn, qFn, aFn,
    pFn, uFn, lengthPlusOne, pPlusOne,
    entryBaseFn, entryBase, pMulU] using hAll

/-- The finite certificate for `Code` is a Diophantine relation in the
visible variables `(length,q,a)`. -/
theorem codeCertificate_dioph :
    Dioph {v : Fin 3 → ℕ |
      CodeCertificate (v 0) (v 1) (v 2)} := by
  let lengthFn : (Fin 3 → ℕ) → ℕ :=
    fun v => v 0
  let qFn : (Fin 3 → ℕ) → ℕ :=
    fun v => v 1
  let aFn : (Fin 3 → ℕ) → ℕ :=
    fun v => v 2
  have hlength : Dioph.DiophFn lengthFn :=
    Dioph.proj_dioph 0
  have hq : Dioph.DiophFn qFn :=
    Dioph.proj_dioph 1
  have ha : Dioph.DiophFn aFn :=
    Dioph.proj_dioph 2
  have hzero :
      Dioph.DiophFn (fun _ : Fin 3 → ℕ => 0) :=
    Dioph.const_dioph 0
  have hone :
      Dioph.DiophFn (fun _ : Fin 3 → ℕ => 1) :=
    Dioph.const_dioph 1
  have hEmpty :
      Dioph {v : Fin 3 → ℕ |
        lengthFn v = 0 ∧ 1 < qFn v ∧
          aFn v = 0} :=
    (Dioph.eq_dioph hlength hzero).inter
      ((Dioph.lt_dioph hone hq).inter
        (Dioph.eq_dioph ha hzero))
  have hNonempty :
      Dioph {v : Fin 3 → ℕ |
        ∃ witness : Fin 3 → ℕ,
          CodeCore (Sum.elim v witness)} := by
    simpa only using
      (Dioph.ex_dioph codeCore_dioph)
  refine
    Dioph.ext (Dioph.union hEmpty hNonempty)
      fun v => ?_
  simp only [Set.mem_union, Set.mem_setOf_eq,
    lengthFn, qFn, aFn]
  rw [exists_codeCore_iff]
  rfl

/-- The semantic sparse-cipher `Code` predicate is Diophantine.  No
primitive-recursion or DPRM closure theorem is assumed here. -/
theorem code_dioph :
    Dioph {v : Fin 3 → ℕ |
      Code (v 0) (v 1) (v 2)} := by
  exact
    Dioph.ext codeCertificate_dioph fun v =>
      (code_iff_certificate
        (length := v 0) (q := v 1)
        (a := v 2)).symm

/-! ## Constant tuple ciphers -/

/-- `value` is the cipher of the constant tuple
`(coefficient, ..., coefficient)`. -/
def ConstCode
    (length q coefficient value : ℕ) : Prop :=
  ∃ entry : Fin length → ℕ,
    CipherOf length q entry value ∧
    ∀ i, entry i = coefficient

/-- Relative to a fixed valid cipher, `ConstCode` says exactly that
every represented coordinate equals the stated constant. -/
theorem constCode_spec
    {length q coefficient value : ℕ}
    {entry : Fin length → ℕ}
    (hentry : CipherOf length q entry value) :
    ConstCode length q coefficient value ↔
      ∀ i, entry i = coefficient := by
  constructor
  · rintro ⟨other, hother, hconstant⟩
    have hfunctions : entry = other :=
      hentry.entry_eq hother
    intro i
    rw [hfunctions]
    exact hconstant i
  · intro hconstant
    exact ⟨entry, hentry, hconstant⟩

/-- Arithmetic certificate for a constant tuple cipher. -/
def ConstCertificate
    (length q coefficient value : ℕ) : Prop :=
  (length = 0 ∧ 1 < q ∧ value = 0) ∨
    (0 < length ∧ length + 1 < q ∧
      ∃ p u u₁ : ℕ,
        p = entryBase q ∧
        coefficient < p ∧
        SeqsOfOnes length q u u₁ ∧
        value = coefficient * u)

/-- Correctness of the constant-tuple certificate.  The nonempty case
uses one actual coordinate to recover the bound on the repeated
coefficient; its numeric value follows from `encode_constant`. -/
theorem constCode_iff_certificate
    {length q coefficient value : ℕ} :
    ConstCode length q coefficient value ↔
      ConstCertificate length q coefficient value := by
  constructor
  · rintro ⟨entry, hcipher, hconstant⟩
    rcases hcipher with ⟨hlq, hentry, hvalue⟩
    by_cases hzero : length = 0
    · left
      subst length
      have hvalueZero : value = 0 := by
        rw [SparseRadixCipher.encode_eq_sum] at hvalue
        simpa using hvalue
      exact ⟨rfl, by omega, hvalueZero⟩
    · right
      have hlength : 0 < length :=
        Nat.pos_of_ne_zero hzero
      refine
        ⟨hlength, hlq, entryBase q,
          sparseOnes length q,
          shiftedSparseOnes length q,
          rfl, ?_, ⟨hlq, rfl, rfl⟩, ?_⟩
      · let first : Fin length := ⟨0, hlength⟩
        calc
          coefficient = entry first :=
            (hconstant first).symm
          _ < entryBase q :=
            hentry first
      · calc
          value =
              encode (cipherBase q) entry :=
            hvalue
          _ =
              encode (cipherBase q)
                (fun _ : Fin length => coefficient) := by
            congr 1
            funext i
            exact hconstant i
          _ = coefficient * sparseOnes length q :=
            encode_constant length q coefficient
  · intro hcertificate
    rcases hcertificate with hempty | hnonempty
    · rcases hempty with ⟨rfl, hq, rfl⟩
      refine ⟨Fin.elim0, ?_, ?_⟩
      · refine ⟨by omega, ?_, ?_⟩
        · intro i
          exact Fin.elim0 i
        · rw [SparseRadixCipher.encode_eq_sum]
          simp
      · intro i
        exact Fin.elim0 i
    · rcases hnonempty with
        ⟨hlength, hlq, p, u, u₁,
          hp, hcoefficient, hseq, hvalue⟩
      rcases hseq with ⟨hlq', hu, hu₁⟩
      refine
        ⟨(fun _ : Fin length => coefficient),
          ?_, fun _ => rfl⟩
      refine ⟨hlq, ?_, ?_⟩
      · intro i
        simpa only [hp] using hcoefficient
      · calc
          value =
              coefficient * u :=
            hvalue
          _ =
              coefficient * sparseOnes length q := by
            rw [hu]
          _ =
              encode (cipherBase q)
                (fun _ : Fin length => coefficient) :=
            (encode_constant
              length q coefficient).symm

/-- The nonempty constant-tuple certificate with witnesses
`(p,u,u₁)` exposed.  Visible coordinates are
`(length,q,coefficient,value)`. -/
def ConstCore
    (v : (Fin 4 ⊕ Fin 3) → ℕ) : Prop :=
  0 < v (Sum.inl 0) ∧
  v (Sum.inl 0) + 1 < v (Sum.inl 1) ∧
  v (Sum.inr 0) =
    entryBase (v (Sum.inl 1)) ∧
  v (Sum.inl 2) < v (Sum.inr 0) ∧
  SeqsOfOnes
    (v (Sum.inl 0)) (v (Sum.inl 1))
    (v (Sum.inr 1)) (v (Sum.inr 2)) ∧
  v (Sum.inl 3) =
    v (Sum.inl 2) * v (Sum.inr 1)

theorem exists_constCore_iff
    (v : Fin 4 → ℕ) :
    (∃ witness : Fin 3 → ℕ,
      ConstCore (Sum.elim v witness)) ↔
      (0 < v 0 ∧ v 0 + 1 < v 1 ∧
        ∃ p u u₁ : ℕ,
          p = entryBase (v 1) ∧
          v 2 < p ∧
          SeqsOfOnes (v 0) (v 1) u u₁ ∧
          v 3 = v 2 * u) := by
  constructor
  · rintro ⟨witness, h⟩
    exact
      ⟨h.1, h.2.1,
        witness 0, witness 1, witness 2,
        h.2.2⟩
  · rintro
      ⟨hlength, hlq, p, u, u₁,
        hp, hcoefficient, hseq, hvalue⟩
    exact
      ⟨![p, u, u₁],
        hlength, hlq, hp, hcoefficient,
        hseq, hvalue⟩

/-- The exposed nonempty constant-tuple certificate is
Diophantine. -/
theorem constCore_dioph :
    Dioph {v : (Fin 4 ⊕ Fin 3) → ℕ |
      ConstCore v} := by
  let lengthFn : ((Fin 4 ⊕ Fin 3) → ℕ) → ℕ :=
    fun v => v (Sum.inl 0)
  let qFn : ((Fin 4 ⊕ Fin 3) → ℕ) → ℕ :=
    fun v => v (Sum.inl 1)
  let coefficientFn :
      ((Fin 4 ⊕ Fin 3) → ℕ) → ℕ :=
    fun v => v (Sum.inl 2)
  let valueFn : ((Fin 4 ⊕ Fin 3) → ℕ) → ℕ :=
    fun v => v (Sum.inl 3)
  let pFn : ((Fin 4 ⊕ Fin 3) → ℕ) → ℕ :=
    fun v => v (Sum.inr 0)
  let uFn : ((Fin 4 ⊕ Fin 3) → ℕ) → ℕ :=
    fun v => v (Sum.inr 1)
  have hlength : Dioph.DiophFn lengthFn :=
    Dioph.proj_dioph (Sum.inl 0)
  have hq : Dioph.DiophFn qFn :=
    Dioph.proj_dioph (Sum.inl 1)
  have hcoefficient :
      Dioph.DiophFn coefficientFn :=
    Dioph.proj_dioph (Sum.inl 2)
  have hvalue : Dioph.DiophFn valueFn :=
    Dioph.proj_dioph (Sum.inl 3)
  have hp : Dioph.DiophFn pFn :=
    Dioph.proj_dioph (Sum.inr 0)
  have hu : Dioph.DiophFn uFn :=
    Dioph.proj_dioph (Sum.inr 1)
  have hzero :
      Dioph.DiophFn
        (fun _ : (Fin 4 ⊕ Fin 3) → ℕ => 0) :=
    Dioph.const_dioph 0
  have hone :
      Dioph.DiophFn
        (fun _ : (Fin 4 ⊕ Fin 3) → ℕ => 1) :=
    Dioph.const_dioph 1
  have htwo :
      Dioph.DiophFn
        (fun _ : (Fin 4 ⊕ Fin 3) → ℕ => 2) :=
    Dioph.const_dioph 2
  let lengthPlusOne := fun v => lengthFn v + 1
  have hlengthPlusOne :
      Dioph.DiophFn lengthPlusOne :=
    Dioph.add_dioph hlength hone
  let entryBaseFn := fun v => 2 ^ qFn v
  have hentryBase : Dioph.DiophFn entryBaseFn :=
    Dioph.pow_dioph htwo hq
  let scaled := fun v =>
    coefficientFn v * uFn v
  have hscaled : Dioph.DiophFn scaled :=
    Dioph.mul_dioph hcoefficient hu
  have hPos :
      Dioph {v | 0 < lengthFn v} :=
    Dioph.lt_dioph hzero hlength
  have hLengthBound :
      Dioph {v | lengthPlusOne v < qFn v} :=
    Dioph.lt_dioph hlengthPlusOne hq
  have hBase :
      Dioph {v | pFn v = entryBaseFn v} :=
    Dioph.eq_dioph hp hentryBase
  have hCoefficientBound :
      Dioph {v | coefficientFn v < pFn v} :=
    Dioph.lt_dioph hcoefficient hp
  have hSeq :
      Dioph {v : (Fin 4 ⊕ Fin 3) → ℕ |
        SeqsOfOnes
          (lengthFn v) (qFn v)
          (uFn v) (v (Sum.inr 2))} := by
    simpa only [lengthFn, qFn, uFn] using
      (Dioph.reindex_dioph
        (Fin 4 ⊕ Fin 3)
        ![Sum.inl 0, Sum.inl 1,
          Sum.inr 1, Sum.inr 2]
        seqsOfOnes_dioph)
  have hValue :
      Dioph {v | valueFn v = scaled v} :=
    Dioph.eq_dioph hvalue hscaled
  have hAll :=
    hPos.inter
      (hLengthBound.inter
        (hBase.inter
          (hCoefficientBound.inter
            (hSeq.inter hValue))))
  simpa only [ConstCore, Set.mem_inter_iff,
    Set.mem_setOf_eq, lengthFn, qFn,
    coefficientFn, valueFn, pFn, uFn,
    lengthPlusOne, entryBaseFn, entryBase,
    scaled] using hAll

/-- The finite constant-tuple certificate is Diophantine in its four
visible parameters. -/
theorem constCertificate_dioph :
    Dioph {v : Fin 4 → ℕ |
      ConstCertificate
        (v 0) (v 1) (v 2) (v 3)} := by
  let lengthFn : (Fin 4 → ℕ) → ℕ :=
    fun v => v 0
  let qFn : (Fin 4 → ℕ) → ℕ :=
    fun v => v 1
  let valueFn : (Fin 4 → ℕ) → ℕ :=
    fun v => v 3
  have hlength : Dioph.DiophFn lengthFn :=
    Dioph.proj_dioph 0
  have hq : Dioph.DiophFn qFn :=
    Dioph.proj_dioph 1
  have hvalue : Dioph.DiophFn valueFn :=
    Dioph.proj_dioph 3
  have hzero :
      Dioph.DiophFn (fun _ : Fin 4 → ℕ => 0) :=
    Dioph.const_dioph 0
  have hone :
      Dioph.DiophFn (fun _ : Fin 4 → ℕ => 1) :=
    Dioph.const_dioph 1
  have hEmpty :
      Dioph {v : Fin 4 → ℕ |
        lengthFn v = 0 ∧ 1 < qFn v ∧
          valueFn v = 0} :=
    (Dioph.eq_dioph hlength hzero).inter
      ((Dioph.lt_dioph hone hq).inter
        (Dioph.eq_dioph hvalue hzero))
  have hNonempty :
      Dioph {v : Fin 4 → ℕ |
        ∃ witness : Fin 3 → ℕ,
          ConstCore (Sum.elim v witness)} := by
    simpa only using
      (Dioph.ex_dioph constCore_dioph)
  refine
    Dioph.ext (Dioph.union hEmpty hNonempty)
      fun v => ?_
  simp only [Set.mem_union, Set.mem_setOf_eq,
    lengthFn, qFn, valueFn]
  rw [exists_constCore_iff]
  rfl

/-- Ciphers of constant finite tuples form a Diophantine relation.
This is the formal counterpart of `Const_dio`. -/
theorem constCode_dioph :
    Dioph {v : Fin 4 → ℕ |
      ConstCode (v 0) (v 1) (v 2) (v 3)} := by
  exact
    Dioph.ext constCertificate_dioph fun v =>
      (constCode_iff_certificate
        (length := v 0) (q := v 1)
        (coefficient := v 2)
        (value := v 3)).symm

end SparseCipherCode

end HGAS
