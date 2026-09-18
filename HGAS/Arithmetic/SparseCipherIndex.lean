import HGAS.Arithmetic.SparseCipherOperations
import Mathlib.Tactic

/-!
# The sparse cipher of the index sequence

The bounded-universal compiler needs, in addition to arbitrary and
constant tuple ciphers, the distinguished cipher of

```
0, 1, ..., length - 1.
```

Writing this finite sum directly would leave a variable-length
summation.  Matiyasevich's cipher recognizes it instead by two endpoint
recurrences involving a second arbitrary cipher.  This file proves that
certificate correct.

The proof is most transparent at the tuple level.  If `f` and `g` are
the tuples represented by the two arbitrary codes, the first masked
product says

```
snoc f length = cons 0 g,
```

while the second endpoint equation says

```
snoc (fun i => f i + 1) 1 = snoc g 1.
```

Hence `f 0 = 0` and `f (i+1) = f i + 1`, so `f i = i`.
The numerical equations below are exactly sparse encodings of those
two intuitive identities.

`codeNat_iff_certificate` corresponds to `CodeNat_dio` in the
Coq/Undecidability formalization of DPRM.
-/

namespace HGAS

namespace SparseCipherIndex

open SparseRadixCipher
open SparseOnesCipher
open SparseCipherCode
open SparseCipherOperations

/-- The code of the increasing index tuple. -/
def CodeNat (length q value : ℕ) : Prop :=
  CipherOf length q
    (fun i : Fin length => i)
    value

/-- The finite arithmetic index-word certificate. -/
def CodeNatCertificate
    (length q value : ℕ) : Prop :=
  (length = 0 ∧ 1 < q ∧ value = 0) ∨
    (0 < length ∧
      ∃ next ones shifted base endpointExponent
          endpoint predecessor : ℕ,
        base = cipherBase q ∧
        predecessor + 1 = base ∧
        endpointExponent = slot length ∧
        endpoint = base ^ endpointExponent ∧
        SeqsOfOnes length q ones shifted ∧
        Code length q value ∧
        Code length q next ∧
        value + length * endpoint =
          (next * ones) &&&
            (predecessor * shifted) ∧
        value + shifted + base * base =
          next + endpoint)

/-- Appending its final value to the identity tuple gives the identity
tuple of successor length. -/
theorem snoc_finVal (length : ℕ) :
    Fin.snoc (fun i : Fin length => (i : ℕ)) length =
      fun i : Fin (length + 1) => (i : ℕ) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp

/-- Prepending zero to the successor tuple gives the same identity
tuple of successor length. -/
theorem cons_zero_succVal (length : ℕ) :
    (Fin.cons 0
        (fun i : Fin length => (i : ℕ) + 1) :
      Fin (length + 1) → ℕ) =
      fun i : Fin (length + 1) => (i : ℕ) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp

theorem snoc_finVal_eq_cons_zero_succVal
    (length : ℕ) :
    (Fin.snoc
        (fun i : Fin length => (i : ℕ)) length :
      Fin (length + 1) → ℕ) =
      (Fin.cons 0
        (fun i : Fin length => (i : ℕ) + 1) :
      Fin (length + 1) → ℕ) := by
  rw [snoc_finVal, cons_zero_succVal]

theorem successorEntry_lt_entryBase
    {length q : ℕ} (hlq : length + 1 < q)
    (i : Fin length) :
    (i : ℕ) + 1 < entryBase q := by
  have hq : q < 2 ^ q :=
    Nat.lt_two_pow_self
  exact (by omega : (i : ℕ) + 1 < q).trans hq

theorem length_lt_cipherBase
    {length q : ℕ} (hlq : length + 1 < q) :
    length < cipherBase q := by
  have hq : q < entryBase q := by
    exact Nat.lt_two_pow_self
  exact
    (by omega : length < q)
      |>.trans hq
      |>.trans_le (entryBase_le_cipherBase q)

theorem one_lt_cipherBase_of_length_bound
    {length q : ℕ} (hlq : length + 1 < q) :
    1 < cipherBase q := by
  have hq : 0 < q := by omega
  exact cipherBase_ge_two hq

theorem entryBase_lt_cipherBase
    {q : ℕ} (hq : 0 < q) :
    entryBase q < cipherBase q := by
  rw [entryBase, cipherBase]
  exact
    Nat.pow_lt_pow_right (by norm_num)
      (by omega)

/-- A concrete index cipher supplies the finite recurrence
certificate. -/
theorem CodeNat.toCertificate
    {length q value : ℕ}
    (hcodeNat : CodeNat length q value) :
    CodeNatCertificate length q value := by
  rcases hcodeNat with
    ⟨hlq, hindexBound, hvalue⟩
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
    let successor : Fin length → ℕ :=
      fun i => (i : ℕ) + 1
    let next :=
      encode (cipherBase q) successor
    have hsuccessorCipher :
        CipherOf length q successor next := by
      exact
        ⟨hlq,
          successorEntry_lt_entryBase hlq,
          rfl⟩
    refine
      ⟨hlength, next,
        sparseOnes length q,
        shiftedSparseOnes length q,
        cipherBase q, slot length,
        cipherBase q ^ slot length,
        cipherBase q - 1,
        rfl, ?_, rfl, rfl,
        ⟨hlq, rfl, rfl⟩,
        ⟨(fun i : Fin length => (i : ℕ)),
          hlq, hindexBound, hvalue⟩,
        ⟨successor, hsuccessorCipher⟩,
        ?_, ?_⟩
    · have hpositive := cipherBase_pos q
      omega
    · calc
        value +
              length *
                cipherBase q ^ slot length =
            encode (cipherBase q)
              (Fin.snoc
                (fun i : Fin length => (i : ℕ))
                length) := by
          rw [SparseRadixCipher.encode_snoc]
          exact congrArg
            (fun n =>
              n + length *
                cipherBase q ^ slot length)
            hvalue
        _ =
            encode (cipherBase q)
              (Fin.cons 0 successor) := by
          congr 1
          exact
            snoc_finVal_eq_cons_zero_succVal
              length
        _ =
            diagonalProductCode (4 * q)
              successor
              (fun _ : Fin length => 1) := by
          exact
            (diagonalProductCode_right_one_eq_encode_cons
              (4 * q) successor).symm
        _ =
            (next * sparseOnes length q) &&&
              ((cipherBase q - 1) *
                shiftedSparseOnes length q) := by
          exact
            (land_product_cipherMask
              hsuccessorCipher
              (ones_cipherOf hlq)).symm
    · calc
        value + shiftedSparseOnes length q +
              cipherBase q * cipherBase q =
            value +
              (cipherBase q ^ 2 +
                shiftedSparseOnes length q) := by
          rw [pow_two]
          omega
        _ =
            value +
              (sparseOnes length q +
                cipherBase q ^ slot length) := by
          rw [shifted_add_endpoint]
        _ =
            (value + sparseOnes length q) +
              cipherBase q ^ slot length := by
          omega
        _ =
            (encode (cipherBase q)
                (fun i : Fin length => (i : ℕ)) +
              encode (cipherBase q)
                (fun _ : Fin length => 1)) +
              cipherBase q ^ slot length := by
          rw [← hvalue]
          rfl
        _ =
            encode (cipherBase q) successor +
              cipherBase q ^ slot length := by
          rw [← SparseRadixCipher.encode_add]
        _ =
            next + cipherBase q ^ slot length := by
          rfl

/-- The first recurrence equation, after decoding, equates an appended
tuple to a zero-prepended tuple. -/
theorem first_tuple_identity_of_certificate
    {length q value next : ℕ}
    {entry successor : Fin length → ℕ}
    (hvalue :
      CipherOf length q entry value)
    (hnext :
      CipherOf length q successor next)
    (hfirst :
      value + length * cipherBase q ^ slot length =
        (next * sparseOnes length q) &&&
          ((cipherBase q - 1) *
            shiftedSparseOnes length q)) :
    (Fin.snoc entry length :
      Fin (length + 1) → ℕ) =
      (Fin.cons 0 successor :
        Fin (length + 1) → ℕ) := by
  have hlq : length + 1 < q :=
    hvalue.1
  have hencoded :
      encode (cipherBase q)
          (Fin.snoc entry length) =
        encode (cipherBase q)
          (Fin.cons 0 successor) := by
    calc
      encode (cipherBase q)
            (Fin.snoc entry length) =
          value +
            length * cipherBase q ^ slot length := by
        rw [SparseRadixCipher.encode_snoc,
          ← hvalue.2.2]
      _ =
          (next * sparseOnes length q) &&&
            ((cipherBase q - 1) *
              shiftedSparseOnes length q) :=
        hfirst
      _ =
          diagonalProductCode (4 * q)
            successor
            (fun _ : Fin length => 1) :=
        land_product_cipherMask
          hnext (ones_cipherOf hlq)
      _ =
          encode (cipherBase q)
            (Fin.cons 0 successor) :=
        diagonalProductCode_right_one_eq_encode_cons
          (4 * q) successor
  apply
    SparseRadixCipher.encode_injective
      (cipherBase_pos q)
      (left := Fin.snoc entry length)
      (right := Fin.cons 0 successor)
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using length_lt_cipherBase hlq
    · simpa using
        (hvalue.2.1 j).trans_le
          (entryBase_le_cipherBase q)
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [cipherBase]
    · simpa using
        (hnext.2.1 j).trans_le
          (entryBase_le_cipherBase q)
  · exact hencoded

/-- The second endpoint equation, after decoding, says that the second
tuple is the pointwise successor of the first. -/
theorem second_tuple_identity_of_certificate
    {length q value next : ℕ}
    {entry successor : Fin length → ℕ}
    (hvalue :
      CipherOf length q entry value)
    (hnext :
      CipherOf length q successor next)
    (hsecond :
      value + shiftedSparseOnes length q +
          cipherBase q * cipherBase q =
        next + cipherBase q ^ slot length) :
    (fun i => entry i + 1) = successor := by
  have hlq : length + 1 < q :=
    hvalue.1
  have hencoded :
      encode (cipherBase q)
          (Fin.snoc (fun i => entry i + 1) 1) =
        encode (cipherBase q)
          (Fin.snoc successor 1 :
            Fin (length + 1) → ℕ) := by
    calc
      encode (cipherBase q)
            (Fin.snoc (fun i => entry i + 1) 1) =
          (encode (cipherBase q) entry +
              sparseOnes length q) +
            cipherBase q ^ slot length := by
        rw [SparseRadixCipher.encode_snoc,
          SparseRadixCipher.encode_add]
        rw [show
          encode (cipherBase q)
              (fun _ : Fin length => 1) =
            sparseOnes length q from rfl]
        simp
      _ =
          value +
            (sparseOnes length q +
              cipherBase q ^ slot length) := by
        rw [hvalue.2.2]
        omega
      _ =
          value +
            (cipherBase q ^ 2 +
              shiftedSparseOnes length q) := by
        rw [shifted_add_endpoint]
      _ =
          value + shiftedSparseOnes length q +
            cipherBase q * cipherBase q := by
        rw [pow_two]
        omega
      _ =
          next + cipherBase q ^ slot length :=
        hsecond
      _ =
          encode (cipherBase q)
            (Fin.snoc successor 1) := by
        rw [SparseRadixCipher.encode_snoc,
          ← hnext.2.2]
        simp
  have hfunctions :
      (Fin.snoc (fun i => entry i + 1) 1 :
        Fin (length + 1) → ℕ) =
        (Fin.snoc successor 1 :
          Fin (length + 1) → ℕ) := by
    apply
      SparseRadixCipher.encode_injective
        (cipherBase_pos q)
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using
          one_lt_cipherBase_of_length_bound hlq
      · have hle :
            entry j + 1 ≤ entryBase q :=
          Nat.succ_le_of_lt (hvalue.2.1 j)
        have hq : 0 < q := by omega
        simpa using
          hle.trans_lt (entryBase_lt_cipherBase hq)
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using
          one_lt_cipherBase_of_length_bound hlq
      · simpa using
          (hnext.2.1 j).trans_le
            (entryBase_le_cipherBase q)
    · exact hencoded
  exact
    Fin.snoc_left_injective 1 hfunctions

/-- The two decoded recurrences uniquely force the index tuple. -/
theorem entry_eq_finVal_of_recurrences
    {length : ℕ} (hlength : 0 < length)
    {entry successor : Fin length → ℕ}
    (hfirst :
      (Fin.snoc entry length :
        Fin (length + 1) → ℕ) =
        (Fin.cons 0 successor :
          Fin (length + 1) → ℕ))
    (hsecond :
      (fun i => entry i + 1) = successor) :
    entry = fun i : Fin length => (i : ℕ) := by
  let zero : Fin length := ⟨0, hlength⟩
  have hzero : entry zero = 0 := by
    have h :=
      congrFun hfirst zero.castSucc
    rw [Fin.snoc_castSucc] at h
    have hzeroIndex :
        zero.castSucc = (0 : Fin (length + 1)) := by
      ext
      rfl
    rw [hzeroIndex, Fin.cons_zero] at h
    exact h
  have hshift :
      ∀ (i : Fin length),
        ∀ hi : (i : ℕ) + 1 < length,
        entry ⟨(i : ℕ) + 1, hi⟩ =
          successor i := by
    intro i hi
    let nextIndex : Fin length :=
      ⟨(i : ℕ) + 1, hi⟩
    have h :=
      congrFun hfirst i.succ
    rw [Fin.cons_succ] at h
    have heq :
        i.succ = nextIndex.castSucc := by
      ext
      rfl
    rw [heq, Fin.snoc_castSucc] at h
    exact h
  funext i
  have hinduction :
      ∀ n : ℕ, ∀ hn : n < length,
        entry ⟨n, hn⟩ = n := by
    intro n
    induction n with
    | zero =>
        intro hn
        simpa [zero] using hzero
    | succ n ih =>
        intro hn
        have hnPrevious : n < length := by
          omega
        let previous : Fin length :=
          ⟨n, hnPrevious⟩
        have hstep :=
          hshift previous hn
        have hsuccessor :=
          congrFun hsecond previous
        calc
          entry ⟨n + 1, hn⟩ =
              successor previous :=
            hstep
          _ = entry previous + 1 :=
            hsuccessor.symm
          _ = n + 1 := by
            rw [ih hnPrevious]
  exact hinduction i i.isLt

/-- Every finite arithmetic certificate reconstructs the intended
increasing index cipher. -/
theorem CodeNatCertificate.toCodeNat
    {length q value : ℕ}
    (hcertificate :
      CodeNatCertificate length q value) :
    CodeNat length q value := by
  rcases hcertificate with hempty | hnonempty
  · rcases hempty with ⟨rfl, hq, rfl⟩
    refine ⟨by omega, ?_, ?_⟩
    · intro i
      exact Fin.elim0 i
    · rw [SparseRadixCipher.encode_eq_sum]
      simp
  · rcases hnonempty with
      ⟨hlength, next, ones, shifted, base,
        endpointExponent, endpoint, predecessor,
        hbase, hpredecessor, hendpointExponent,
        hendpoint, hseq, hvalueCode, hnextCode,
        hfirst, hsecond⟩
    rcases hseq with ⟨hlq, hones, hshifted⟩
    rcases hvalueCode with ⟨entry, hentry⟩
    rcases hnextCode with ⟨successor, hsuccessor⟩
    have hbasePositive := cipherBase_pos q
    have hpredecessorValue :
        predecessor = cipherBase q - 1 := by
      omega
    have hfirst' :
        value +
              length * cipherBase q ^ slot length =
            (next * sparseOnes length q) &&&
              ((cipherBase q - 1) *
                shiftedSparseOnes length q) := by
      simpa only [hbase, hendpointExponent,
        hendpoint, hones, hshifted,
        hpredecessorValue] using hfirst
    have hsecond' :
        value + shiftedSparseOnes length q +
              cipherBase q * cipherBase q =
            next + cipherBase q ^ slot length := by
      simpa only [hbase, hendpointExponent,
        hendpoint, hshifted] using hsecond
    have hfirstTuple :=
      first_tuple_identity_of_certificate
        hentry hsuccessor hfirst'
    have hsecondTuple :=
      second_tuple_identity_of_certificate
        hentry hsuccessor hsecond'
    have hentryValue :=
      entry_eq_finVal_of_recurrences
        hlength hfirstTuple hsecondTuple
    simpa only [CodeNat, hentryValue] using hentry

/-- Exact correctness of the index-word certificate. -/
theorem codeNat_iff_certificate
    {length q value : ℕ} :
    CodeNat length q value ↔
      CodeNatCertificate length q value :=
  ⟨CodeNat.toCertificate,
    CodeNatCertificate.toCodeNat⟩

/-! ## Diophantine closure -/

/-- The nonempty index-word certificate with its seven witnesses
exposed.  Visible coordinates are `(length,q,value)`. -/
def CodeNatCore
    (v : (Fin 3 ⊕ Fin 7) → ℕ) : Prop :=
  0 < v (Sum.inl 0) ∧
  v (Sum.inr 3) =
    cipherBase (v (Sum.inl 1)) ∧
  v (Sum.inr 6) + 1 = v (Sum.inr 3) ∧
  v (Sum.inr 4) = slot (v (Sum.inl 0)) ∧
  v (Sum.inr 5) =
    v (Sum.inr 3) ^ v (Sum.inr 4) ∧
  SeqsOfOnes
    (v (Sum.inl 0)) (v (Sum.inl 1))
    (v (Sum.inr 1)) (v (Sum.inr 2)) ∧
  Code
    (v (Sum.inl 0)) (v (Sum.inl 1))
    (v (Sum.inl 2)) ∧
  Code
    (v (Sum.inl 0)) (v (Sum.inl 1))
    (v (Sum.inr 0)) ∧
  v (Sum.inl 2) +
      v (Sum.inl 0) * v (Sum.inr 5) =
    (v (Sum.inr 0) * v (Sum.inr 1)) &&&
      (v (Sum.inr 6) * v (Sum.inr 2)) ∧
  v (Sum.inl 2) + v (Sum.inr 2) +
      v (Sum.inr 3) * v (Sum.inr 3) =
    v (Sum.inr 0) + v (Sum.inr 5)

theorem exists_codeNatCore_iff
    (v : Fin 3 → ℕ) :
    (∃ witness : Fin 7 → ℕ,
      CodeNatCore (Sum.elim v witness)) ↔
      (0 < v 0 ∧
        ∃ next ones shifted base endpointExponent
            endpoint predecessor : ℕ,
          base = cipherBase (v 1) ∧
          predecessor + 1 = base ∧
          endpointExponent = slot (v 0) ∧
          endpoint = base ^ endpointExponent ∧
          SeqsOfOnes (v 0) (v 1)
            ones shifted ∧
          Code (v 0) (v 1) (v 2) ∧
          Code (v 0) (v 1) next ∧
          v 2 + v 0 * endpoint =
            (next * ones) &&&
              (predecessor * shifted) ∧
          v 2 + shifted + base * base =
            next + endpoint) := by
  constructor
  · rintro ⟨witness, h⟩
    exact
      ⟨h.1,
        witness 0, witness 1, witness 2,
        witness 3, witness 4, witness 5,
        witness 6, h.2⟩
  · rintro
      ⟨hlength, next, ones, shifted, base,
        endpointExponent, endpoint, predecessor,
        hbase, hpredecessor, hexponent,
        hendpoint, hseq, hvalueCode, hnextCode,
        hfirst, hsecond⟩
    exact
      ⟨![next, ones, shifted, base,
          endpointExponent, endpoint, predecessor],
        hlength, hbase, hpredecessor, hexponent,
        hendpoint, hseq, hvalueCode, hnextCode,
        hfirst, hsecond⟩

/-- The exposed nonempty index-word certificate is Diophantine. -/
theorem codeNatCore_dioph :
    Dioph {v : (Fin 3 ⊕ Fin 7) → ℕ |
      CodeNatCore v} := by
  let lengthFn : ((Fin 3 ⊕ Fin 7) → ℕ) → ℕ :=
    fun v => v (Sum.inl 0)
  let qFn : ((Fin 3 ⊕ Fin 7) → ℕ) → ℕ :=
    fun v => v (Sum.inl 1)
  let valueFn : ((Fin 3 ⊕ Fin 7) → ℕ) → ℕ :=
    fun v => v (Sum.inl 2)
  let nextFn : ((Fin 3 ⊕ Fin 7) → ℕ) → ℕ :=
    fun v => v (Sum.inr 0)
  let onesFn : ((Fin 3 ⊕ Fin 7) → ℕ) → ℕ :=
    fun v => v (Sum.inr 1)
  let shiftedFn : ((Fin 3 ⊕ Fin 7) → ℕ) → ℕ :=
    fun v => v (Sum.inr 2)
  let baseFn : ((Fin 3 ⊕ Fin 7) → ℕ) → ℕ :=
    fun v => v (Sum.inr 3)
  let endpointExponentFn :
      ((Fin 3 ⊕ Fin 7) → ℕ) → ℕ :=
    fun v => v (Sum.inr 4)
  let endpointFn :
      ((Fin 3 ⊕ Fin 7) → ℕ) → ℕ :=
    fun v => v (Sum.inr 5)
  let predecessorFn :
      ((Fin 3 ⊕ Fin 7) → ℕ) → ℕ :=
    fun v => v (Sum.inr 6)
  have hlength : Dioph.DiophFn lengthFn :=
    Dioph.proj_dioph (Sum.inl 0)
  have hq : Dioph.DiophFn qFn :=
    Dioph.proj_dioph (Sum.inl 1)
  have hvalue : Dioph.DiophFn valueFn :=
    Dioph.proj_dioph (Sum.inl 2)
  have hnext : Dioph.DiophFn nextFn :=
    Dioph.proj_dioph (Sum.inr 0)
  have hones : Dioph.DiophFn onesFn :=
    Dioph.proj_dioph (Sum.inr 1)
  have hshifted : Dioph.DiophFn shiftedFn :=
    Dioph.proj_dioph (Sum.inr 2)
  have hbase : Dioph.DiophFn baseFn :=
    Dioph.proj_dioph (Sum.inr 3)
  have hendpointExponent :
      Dioph.DiophFn endpointExponentFn :=
    Dioph.proj_dioph (Sum.inr 4)
  have hendpoint : Dioph.DiophFn endpointFn :=
    Dioph.proj_dioph (Sum.inr 5)
  have hpredecessor :
      Dioph.DiophFn predecessorFn :=
    Dioph.proj_dioph (Sum.inr 6)
  have hzero :
      Dioph.DiophFn
        (fun _ : (Fin 3 ⊕ Fin 7) → ℕ => 0) :=
    Dioph.const_dioph 0
  have hone :
      Dioph.DiophFn
        (fun _ : (Fin 3 ⊕ Fin 7) → ℕ => 1) :=
    Dioph.const_dioph 1
  have htwo :
      Dioph.DiophFn
        (fun _ : (Fin 3 ⊕ Fin 7) → ℕ => 2) :=
    Dioph.const_dioph 2
  have hfour :
      Dioph.DiophFn
        (fun _ : (Fin 3 ⊕ Fin 7) → ℕ => 4) :=
    Dioph.const_dioph 4
  let fourQ := fun v => 4 * qFn v
  have hfourQ : Dioph.DiophFn fourQ :=
    Dioph.mul_dioph hfour hq
  let cipherBaseFn := fun v => 2 ^ fourQ v
  have hcipherBase :
      Dioph.DiophFn cipherBaseFn :=
    Dioph.pow_dioph htwo hfourQ
  let predecessorPlusOne :=
    fun v => predecessorFn v + 1
  have hpredecessorPlusOne :
      Dioph.DiophFn predecessorPlusOne :=
    Dioph.add_dioph hpredecessor hone
  let lengthPlusOne := fun v => lengthFn v + 1
  have hlengthPlusOne :
      Dioph.DiophFn lengthPlusOne :=
    Dioph.add_dioph hlength hone
  let slotFn := fun v => 2 ^ lengthPlusOne v
  have hslot : Dioph.DiophFn slotFn :=
    Dioph.pow_dioph htwo hlengthPlusOne
  let endpointPower :=
    fun v => baseFn v ^ endpointExponentFn v
  have hendpointPower :
      Dioph.DiophFn endpointPower :=
    Dioph.pow_dioph hbase hendpointExponent
  let lengthTimesEndpoint :=
    fun v => lengthFn v * endpointFn v
  have hlengthTimesEndpoint :
      Dioph.DiophFn lengthTimesEndpoint :=
    Dioph.mul_dioph hlength hendpoint
  let firstLeft :=
    fun v => valueFn v + lengthTimesEndpoint v
  have hfirstLeft : Dioph.DiophFn firstLeft :=
    Dioph.add_dioph hvalue hlengthTimesEndpoint
  let nextTimesOnes :=
    fun v => nextFn v * onesFn v
  have hnextTimesOnes :
      Dioph.DiophFn nextTimesOnes :=
    Dioph.mul_dioph hnext hones
  let predecessorTimesShifted :=
    fun v => predecessorFn v * shiftedFn v
  have hpredecessorTimesShifted :
      Dioph.DiophFn predecessorTimesShifted :=
    Dioph.mul_dioph hpredecessor hshifted
  let firstRight :=
    fun v =>
      nextTimesOnes v &&&
        predecessorTimesShifted v
  have hfirstRight : Dioph.DiophFn firstRight :=
    DiophantineBitwise.land_diophFn
      hnextTimesOnes hpredecessorTimesShifted
  let valuePlusShifted :=
    fun v => valueFn v + shiftedFn v
  have hvaluePlusShifted :
      Dioph.DiophFn valuePlusShifted :=
    Dioph.add_dioph hvalue hshifted
  let baseSquare := fun v => baseFn v * baseFn v
  have hbaseSquare : Dioph.DiophFn baseSquare :=
    Dioph.mul_dioph hbase hbase
  let secondLeft :=
    fun v => valuePlusShifted v + baseSquare v
  have hsecondLeft : Dioph.DiophFn secondLeft :=
    Dioph.add_dioph hvaluePlusShifted hbaseSquare
  let secondRight :=
    fun v => nextFn v + endpointFn v
  have hsecondRight : Dioph.DiophFn secondRight :=
    Dioph.add_dioph hnext hendpoint
  have hPos :
      Dioph {v | 0 < lengthFn v} :=
    Dioph.lt_dioph hzero hlength
  have hBase :
      Dioph {v | baseFn v = cipherBaseFn v} :=
    Dioph.eq_dioph hbase hcipherBase
  have hPredecessor :
      Dioph {v |
        predecessorPlusOne v = baseFn v} :=
    Dioph.eq_dioph hpredecessorPlusOne hbase
  have hEndpointExponent :
      Dioph {v |
        endpointExponentFn v = slotFn v} :=
    Dioph.eq_dioph hendpointExponent hslot
  have hEndpoint :
      Dioph {v |
        endpointFn v = endpointPower v} :=
    Dioph.eq_dioph hendpoint hendpointPower
  have hSeq :
      Dioph {v : (Fin 3 ⊕ Fin 7) → ℕ |
        SeqsOfOnes
          (lengthFn v) (qFn v)
          (onesFn v) (shiftedFn v)} := by
    simpa only [lengthFn, qFn, onesFn, shiftedFn] using
      (Dioph.reindex_dioph
        (Fin 3 ⊕ Fin 7)
        ![Sum.inl 0, Sum.inl 1,
          Sum.inr 1, Sum.inr 2]
        seqsOfOnes_dioph)
  have hValueCode :
      Dioph {v : (Fin 3 ⊕ Fin 7) → ℕ |
        Code (lengthFn v) (qFn v) (valueFn v)} := by
    simpa only [lengthFn, qFn, valueFn] using
      (Dioph.reindex_dioph
        (Fin 3 ⊕ Fin 7)
        ![Sum.inl 0, Sum.inl 1, Sum.inl 2]
        code_dioph)
  have hNextCode :
      Dioph {v : (Fin 3 ⊕ Fin 7) → ℕ |
        Code (lengthFn v) (qFn v) (nextFn v)} := by
    simpa only [lengthFn, qFn, nextFn] using
      (Dioph.reindex_dioph
        (Fin 3 ⊕ Fin 7)
        ![Sum.inl 0, Sum.inl 1, Sum.inr 0]
        code_dioph)
  have hFirst :
      Dioph {v | firstLeft v = firstRight v} :=
    Dioph.eq_dioph hfirstLeft hfirstRight
  have hSecond :
      Dioph {v | secondLeft v = secondRight v} :=
    Dioph.eq_dioph hsecondLeft hsecondRight
  have hAll :=
    hPos.inter
      (hBase.inter
        (hPredecessor.inter
          (hEndpointExponent.inter
            (hEndpoint.inter
              (hSeq.inter
                (hValueCode.inter
                  (hNextCode.inter
                    (hFirst.inter hSecond))))))))
  simpa only [CodeNatCore, Set.mem_inter_iff,
    Set.mem_setOf_eq, lengthFn, qFn, valueFn,
    nextFn, onesFn, shiftedFn, baseFn,
    endpointExponentFn, endpointFn, predecessorFn,
    fourQ, cipherBaseFn, cipherBase,
    predecessorPlusOne, lengthPlusOne, slotFn, slot,
    endpointPower, lengthTimesEndpoint, firstLeft,
    nextTimesOnes, predecessorTimesShifted, firstRight,
    valuePlusShifted, baseSquare, secondLeft,
    secondRight] using hAll

/-- The finite index-word certificate is Diophantine in the visible
variables `(length,q,value)`. -/
theorem codeNatCertificate_dioph :
    Dioph {v : Fin 3 → ℕ |
      CodeNatCertificate (v 0) (v 1) (v 2)} := by
  let lengthFn : (Fin 3 → ℕ) → ℕ :=
    fun v => v 0
  let qFn : (Fin 3 → ℕ) → ℕ :=
    fun v => v 1
  let valueFn : (Fin 3 → ℕ) → ℕ :=
    fun v => v 2
  have hlength : Dioph.DiophFn lengthFn :=
    Dioph.proj_dioph 0
  have hq : Dioph.DiophFn qFn :=
    Dioph.proj_dioph 1
  have hvalue : Dioph.DiophFn valueFn :=
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
          valueFn v = 0} :=
    (Dioph.eq_dioph hlength hzero).inter
      ((Dioph.lt_dioph hone hq).inter
        (Dioph.eq_dioph hvalue hzero))
  have hNonempty :
      Dioph {v : Fin 3 → ℕ |
        ∃ witness : Fin 7 → ℕ,
          CodeNatCore (Sum.elim v witness)} := by
    simpa only using
      (Dioph.ex_dioph codeNatCore_dioph)
  refine
    Dioph.ext (Dioph.union hEmpty hNonempty)
      fun v => ?_
  simp only [Set.mem_union, Set.mem_setOf_eq,
    lengthFn, qFn, valueFn]
  rw [exists_codeNatCore_iff]
  rfl

/-- The increasing index cipher is a Diophantine relation.  This is the
formal counterpart of `dio_rel_CodeNat`. -/
theorem codeNat_dioph :
    Dioph {v : Fin 3 → ℕ |
      CodeNat (v 0) (v 1) (v 2)} := by
  exact
    Dioph.ext codeNatCertificate_dioph fun v =>
      (codeNat_iff_certificate
        (length := v 0) (q := v 1)
        (value := v 2)).symm

end SparseCipherIndex

end HGAS
