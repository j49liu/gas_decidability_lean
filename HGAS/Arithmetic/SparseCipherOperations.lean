import HGAS.Arithmetic.SparseCipherCode
import Mathlib.Tactic

/-!
# Arithmetic operations on sparse ciphers

This module formalizes the addition and multiplication tests used by
Matiyasevich's bounded-universal compiler.

Addition needs no extra certificate: ordinary addition of two sparse
codes is componentwise addition, provided the result is itself known to
be a valid cipher.

Multiplication is subtler.  The product of two codes contains diagonal
terms `bᵢ cᵢ` and off-diagonal cross terms.  A binary mask supported at
the shifted sparse positions removes every cross term.  Equality of two
masked products is therefore equivalent to coordinatewise
multiplication.  The mask is made Diophantine by the already formalized
`SeqsOfOnes` relation.

The semantic theorem `codeMul_spec` and the Diophantine theorem
`codeMul_dioph` are the counterparts of `Code_mult_spec` and
`dio_rel_Code_mult` in the Coq/Undecidability DPRM development.
-/

namespace HGAS

namespace SparseCipherOperations

open SparseRadixCipher
open SparseOnesCipher
open SparseCipherCode

/-! ## Addition -/

/-- Numeric addition test on three cipher words. -/
def CodeAdd (result left right : ℕ) : Prop :=
  result = left + right

/-- Under valid-cipher hypotheses, numeric addition is exactly
coordinatewise addition. -/
theorem codeAdd_spec
    {length q resultCode leftCode rightCode : ℕ}
    {result left right : Fin length → ℕ}
    (hresult :
      CipherOf length q result resultCode)
    (hleft :
      CipherOf length q left leftCode)
    (hright :
      CipherOf length q right rightCode) :
    CodeAdd resultCode leftCode rightCode ↔
      ∀ i, result i = left i + right i := by
  rcases hresult with
    ⟨hlq, hresultBound, hresultCode⟩
  rcases hleft with
    ⟨hlqLeft, hleftBound, hleftCode⟩
  rcases hright with
    ⟨hlqRight, hrightBound, hrightCode⟩
  have hq : 0 < q := by omega
  have hsumBound :
      ∀ i, left i + right i < cipherBase q := by
    intro i
    calc
      left i + right i <
          entryBase q + entryBase q :=
        Nat.add_lt_add
          (hleftBound i) (hrightBound i)
      _ = 2 ^ (q + 1) := by
        rw [entryBase, pow_succ]
        ring
      _ ≤ 2 ^ (4 * q) := by
        exact
          Nat.pow_le_pow_right (by norm_num)
            (by omega)
      _ = cipherBase q := by
        rfl
  constructor
  · intro hcode
    have hencode :
        encode (cipherBase q) result =
          encode (cipherBase q)
            (fun i => left i + right i) := by
      calc
        encode (cipherBase q) result =
            resultCode :=
          hresultCode.symm
        _ = leftCode + rightCode :=
          hcode
        _ =
            encode (cipherBase q) left +
              encode (cipherBase q) right := by
          rw [hleftCode, hrightCode]
        _ =
            encode (cipherBase q)
              (fun i => left i + right i) :=
          (SparseRadixCipher.encode_add
            (cipherBase q) left right).symm
    have hfunctions :=
      SparseRadixCipher.encode_injective
        (cipherBase_pos q)
        (fun i =>
          (hresultBound i).trans_le
            (entryBase_le_cipherBase q))
        hsumBound hencode
    exact fun i => congrFun hfunctions i
  · intro hpointwise
    unfold CodeAdd
    calc
      resultCode =
          encode (cipherBase q) result :=
        hresultCode
      _ =
          encode (cipherBase q)
            (fun i => left i + right i) := by
        congr 1
        funext i
        exact hpointwise i
      _ =
          encode (cipherBase q) left +
            encode (cipherBase q) right :=
        SparseRadixCipher.encode_add
          (cipherBase q) left right
      _ = leftCode + rightCode := by
        rw [← hleftCode, ← hrightCode]

/-- Numeric cipher addition is Diophantine. -/
theorem codeAdd_dioph :
    Dioph {v : Fin 3 → ℕ |
      CodeAdd (v 0) (v 1) (v 2)} := by
  exact
    Dioph.eq_dioph
      (Dioph.proj_dioph 0)
      (Dioph.add_dioph
        (Dioph.proj_dioph 1)
        (Dioph.proj_dioph 2))

/-! ## Multiplication mask -/

theorem coordinateProduct_lt_cipherBase
    {q : ℕ} {left right : ℕ}
    (hleft : left < entryBase q)
    (hright : right < entryBase q) :
    left * right < cipherBase q := by
  calc
    left * right <
        entryBase q * entryBase q :=
      Nat.mul_lt_mul_of_lt_of_lt hleft hright
    _ = 2 ^ (2 * q) := by
      rw [entryBase, ← pow_add]
      congr 1
      omega
    _ ≤ 2 ^ (4 * q) := by
      exact
        Nat.pow_le_pow_right (by norm_num)
          (by omega)
    _ = cipherBase q := by
      rfl

/-- The traditional parameter inequality `length+1<q` makes the
`4q`-bit cipher radix wide enough for every convolution coefficient. -/
theorem convolutionAt_lt_cipherBase
    {length q : ℕ}
    {left right : Fin length → ℕ}
    (hlq : length + 1 < q)
    (hleft : ∀ i, left i < entryBase q)
    (hright : ∀ i, right i < entryBase q)
    (position : ℕ) :
    convolutionAt left right position <
      cipherBase q := by
  have hsafe :
      safeWidth q length ≤ 4 * q := by
    simp only [safeWidth]
    omega
  calc
    convolutionAt left right position <
        2 ^ safeWidth q length :=
      convolutionAt_lt_safeWidth
        hleft hright position
    _ ≤ 2 ^ (4 * q) :=
      Nat.pow_le_pow_right (by norm_num) hsafe
    _ = cipherBase q := by
      rfl

/-- The concrete multiplication mask is the abstract diagonal mask
from `SparseRadixCipher`. -/
theorem diagonalMaskCode_eq_cipherMask
    (length q : ℕ) :
    diagonalMaskCode (4 * q) length =
      (cipherBase q - 1) *
        shiftedSparseOnes length q := by
  simpa only [cipherBase, shiftedSparseOnes] using
    (diagonalMaskCode_eq_scale_ones
      (4 * q) length)

/-- Masking a product of two valid ciphers leaves exactly the shifted
coordinatewise products. -/
theorem land_product_cipherMask
    {length q leftCode rightCode : ℕ}
    {left right : Fin length → ℕ}
    (hleft :
      CipherOf length q left leftCode)
    (hright :
      CipherOf length q right rightCode) :
    (leftCode * rightCode) &&&
        ((cipherBase q - 1) *
          shiftedSparseOnes length q) =
      diagonalProductCode (4 * q) left right := by
  rcases hleft with
    ⟨hlq, hleftBound, hleftCode⟩
  rcases hright with
    ⟨hlqRight, hrightBound, hrightCode⟩
  rw [hleftCode, hrightCode,
    ← diagonalMaskCode_eq_cipherMask]
  change
    (encode (2 ^ (4 * q)) left *
        encode (2 ^ (4 * q)) right) &&&
        diagonalMaskCode (4 * q) length =
      diagonalProductCode (4 * q) left right
  exact
    land_product_diagonalMask left right
      (fun position => by
        simpa only [cipherBase] using
          convolutionAt_lt_cipherBase
            hlq hleftBound hrightBound position)

theorem ones_cipherOf
    {length q : ℕ} (hlq : length + 1 < q) :
    CipherOf length q
      (fun _ : Fin length => 1)
      (sparseOnes length q) := by
  refine ⟨hlq, ?_, rfl⟩
  intro i
  have hq : 0 < q := by omega
  exact Nat.one_lt_two_pow (Nat.ne_of_gt hq)

/-! ## The multiplication certificate -/

/-- Finite arithmetic test for coordinatewise multiplication of three
cipher words. -/
def CodeMul
    (length q resultCode leftCode rightCode : ℕ) : Prop :=
  length = 0 ∨
    (0 < length ∧
      ∃ ones shifted predecessor base masked : ℕ,
        base = cipherBase q ∧
        base = predecessor + 1 ∧
        SeqsOfOnes length q ones shifted ∧
        masked =
          (resultCode * ones) &&&
            (predecessor * shifted) ∧
        masked =
          (leftCode * rightCode) &&&
            (predecessor * shifted))

/-- The multiplication certificate is correct whenever its three
visible numbers are valid ciphers. -/
theorem codeMul_spec
    {length q resultCode leftCode rightCode : ℕ}
    {result left right : Fin length → ℕ}
    (hresult :
      CipherOf length q result resultCode)
    (hleft :
      CipherOf length q left leftCode)
    (hright :
      CipherOf length q right rightCode) :
    CodeMul length q resultCode leftCode rightCode ↔
      ∀ i, result i = left i * right i := by
  have hlq : length + 1 < q :=
    hresult.1
  have hresultProduct :
      ∀ i, result i * 1 < cipherBase q := by
    intro i
    simpa using
      (hresult.2.1 i).trans_le
        (entryBase_le_cipherBase q)
  have hleftRightProduct :
      ∀ i, left i * right i < cipherBase q := by
    intro i
    exact
      coordinateProduct_lt_cipherBase
        (hleft.2.1 i) (hright.2.1 i)
  constructor
  · intro hcertificate
    rcases hcertificate with hzero | hnonempty
    · subst length
      exact fun i => Fin.elim0 i
    · rcases hnonempty with
        ⟨hlength, ones, shifted, predecessor,
          base, masked, hbase, hpredecessor,
          hseq, hresultMask, hproductMask⟩
      rcases hseq with
        ⟨hlqSeq, hones, hshifted⟩
      have hbasePositive :
          0 < cipherBase q :=
        cipherBase_pos q
      have hpredecessorValue :
          predecessor = cipherBase q - 1 := by
        omega
      have hmaskedEquality :
          (resultCode * sparseOnes length q) &&&
              ((cipherBase q - 1) *
                shiftedSparseOnes length q) =
            (leftCode * rightCode) &&&
              ((cipherBase q - 1) *
                shiftedSparseOnes length q) := by
        calc
          (resultCode * sparseOnes length q) &&&
                ((cipherBase q - 1) *
                  shiftedSparseOnes length q) =
              masked := by
            calc
              (resultCode * sparseOnes length q) &&&
                    ((cipherBase q - 1) *
                      shiftedSparseOnes length q) =
                  (resultCode * ones) &&&
                    (predecessor * shifted) := by
                rw [hones, hshifted,
                  hpredecessorValue]
              _ = masked :=
                hresultMask.symm
          _ =
              (leftCode * rightCode) &&&
                ((cipherBase q - 1) *
                  shiftedSparseOnes length q) :=
            calc
              masked =
                  (leftCode * rightCode) &&&
                    (predecessor * shifted) :=
                hproductMask
              _ =
                  (leftCode * rightCode) &&&
                    ((cipherBase q - 1) *
                      shiftedSparseOnes length q) := by
                rw [hshifted,
                  hpredecessorValue]
      have hdiagonal :
          diagonalProductCode (4 * q)
              result (fun _ : Fin length => 1) =
            diagonalProductCode (4 * q)
              left right := by
        calc
          diagonalProductCode (4 * q)
                result (fun _ : Fin length => 1) =
              (resultCode * sparseOnes length q) &&&
                ((cipherBase q - 1) *
                  shiftedSparseOnes length q) :=
            (land_product_cipherMask
              hresult (ones_cipherOf hlq)).symm
          _ =
              (leftCode * rightCode) &&&
                ((cipherBase q - 1) *
                  shiftedSparseOnes length q) :=
            hmaskedEquality
          _ =
              diagonalProductCode (4 * q)
                left right :=
            land_product_cipherMask hleft hright
      have hproducts :=
        diagonalProductCode_products_injective
          hresultProduct hleftRightProduct hdiagonal
      intro i
      simpa using hproducts i
  · intro hpointwise
    by_cases hzero : length = 0
    · exact Or.inl hzero
    · right
      have hlength : 0 < length :=
        Nat.pos_of_ne_zero hzero
      let mask :=
        (resultCode * sparseOnes length q) &&&
          ((cipherBase q - 1) *
            shiftedSparseOnes length q)
      refine
        ⟨hlength,
          sparseOnes length q,
          shiftedSparseOnes length q,
          cipherBase q - 1,
          cipherBase q, mask,
          rfl, ?_, ⟨hlq, rfl, rfl⟩,
          rfl, ?_⟩
      · have hpositive := cipherBase_pos q
        omega
      · dsimp only [mask]
        calc
          (resultCode * sparseOnes length q) &&&
                ((cipherBase q - 1) *
                  shiftedSparseOnes length q) =
              diagonalProductCode (4 * q)
                result (fun _ : Fin length => 1) :=
            land_product_cipherMask
              hresult (ones_cipherOf hlq)
          _ =
              diagonalProductCode (4 * q)
                left right := by
            unfold diagonalProductCode
            congr 2
            funext i
            simp [hpointwise i]
          _ =
              (leftCode * rightCode) &&&
                ((cipherBase q - 1) *
                  shiftedSparseOnes length q) :=
            (land_product_cipherMask
              hleft hright).symm

/-- The nonempty multiplication certificate with all five witnesses
exposed.  Visible coordinates are
`(length,q,resultCode,leftCode,rightCode)` and witness coordinates are
`(ones,shifted,predecessor,base,masked)`. -/
def MulCore
    (v : (Fin 5 ⊕ Fin 5) → ℕ) : Prop :=
  0 < v (Sum.inl 0) ∧
  v (Sum.inr 3) =
    cipherBase (v (Sum.inl 1)) ∧
  v (Sum.inr 3) = v (Sum.inr 2) + 1 ∧
  SeqsOfOnes
    (v (Sum.inl 0)) (v (Sum.inl 1))
    (v (Sum.inr 0)) (v (Sum.inr 1)) ∧
  v (Sum.inr 4) =
    (v (Sum.inl 2) * v (Sum.inr 0)) &&&
      (v (Sum.inr 2) * v (Sum.inr 1)) ∧
  v (Sum.inr 4) =
    (v (Sum.inl 3) * v (Sum.inl 4)) &&&
      (v (Sum.inr 2) * v (Sum.inr 1))

theorem exists_mulCore_iff
    (v : Fin 5 → ℕ) :
    (∃ witness : Fin 5 → ℕ,
      MulCore (Sum.elim v witness)) ↔
      (0 < v 0 ∧
        ∃ ones shifted predecessor base masked : ℕ,
          base = cipherBase (v 1) ∧
          base = predecessor + 1 ∧
          SeqsOfOnes (v 0) (v 1) ones shifted ∧
          masked =
            (v 2 * ones) &&&
              (predecessor * shifted) ∧
          masked =
            (v 3 * v 4) &&&
              (predecessor * shifted)) := by
  constructor
  · rintro ⟨witness, h⟩
    exact
      ⟨h.1,
        witness 0, witness 1, witness 2,
        witness 3, witness 4, h.2⟩
  · rintro
      ⟨hlength, ones, shifted, predecessor,
        base, masked, hbase, hpredecessor,
        hseq, hresult, hproduct⟩
    exact
      ⟨![ones, shifted, predecessor, base, masked],
        hlength, hbase, hpredecessor,
        hseq, hresult, hproduct⟩

/-- The exposed nonempty multiplication certificate is
Diophantine. -/
theorem mulCore_dioph :
    Dioph {v : (Fin 5 ⊕ Fin 5) → ℕ |
      MulCore v} := by
  let lengthFn : ((Fin 5 ⊕ Fin 5) → ℕ) → ℕ :=
    fun v => v (Sum.inl 0)
  let qFn : ((Fin 5 ⊕ Fin 5) → ℕ) → ℕ :=
    fun v => v (Sum.inl 1)
  let resultFn : ((Fin 5 ⊕ Fin 5) → ℕ) → ℕ :=
    fun v => v (Sum.inl 2)
  let leftFn : ((Fin 5 ⊕ Fin 5) → ℕ) → ℕ :=
    fun v => v (Sum.inl 3)
  let rightFn : ((Fin 5 ⊕ Fin 5) → ℕ) → ℕ :=
    fun v => v (Sum.inl 4)
  let onesFn : ((Fin 5 ⊕ Fin 5) → ℕ) → ℕ :=
    fun v => v (Sum.inr 0)
  let shiftedFn : ((Fin 5 ⊕ Fin 5) → ℕ) → ℕ :=
    fun v => v (Sum.inr 1)
  let predecessorFn :
      ((Fin 5 ⊕ Fin 5) → ℕ) → ℕ :=
    fun v => v (Sum.inr 2)
  let baseFn : ((Fin 5 ⊕ Fin 5) → ℕ) → ℕ :=
    fun v => v (Sum.inr 3)
  let maskedFn : ((Fin 5 ⊕ Fin 5) → ℕ) → ℕ :=
    fun v => v (Sum.inr 4)
  have hlength : Dioph.DiophFn lengthFn :=
    Dioph.proj_dioph (Sum.inl 0)
  have hq : Dioph.DiophFn qFn :=
    Dioph.proj_dioph (Sum.inl 1)
  have hresult : Dioph.DiophFn resultFn :=
    Dioph.proj_dioph (Sum.inl 2)
  have hleft : Dioph.DiophFn leftFn :=
    Dioph.proj_dioph (Sum.inl 3)
  have hright : Dioph.DiophFn rightFn :=
    Dioph.proj_dioph (Sum.inl 4)
  have hones : Dioph.DiophFn onesFn :=
    Dioph.proj_dioph (Sum.inr 0)
  have hshifted : Dioph.DiophFn shiftedFn :=
    Dioph.proj_dioph (Sum.inr 1)
  have hpredecessor :
      Dioph.DiophFn predecessorFn :=
    Dioph.proj_dioph (Sum.inr 2)
  have hbase : Dioph.DiophFn baseFn :=
    Dioph.proj_dioph (Sum.inr 3)
  have hmasked : Dioph.DiophFn maskedFn :=
    Dioph.proj_dioph (Sum.inr 4)
  have hzero :
      Dioph.DiophFn
        (fun _ : (Fin 5 ⊕ Fin 5) → ℕ => 0) :=
    Dioph.const_dioph 0
  have hone :
      Dioph.DiophFn
        (fun _ : (Fin 5 ⊕ Fin 5) → ℕ => 1) :=
    Dioph.const_dioph 1
  have htwo :
      Dioph.DiophFn
        (fun _ : (Fin 5 ⊕ Fin 5) → ℕ => 2) :=
    Dioph.const_dioph 2
  have hfour :
      Dioph.DiophFn
        (fun _ : (Fin 5 ⊕ Fin 5) → ℕ => 4) :=
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
  let resultTimesOnes :=
    fun v => resultFn v * onesFn v
  have hresultTimesOnes :
      Dioph.DiophFn resultTimesOnes :=
    Dioph.mul_dioph hresult hones
  let leftTimesRight :=
    fun v => leftFn v * rightFn v
  have hleftTimesRight :
      Dioph.DiophFn leftTimesRight :=
    Dioph.mul_dioph hleft hright
  let maskWord :=
    fun v => predecessorFn v * shiftedFn v
  have hmaskWord : Dioph.DiophFn maskWord :=
    Dioph.mul_dioph hpredecessor hshifted
  let resultMasked :=
    fun v => resultTimesOnes v &&& maskWord v
  have hresultMasked :
      Dioph.DiophFn resultMasked :=
    DiophantineBitwise.land_diophFn
      hresultTimesOnes hmaskWord
  let productMasked :=
    fun v => leftTimesRight v &&& maskWord v
  have hproductMasked :
      Dioph.DiophFn productMasked :=
    DiophantineBitwise.land_diophFn
      hleftTimesRight hmaskWord
  have hPos :
      Dioph {v | 0 < lengthFn v} :=
    Dioph.lt_dioph hzero hlength
  have hBase :
      Dioph {v | baseFn v = cipherBaseFn v} :=
    Dioph.eq_dioph hbase hcipherBase
  have hPredecessor :
      Dioph {v |
        baseFn v = predecessorPlusOne v} :=
    Dioph.eq_dioph hbase hpredecessorPlusOne
  have hSeq :
      Dioph {v : (Fin 5 ⊕ Fin 5) → ℕ |
        SeqsOfOnes
          (lengthFn v) (qFn v)
          (onesFn v) (shiftedFn v)} := by
    simpa only [lengthFn, qFn, onesFn, shiftedFn] using
      (Dioph.reindex_dioph
        (Fin 5 ⊕ Fin 5)
        ![Sum.inl 0, Sum.inl 1,
          Sum.inr 0, Sum.inr 1]
        seqsOfOnes_dioph)
  have hResult :
      Dioph {v | maskedFn v = resultMasked v} :=
    Dioph.eq_dioph hmasked hresultMasked
  have hProduct :
      Dioph {v | maskedFn v = productMasked v} :=
    Dioph.eq_dioph hmasked hproductMasked
  have hAll :=
    hPos.inter
      (hBase.inter
        (hPredecessor.inter
          (hSeq.inter
            (hResult.inter hProduct))))
  simpa only [MulCore, Set.mem_inter_iff,
    Set.mem_setOf_eq, lengthFn, qFn,
    resultFn, leftFn, rightFn, onesFn,
    shiftedFn, predecessorFn, baseFn,
    maskedFn, fourQ, cipherBaseFn, cipherBase,
    predecessorPlusOne, resultTimesOnes,
    leftTimesRight, maskWord, resultMasked,
    productMasked] using hAll

/-- Coordinatewise multiplication of valid sparse ciphers is tested by
a Diophantine relation in the five visible variables. -/
theorem codeMul_dioph :
    Dioph {v : Fin 5 → ℕ |
      CodeMul (v 0) (v 1) (v 2)
        (v 3) (v 4)} := by
  let lengthFn : (Fin 5 → ℕ) → ℕ :=
    fun v => v 0
  have hlength : Dioph.DiophFn lengthFn :=
    Dioph.proj_dioph 0
  have hzero :
      Dioph.DiophFn (fun _ : Fin 5 → ℕ => 0) :=
    Dioph.const_dioph 0
  have hEmpty :
      Dioph {v : Fin 5 → ℕ |
        lengthFn v = 0} :=
    Dioph.eq_dioph hlength hzero
  have hNonempty :
      Dioph {v : Fin 5 → ℕ |
        ∃ witness : Fin 5 → ℕ,
          MulCore (Sum.elim v witness)} := by
    simpa only using
      (Dioph.ex_dioph mulCore_dioph)
  refine
    Dioph.ext (Dioph.union hEmpty hNonempty)
      fun v => ?_
  simp only [Set.mem_union, Set.mem_setOf_eq,
    lengthFn]
  rw [exists_mulCore_iff]
  rfl

end SparseCipherOperations

end HGAS
