import HGAS.Arithmetic.DQL
import Mathlib.Computability.RE
import Mathlib.Computability.Primrec.List

/-!
# Recursive enumerability of DQL solvability

For fixed finite numbers of rows and variables, a DQL system is finite data.
This file makes that assertion computationally explicit and proves that
integer solvability is recursively enumerable.

There are two small coding layers.

* `SignedCode = ℕ ⊕ ℕ` is the canonical constructor code for an integer:
  `inl n` denotes `n`, while `inr n` denotes `-(n+1)`.
* `DQLFiniteCode` is the literal tuple of the three finite coefficient
  arrays in a `DQLSystem`, with every integer replaced by a `SignedCode`.

The equivalence `dqlSystemCodeEquiv` is used to install the `Primcodable`
instance for systems.  Witnesses are decoded explicitly from a natural
number by `decodeSignedWitness`; `decodeIntegerWitness_surjective` proves
that this loses no integer vector.

To keep the checker visibly primitive, its integer arithmetic is evaluated
with pairs `(p,n)` denoting `p-n`.  Pair addition and multiplication use
only natural-number addition and multiplication.  Their correctness is
proved before the computability proof.
-/

namespace HGAS

open scoped BigOperators
open Encodable

/-- Canonical finite code for an integer.  The right summand uses `negSucc`,
so there is no duplicate representation of zero. -/
abbrev SignedCode := ℕ ⊕ ℕ

/-- Mathematical value of a signed code. -/
def signedCodeValue : SignedCode → ℤ :=
  Sum.elim Int.ofNat Int.negSucc

/-- The canonical constructor equivalence between integers and signed
codes. -/
def intSignedCodeEquiv : ℤ ≃ SignedCode :=
  Equiv.intEquivNatSumNat

@[simp]
theorem signedCodeValue_intCode (z : ℤ) :
    signedCodeValue (intSignedCodeEquiv z) = z := by
  cases z <;> rfl

@[simp]
theorem intCode_signedCodeValue (c : SignedCode) :
    intSignedCodeEquiv (signedCodeValue c) = c := by
  cases c with
  | inl n => rfl
  | inr n => rfl

/-- A completely explicit finite code for the three arrays in a DQL
system. -/
abbrev DQLFiniteCode (eqs vars : ℕ) :=
  ((Fin eqs → Fin vars → SignedCode) ×
    (Fin eqs → Fin vars → SignedCode)) ×
    (Fin eqs → SignedCode)

/-- Replace every integer coefficient by its canonical constructor code. -/
def dqlSystemCodeEquiv (eqs vars : ℕ) :
    DQLSystem eqs vars ≃ DQLFiniteCode eqs vars where
  toFun I :=
    ((fun r j ↦ intSignedCodeEquiv (I.quadratic r j),
      fun r j ↦ intSignedCodeEquiv (I.linear r j)),
      fun r ↦ intSignedCodeEquiv (I.rhs r))
  invFun c :=
    { quadratic := fun r j ↦ signedCodeValue (c.1.1 r j)
      linear := fun r j ↦ signedCodeValue (c.1.2 r j)
      rhs := fun r ↦ signedCodeValue (c.2 r) }
  left_inv I := by
    cases I
    simp only [signedCodeValue_intCode]
  right_inv c := by
    rcases c with ⟨⟨q, l⟩, b⟩
    simp only [intCode_signedCodeValue]

/-- The primitive code for a DQL system is precisely its finite coefficient
tuple, not an opaque classical encoding. -/
instance dqlSystemPrimcodable (eqs vars : ℕ) :
    Primcodable (DQLSystem eqs vars) :=
  Primcodable.ofEquiv (DQLFiniteCode eqs vars)
    (dqlSystemCodeEquiv eqs vars)

theorem dqlSystemCodeEquiv_primrec (eqs vars : ℕ) :
    Primrec (dqlSystemCodeEquiv eqs vars) :=
  Primrec.of_equiv

/-- Decode a natural number as a fixed-length vector of signed codes.
Numbers outside the range of the standard encoding denote the zero vector. -/
def decodeSignedWitness (vars : ℕ) (n : ℕ) : Fin vars → SignedCode :=
  (@Encodable.decode (Fin vars → SignedCode)
    (@Primcodable.toEncodable (Fin vars → SignedCode) inferInstance) n).getD
    (fun _ ↦ Sum.inl 0)

theorem decodeSignedWitness_primrec (vars : ℕ) :
    Primrec (decodeSignedWitness vars) := by
  exact Primrec.option_getD.comp
    (@Primrec.decode (Fin vars → SignedCode) _)
    (Primrec.const (fun _ ↦ Sum.inl 0))

/-- Interpret the decoded signed-code vector as an integer vector. -/
def decodeIntegerWitness (vars : ℕ) (n : ℕ) : Fin vars → ℤ :=
  fun i ↦ signedCodeValue (decodeSignedWitness vars n i)

/-- Every integer vector occurs in the explicit natural-number witness
enumeration. -/
theorem decodeIntegerWitness_surjective (vars : ℕ) :
    Function.Surjective (decodeIntegerWitness vars) := by
  intro x
  let c : Fin vars → SignedCode := fun i ↦ intSignedCodeEquiv (x i)
  let code :=
    @Encodable.encode (Fin vars → SignedCode)
      (@Primcodable.toEncodable (Fin vars → SignedCode) inferInstance) c
  refine ⟨code, ?_⟩
  funext i
  simp [decodeIntegerWitness, decodeSignedWitness, code, c]

/-- A difference pair `(p,n)` denotes the integer `p-n`.  Unlike
`SignedCode`, this representation need not be canonical; that makes its
arithmetic especially transparent. -/
abbrev DifferencePair := ℕ × ℕ

/-- Integer denoted by a difference pair. -/
def differencePairValue (a : DifferencePair) : ℤ :=
  (a.1 : ℤ) - (a.2 : ℤ)

/-- Convert a canonical signed code into a difference pair. -/
def signedCodeToDifference : SignedCode → DifferencePair
  | Sum.inl n => (n, 0)
  | Sum.inr n => (0, n + 1)

/-- Addition of represented integers. -/
def differencePairAdd
    (a b : DifferencePair) : DifferencePair :=
  (a.1 + b.1, a.2 + b.2)

/-- Multiplication of represented integers:
`(p-n)(q-m) = (pq+nm) - (pm+nq)`. -/
def differencePairMul
    (a b : DifferencePair) : DifferencePair :=
  (a.1 * b.1 + a.2 * b.2,
    a.1 * b.2 + a.2 * b.1)

/-- Equality of the represented integers, using only natural arithmetic. -/
def DifferencePair.Equivalent
    (a b : DifferencePair) : Prop :=
  a.1 + b.2 = b.1 + a.2

instance (a b : DifferencePair) :
    Decidable (a.Equivalent b) :=
  by
    unfold DifferencePair.Equivalent
    infer_instance

@[simp]
theorem differencePairValue_signedCodeToDifference (c : SignedCode) :
    differencePairValue (signedCodeToDifference c) = signedCodeValue c := by
  cases c with
  | inl n =>
      simp [signedCodeToDifference, differencePairValue, signedCodeValue]
  | inr n =>
      change (0 : ℤ) - (n + 1 : ℕ) = Int.negSucc n
      rw [Int.negSucc_eq]
      push_cast
      ring

@[simp]
theorem differencePairValue_zero :
    differencePairValue (0 : DifferencePair) = 0 := by
  simp [differencePairValue]

theorem differencePairValue_add (a b : DifferencePair) :
    differencePairValue (differencePairAdd a b) =
      differencePairValue a + differencePairValue b := by
  simp [differencePairValue, differencePairAdd]
  omega

theorem differencePairValue_mul (a b : DifferencePair) :
    differencePairValue (differencePairMul a b) =
      differencePairValue a * differencePairValue b := by
  simp [differencePairValue, differencePairMul]
  ring

theorem differencePair_equivalent_iff (a b : DifferencePair) :
    a.Equivalent b ↔
      differencePairValue a = differencePairValue b := by
  simp only [DifferencePair.Equivalent, differencePairValue]
  omega

theorem signedCodeToDifference_primrec :
    Primrec signedCodeToDifference := by
  refine
    (Primrec.sumCasesOn Primrec.id
      (Primrec.pair Primrec.snd (Primrec.const 0)).to₂
      (Primrec.pair (Primrec.const 0)
        (Primrec.succ.comp Primrec.snd)).to₂).of_eq ?_
  intro c
  cases c <;> rfl

theorem differencePairAdd_primrec :
    Primrec₂ differencePairAdd := by
  exact Primrec.pair
    (Primrec.nat_add.comp
      (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd))
    (Primrec.nat_add.comp
      (Primrec.snd.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd))

theorem differencePairMul_primrec :
    Primrec₂ differencePairMul := by
  exact Primrec.pair
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp
        (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd))
      (Primrec.nat_mul.comp
        (Primrec.snd.comp Primrec.fst)
        (Primrec.snd.comp Primrec.snd)))
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp
        (Primrec.fst.comp Primrec.fst)
        (Primrec.snd.comp Primrec.snd))
      (Primrec.nat_mul.comp
        (Primrec.snd.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd)))

theorem differencePairEquivalent_primrec :
    PrimrecRel DifferencePair.Equivalent := by
  exact Primrec.eq.comp₂
    (Primrec.nat_add.comp
      (Primrec.fst.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd))
    (Primrec.nat_add.comp
      (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.fst))

/-- Quadratic coefficient stored in a finite DQL code. -/
def finiteCodeQuadratic {eqs vars : ℕ}
    (c : DQLFiniteCode eqs vars) (r : Fin eqs) (j : Fin vars) :
    SignedCode :=
  c.1.1 r j

/-- Linear coefficient stored in a finite DQL code. -/
def finiteCodeLinear {eqs vars : ℕ}
    (c : DQLFiniteCode eqs vars) (r : Fin eqs) (j : Fin vars) :
    SignedCode :=
  c.1.2 r j

/-- Right-hand side stored in a finite DQL code. -/
def finiteCodeRhs {eqs vars : ℕ}
    (c : DQLFiniteCode eqs vars) (r : Fin eqs) : SignedCode :=
  c.2 r

theorem finiteCodeQuadratic_primrec {eqs vars : ℕ}
    (r : Fin eqs) (j : Fin vars) :
    Primrec (fun c : DQLFiniteCode eqs vars ↦
      finiteCodeQuadratic c r j) := by
  exact Primrec.fin_app.comp
    (Primrec.fin_app.comp
      (Primrec.fst.comp (Primrec.fst : Primrec
        (Prod.fst : DQLFiniteCode eqs vars →
          (Fin eqs → Fin vars → SignedCode) ×
            (Fin eqs → Fin vars → SignedCode))))
      (Primrec.const r))
    (Primrec.const j)

theorem finiteCodeLinear_primrec {eqs vars : ℕ}
    (r : Fin eqs) (j : Fin vars) :
    Primrec (fun c : DQLFiniteCode eqs vars ↦
      finiteCodeLinear c r j) := by
  exact Primrec.fin_app.comp
    (Primrec.fin_app.comp
      (Primrec.snd.comp (Primrec.fst : Primrec
        (Prod.fst : DQLFiniteCode eqs vars →
          (Fin eqs → Fin vars → SignedCode) ×
            (Fin eqs → Fin vars → SignedCode))))
      (Primrec.const r))
    (Primrec.const j)

theorem finiteCodeRhs_primrec {eqs vars : ℕ}
    (r : Fin eqs) :
    Primrec (fun c : DQLFiniteCode eqs vars ↦
      finiteCodeRhs c r) := by
  exact Primrec.fin_app.comp Primrec.snd (Primrec.const r)

@[simp]
theorem finiteCodeQuadratic_systemCode {eqs vars : ℕ}
    (I : DQLSystem eqs vars) (r : Fin eqs) (j : Fin vars) :
    finiteCodeQuadratic (dqlSystemCodeEquiv eqs vars I) r j =
      intSignedCodeEquiv (I.quadratic r j) :=
  rfl

@[simp]
theorem finiteCodeLinear_systemCode {eqs vars : ℕ}
    (I : DQLSystem eqs vars) (r : Fin eqs) (j : Fin vars) :
    finiteCodeLinear (dqlSystemCodeEquiv eqs vars I) r j =
      intSignedCodeEquiv (I.linear r j) :=
  rfl

@[simp]
theorem finiteCodeRhs_systemCode {eqs vars : ℕ}
    (I : DQLSystem eqs vars) (r : Fin eqs) :
    finiteCodeRhs (dqlSystemCodeEquiv eqs vars I) r =
      intSignedCodeEquiv (I.rhs r) :=
  rfl

theorem signedWitnessEntry_primrec {vars : ℕ} (j : Fin vars) :
    Primrec (fun x : Fin vars → SignedCode ↦ x j) := by
  exact Primrec.fin_app.comp Primrec.id (Primrec.const j)

/-- Difference-pair evaluation of one summand
`aⱼ xⱼ² + bⱼ xⱼ`. -/
def dqlTermDifference {eqs vars : ℕ}
    (c : DQLFiniteCode eqs vars) (x : Fin vars → SignedCode)
    (r : Fin eqs) (j : Fin vars) : DifferencePair :=
  let q := signedCodeToDifference (finiteCodeQuadratic c r j)
  let l := signedCodeToDifference (finiteCodeLinear c r j)
  let y := signedCodeToDifference (x j)
  differencePairAdd
    (differencePairMul q (differencePairMul y y))
    (differencePairMul l y)

/-- Sum a finite list of represented integers. -/
def differencePairSum (l : List DifferencePair) : DifferencePair :=
  l.foldr differencePairAdd 0

/-- Difference-pair evaluation of one complete DQL row. -/
def dqlRowDifference {eqs vars : ℕ}
    (c : DQLFiniteCode eqs vars) (x : Fin vars → SignedCode)
    (r : Fin eqs) : DifferencePair :=
  differencePairSum
    (List.ofFn fun j ↦ dqlTermDifference c x r j)

/-- Boolean checker for one row. -/
def dqlRowCheck {eqs vars : ℕ}
    (c : DQLFiniteCode eqs vars) (x : Fin vars → SignedCode)
    (r : Fin eqs) : Bool :=
  decide ((dqlRowDifference c x r).Equivalent
    (signedCodeToDifference (finiteCodeRhs c r)))

/-- Total Boolean checker for a coded system and coded witness. -/
def dqlFiniteCheck {eqs vars : ℕ}
    (c : DQLFiniteCode eqs vars) (x : Fin vars → SignedCode) : Bool :=
  (List.ofFn fun r ↦ dqlRowCheck c x r).all id

theorem differencePairValue_sum (l : List DifferencePair) :
    differencePairValue (differencePairSum l) =
      (l.map differencePairValue).sum := by
  induction l with
  | nil => simp [differencePairSum]
  | cons a l ih =>
      change
        differencePairValue
            (differencePairAdd a (differencePairSum l)) =
          differencePairValue a +
            (List.map differencePairValue l).sum
      rw [differencePairValue_add, ih]

theorem dqlTermDifference_value {eqs vars : ℕ}
    (c : DQLFiniteCode eqs vars) (x : Fin vars → SignedCode)
    (r : Fin eqs) (j : Fin vars) :
    differencePairValue (dqlTermDifference c x r j) =
      signedCodeValue (finiteCodeQuadratic c r j) *
          signedCodeValue (x j) ^ 2 +
        signedCodeValue (finiteCodeLinear c r j) *
          signedCodeValue (x j) := by
  simp only [dqlTermDifference, differencePairValue_add,
    differencePairValue_mul,
    differencePairValue_signedCodeToDifference]
  ring

theorem dqlRowDifference_value {eqs vars : ℕ}
    (c : DQLFiniteCode eqs vars) (x : Fin vars → SignedCode)
    (r : Fin eqs) :
    differencePairValue (dqlRowDifference c x r) =
      ∑ j, (signedCodeValue (finiteCodeQuadratic c r j) *
          signedCodeValue (x j) ^ 2 +
        signedCodeValue (finiteCodeLinear c r j) *
          signedCodeValue (x j)) := by
  rw [dqlRowDifference, differencePairValue_sum, List.map_ofFn,
    List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro j _
  exact dqlTermDifference_value c x r j

theorem dqlRowCheck_eq_true_iff {eqs vars : ℕ}
    (c : DQLFiniteCode eqs vars) (x : Fin vars → SignedCode)
    (r : Fin eqs) :
    dqlRowCheck c x r = true ↔
      (∑ j, (signedCodeValue (finiteCodeQuadratic c r j) *
          signedCodeValue (x j) ^ 2 +
        signedCodeValue (finiteCodeLinear c r j) *
          signedCodeValue (x j))) =
        signedCodeValue (finiteCodeRhs c r) := by
  rw [dqlRowCheck, decide_eq_true_eq, differencePair_equivalent_iff,
    dqlRowDifference_value,
    differencePairValue_signedCodeToDifference]

theorem dqlFiniteCheck_eq_true_iff {eqs vars : ℕ}
    (c : DQLFiniteCode eqs vars) (x : Fin vars → SignedCode) :
    dqlFiniteCheck c x = true ↔
      ∀ r,
        (∑ j, (signedCodeValue (finiteCodeQuadratic c r j) *
            signedCodeValue (x j) ^ 2 +
          signedCodeValue (finiteCodeLinear c r j) *
            signedCodeValue (x j))) =
          signedCodeValue (finiteCodeRhs c r) := by
  rw [dqlFiniteCheck, List.all_eq_true]
  constructor
  · intro h r
    have hr := h (dqlRowCheck c x r)
      (List.mem_ofFn.mpr ⟨r, rfl⟩)
    exact (dqlRowCheck_eq_true_iff c x r).mp hr
  · intro h b hb
    obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hb
    exact (dqlRowCheck_eq_true_iff c x r).mpr (h r)

theorem dqlTermDifference_primrec {eqs vars : ℕ}
    (r : Fin eqs) (j : Fin vars) :
    Primrec
      (fun p : DQLFiniteCode eqs vars × (Fin vars → SignedCode) ↦
        dqlTermDifference p.1 p.2 r j) := by
  have hq :
      Primrec
        (fun p : DQLFiniteCode eqs vars × (Fin vars → SignedCode) ↦
          signedCodeToDifference (finiteCodeQuadratic p.1 r j)) :=
    signedCodeToDifference_primrec.comp
      ((finiteCodeQuadratic_primrec r j).comp Primrec.fst)
  have hl :
      Primrec
        (fun p : DQLFiniteCode eqs vars × (Fin vars → SignedCode) ↦
          signedCodeToDifference (finiteCodeLinear p.1 r j)) :=
    signedCodeToDifference_primrec.comp
      ((finiteCodeLinear_primrec r j).comp Primrec.fst)
  have hy :
      Primrec
        (fun p : DQLFiniteCode eqs vars × (Fin vars → SignedCode) ↦
          signedCodeToDifference (p.2 j)) :=
    signedCodeToDifference_primrec.comp
      ((signedWitnessEntry_primrec j).comp Primrec.snd)
  exact differencePairAdd_primrec.comp
    (differencePairMul_primrec.comp hq
      (differencePairMul_primrec.comp hy hy))
    (differencePairMul_primrec.comp hl hy)

theorem differencePairSum_primrec :
    Primrec differencePairSum := by
  have hstep :
      Primrec₂
        (fun (_ : List DifferencePair)
          (p : DifferencePair × DifferencePair) ↦
            differencePairAdd p.1 p.2) :=
    differencePairAdd_primrec.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.right)
  exact (Primrec.list_foldr Primrec.id (Primrec.const 0) hstep).of_eq
    (fun l ↦ rfl)

theorem dqlRowDifference_primrec {eqs vars : ℕ}
    (r : Fin eqs) :
    Primrec
      (fun p : DQLFiniteCode eqs vars × (Fin vars → SignedCode) ↦
        dqlRowDifference p.1 p.2 r) := by
  have hterms :
      Primrec
        (fun p : DQLFiniteCode eqs vars × (Fin vars → SignedCode) ↦
          List.ofFn fun j ↦ dqlTermDifference p.1 p.2 r j) :=
    Primrec.list_ofFn (fun j ↦ dqlTermDifference_primrec r j)
  exact differencePairSum_primrec.comp hterms

theorem dqlRowRhsDifference_primrec {eqs vars : ℕ}
    (r : Fin eqs) :
    Primrec
      (fun p : DQLFiniteCode eqs vars × (Fin vars → SignedCode) ↦
        signedCodeToDifference (finiteCodeRhs p.1 r)) :=
  signedCodeToDifference_primrec.comp
    ((finiteCodeRhs_primrec r).comp Primrec.fst)

theorem dqlRowCheck_primrec {eqs vars : ℕ}
    (r : Fin eqs) :
    Primrec
      (fun p : DQLFiniteCode eqs vars × (Fin vars → SignedCode) ↦
        dqlRowCheck p.1 p.2 r) := by
  exact differencePairEquivalent_primrec.decide.comp
    (dqlRowDifference_primrec r)
    (dqlRowRhsDifference_primrec r)

/-- Boolean conjunction over a list is primitive recursive. -/
theorem boolListAll_primrec :
    Primrec (fun l : List Bool ↦ l.all id) := by
  have hstep :
      Primrec₂
        (fun (_ : List Bool) (p : Bool × Bool) ↦ p.1 && p.2) :=
    Primrec.and.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.right)
  refine
    (Primrec.list_foldr Primrec.id (Primrec.const true) hstep).of_eq ?_
  intro l
  induction l with
  | nil => rfl
  | cons b l ih =>
      change
        List.foldr (fun b s ↦ b && s) true l = l.all id at ih
      change
        (b && List.foldr (fun b s ↦ b && s) true l) =
          (b && l.all id)
      rw [ih]

theorem dqlFiniteCheck_primrec {eqs vars : ℕ} :
    Primrec
      (fun p : DQLFiniteCode eqs vars × (Fin vars → SignedCode) ↦
        dqlFiniteCheck p.1 p.2) := by
  have hrows :
      Primrec
        (fun p : DQLFiniteCode eqs vars × (Fin vars → SignedCode) ↦
          List.ofFn fun r ↦ dqlRowCheck p.1 p.2 r) :=
    Primrec.list_ofFn (fun r ↦ dqlRowCheck_primrec r)
  exact boolListAll_primrec.comp hrows

/-- Run the finite checker on the canonical code of a system and the
natural-number decoding of a witness. -/
def dqlNatWitnessCheck {eqs vars : ℕ}
    (I : DQLSystem eqs vars) (n : ℕ) : Bool :=
  dqlFiniteCheck (dqlSystemCodeEquiv eqs vars I)
    (decodeSignedWitness vars n)

theorem dqlSystemCodeOnInput_computable {eqs vars : ℕ} :
    Computable
      (fun p : DQLSystem eqs vars × ℕ ↦
        dqlSystemCodeEquiv eqs vars p.1) :=
  (dqlSystemCodeEquiv_primrec eqs vars).to_comp.comp Computable.fst

theorem decodeSignedWitnessOnInput_computable {eqs vars : ℕ} :
    Computable
      (fun p : DQLSystem eqs vars × ℕ ↦
        decodeSignedWitness vars p.2) :=
  (decodeSignedWitness_primrec vars).to_comp.comp Computable.snd

theorem dqlCodeWitnessPair_computable {eqs vars : ℕ} :
    Computable
      (fun p : DQLSystem eqs vars × ℕ ↦
        (dqlSystemCodeEquiv eqs vars p.1,
          decodeSignedWitness vars p.2)) :=
  Computable.pair dqlSystemCodeOnInput_computable
    decodeSignedWitnessOnInput_computable

theorem dqlNatWitnessCheck_computable {eqs vars : ℕ} :
    Computable
      (fun p : DQLSystem eqs vars × ℕ ↦
        dqlNatWitnessCheck p.1 p.2) := by
  change
    Computable
      (fun p : DQLSystem eqs vars × ℕ ↦
        dqlFiniteCheck (dqlSystemCodeEquiv eqs vars p.1)
          (decodeSignedWitness vars p.2))
  exact
    @Computable.comp
      (DQLSystem eqs vars × ℕ)
      (DQLFiniteCode eqs vars × (Fin vars → SignedCode))
      Bool
      inferInstance inferInstance inferInstance
      (fun q ↦ dqlFiniteCheck q.1 q.2)
      (fun p ↦
        (dqlSystemCodeEquiv eqs vars p.1,
          decodeSignedWitness vars p.2))
      (dqlFiniteCheck_primrec
        (eqs := eqs) (vars := vars)).to_comp
      dqlCodeWitnessPair_computable

/-- Correctness of the executable checker: it accepts exactly when the
decoded integer vector satisfies the original DQL system. -/
theorem dqlNatWitnessCheck_eq_true_iff {eqs vars : ℕ}
    (I : DQLSystem eqs vars) (n : ℕ) :
    dqlNatWitnessCheck I n = true ↔
      I.Satisfies (decodeIntegerWitness vars n) := by
  rw [dqlNatWitnessCheck, dqlFiniteCheck_eq_true_iff]
  simp only [finiteCodeQuadratic_systemCode,
    finiteCodeLinear_systemCode, finiteCodeRhs_systemCode,
    signedCodeValue_intCode]
  unfold DQLSystem.Satisfies decodeIntegerWitness
  rfl

/-- The computable relation between a system and one natural-coded
witness. -/
def DQLSystem.NatWitnessRelation {eqs vars : ℕ}
    (I : DQLSystem eqs vars) (n : ℕ) : Prop :=
  dqlNatWitnessCheck I n = true

instance {eqs vars : ℕ} :
    DecidableRel
      (DQLSystem.NatWitnessRelation :
        DQLSystem eqs vars → ℕ → Prop) :=
  fun I n ↦ by
    unfold DQLSystem.NatWitnessRelation
    infer_instance

theorem DQLSystem.natWitnessRelation_iff_satisfies
    {eqs vars : ℕ} (I : DQLSystem eqs vars) (n : ℕ) :
    I.NatWitnessRelation n ↔
      I.Satisfies (decodeIntegerWitness vars n) :=
  dqlNatWitnessCheck_eq_true_iff I n

theorem dqlNatWitnessRelation_computable {eqs vars : ℕ} :
    ComputablePred
      (fun p : DQLSystem eqs vars × ℕ ↦
        p.1.NatWitnessRelation p.2) := by
  refine ComputablePred.computable_iff.mpr ?_
  exact ⟨_, dqlNatWitnessCheck_computable, rfl⟩

/-- A reusable unbounded-search lemma.  Existential quantification over a
natural-coded witness turns a computable relation into an r.e. predicate. -/
theorem rePred_exists_nat_of_computableRel
    {α : Type*} [Primcodable α]
    (R : α → ℕ → Prop)
    (hR : ComputablePred (fun p : α × ℕ ↦ R p.1 p.2)) :
    REPred (fun a ↦ ∃ n, R a n) := by
  let pairDecision :
      DecidablePred (fun p : α × ℕ ↦ R p.1 p.2) :=
    hR.choose
  letI : DecidableRel R :=
    fun a n ↦ pairDecision (a, n)
  have hsearch :
      Partrec
        (fun a ↦ Nat.rfind
          (fun n ↦ Part.some (decide (R a n)))) :=
    Partrec.rfind hR.decide.partrec
  refine (Partrec.dom_re hsearch).of_eq ?_
  intro a
  rw [Nat.rfind_dom]
  simp

theorem DQLSystem.solvable_iff_exists_natWitness
    {eqs vars : ℕ} (I : DQLSystem eqs vars) :
    I.Solvable ↔ ∃ n, I.NatWitnessRelation n := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨n, hn⟩ := decodeIntegerWitness_surjective vars x
    refine ⟨n, ?_⟩
    rw [I.natWitnessRelation_iff_satisfies, hn]
    exact hx
  · rintro ⟨n, hn⟩
    exact ⟨decodeIntegerWitness vars n,
      (I.natWitnessRelation_iff_satisfies n).mp hn⟩

/-- For every fixed finite number of equations and variables, solvability
of encoded DQL systems is recursively enumerable. -/
theorem DQLSystem.solvable_re (eqs vars : ℕ) :
    REPred
      (DQLSystem.Solvable :
        DQLSystem eqs vars → Prop) := by
  apply REPred.of_eq
    (rePred_exists_nat_of_computableRel
      DQLSystem.NatWitnessRelation
      (dqlNatWitnessRelation_computable
        (eqs := eqs) (vars := vars)))
  intro I
  exact (I.solvable_iff_exists_natWitness).symm

end HGAS
