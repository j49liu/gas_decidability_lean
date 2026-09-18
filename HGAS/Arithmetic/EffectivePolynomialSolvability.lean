import HGAS.Arithmetic.UniversalHaltingDiophantineGap
import HGAS.Arithmetic.DQLEnumerability
import HGAS.Computability.SigmaOne
import Mathlib.Computability.Primrec.List
import Mathlib.Tactic

/-!
# Effective specialization and sparse-polynomial solvability

A finite Diophantine representation is useful for a hardness reduction
only after its parameter substitution has been shown computable.  This
file supplies that missing effective layer for the sparse polynomial
syntax used throughout `HGAS.Arithmetic`.

The construction is independent of DPRM:

* parameter substitution in a sparse integer polynomial is primitive
  recursive;
* evaluation of sparse integer polynomials is represented by a primitive
  recursive signed-magnitude evaluator;
* existential natural-zero solvability is recursively enumerable;
* every finite Diophantine representation induces a computable many-one
  reduction to that solvability language.

At the end we instantiate these generic results with the conditional
universal-halting representation from
`UniversalHaltingDiophantineGap`.  Consequently the only remaining
arithmetic hypothesis in that instantiation is the explicitly named
primitive-recursive-to-Diophantine closure theorem.
-/

namespace HGAS

open Encodable

namespace IntegerPolynomialCode

/-! ## Primitive-recursive sparse parameter substitution -/

variable {m k : ℕ}

/-- Raising two natural numbers to a natural power is primitive
recursive. -/
theorem natPow_primrec₂ : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  by
    have hstep :
        Primrec₂
          (fun base : ℕ => fun state : ℕ × ℕ =>
            state.2 * base) := by
      exact
        (Primrec.nat_mul.comp
          (Primrec.snd.comp Primrec.snd)
          Primrec.fst).to₂
    exact
      (Primrec.nat_rec (Primrec.const 1) hstep).of_eq
        fun base exponent => by
          induction exponent with
          | zero => rfl
          | succ exponent ih =>
              simp only [ih, pow_succ]

/-- The parameter factor of a monomial is primitive recursive jointly in
the parameter tuple and the exponent vector. -/
theorem parameterFactor_primrec :
    Primrec₂
      (parameterFactor :
        (Fin m → ℕ) → ExponentCode (m + k) → ℕ) := by
  let entries :
      ((Fin m → ℕ) × ExponentCode (m + k)) → List ℕ :=
    fun input =>
      List.ofFn fun i =>
        input.1 i ^ input.2 (Fin.castAdd k i)
  have hentries : Primrec entries := by
    apply Primrec.list_ofFn
    intro i
    apply natPow_primrec₂.comp
    · exact Primrec.fin_app.comp Primrec.fst (Primrec.const i)
    · exact Primrec.fin_app.comp Primrec.snd
        (Primrec.const (Fin.castAdd k i))
  have hmul :
      Primrec₂
        (fun (_ :
            (Fin m → ℕ) × ExponentCode (m + k))
          (state : ℕ × ℕ) => state.1 * state.2) := by
    exact
      (Primrec.nat_mul.comp
        (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)).to₂
  exact
    (Primrec.list_foldl hentries (Primrec.const 1) hmul).to₂.of_eq
      fun parameters exponent => by
        simp only [entries, parameterFactor]
        rw [List.prod_eq_foldl]

/-- Restriction of an exponent vector to witness coordinates is primitive
recursive. -/
theorem witnessExponent_primrec :
    Primrec
      (witnessExponent :
        ExponentCode (m + k) → ExponentCode k) := by
  apply Primrec.fin_curry.mpr
  have hindex :
      Primrec (Fin.natAdd m : Fin k → Fin (m + k)) := by
    apply Primrec.fin_val_iff.mp
    exact
      Primrec.nat_add.comp
        (Primrec.const m) Primrec.fin_val
  exact
    (Primrec.fin_app.comp
      Primrec.fst (hindex.comp Primrec.snd)).to₂

/-- Substitution in one sparse term is primitive recursive. -/
theorem specializeTerm_primrec :
    Primrec₂
      (specializeTerm :
        (Fin m → ℕ) →
          (ExponentCode (m + k) × SignedMagnitudeCode) →
            ExponentCode k × SignedMagnitudeCode) := by
  have hfactor :
      Primrec
        (fun input :
            (Fin m → ℕ) ×
              (ExponentCode (m + k) × SignedMagnitudeCode) =>
          parameterFactor input.1 input.2.1) :=
    parameterFactor_primrec.comp Primrec.fst
      (Primrec.fst.comp Primrec.snd)
  have hfactorCode :
      Primrec
        (fun input :
            (Fin m → ℕ) ×
              (ExponentCode (m + k) × SignedMagnitudeCode) =>
          SignedMagnitudeCode.encode
            (parameterFactor input.1 input.2.1 : ℤ)) := by
    exact
      (Primrec.pair (Primrec.const false) hfactor).of_eq
        fun _ => rfl
  exact
    (Primrec.pair
      (witnessExponent_primrec.comp
        (Primrec.fst.comp Primrec.snd))
      (SignedMagnitudeCode.mul_primrec.comp
        (Primrec.snd.comp Primrec.snd)
        hfactorCode)).to₂.of_eq fun _ _ => rfl

/-- Sparse parameter substitution is primitive recursive jointly in the
polynomial and parameter tuple. -/
theorem specializeParameters_primrec :
    Primrec₂
      (specializeParameters :
        IntegerPolynomialCode (m + k) →
          (Fin m → ℕ) → IntegerPolynomialCode k) := by
  have hmap :
      Primrec
        (fun input :
            IntegerPolynomialCode (m + k) × (Fin m → ℕ) =>
          input.1.map (specializeTerm input.2)) := by
    exact
      (Primrec.list_map Primrec.fst
        (specializeTerm_primrec.comp₂
          (Primrec.snd.comp₂ Primrec₂.left)
          Primrec₂.right)).of_eq fun _ => rfl
  exact hmap.to₂.of_eq fun _ _ => rfl

/-- Specialization of a fixed sparse polynomial is a total computable
map of its parameter tuple. -/
theorem specializeParameters_fixed_computable
    (polynomial : IntegerPolynomialCode (m + k)) :
    Computable
      (specializeParameters polynomial :
        (Fin m → ℕ) → IntegerPolynomialCode k) :=
  (specializeParameters_primrec.comp
    (Primrec.const polynomial) Primrec.id).to_comp

end IntegerPolynomialCode

namespace NaturalPolynomialCode

/-! ## A primitive-recursive monomial evaluator -/

variable {n : ℕ}

/-- Sparse monomial evaluation is primitive recursive jointly in the
exponent vector and the point. -/
theorem evalMonomial_primrec₂ :
    Primrec₂
      (evalMonomial :
        ExponentCode n → (Fin n → ℕ) → ℕ) := by
  let entries :
      (ExponentCode n × (Fin n → ℕ)) → List ℕ :=
    fun input =>
      List.ofFn fun i => input.2 i ^ input.1 i
  have hentries : Primrec entries := by
    apply Primrec.list_ofFn
    intro i
    apply IntegerPolynomialCode.natPow_primrec₂.comp
    · exact Primrec.fin_app.comp Primrec.snd (Primrec.const i)
    · exact Primrec.fin_app.comp Primrec.fst (Primrec.const i)
  have hmul :
      Primrec₂
        (fun (_ : ExponentCode n × (Fin n → ℕ))
          (state : ℕ × ℕ) => state.1 * state.2) := by
    exact
      (Primrec.nat_mul.comp
        (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)).to₂
  exact
    (Primrec.list_foldl hentries (Primrec.const 1) hmul).to₂.of_eq
      fun exponent point => by
        simp only [entries, evalMonomial]
        rw [List.prod_eq_foldl]

end NaturalPolynomialCode

namespace IntegerPolynomialCode

variable {n : ℕ}

/-- Signed-magnitude value of one sparse term. -/
def evalTermCode (point : Fin n → ℕ)
    (term : ExponentCode n × SignedMagnitudeCode) :
    SignedMagnitudeCode :=
  SignedMagnitudeCode.mul term.2
    (SignedMagnitudeCode.encode
      (NaturalPolynomialCode.evalMonomial term.1 point : ℤ))

/-- Evaluate a sparse integer polynomial while remaining entirely in the
primitive-codable signed-magnitude representation. -/
def evalCode (polynomial : IntegerPolynomialCode n)
    (point : Fin n → ℕ) : SignedMagnitudeCode :=
  (polynomial.map (evalTermCode point)).foldr
    SignedMagnitudeCode.add (SignedMagnitudeCode.encode 0)

@[simp]
theorem decode_evalTermCode
    (point : Fin n → ℕ)
    (term : ExponentCode n × SignedMagnitudeCode) :
    SignedMagnitudeCode.decode (evalTermCode point term) =
      SignedMagnitudeCode.decode term.2 *
        (NaturalPolynomialCode.evalMonomial term.1 point : ℤ) := by
  simp [evalTermCode, SignedMagnitudeCode.decode_mul]

@[simp]
theorem decode_evalCode
    (polynomial : IntegerPolynomialCode n)
    (point : Fin n → ℕ) :
    SignedMagnitudeCode.decode (evalCode polynomial point) =
      eval polynomial point := by
  induction polynomial with
  | nil =>
      simp [evalCode]
  | cons term polynomial ih =>
      rw [show evalCode (term :: polynomial) point =
          SignedMagnitudeCode.add
            (evalTermCode point term)
            (evalCode polynomial point) by rfl]
      rw [SignedMagnitudeCode.decode_add,
        decode_evalTermCode, ih]
      rfl

/-- One-term signed-magnitude evaluation is primitive recursive. -/
theorem evalTermCode_primrec₂ :
    Primrec₂
      (evalTermCode :
        (Fin n → ℕ) →
          (ExponentCode n × SignedMagnitudeCode) →
            SignedMagnitudeCode) := by
  have hmonomial :
      Primrec
        (fun input :
            (Fin n → ℕ) ×
              (ExponentCode n × SignedMagnitudeCode) =>
          NaturalPolynomialCode.evalMonomial input.2.1 input.1) :=
    NaturalPolynomialCode.evalMonomial_primrec₂.comp
      (Primrec.fst.comp Primrec.snd) Primrec.fst
  have hmonomialCode :
      Primrec
        (fun input :
            (Fin n → ℕ) ×
              (ExponentCode n × SignedMagnitudeCode) =>
          SignedMagnitudeCode.encode
            (NaturalPolynomialCode.evalMonomial
              input.2.1 input.1 : ℤ)) := by
    exact
      (Primrec.pair (Primrec.const false) hmonomial).of_eq
        fun _ => rfl
  exact
    (SignedMagnitudeCode.mul_primrec.comp
      (Primrec.snd.comp Primrec.snd)
      hmonomialCode).to₂.of_eq fun _ _ => rfl

/-- The signed-magnitude evaluator is primitive recursive jointly in the
sparse polynomial and the point. -/
theorem evalCode_primrec₂ :
    Primrec₂
      (evalCode :
        IntegerPolynomialCode n →
          (Fin n → ℕ) → SignedMagnitudeCode) := by
  let codedTerms :
      (IntegerPolynomialCode n × (Fin n → ℕ)) →
        List SignedMagnitudeCode :=
    fun input => input.1.map (evalTermCode input.2)
  have hcodedTerms : Primrec codedTerms := by
    exact
      (Primrec.list_map Primrec.fst
        (evalTermCode_primrec₂.comp₂
          (Primrec.snd.comp₂ Primrec₂.left)
          Primrec₂.right)).of_eq fun _ => rfl
  have hadd :
      Primrec₂
        (fun (_ :
            IntegerPolynomialCode n × (Fin n → ℕ))
          (state : SignedMagnitudeCode × SignedMagnitudeCode) =>
            SignedMagnitudeCode.add state.1 state.2) := by
    exact
      (SignedMagnitudeCode.add_primrec.comp
        (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)).to₂
  exact
    (Primrec.list_foldr hcodedTerms
      (Primrec.const (SignedMagnitudeCode.encode 0))
      hadd).to₂.of_eq fun _ _ => rfl

/-- Boolean zero test for the signed-magnitude evaluator. -/
def evalCodeZero (polynomial : IntegerPolynomialCode n)
    (point : Fin n → ℕ) : Bool :=
  SignedMagnitudeCode.equal (evalCode polynomial point)
    (SignedMagnitudeCode.encode 0)

@[simp]
theorem evalCodeZero_eq_true_iff
    (polynomial : IntegerPolynomialCode n)
    (point : Fin n → ℕ) :
    evalCodeZero polynomial point = true ↔
      eval polynomial point = 0 := by
  rw [evalCodeZero, SignedMagnitudeCode.equal_eq_true_iff,
    decode_evalCode, SignedMagnitudeCode.decode_encode]

/-- The Boolean zero checker is primitive recursive. -/
theorem evalCodeZero_primrec₂ :
    Primrec₂
      (evalCodeZero :
        IntegerPolynomialCode n → (Fin n → ℕ) → Bool) := by
  exact
    (SignedMagnitudeCode.equal_primrec.comp
      evalCode_primrec₂
      (Primrec.const (SignedMagnitudeCode.encode 0))).to₂.of_eq
        fun _ _ => rfl

end IntegerPolynomialCode

/-! ## Natural-zero solvability as a c.e. language -/

/-- Decode one natural number as a finite tuple of natural witnesses. -/
def decodeNaturalWitness (n : ℕ) (code : ℕ) : Fin n → ℕ :=
  (@decode (Fin n → ℕ)
    (@Primcodable.toEncodable (Fin n → ℕ) inferInstance)
    code).getD (fun _ => 0)

/-- Tuple decoding is primitive recursive. -/
theorem decodeNaturalWitness_primrec (n : ℕ) :
    Primrec (decodeNaturalWitness n) := by
  simpa only [decodeNaturalWitness] using
    (Primrec.option_getD_default.comp
      (Primrec.decode (α := Fin n → ℕ)))

/-- Every finite natural tuple has a natural-number code. -/
theorem decodeNaturalWitness_surjective (n : ℕ) :
    Function.Surjective (decodeNaturalWitness n) := by
  intro witness
  let code :=
    @encode (Fin n → ℕ)
      (@Primcodable.toEncodable (Fin n → ℕ) inferInstance)
      witness
  refine ⟨code, ?_⟩
  simp [decodeNaturalWitness, code, Encodable.encodek]

namespace IntegerPolynomialCode

variable {n : ℕ}

/-- Existential natural-zero solvability for sparse integer polynomial
codes in a fixed number of variables. -/
def HasNaturalZero (polynomial : IntegerPolynomialCode n) : Prop :=
  ∃ point : Fin n → ℕ, eval polynomial point = 0

/-- Natural-coded witness relation used for unbounded search. -/
def NaturalZeroWitnessRelation
    (polynomial : IntegerPolynomialCode n) (code : ℕ) : Prop :=
  evalCodeZero polynomial (decodeNaturalWitness n code) = true

instance naturalZeroWitnessRelationDecidable :
    DecidableRel
      (NaturalZeroWitnessRelation :
        IntegerPolynomialCode n → ℕ → Prop) :=
  fun _ _ => by
    unfold NaturalZeroWitnessRelation
    infer_instance

/-- The natural-coded witness relation is computable. -/
theorem naturalZeroWitnessRelation_computable :
    ComputablePred
      (fun input : IntegerPolynomialCode n × ℕ =>
        NaturalZeroWitnessRelation input.1 input.2) := by
  refine ComputablePred.computable_iff.mpr ?_
  refine ⟨
    (fun input : IntegerPolynomialCode n × ℕ =>
      evalCodeZero input.1
        (decodeNaturalWitness n input.2)), ?_, rfl⟩
  exact
    evalCodeZero_primrec₂.to_comp.comp
      Computable.fst
      ((decodeNaturalWitness_primrec n).to_comp.comp
        Computable.snd)

/-- Natural-coded witnesses express exactly existential tuple
solvability. -/
theorem hasNaturalZero_iff_exists_natWitness
    (polynomial : IntegerPolynomialCode n) :
    polynomial.HasNaturalZero ↔
      ∃ code, NaturalZeroWitnessRelation polynomial code := by
  constructor
  · rintro ⟨point, hpoint⟩
    obtain ⟨code, hcode⟩ :=
      decodeNaturalWitness_surjective n point
    refine ⟨code, ?_⟩
    rw [NaturalZeroWitnessRelation,
      evalCodeZero_eq_true_iff, hcode]
    exact hpoint
  · rintro ⟨code, hcode⟩
    exact ⟨decodeNaturalWitness n code,
      (evalCodeZero_eq_true_iff _ _).mp hcode⟩

/-- For every fixed variable count, sparse integer polynomial
natural-zero solvability is recursively enumerable. -/
theorem hasNaturalZero_re (n : ℕ) :
    REPred
      (HasNaturalZero :
        IntegerPolynomialCode n → Prop) := by
  apply REPred.of_eq
    (rePred_exists_nat_of_computableRel
      NaturalZeroWitnessRelation
      (naturalZeroWitnessRelation_computable (n := n)))
  intro polynomial
  exact polynomial.hasNaturalZero_iff_exists_natWitness.symm

end IntegerPolynomialCode

/-! ## Effective reductions supplied by finite representations -/

namespace FiniteDiophantineRepresentation

variable {m : ℕ} {set : Set (Fin m → ℕ)}

/-- A finite Diophantine representation induces an explicit computable
many-one reduction from membership in the represented set to sparse
polynomial natural-zero solvability. -/
theorem manyOneReducible_hasNaturalZero
    (representation : FiniteDiophantineRepresentation m set) :
    (fun parameters => parameters ∈ set) ≤₀
      (IntegerPolynomialCode.HasNaturalZero :
        IntegerPolynomialCode representation.witnessCount → Prop) := by
  refine ⟨
    fun parameters =>
      IntegerPolynomialCode.specializeParameters
        representation.polynomial parameters,
    IntegerPolynomialCode.specializeParameters_fixed_computable
      representation.polynomial,
    ?_⟩
  intro parameters
  simpa only [IntegerPolynomialCode.HasNaturalZero,
    IntegerPolynomialCode.eval_specializeParameters] using
      representation.represents parameters

end FiniteDiophantineRepresentation

namespace UniversalHalting

/-- Conditional only on the named DPRM closure theorem, universal
halting many-one reduces effectively to sparse-polynomial natural-zero
solvability in one fixed number of variables. -/
theorem predicate_manyOneReducible_hasNaturalZero
    (closure :
      BinaryPrimitiveRecursiveRelationsAreDiophantine) :
    Predicate ≤₀
      (IntegerPolynomialCode.HasNaturalZero :
        IntegerPolynomialCode
          (universalHaltingRepresentationOfPrimitiveRecursiveClosure
            closure).witnessCount → Prop) := by
  exact
    predicate_manyOneEquiv_unarySet.1.trans
      ((universalHaltingRepresentationOfPrimitiveRecursiveClosure
        closure).manyOneReducible_hasNaturalZero)

/-- The fixed-variable sparse-polynomial natural-zero language is
`Σ⁰₁`-complete, conditional only on the precise primitive-recursive
Diophantine closure statement isolated in
`UniversalHaltingDiophantineGap`. -/
theorem hasNaturalZero_sigmaOneComplete
    (closure :
      BinaryPrimitiveRecursiveRelationsAreDiophantine) :
    SigmaOneComplete
      (IntegerPolynomialCode.HasNaturalZero :
        IntegerPolynomialCode
          (universalHaltingRepresentationOfPrimitiveRecursiveClosure
            closure).witnessCount → Prop) := by
  constructor
  · exact
      IntegerPolynomialCode.hasNaturalZero_re
        (universalHaltingRepresentationOfPrimitiveRecursiveClosure
          closure).witnessCount
  · intro predicate hpredicate
    exact
      (re_manyOneReducible_predicate hpredicate).trans
        (predicate_manyOneReducible_hasNaturalZero closure)

/-- In particular, the same sparse-polynomial solvability language is
not computable. -/
theorem hasNaturalZero_not_computable
    (closure :
      BinaryPrimitiveRecursiveRelationsAreDiophantine) :
    ¬ComputablePred
      (IntegerPolynomialCode.HasNaturalZero :
        IntegerPolynomialCode
          (universalHaltingRepresentationOfPrimitiveRecursiveClosure
            closure).witnessCount → Prop) :=
  (hasNaturalZero_sigmaOneComplete closure).not_computable

end UniversalHalting

end HGAS
