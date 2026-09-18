import HGAS.Foundation.FinitePolynomialCode
import HGAS.Lyapunov.SOSCertificate
import Mathlib.Computability.RE
import Mathlib.Tactic

/-!
# Effective enumeration of rational SOS-margin certificates

This file turns the semantic certificates from `SOSCertificate.lean` into a
finite, executable certificate language.

A candidate strict-margin certificate consists only of

* a rational code for `ε`, and
* a list of sparse polynomial codes for the proposed square roots.

The checker verifies, using exact integer/natural arithmetic:

1. `ε > 0`;
2. every square root is homogeneous of degree `k`; and
3. the exact polynomial identity
   `p - ε ρ^k = ∑ sᵢ²`.

No floating-point calculation is involved.  Soundness converts every
accepted code into `StrictHomogeneousMarginCertificate`.  Conversely, every
semantic certificate over `ℚ` has some accepted finite code.  This is an
enumeration theorem for this certificate class only; it does **not** assert
that every positive form possesses such an SOS certificate.
-/

namespace HGAS

open MvPolynomial
open scoped BigOperators

variable {n : ℕ}

/-! ## A code for the radial polynomial -/

namespace ExponentCode

/-- Exponent vector of the monomial `X i ^ 2`. -/
def variableSquare (i : Fin n) : ExponentCode n :=
  fun j ↦ if j = i then 2 else 0

@[simp]
theorem decode_variableSquare (i : Fin n) :
    decode (variableSquare i) = Finsupp.single i 2 := by
  ext j
  simp [variableSquare, decode, Finsupp.single_apply, eq_comm]

end ExponentCode

namespace PolynomialCode

/-- Sparse code for `ρ = ∑ i, X i ^ 2`. -/
def rho (n : ℕ) : PolynomialCode n :=
  List.ofFn fun i : Fin n ↦
    (ExponentCode.variableSquare i, RationalCode.one)

@[simp]
theorem decode_rho (n : ℕ) :
    decode (rho n) = rhoPolynomial (n := n) := by
  rw [rho, decode, rhoPolynomial]
  simp only [List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Function.comp_apply, decodeTerm, ← X_pow_eq_monomial]

end PolynomialCode

/-! ## Finite SOS codes and their checker -/

/-- A finite SOS code is just the list of its rational square roots. -/
abbrev SOSListCode (n : ℕ) :=
  List (PolynomialCode n)

/-- Sum the squares represented by a finite SOS list. -/
def sumSquaresCode (squares : SOSListCode n) : PolynomialCode n :=
  squares.foldr
    (fun s acc ↦
      PolynomialCode.add (PolynomialCode.mul s s) acc)
    PolynomialCode.zero

@[simp]
theorem decode_sumSquaresCode (squares : SOSListCode n) :
    PolynomialCode.decode (sumSquaresCode squares) =
      (squares.map fun s ↦ PolynomialCode.decode s ^ 2).sum := by
  unfold sumSquaresCode
  induction squares with
  | nil => simp
  | cons s squares ih =>
      simp [ih, pow_two]

/-- Exact Boolean checker for an SOS identity with a coded target. -/
def checkSOS (target : PolynomialCode n) (squares : SOSListCode n) :
    Bool :=
  PolynomialCode.equal target (sumSquaresCode squares)

@[simp]
theorem checkSOS_eq_true_iff
    (target : PolynomialCode n) (squares : SOSListCode n) :
    checkSOS target squares = true ↔
      PolynomialCode.decode target =
        (squares.map fun s ↦ PolynomialCode.decode s ^ 2).sum := by
  simp [checkSOS]

/-! ## Strict homogeneous margin codes -/

/-- A candidate strict homogeneous margin: a rational `ε` and a finite list
of proposed homogeneous square roots. -/
abbrev StrictMarginCode (n : ℕ) :=
  RationalCode × SOSListCode n

/-- Coded polynomial `p - ε ρ^k`. -/
def strictMarginTargetCode
    (p : PolynomialCode n) (epsilon : RationalCode) (k : ℕ) :
    PolynomialCode n :=
  PolynomialCode.sub p
    (PolynomialCode.mul
      (PolynomialCode.constant epsilon)
      (PolynomialCode.pow (PolynomialCode.rho n) k))

@[simp]
theorem decode_strictMarginTargetCode
    (p : PolynomialCode n) (epsilon : RationalCode) (k : ℕ) :
    PolynomialCode.decode (strictMarginTargetCode p epsilon k) =
      PolynomialCode.decode p -
        C (RationalCode.decode epsilon) *
          (rhoPolynomial (n := n)) ^ k := by
  simp [strictMarginTargetCode]

/-- Exact checker for a strict homogeneous SOS margin. -/
def checkStrictMargin
    (p : PolynomialCode n) (k : ℕ) (candidate : StrictMarginCode n) :
    Bool :=
  RationalCode.positive candidate.1 &&
    candidate.2.all (PolynomialCode.homogeneous k) &&
      checkSOS
        (strictMarginTargetCode p candidate.1 k)
        candidate.2

@[simp]
theorem checkStrictMargin_eq_true_iff
    (p : PolynomialCode n) (k : ℕ) (candidate : StrictMarginCode n) :
    checkStrictMargin p k candidate = true ↔
      0 < RationalCode.decode candidate.1 ∧
      (∀ s ∈ candidate.2,
        (PolynomialCode.decode s).IsHomogeneous k) ∧
      PolynomialCode.decode p -
          C (RationalCode.decode candidate.1) *
            (rhoPolynomial (n := n)) ^ k =
        (candidate.2.map fun s ↦
          PolynomialCode.decode s ^ 2).sum := by
  simp only [checkStrictMargin, Bool.and_eq_true,
    RationalCode.positive_eq_true_iff, List.all_eq_true,
    PolynomialCode.homogeneous_eq_true_iff,
    checkSOS_eq_true_iff, decode_strictMarginTargetCode]
  tauto

/-! ## Soundness and exhaustiveness -/

/-- Every accepted finite code produces the semantic SOS certificate used
by the analytic soundness theorems. -/
noncomputable def strictMarginCertificateOfCheck
    (p : PolynomialCode n) (k : ℕ) (candidate : StrictMarginCode n)
    (hcheck : checkStrictMargin p k candidate = true) :
    StrictHomogeneousMarginCertificate
      (PolynomialCode.decode p) k := by
  have h := (checkStrictMargin_eq_true_iff p k candidate).mp hcheck
  refine
    { epsilon := RationalCode.decode candidate.1
      epsilon_pos := h.1
      sos :=
        { numSquares := candidate.2.length
          square := fun i ↦ PolynomialCode.decode (candidate.2.get i)
          identity := ?_ }
      square_homogeneous := ?_ }
  · rw [h.2.2]
    exact (Fin.sum_univ_fun_getElem candidate.2
      (fun s ↦ PolynomialCode.decode s ^ 2)).symm
  · intro i
    exact h.2.1 (candidate.2.get i) (List.get_mem candidate.2 i)

/-- Encode a semantic strict-margin certificate as finite data.  This
definition uses the semantic polynomial encoder, so it is used only to
prove exhaustiveness of the raw enumeration, not by the checker. -/
noncomputable def strictMarginCodeOfCertificate
    {p : MvPolynomial (Fin n) ℚ} {k : ℕ}
    (cert : StrictHomogeneousMarginCertificate p k) :
    StrictMarginCode n :=
  (RationalCode.encode cert.epsilon,
    List.ofFn fun i ↦ PolynomialCode.encode (cert.sos.square i))

/-- Every semantic rational strict-margin certificate is represented by an
accepted finite code. -/
theorem check_strictMarginCodeOfCertificate
    {p : MvPolynomial (Fin n) ℚ} {k : ℕ}
    (cert : StrictHomogeneousMarginCertificate p k) :
    checkStrictMargin (PolynomialCode.encode p) k
      (strictMarginCodeOfCertificate cert) = true := by
  rw [checkStrictMargin_eq_true_iff]
  refine ⟨by
    simpa [strictMarginCodeOfCertificate] using cert.epsilon_pos, ?_, ?_⟩
  · intro s hs
    simp only [strictMarginCodeOfCertificate] at hs
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hs
    simpa using cert.square_homogeneous i
  · rw [PolynomialCode.decode_encode]
    simp only [strictMarginCodeOfCertificate]
    rw [RationalCode.decode_encode]
    calc
      p - C cert.epsilon * (rhoPolynomial (n := n)) ^ k =
          ∑ i, cert.sos.square i ^ 2 :=
        cert.sos.identity
      _ = ((List.ofFn fun i ↦
          PolynomialCode.encode (cert.sos.square i)).map
            fun s ↦ PolynomialCode.decode s ^ 2).sum := by
        simp only [List.map_ofFn, List.sum_ofFn,
          Function.comp_apply, PolynomialCode.decode_encode]

/-- Accepted finite codes are equivalent to semantic rational strict-margin
certificates.  The backward implication uses the canonical finite encoder;
it makes no completeness claim beyond this SOS certificate class. -/
theorem exists_checked_strictMargin_iff
    (p : MvPolynomial (Fin n) ℚ) (k : ℕ) :
    (∃ candidate : StrictMarginCode n,
        checkStrictMargin (PolynomialCode.encode p) k candidate = true) ↔
      Nonempty (StrictHomogeneousMarginCertificate p k) := by
  constructor
  · rintro ⟨candidate, hcandidate⟩
    exact ⟨by
      simpa using
        strictMarginCertificateOfCheck
          (PolynomialCode.encode p) k candidate hcandidate⟩
  · rintro ⟨cert⟩
    exact ⟨strictMarginCodeOfCertificate cert,
      check_strictMarginCodeOfCertificate cert⟩

/-! The candidate language is primitive-codable, so `Encodable.decode`
gives a single exhaustive natural-number enumeration. -/

example (n : ℕ) : Primcodable (SOSListCode n) := inferInstance
example (n : ℕ) : Primcodable (StrictMarginCode n) := inferInstance

/-- Natural-number enumeration of all candidate strict-margin codes. -/
def decodeStrictMarginCandidate (n code : ℕ) :
    Option (StrictMarginCode n) :=
  @Encodable.decode (StrictMarginCode n)
    (@Primcodable.toEncodable (StrictMarginCode n) inferInstance) code

/-- The natural-number enumeration is exhaustive. -/
theorem decodeStrictMarginCandidate_surjective
    (candidate : StrictMarginCode n) :
    ∃ code, decodeStrictMarginCandidate n code = some candidate := by
  let code :=
    @Encodable.encode (StrictMarginCode n)
      (@Primcodable.toEncodable (StrictMarginCode n) inferInstance)
      candidate
  refine ⟨code, ?_⟩
  simp [decodeStrictMarginCandidate, code]

/-! ## Primitive-recursive checking and the RE theorem -/

private theorem boolListAll_primrec :
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

theorem sumSquaresCode_primrec {n : ℕ} :
    Primrec (sumSquaresCode : SOSListCode n → PolynomialCode n) := by
  have hstep :
      Primrec₂
        (fun (_ : SOSListCode n)
          (p : PolynomialCode n × PolynomialCode n) ↦
            PolynomialCode.add
              (PolynomialCode.mul p.1 p.1) p.2) :=
    PolynomialCode.add_primrec.comp₂
      (PolynomialCode.mul_primrec.comp₂
        (Primrec.fst.comp₂ Primrec₂.right)
        (Primrec.fst.comp₂ Primrec₂.right))
      (Primrec.snd.comp₂ Primrec₂.right)
  exact
    (Primrec.list_foldr Primrec.id
      (Primrec.const PolynomialCode.zero) hstep).of_eq
      fun _ ↦ rfl

theorem checkSOS_primrec {n : ℕ} :
    Primrec₂ (checkSOS :
      PolynomialCode n → SOSListCode n → Bool) := by
  exact PolynomialCode.equal_primrec.comp Primrec.fst
    (sumSquaresCode_primrec.comp Primrec.snd)

theorem strictMarginTargetCode_primrec {n : ℕ} :
    Primrec
      (fun q : (PolynomialCode n × RationalCode) × ℕ ↦
        strictMarginTargetCode q.1.1 q.1.2 q.2) := by
  have hpower :
      Primrec
        (fun q : (PolynomialCode n × RationalCode) × ℕ ↦
          PolynomialCode.pow (PolynomialCode.rho n) q.2) :=
    PolynomialCode.pow_primrec.comp
      (Primrec.const (PolynomialCode.rho n))
      Primrec.snd
  have hconstant :
      Primrec
        (fun q : (PolynomialCode n × RationalCode) × ℕ ↦
          (PolynomialCode.constant (n := n) q.1.2 :
            PolynomialCode n)) :=
    (PolynomialCode.constant_primrec (n := n)).comp
      (Primrec.snd.comp Primrec.fst)
  exact (PolynomialCode.sub_primrec (n := n)).comp
    (Primrec.fst.comp Primrec.fst)
    ((PolynomialCode.mul_primrec (n := n)).comp hconstant hpower)

/-- The full checker is primitive recursive, uniformly in the coded target,
the degree parameter, and the candidate certificate. -/
theorem checkStrictMargin_primrec {n : ℕ} :
    Primrec
      (fun q :
          (PolynomialCode n × ℕ) × StrictMarginCode n ↦
        checkStrictMargin q.1.1 q.1.2 q.2) := by
  have hpositive :
      Primrec
        (fun q :
            (PolynomialCode n × ℕ) × StrictMarginCode n ↦
          RationalCode.positive q.2.1) :=
    RationalCode.positive_primrec.comp
      (Primrec.fst.comp Primrec.snd)
  have hsquares :
      Primrec
        (fun q :
            (PolynomialCode n × ℕ) × StrictMarginCode n ↦
          q.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hhomogeneous :
      Primrec₂
        (fun (q :
            (PolynomialCode n × ℕ) × StrictMarginCode n)
          (s : PolynomialCode n) ↦
            PolynomialCode.homogeneous q.1.2 s) :=
    PolynomialCode.homogeneous_primrec.comp₂
      (Primrec.snd.comp₂
        (Primrec.fst.comp₂ Primrec₂.left))
      Primrec₂.right
  have hhomogeneousChecks :
      Primrec
        (fun q :
            (PolynomialCode n × ℕ) × StrictMarginCode n ↦
          q.2.2.map fun s ↦
            PolynomialCode.homogeneous q.1.2 s) :=
    Primrec.list_map hsquares hhomogeneous
  have hallHomogeneous :
      Primrec
        (fun q :
            (PolynomialCode n × ℕ) × StrictMarginCode n ↦
          q.2.2.all (PolynomialCode.homogeneous q.1.2)) :=
    (boolListAll_primrec.comp hhomogeneousChecks).of_eq
      fun q ↦ by simp
  have htargetInput :
      Primrec
        (fun q :
            (PolynomialCode n × ℕ) × StrictMarginCode n ↦
          ((q.1.1, q.2.1), q.1.2)) :=
    Primrec.pair
      (Primrec.pair
        (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.fst)
  have htarget :
      Primrec
        (fun q :
            (PolynomialCode n × ℕ) × StrictMarginCode n ↦
          strictMarginTargetCode q.1.1 q.2.1 q.1.2) :=
    strictMarginTargetCode_primrec.comp htargetInput
  have hsos :
      Primrec
        (fun q :
            (PolynomialCode n × ℕ) × StrictMarginCode n ↦
          checkSOS
            (strictMarginTargetCode q.1.1 q.2.1 q.1.2)
            q.2.2) :=
    checkSOS_primrec.comp htarget hsquares
  exact
    (Primrec.and.comp
      (Primrec.and.comp hpositive hallHomogeneous)
      hsos).of_eq fun _ ↦ rfl

/-- Total version of the natural-number candidate enumeration.  Invalid
natural codes denote the harmless candidate `(0, [])`. -/
def decodeStrictMarginCandidateTotal (n code : ℕ) :
    StrictMarginCode n :=
  (decodeStrictMarginCandidate n code).getD
    (RationalCode.zero, [])

theorem decodeStrictMarginCandidateTotal_primrec (n : ℕ) :
    Primrec (decodeStrictMarginCandidateTotal n) := by
  exact Primrec.option_getD.comp
    (@Primrec.decode (StrictMarginCode n) _)
    (Primrec.const (RationalCode.zero, []))

theorem decodeStrictMarginCandidateTotal_surjective (n : ℕ) :
    Function.Surjective (decodeStrictMarginCandidateTotal n) := by
  intro candidate
  obtain ⟨code, hcode⟩ :=
    decodeStrictMarginCandidate_surjective candidate
  exact ⟨code, by simp [decodeStrictMarginCandidateTotal, hcode]⟩

/-- Run the exact checker on the candidate decoded from a natural number. -/
def strictMarginNatCheck (input : PolynomialCode n × ℕ) (code : ℕ) :
    Bool :=
  checkStrictMargin input.1 input.2
    (decodeStrictMarginCandidateTotal n code)

theorem strictMarginNatCheck_primrec (n : ℕ) :
    Primrec
      (fun q : (PolynomialCode n × ℕ) × ℕ ↦
        strictMarginNatCheck q.1 q.2) := by
  have hcandidate :
      Primrec
        (fun q : (PolynomialCode n × ℕ) × ℕ ↦
          decodeStrictMarginCandidateTotal n q.2) :=
    (decodeStrictMarginCandidateTotal_primrec n).comp
      Primrec.snd
  have hinput :
      Primrec
        (fun q : (PolynomialCode n × ℕ) × ℕ ↦
          (q.1, decodeStrictMarginCandidateTotal n q.2)) :=
    Primrec.pair Primrec.fst hcandidate
  exact
    ((checkStrictMargin_primrec (n := n)).comp hinput).of_eq
      fun _ ↦ rfl

/-- The computable relation between a coded target/degree pair and one
natural-coded candidate. -/
def StrictMarginNatRelation
    (input : PolynomialCode n × ℕ) (code : ℕ) : Prop :=
  strictMarginNatCheck input code = true

instance :
    DecidableRel
      (StrictMarginNatRelation :
        (PolynomialCode n × ℕ) → ℕ → Prop) :=
  fun input code ↦ by
    unfold StrictMarginNatRelation
    infer_instance

theorem strictMarginNatRelation_computable (n : ℕ) :
    ComputablePred
      (fun q : (PolynomialCode n × ℕ) × ℕ ↦
        StrictMarginNatRelation q.1 q.2) := by
  refine ComputablePred.computable_iff.mpr ?_
  exact
    ⟨_, (strictMarginNatCheck_primrec n).to_comp, rfl⟩

/-- Existence of an accepted finite strict-margin certificate. -/
def HasCheckedStrictMargin (input : PolynomialCode n × ℕ) : Prop :=
  ∃ candidate : StrictMarginCode n,
    checkStrictMargin input.1 input.2 candidate = true

/-- On a semantic polynomial encoded by `PolynomialCode.encode`, the RE
predicate is exactly existence of the corresponding semantic strict-margin
certificate. -/
theorem hasCheckedStrictMargin_encode_iff
    (p : MvPolynomial (Fin n) ℚ) (k : ℕ) :
    HasCheckedStrictMargin (PolynomialCode.encode p, k) ↔
      Nonempty (StrictHomogeneousMarginCertificate p k) := by
  simpa only [HasCheckedStrictMargin] using
    exists_checked_strictMargin_iff p k

theorem hasCheckedStrictMargin_iff_exists_nat
    (input : PolynomialCode n × ℕ) :
    HasCheckedStrictMargin input ↔
      ∃ code, StrictMarginNatRelation input code := by
  constructor
  · rintro ⟨candidate, hcandidate⟩
    obtain ⟨code, hcode⟩ :=
      decodeStrictMarginCandidateTotal_surjective n candidate
    exact ⟨code, by
      simpa [StrictMarginNatRelation, strictMarginNatCheck,
        hcode] using hcandidate⟩
  · rintro ⟨code, hcode⟩
    exact
      ⟨decodeStrictMarginCandidateTotal n code, hcode⟩

/-- Unbounded natural-number search turns a computable witness relation
into an r.e. predicate. -/
private theorem rePred_exists_nat_of_computableRel
    {α : Type*} [Primcodable α]
    (R : α → ℕ → Prop)
    (hR : ComputablePred (fun p : α × ℕ ↦ R p.1 p.2)) :
    REPred (fun a ↦ ∃ code, R a code) := by
  let pairDecision :
      DecidablePred (fun p : α × ℕ ↦ R p.1 p.2) :=
    hR.choose
  letI : DecidableRel R :=
    fun a code ↦ pairDecision (a, code)
  have hsearch :
      Partrec
        (fun a ↦ Nat.rfind
          (fun code ↦ Part.some (decide (R a code)))) :=
    Partrec.rfind hR.decide.partrec
  refine (Partrec.dom_re hsearch).of_eq ?_
  intro a
  rw [Nat.rfind_dom]
  simp

/-- Uniform RE theorem: for each fixed variable count `n`, the coded
target/degree pairs admitting a checked rational strict SOS margin form a
recursively enumerable set. -/
theorem hasCheckedStrictMargin_re (n : ℕ) :
    REPred
      (HasCheckedStrictMargin :
        (PolynomialCode n × ℕ) → Prop) := by
  apply REPred.of_eq
    (rePred_exists_nat_of_computableRel
      StrictMarginNatRelation
      (strictMarginNatRelation_computable n))
  intro input
  exact (hasCheckedStrictMargin_iff_exists_nat input).symm

end HGAS
