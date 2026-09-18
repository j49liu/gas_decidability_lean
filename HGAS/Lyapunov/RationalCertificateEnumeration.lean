import HGAS.Foundation.PolynomialDifferentiationCode
import HGAS.Lyapunov.SOSCertificateEnumeration
import Mathlib.Computability.RE
import Mathlib.Tactic

/-!
# Enumeration of complete rational Lyapunov certificates

This module combines the exact sparse differentiation compiler with the
strict SOS-margin checker.  A finite candidate contains

* a denominator exponent `r`;
* a sparse numerator `p`;
* a strict margin certificate for `p` at exponent `r+1`;
* a homogeneous exponent `k ≥ r+1`; and
* a strict margin certificate for the exactly compiled decay numerator
  `q(F,p,r)`.

The Boolean checker performs only exact natural/integer/rational
arithmetic.  It is primitive recursive, its accepted codes are equivalent
to the corresponding semantic certificates, and existence of an accepted
code is an actual Mathlib `REPred`.

This is the effective certificate-search half of the c.e. upper bound.  It
does not by itself assert the converse theorem that every GAS homogeneous
field possesses such a certificate; that analytic/algebraic completeness
theorem is a separate module obligation.
-/

namespace HGAS

open MvPolynomial

/-- Nested-product representation of a finite rational Lyapunov
certificate candidate.

The fields are, in order, `r`, `p`, the value-margin certificate, `k`, and
the decay-margin certificate.  A product representation gives a canonical
`Primcodable` instance without adding any trusted serialization code. -/
abbrev RationalLyapunovCandidate (n : ℕ) :=
  (ℕ × PolynomialCode n) ×
    (StrictMarginCode n × (ℕ × StrictMarginCode n))

namespace RationalLyapunovCandidate

variable {n : ℕ}

def denominatorExponent (c : RationalLyapunovCandidate n) : ℕ :=
  c.1.1

def numerator (c : RationalLyapunovCandidate n) : PolynomialCode n :=
  c.1.2

def valueMargin (c : RationalLyapunovCandidate n) : StrictMarginCode n :=
  c.2.1

def decayExponent (c : RationalLyapunovCandidate n) : ℕ :=
  c.2.2.1

def decayMargin (c : RationalLyapunovCandidate n) : StrictMarginCode n :=
  c.2.2.2

end RationalLyapunovCandidate

open RationalLyapunovCandidate

/-- Exact Boolean checker for a complete coded rational Lyapunov
certificate. -/
def checkRationalLyapunov
    (F : PolynomialFieldCode n)
    (candidate : RationalLyapunovCandidate n) : Bool :=
  checkStrictMargin
      candidate.numerator
      (candidate.denominatorExponent + 1)
      candidate.valueMargin &&
    decide
      (candidate.denominatorExponent + 1 ≤
        candidate.decayExponent) &&
    checkStrictMargin
      (PolynomialCode.rationalLyapunovNumerator
        F candidate.numerator candidate.denominatorExponent)
      candidate.decayExponent
      candidate.decayMargin

@[simp]
theorem checkRationalLyapunov_eq_true_iff
    (F : PolynomialFieldCode n)
    (candidate : RationalLyapunovCandidate n) :
    checkRationalLyapunov F candidate = true ↔
      checkStrictMargin
          candidate.numerator
          (candidate.denominatorExponent + 1)
          candidate.valueMargin = true ∧
      candidate.denominatorExponent + 1 ≤
        candidate.decayExponent ∧
      checkStrictMargin
          (PolynomialCode.rationalLyapunovNumerator
            F candidate.numerator candidate.denominatorExponent)
          candidate.decayExponent
          candidate.decayMargin = true := by
  simp only [checkRationalLyapunov, Bool.and_eq_true,
    decide_eq_true_eq]
  tauto

/-- Semantic value-margin certificate extracted from an accepted finite
candidate. -/
noncomputable def valueCertificateOfCheck
    (F : PolynomialFieldCode n)
    (candidate : RationalLyapunovCandidate n)
    (hcheck : checkRationalLyapunov F candidate = true) :
    LyapunovValueMarginCertificate
      (PolynomialCode.decode candidate.numerator)
      candidate.denominatorExponent := by
  exact strictMarginCertificateOfCheck
    candidate.numerator
    (candidate.denominatorExponent + 1)
    candidate.valueMargin
    ((checkRationalLyapunov_eq_true_iff F candidate).mp hcheck).1

/-- Semantic decay-margin certificate extracted from an accepted finite
candidate. -/
noncomputable def decayCertificateOfCheck
    (F : PolynomialFieldCode n)
    (candidate : RationalLyapunovCandidate n)
    (hcheck : checkRationalLyapunov F candidate = true) :
    StrictDecayMarginCertificate
      (PolynomialFieldCode.decode F)
      (PolynomialCode.decode candidate.numerator)
      candidate.denominatorExponent
      candidate.decayExponent := by
  have hdecay :=
    ((checkRationalLyapunov_eq_true_iff F candidate).mp hcheck).2.2
  simpa using
    strictMarginCertificateOfCheck
      (PolynomialCode.rationalLyapunovNumerator
        F candidate.numerator candidate.denominatorExponent)
      candidate.decayExponent
      candidate.decayMargin hdecay

/-- The exponent inequality stored in every accepted candidate. -/
theorem denominatorExponent_le_decayExponent_of_check
    (F : PolynomialFieldCode n)
    (candidate : RationalLyapunovCandidate n)
    (hcheck : checkRationalLyapunov F candidate = true) :
    candidate.denominatorExponent + 1 ≤ candidate.decayExponent :=
  ((checkRationalLyapunov_eq_true_iff F candidate).mp hcheck).2.1

/-! ## Primitive-recursive checking -/

set_option maxHeartbeats 800000 in
-- The proof assembles a deeply nested primitive-recursive tuple program;
-- elaborating the resulting dependent compositions needs a larger budget.
theorem checkRationalLyapunov_primrec (n : ℕ) :
    Primrec
      (fun q : PolynomialFieldCode n × RationalLyapunovCandidate n ↦
        checkRationalLyapunov q.1 q.2) := by
  have hF :
      Primrec
        (fun q : PolynomialFieldCode n × RationalLyapunovCandidate n ↦
          q.1) :=
    Primrec.fst
  have hr :
      Primrec
        (fun q : PolynomialFieldCode n × RationalLyapunovCandidate n ↦
          q.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have hp :
      Primrec
        (fun q : PolynomialFieldCode n × RationalLyapunovCandidate n ↦
          q.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have hvalueCandidate :
      Primrec
        (fun q : PolynomialFieldCode n × RationalLyapunovCandidate n ↦
          q.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hk :
      Primrec
        (fun q : PolynomialFieldCode n × RationalLyapunovCandidate n ↦
          q.2.2.2.1) :=
    Primrec.fst.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hdecayCandidate :
      Primrec
        (fun q : PolynomialFieldCode n × RationalLyapunovCandidate n ↦
          q.2.2.2.2) :=
    Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hvalueInput :
      Primrec
        (fun q : PolynomialFieldCode n × RationalLyapunovCandidate n ↦
          ((q.2.1.2, q.2.1.1 + 1), q.2.2.1)) :=
    Primrec.pair
      (Primrec.pair hp (Primrec.succ.comp hr))
      hvalueCandidate
  have hvalue :
      Primrec
        (fun q : PolynomialFieldCode n × RationalLyapunovCandidate n ↦
          checkStrictMargin q.2.1.2 (q.2.1.1 + 1) q.2.2.1) :=
    (checkStrictMargin_primrec (n := n)).comp hvalueInput
  have hle :
      Primrec
        (fun q : PolynomialFieldCode n × RationalLyapunovCandidate n ↦
          decide (q.2.1.1 + 1 ≤ q.2.2.2.1)) := by
    exact
      (Primrec.nat_le.comp (Primrec.succ.comp hr) hk).decide
  have hnumeratorInput :
      Primrec
        (fun q : PolynomialFieldCode n × RationalLyapunovCandidate n ↦
          ((q.1, q.2.1.2), q.2.1.1)) :=
    Primrec.pair (Primrec.pair hF hp) hr
  have hnumerator :
      Primrec
        (fun q : PolynomialFieldCode n × RationalLyapunovCandidate n ↦
          PolynomialCode.rationalLyapunovNumerator
            q.1 q.2.1.2 q.2.1.1) :=
    PolynomialCode.rationalLyapunovNumerator_primrec.comp
      hnumeratorInput
  have hdecayInput :
      Primrec
        (fun q : PolynomialFieldCode n × RationalLyapunovCandidate n ↦
          ((PolynomialCode.rationalLyapunovNumerator
              q.1 q.2.1.2 q.2.1.1,
            q.2.2.2.1),
            q.2.2.2.2)) :=
    Primrec.pair
      (Primrec.pair hnumerator hk)
      hdecayCandidate
  have hdecay :
      Primrec
        (fun q : PolynomialFieldCode n × RationalLyapunovCandidate n ↦
          checkStrictMargin
            (PolynomialCode.rationalLyapunovNumerator
              q.1 q.2.1.2 q.2.1.1)
            q.2.2.2.1 q.2.2.2.2) :=
    (checkStrictMargin_primrec (n := n)).comp hdecayInput
  exact
    (Primrec.and.comp
      (Primrec.and.comp hvalue hle)
      hdecay).of_eq fun _ ↦ rfl

/-! ## Natural-number enumeration and `REPred` -/

/-- Total natural-number decoding of candidates.  Invalid codes denote a
fixed harmless all-zero candidate. -/
def decodeRationalLyapunovCandidateTotal
    (n code : ℕ) : RationalLyapunovCandidate n :=
  (@Encodable.decode (RationalLyapunovCandidate n)
      (@Primcodable.toEncodable (RationalLyapunovCandidate n)
        inferInstance) code).getD
    ((0, PolynomialCode.zero),
      ((RationalCode.zero, []), (0, (RationalCode.zero, []))))

theorem decodeRationalLyapunovCandidateTotal_primrec (n : ℕ) :
    Primrec (decodeRationalLyapunovCandidateTotal n) := by
  exact Primrec.option_getD.comp
    (@Primrec.decode (RationalLyapunovCandidate n) _)
    (Primrec.const
      ((0, PolynomialCode.zero),
        ((RationalCode.zero, []), (0, (RationalCode.zero, [])))))

theorem decodeRationalLyapunovCandidateTotal_surjective (n : ℕ) :
    Function.Surjective (decodeRationalLyapunovCandidateTotal n) := by
  intro candidate
  let code :=
    @Encodable.encode (RationalLyapunovCandidate n)
      (@Primcodable.toEncodable (RationalLyapunovCandidate n)
        inferInstance) candidate
  refine ⟨code, ?_⟩
  simp [decodeRationalLyapunovCandidateTotal, code]

/-- Computable witness relation between a field code and a natural-coded
candidate. -/
def RationalLyapunovNatRelation
    (F : PolynomialFieldCode n) (code : ℕ) : Prop :=
  checkRationalLyapunov F
    (decodeRationalLyapunovCandidateTotal n code) = true

instance :
    DecidableRel
      (RationalLyapunovNatRelation :
        PolynomialFieldCode n → ℕ → Prop) :=
  fun F code ↦ by
    unfold RationalLyapunovNatRelation
    infer_instance

theorem rationalLyapunovNatRelation_computable (n : ℕ) :
    ComputablePred
      (fun q : PolynomialFieldCode n × ℕ ↦
        RationalLyapunovNatRelation q.1 q.2) := by
  refine ComputablePred.computable_iff.mpr ?_
  have hinput :
      Primrec
        (fun q : PolynomialFieldCode n × ℕ ↦
          (q.1, decodeRationalLyapunovCandidateTotal n q.2)) :=
    Primrec.pair Primrec.fst
      ((decodeRationalLyapunovCandidateTotal_primrec n).comp
        Primrec.snd)
  exact
    ⟨_, ((checkRationalLyapunov_primrec n).comp hinput).to_comp, rfl⟩

/-- A field code admits an accepted finite rational Lyapunov certificate. -/
def HasCheckedRationalLyapunov (F : PolynomialFieldCode n) : Prop :=
  ∃ candidate : RationalLyapunovCandidate n,
    checkRationalLyapunov F candidate = true

theorem hasCheckedRationalLyapunov_iff_exists_nat
    (F : PolynomialFieldCode n) :
    HasCheckedRationalLyapunov F ↔
      ∃ code, RationalLyapunovNatRelation F code := by
  constructor
  · rintro ⟨candidate, hcandidate⟩
    obtain ⟨code, hcode⟩ :=
      decodeRationalLyapunovCandidateTotal_surjective n candidate
    exact ⟨code, by
      simpa [RationalLyapunovNatRelation, hcode] using hcandidate⟩
  · rintro ⟨code, hcode⟩
    exact
      ⟨decodeRationalLyapunovCandidateTotal n code, hcode⟩

theorem rePred_exists_nat_of_computableRel
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

/-- For every fixed dimension, existence of a checked complete rational
Lyapunov certificate is recursively enumerable. -/
theorem hasCheckedRationalLyapunov_re (n : ℕ) :
    REPred
      (HasCheckedRationalLyapunov :
        PolynomialFieldCode n → Prop) := by
  apply REPred.of_eq
    (rePred_exists_nat_of_computableRel
      RationalLyapunovNatRelation
      (rationalLyapunovNatRelation_computable n))
  intro F
  exact (hasCheckedRationalLyapunov_iff_exists_nat F).symm

end HGAS
