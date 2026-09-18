import HGAS.Computability.HGASLanguage
import HGAS.Lyapunov.ExactGridPositivityComputability
import Mathlib.Computability.RE
import Mathlib.Tactic

/-!
# Complete exact-grid certificates for rational Lyapunov functions

For a homogeneous polynomial field `F`, a denominator exponent `r`, and a
homogeneous numerator `p` of degree `2(r+1)`, put

```
V(x) = p(x) / ρ(x)^r
q(x) = -ρ(x) (∇p(x) · F(x)) + 2r p(x) (x · F(x)).
```

The analytic identity is `-V̇ = q / ρ^(r+1)`.  Thus strict positivity of
`p` and `q` away from the origin is the complete finite-data condition
needed from a rational converse-Lyapunov witness.

This module turns that condition into an actual semidecision procedure.  A
candidate contains only:

* the exponent `r`;
* a sparse rational code for `p`; and
* two natural grid resolutions, one for `p` and one for the compiled `q`.

The checker uses exact rational arithmetic.  Its soundness and completeness
are consequences of `ExactGridPositivity`: a homogeneous rational
polynomial is positive away from zero exactly when some finite boundary
grid is accepted.  No real quantifier elimination and no
Positivstellensatz is used.
-/

namespace HGAS

open MvPolynomial
open ExactGridPositivity

namespace GridRationalLyapunovCandidate

/-- Finite witness `(r,p,mₚ,m_q)` for the exact-grid Lyapunov search. -/
abbrev Candidate (n : ℕ) :=
  (ℕ × PolynomialCode n) × (ℕ × ℕ)

variable {n : ℕ}

def denominatorExponent (c : Candidate n) : ℕ := c.1.1
def numerator (c : Candidate n) : PolynomialCode n := c.1.2
def valueResolution (c : Candidate n) : ℕ := c.2.1
def decayResolution (c : Candidate n) : ℕ := c.2.2

end GridRationalLyapunovCandidate

open GridRationalLyapunovCandidate

/-- Exact Boolean checker for a homogeneous field and a rational Lyapunov
pair.  The field-validity test is included so malformed raw codes are
negative instances. -/
def checkGridRationalLyapunov
    (d : ℕ) (F : PolynomialFieldCode n) (c : Candidate n) : Bool :=
  PolynomialFieldCode.homogeneous d F &&
  PolynomialCode.homogeneous
      (2 * (denominatorExponent c + 1)) (numerator c) &&
  checkStrictPositiveOnSupSphere
      (numerator c) (valueResolution c) &&
  checkStrictPositiveOnSupSphere
      (PolynomialCode.rationalLyapunovNumerator
        F (numerator c) (denominatorExponent c))
      (decayResolution c)

@[simp]
theorem checkGridRationalLyapunov_eq_true_iff
    (d : ℕ) (F : PolynomialFieldCode n) (c : Candidate n) :
    checkGridRationalLyapunov d F c = true ↔
      PolynomialFieldCode.homogeneous d F = true ∧
      PolynomialCode.homogeneous
          (2 * (denominatorExponent c + 1)) (numerator c) = true ∧
      checkStrictPositiveOnSupSphere
          (numerator c) (valueResolution c) = true ∧
      checkStrictPositiveOnSupSphere
          (PolynomialCode.rationalLyapunovNumerator
            F (numerator c) (denominatorExponent c))
          (decayResolution c) = true := by
  simp only [checkGridRationalLyapunov, Bool.and_eq_true]
  tauto

/-- Semantic content extracted from an accepted exact-grid candidate. -/
theorem semantic_of_checkGridRationalLyapunov
    {d : ℕ} {F : PolynomialFieldCode n} {c : Candidate n}
    (hcheck : checkGridRationalLyapunov d F c = true) :
    (∀ i : Fin n,
      (PolynomialCode.decode (F i)).IsHomogeneous d) ∧
    (PolynomialCode.decode (numerator c)).IsHomogeneous
      (2 * (denominatorExponent c + 1)) ∧
    (∀ x : Fin n → ℝ, x ≠ 0 →
      0 < ratMvPolynomialEval
        (PolynomialCode.decode (numerator c)) x) ∧
    (∀ x : Fin n → ℝ, x ≠ 0 →
      0 < ratMvPolynomialEval
        (rationalLyapunovNumerator
          (PolynomialFieldCode.decode F)
          (PolynomialCode.decode (numerator c))
          (denominatorExponent c)) x) := by
  have hparts :=
    (checkGridRationalLyapunov_eq_true_iff d F c).mp hcheck
  have hF :=
    (PolynomialFieldCode.homogeneous_eq_true_iff d F).mp hparts.1
  have hp :=
    (PolynomialCode.homogeneous_eq_true_iff
      (2 * (denominatorExponent c + 1)) (numerator c)).mp
      hparts.2.1
  have hpPos :=
    checkStrictPositiveOnSupSphere_sound_nonzero
      (numerator c) (valueResolution c) hp hparts.2.2.1
  have hq :
      (PolynomialCode.decode
        (PolynomialCode.rationalLyapunovNumerator
          F (numerator c) (denominatorExponent c))).IsHomogeneous
        (2 * denominatorExponent c + d + 3) := by
    rw [PolynomialCode.decode_rationalLyapunovNumerator]
    have hp' :
        (PolynomialCode.decode (numerator c)).IsHomogeneous
          (2 * denominatorExponent c + 2) := by
      convert hp using 1
    exact rationalLyapunovNumerator_isHomogeneous
      (PolynomialFieldCode.decode F)
      (PolynomialCode.decode (numerator c))
      (denominatorExponent c) hF hp'
  have hqPosCode :=
    checkStrictPositiveOnSupSphere_sound_nonzero
      (PolynomialCode.rationalLyapunovNumerator
        F (numerator c) (denominatorExponent c))
      (decayResolution c) hq hparts.2.2.2
  refine ⟨hF, hp, hpPos, ?_⟩
  simpa using hqPosCode

/-- Conversely, every rational homogeneous strict Lyapunov pair is accepted
at some pair of finite grid resolutions. -/
theorem exists_checkGridRationalLyapunov_of_semantic
    {d r : ℕ} (F : PolynomialFieldCode n) (p : PolynomialCode n)
    (hF : ∀ i : Fin n,
      (PolynomialCode.decode (F i)).IsHomogeneous d)
    (hp : (PolynomialCode.decode p).IsHomogeneous (2 * (r + 1)))
    (hpPos : ∀ x : Fin n → ℝ, x ≠ 0 →
      0 < ratMvPolynomialEval (PolynomialCode.decode p) x)
    (hqPos : ∀ x : Fin n → ℝ, x ≠ 0 →
      0 < ratMvPolynomialEval
        (rationalLyapunovNumerator
          (PolynomialFieldCode.decode F)
          (PolynomialCode.decode p) r) x) :
    ∃ c : Candidate n,
      denominatorExponent c = r ∧
      numerator c = p ∧
      checkGridRationalLyapunov d F c = true := by
  have hq :
      (PolynomialCode.decode
        (PolynomialCode.rationalLyapunovNumerator F p r)).IsHomogeneous
        (2 * r + d + 3) := by
    rw [PolynomialCode.decode_rationalLyapunovNumerator]
    have hp' :
        (PolynomialCode.decode p).IsHomogeneous (2 * r + 2) := by
      convert hp using 1
    exact rationalLyapunovNumerator_isHomogeneous
      (PolynomialFieldCode.decode F) (PolynomialCode.decode p) r
      hF hp'
  obtain ⟨mp, hmp⟩ :=
    (exists_checked_iff_positive_nonzero p hp).2 hpPos
  obtain ⟨mq, hmq⟩ :=
    (exists_checked_iff_positive_nonzero
      (PolynomialCode.rationalLyapunovNumerator F p r) hq).2
      (by simpa using hqPos)
  let c : Candidate n := ((r, p), (mp, mq))
  refine ⟨c, rfl, rfl, ?_⟩
  have hFCode :
      PolynomialFieldCode.homogeneous d F = true :=
    (PolynomialFieldCode.homogeneous_eq_true_iff d F).2 hF
  have hpCode :
      PolynomialCode.homogeneous (2 * (r + 1)) p = true :=
    (PolynomialCode.homogeneous_eq_true_iff
      (2 * (r + 1)) p).2 hp
  apply (checkGridRationalLyapunov_eq_true_iff d F c).2
  exact ⟨hFCode, hpCode, hmp, hmq⟩

/-! ## Primitive-recursive checking -/

set_option maxHeartbeats 800000 in
-- The checker proof composes several deeply nested primitive-recursive
-- product programs; elaborating their dependent types needs a larger
-- heartbeat budget.
theorem checkGridRationalLyapunov_primrec (n d : ℕ) :
    Primrec
      (fun q : PolynomialFieldCode n × Candidate n ↦
        checkGridRationalLyapunov d q.1 q.2) := by
  have hF :
      Primrec
        (fun q : PolynomialFieldCode n × Candidate n ↦ q.1) :=
    Primrec.fst
  have hr :
      Primrec
        (fun q : PolynomialFieldCode n × Candidate n ↦ q.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have hp :
      Primrec
        (fun q : PolynomialFieldCode n × Candidate n ↦ q.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have hmp :
      Primrec
        (fun q : PolynomialFieldCode n × Candidate n ↦ q.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hmq :
      Primrec
        (fun q : PolynomialFieldCode n × Candidate n ↦ q.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hvalid :
      Primrec
        (fun q : PolynomialFieldCode n × Candidate n ↦
          PolynomialFieldCode.homogeneous d q.1) :=
    (PolynomialFieldCode.homogeneous_primrec n).comp
      (Primrec.pair (Primrec.const d) hF)
  have hpDegree :
      Primrec
        (fun q : PolynomialFieldCode n × Candidate n ↦
          2 * (q.2.1.1 + 1)) :=
    Primrec.nat_mul.comp
      (Primrec.const 2) (Primrec.succ.comp hr)
  have hpHomogeneous :
      Primrec
        (fun q : PolynomialFieldCode n × Candidate n ↦
          PolynomialCode.homogeneous
            (2 * (q.2.1.1 + 1)) q.2.1.2) :=
    PolynomialCode.homogeneous_primrec.comp hpDegree hp
  have hpGrid :
      Primrec
        (fun q : PolynomialFieldCode n × Candidate n ↦
          checkStrictPositiveOnSupSphere q.2.1.2 q.2.2.1) :=
    checkStrictPositiveOnSupSphere_primrec.comp hp hmp
  have hqInput :
      Primrec
        (fun q : PolynomialFieldCode n × Candidate n ↦
          ((q.1, q.2.1.2), q.2.1.1)) :=
    Primrec.pair (Primrec.pair hF hp) hr
  have hq :
      Primrec
        (fun q : PolynomialFieldCode n × Candidate n ↦
          PolynomialCode.rationalLyapunovNumerator
            q.1 q.2.1.2 q.2.1.1) :=
    PolynomialCode.rationalLyapunovNumerator_primrec.comp hqInput
  have hqGrid :
      Primrec
        (fun q : PolynomialFieldCode n × Candidate n ↦
          checkStrictPositiveOnSupSphere
            (PolynomialCode.rationalLyapunovNumerator
              q.1 q.2.1.2 q.2.1.1) q.2.2.2) :=
    checkStrictPositiveOnSupSphere_primrec.comp hq hmq
  exact
    (Primrec.and.comp
      (Primrec.and.comp
        (Primrec.and.comp hvalid hpHomogeneous)
        hpGrid)
      hqGrid).of_eq fun _ ↦ rfl

/-! ## Natural coding and recursive enumerability -/

/-- Total decoding of a natural number into a grid candidate. -/
def decodeGridRationalLyapunovCandidateTotal
    (n code : ℕ) : Candidate n :=
  (@Encodable.decode (Candidate n)
      (@Primcodable.toEncodable (Candidate n) inferInstance) code).getD
    ((0, PolynomialCode.zero), (0, 0))

theorem decodeGridRationalLyapunovCandidateTotal_primrec (n : ℕ) :
    Primrec (decodeGridRationalLyapunovCandidateTotal n) := by
  exact Primrec.option_getD.comp
    (@Primrec.decode (Candidate n) _)
    (Primrec.const ((0, PolynomialCode.zero), (0, 0)))

theorem decodeGridRationalLyapunovCandidateTotal_surjective (n : ℕ) :
    Function.Surjective (decodeGridRationalLyapunovCandidateTotal n) := by
  intro c
  let code :=
    @Encodable.encode (Candidate n)
      (@Primcodable.toEncodable (Candidate n) inferInstance) c
  refine ⟨code, ?_⟩
  simp [decodeGridRationalLyapunovCandidateTotal, code]

/-- Computable natural witness relation for the exact-grid search. -/
def GridRationalLyapunovNatRelation
    (d : ℕ) (F : PolynomialFieldCode n) (code : ℕ) : Prop :=
  checkGridRationalLyapunov d F
    (decodeGridRationalLyapunovCandidateTotal n code) = true

instance (d : ℕ) :
    DecidableRel
      (GridRationalLyapunovNatRelation (n := n) d) :=
  fun F code ↦ by
    unfold GridRationalLyapunovNatRelation
    infer_instance

theorem gridRationalLyapunovNatRelation_computable (n d : ℕ) :
    ComputablePred
      (fun q : PolynomialFieldCode n × ℕ ↦
        GridRationalLyapunovNatRelation d q.1 q.2) := by
  refine ComputablePred.computable_iff.mpr ?_
  have hinput :
      Primrec
        (fun q : PolynomialFieldCode n × ℕ ↦
          (q.1, decodeGridRationalLyapunovCandidateTotal n q.2)) :=
    Primrec.pair Primrec.fst
      ((decodeGridRationalLyapunovCandidateTotal_primrec n).comp
        Primrec.snd)
  exact
    ⟨_,
      ((checkGridRationalLyapunov_primrec n d).comp hinput).to_comp,
      rfl⟩

/-- A raw field code admits an accepted exact-grid Lyapunov witness. -/
def HasGridRationalLyapunov
    (d : ℕ) (F : PolynomialFieldCode n) : Prop :=
  ∃ c : Candidate n, checkGridRationalLyapunov d F c = true

theorem hasGridRationalLyapunov_iff_exists_nat
    (d : ℕ) (F : PolynomialFieldCode n) :
    HasGridRationalLyapunov d F ↔
      ∃ code, GridRationalLyapunovNatRelation d F code := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨code, rfl⟩ :=
      decodeGridRationalLyapunovCandidateTotal_surjective n c
    exact ⟨code, hc⟩
  · rintro ⟨code, hcode⟩
    exact
      ⟨decodeGridRationalLyapunovCandidateTotal n code, hcode⟩

/-- Existence of a complete exact-grid rational Lyapunov certificate is
recursively enumerable for every fixed dimension and field degree. -/
theorem hasGridRationalLyapunov_re (n d : ℕ) :
    REPred (HasGridRationalLyapunov (n := n) d) := by
  apply REPred.of_eq
    (rePred_exists_nat_of_computableRel
      (GridRationalLyapunovNatRelation (n := n) d)
      (gridRationalLyapunovNatRelation_computable n d))
  intro F
  exact (hasGridRationalLyapunov_iff_exists_nat d F).symm

end HGAS
