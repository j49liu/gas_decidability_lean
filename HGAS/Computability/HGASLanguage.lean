import HGAS.Computability.SigmaOne
import HGAS.Lyapunov.CheckedRationalCertificateSoundness
import Mathlib.Computability.Primrec.List
import Mathlib.Tactic

/-!
# The finite-code homogeneous GAS language

This file pins down the exact decision problem formalized by the project.
For fixed `n` and `d`, an input is a completely finite sparse rational
polynomial-field code.  Malformed inputs--those whose decoded components are
not homogeneous of degree `d`--are negative instances.

Keeping the predicate on raw syntax is important.  A subtype carrying a
proof of homogeneity is convenient for mathematics but obscures the total
machine which first validates an arbitrary input string.
-/

namespace HGAS

namespace PolynomialFieldCode

variable {n : ℕ}

/-- Exact Boolean validation that every decoded coordinate polynomial is
homogeneous of degree `d`. -/
def homogeneous (d : ℕ) (F : PolynomialFieldCode n) : Bool :=
  (List.ofFn fun i : Fin n ↦
    PolynomialCode.homogeneous d (F i)).all id

@[simp]
theorem homogeneous_eq_true_iff
    (d : ℕ) (F : PolynomialFieldCode n) :
    homogeneous d F = true ↔
      ∀ i : Fin n, (PolynomialCode.decode (F i)).IsHomogeneous d := by
  simp [homogeneous]

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

/-- Homogeneity validation is primitive recursive, uniformly in the degree
and the finite field code. -/
theorem homogeneous_primrec (n : ℕ) :
    Primrec
      (fun q : ℕ × PolynomialFieldCode n ↦
        homogeneous q.1 q.2) := by
  have hchecks :
      Primrec
        (fun q : ℕ × PolynomialFieldCode n ↦
          List.ofFn fun i : Fin n ↦
            PolynomialCode.homogeneous q.1 (q.2 i)) :=
    Primrec.list_ofFn fun i ↦
      PolynomialCode.homogeneous_primrec.comp
        Primrec.fst
        (Primrec.fin_app.comp Primrec.snd (Primrec.const i))
  exact (boolListAll_primrec.comp hchecks).of_eq fun q ↦ by
    simp [homogeneous]

end PolynomialFieldCode

/-- The exact rational fixed-dimension, fixed-degree homogeneous GAS
language.  Invalid homogeneity codes are negative by definition. -/
def HGASQ (n d : ℕ) (F : PolynomialFieldCode n) : Prop :=
  PolynomialFieldCode.homogeneous d F = true ∧
    GloballyAsymptoticallyStable
      (PolynomialFieldCode.realize F) 0

/-- Soundness bridge from the already executable rational Lyapunov checker
to the paper's raw-code decision language. -/
theorem hgasQ_of_checkRationalLyapunov
    {n d : ℕ} (hd : 0 < d)
    (F : PolynomialFieldCode n)
    (hvalid : PolynomialFieldCode.homogeneous d F = true)
    (candidate : RationalLyapunovCandidate n)
    (hcheck : checkRationalLyapunov F candidate = true) :
    HGASQ n d F := by
  refine ⟨hvalid, ?_⟩
  exact globallyAsymptoticallyStable_of_check_of_homogeneous
    F hd
      ((PolynomialFieldCode.homogeneous_eq_true_iff d F).mp hvalid)
    candidate hcheck

/-- A valid code is in `HGASQ` exactly when its realized field is GAS. -/
theorem hgasQ_iff_of_homogeneous
    {n d : ℕ} (F : PolynomialFieldCode n)
    (hvalid : PolynomialFieldCode.homogeneous d F = true) :
    HGASQ n d F ↔
      GloballyAsymptoticallyStable
        (PolynomialFieldCode.realize F) 0 := by
  simp [HGASQ, hvalid]

/-! ## The currently executable certificate sublanguage -/

/-- A valid homogeneous field code admits one accepted finite rational
Lyapunov certificate. -/
def HasCheckedHGASCertificate
    (n d : ℕ) (F : PolynomialFieldCode n) : Prop :=
  PolynomialFieldCode.homogeneous d F = true ∧
    HasCheckedRationalLyapunov F

/-- Natural-coded witness relation used by the semidecision procedure. -/
def CheckedHGASNatRelation
    {n : ℕ} (d : ℕ) (F : PolynomialFieldCode n) (code : ℕ) : Prop :=
  PolynomialFieldCode.homogeneous d F = true ∧
    RationalLyapunovNatRelation F code

instance {n d : ℕ} :
    DecidableRel
      (CheckedHGASNatRelation (n := n) d) :=
  fun F code ↦ by
    unfold CheckedHGASNatRelation
    infer_instance

theorem checkedHGASNatRelation_computable (n d : ℕ) :
    ComputablePred
      (fun q : PolynomialFieldCode n × ℕ ↦
        CheckedHGASNatRelation d q.1 q.2) := by
  refine ComputablePred.computable_iff.mpr ?_
  have hvalid :
      Computable
        (fun q : PolynomialFieldCode n × ℕ ↦
          PolynomialFieldCode.homogeneous d q.1) :=
    ((PolynomialFieldCode.homogeneous_primrec n).comp
      (Primrec.pair (Primrec.const d) Primrec.fst)).to_comp
  have hrelation :
      Computable
        (fun q : PolynomialFieldCode n × ℕ ↦
          decide (RationalLyapunovNatRelation q.1 q.2)) :=
    (rationalLyapunovNatRelation_computable n).decide
  exact
    ⟨fun q ↦
        PolynomialFieldCode.homogeneous d q.1 &&
          decide (RationalLyapunovNatRelation q.1 q.2),
      Primrec.and.to_comp.comp hvalid hrelation,
      by
        funext q
        simp [CheckedHGASNatRelation]⟩

theorem hasCheckedHGASCertificate_iff_exists_nat
    {n d : ℕ} (F : PolynomialFieldCode n) :
    HasCheckedHGASCertificate n d F ↔
      ∃ code, CheckedHGASNatRelation d F code := by
  rw [HasCheckedHGASCertificate,
    hasCheckedRationalLyapunov_iff_exists_nat]
  constructor
  · rintro ⟨hvalid, code, hcode⟩
    have hcheck :
        checkRationalLyapunov F
          (decodeRationalLyapunovCandidateTotal n code) = true := by
      exact hcode
    refine ⟨code, ?_⟩
    exact ⟨hvalid, hcheck⟩
  · rintro ⟨code, hcode⟩
    have hboth :
        PolynomialFieldCode.homogeneous d F = true ∧
          checkRationalLyapunov F
            (decodeRationalLyapunovCandidateTotal n code) = true := by
      exact hcode
    exact ⟨hboth.1, code, hboth.2⟩

/-- Existence of an accepted complete finite certificate is recursively
enumerable for every fixed dimension and degree. -/
theorem hasCheckedHGASCertificate_re (n d : ℕ) :
    REPred (HasCheckedHGASCertificate n d) := by
  apply REPred.of_eq
    (rePred_exists_nat_of_computableRel
      (CheckedHGASNatRelation (n := n) d)
      (checkedHGASNatRelation_computable n d))
  intro F
  exact (hasCheckedHGASCertificate_iff_exists_nat F).symm

/-- Every accepted witness is a genuine homogeneous GAS instance. -/
theorem hgasQ_of_hasCheckedHGASCertificate
    {n d : ℕ} (hd : 0 < d) (F : PolynomialFieldCode n)
    (h : HasCheckedHGASCertificate n d F) :
    HGASQ n d F := by
  obtain ⟨hvalid, candidate, hcandidate⟩ := h
  exact hgasQ_of_checkRationalLyapunov
    hd F hvalid candidate hcandidate

end HGAS
