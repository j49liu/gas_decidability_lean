import HGAS.Wrapper.UnitSphereWrapperComputability
import Mathlib.Tactic

/-!
# Syntactic degree calculus for sparse wrapper codes

The executable parity homogenizer is total, but its homogeneity theorem
requires the raw monomial list to have the advertised parity and degree
bound.  This file supplies reusable closure rules for that raw-list
predicate.

Unlike semantic polynomial degree, these lemmas deliberately retain zero
coefficients and duplicate monomials.  That is exactly what an effective
compiler needs: no normalization or support computation occurs between
construction stages.
-/

namespace HGAS

namespace PolynomialCode

variable {n : ℕ}

/-- Total degree is additive under multiplication of coded monomials. -/
theorem totalDegree_exponent_add
    (a b : ExponentCode n) :
    ExponentCode.totalDegree (ExponentCode.add a b) =
      ExponentCode.totalDegree a + ExponentCode.totalDegree b := by
  simp [ExponentCode.totalDegree, List.sum_ofFn,
    ExponentCode.add, Finset.sum_add_distrib]

/-- Multiplying eligible monomials adds target degree bounds and parities. -/
theorem termParityEligible_mulTerm
    {E F : ℕ}
    {a b : ExponentCode n × RationalCode}
    (ha : TermParityEligible E a)
    (hb : TermParityEligible F b) :
    TermParityEligible (E + F) (mulTerm a b) := by
  rcases ha with ⟨haBound, haParity⟩
  rcases hb with ⟨hbBound, hbParity⟩
  constructor
  · simp only [mulTerm, totalDegree_exponent_add]
    omega
  · simp only [mulTerm, totalDegree_exponent_add]
    omega

theorem termsParityEligible_zero (E : ℕ) :
    TermsParityEligible E (zero : PolynomialCode n) := by
  simp [TermsParityEligible, zero]

theorem termsParityEligible_add
    {E : ℕ} {p q : PolynomialCode n}
    (hp : TermsParityEligible E p)
    (hq : TermsParityEligible E q) :
    TermsParityEligible E (add p q) := by
  intro t ht
  rw [add, List.mem_append] at ht
  exact ht.elim (hp t) (hq t)

theorem termsParityEligible_neg
    {E : ℕ} {p : PolynomialCode n}
    (hp : TermsParityEligible E p) :
    TermsParityEligible E (neg p) := by
  intro t ht
  rw [neg, List.mem_map] at ht
  obtain ⟨u, hu, rfl⟩ := ht
  exact hp u hu

theorem termsParityEligible_sub
    {E : ℕ} {p q : PolynomialCode n}
    (hp : TermsParityEligible E p)
    (hq : TermsParityEligible E q) :
    TermsParityEligible E (sub p q) :=
  termsParityEligible_add hp (termsParityEligible_neg hq)

theorem termsParityEligible_mulByTerm
    {E F : ℕ} {a : ExponentCode n × RationalCode}
    {p : PolynomialCode n}
    (ha : TermParityEligible E a)
    (hp : TermsParityEligible F p) :
    TermsParityEligible (E + F) (mulByTerm a p) := by
  intro t ht
  rw [mulByTerm, List.mem_map] at ht
  obtain ⟨u, hu, rfl⟩ := ht
  exact termParityEligible_mulTerm ha (hp u hu)

theorem termsParityEligible_mul
    {E F : ℕ} {p q : PolynomialCode n}
    (hp : TermsParityEligible E p)
    (hq : TermsParityEligible F q) :
    TermsParityEligible (E + F) (mul p q) := by
  induction p with
  | nil =>
      exact termsParityEligible_zero (E + F)
  | cons t p ih =>
      rw [termsParityEligible_cons_iff] at hp
      change
        TermsParityEligible (E + F)
          (mulByTerm t q ++ mul p q)
      exact termsParityEligible_add
        (termsParityEligible_mulByTerm hp.1 hq)
        (ih hp.2)

/-- Raise the permitted target while preserving parity. -/
theorem TermsParityEligible.promote
    {E F : ℕ} {p : PolynomialCode n}
    (hp : TermsParityEligible E p)
    (hle : E ≤ F) (hparity : E % 2 = F % 2) :
    TermsParityEligible F p := by
  intro t ht
  have h := hp t ht
  exact ⟨h.1.trans hle, h.2.trans hparity⟩

theorem termsParityEligible_sumCodes
    {E : ℕ} {ps : List (PolynomialCode n)}
    (hp : ∀ p ∈ ps, TermsParityEligible E p) :
    TermsParityEligible E (sumCodes ps) := by
  induction ps with
  | nil => exact termsParityEligible_zero E
  | cons p ps ih =>
      change TermsParityEligible E (add p (sumCodes ps))
      exact termsParityEligible_add
        (hp p (by simp))
        (ih (fun q hq ↦ hp q (by simp [hq])))

theorem termsParityEligible_one :
    TermsParityEligible 0 (one : PolynomialCode n) := by
  simp [TermsParityEligible, TermParityEligible, one,
    ExponentCode.totalDegree, List.sum_ofFn, ExponentCode.zero]

theorem termsParityEligible_constant (q : RationalCode) :
    TermsParityEligible 0 (constant q : PolynomialCode n) := by
  simp [TermsParityEligible, TermParityEligible, constant,
    ExponentCode.totalDegree, List.sum_ofFn, ExponentCode.zero]

theorem totalDegree_singleVariable (i : Fin n) :
    ExponentCode.totalDegree (ExponentCode.singleVariable i) = 1 := by
  simp [ExponentCode.totalDegree, List.sum_ofFn,
    ExponentCode.singleVariable]

theorem termsParityEligible_varCode (i : Fin n) :
    TermsParityEligible 1 (varCode i) := by
  simp [TermsParityEligible, TermParityEligible, varCode,
    totalDegree_singleVariable]

theorem termsParityEligible_pow
    {E : ℕ} {p : PolynomialCode n}
    (hp : TermsParityEligible E p) :
    ∀ m, TermsParityEligible (E * m) (pow p m)
  | 0 => by
      simpa using (termsParityEligible_one (n := n))
  | m + 1 => by
      rw [pow]
      have hmul :=
        termsParityEligible_mul hp
          (termsParityEligible_pow hp m)
      simpa [Nat.mul_succ, Nat.add_comm] using hmul

/-- Multiplying a finite list of `E`-eligible codes gives degree target
`E * length`. -/
theorem termsParityEligible_foldr_mul
    {E : ℕ} (ps : List (PolynomialCode n))
    (hp : ∀ p ∈ ps, TermsParityEligible E p) :
    TermsParityEligible (E * ps.length)
      (ps.foldr mul one) := by
  induction ps with
  | nil =>
      simpa using (termsParityEligible_one (n := n))
  | cons p ps ih =>
      simp only [List.foldr_cons, List.length_cons]
      have hmul :=
        termsParityEligible_mul
          (hp p (by simp))
          (ih (fun q hq ↦ hp q (by simp [hq])))
      simpa [Nat.mul_add, Nat.add_comm] using hmul

/-- Two-sheet homogenization has exact raw monomial degree `D`. -/
theorem termsParityEligible_twoSheetHomogenize
    (D : ℕ) (p : PolynomialCode n)
    (hp : TermsDegreeLE D p) :
    TermsParityEligible D (twoSheetHomogenize D p) := by
  intro t ht
  rw [twoSheetHomogenize, List.mem_map] at ht
  obtain ⟨u, hu, rfl⟩ := ht
  have hdegree :=
    ExponentCode.totalDegree_chartLift D u.1 (hp u hu)
  exact ⟨by simp [chartLiftTerm, hdegree],
    by simp [chartLiftTerm, hdegree]⟩

end PolynomialCode

end HGAS
