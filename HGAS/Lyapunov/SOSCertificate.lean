import HGAS.Lyapunov.RationalCertificateSoundness
import Mathlib.Tactic

/-!
# Checked sum-of-squares certificates

This file provides a small algebraic certificate language for proving
nonnegativity and strict positivity of rational multivariate polynomials.
A certificate stores finitely many rational polynomials and an exact
polynomial identity, so its soundness reduces to the elementary fact that a
sum of real squares is nonnegative.

For a form `p` of degree `2k`, a strict homogeneous margin certificate has
the shape

```
p - ε ρ^k = ∑ i, sᵢ^2,       ε ∈ ℚ,  ε > 0,
```

with each `sᵢ` homogeneous of degree `k`.  It proves

```
p(x) ≥ ε ρ(x)^k
```

over the reals and hence `p(x) > 0` for every nonzero `x`.

The same certificate types are specialized to
`rationalLyapunovNumerator`.  These specializations discharge the
nonnegativity and scaled-margin hypotheses used by
`RationalCertificateSoundness`.

Nothing in this file asserts that every positive form admits an SOS or
strict-margin certificate.  Any completeness theorem of Reznick type is a
separate obligation.
-/

namespace HGAS

open MvPolynomial
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## General SOS certificates -/

/-- A finite, exact rational sum-of-squares representation of `p`. -/
structure SOSCertificate (p : MvPolynomial (Fin n) ℚ) where
  /-- Number of square terms in the certificate. -/
  numSquares : ℕ
  /-- Rational polynomials whose squares are summed. -/
  square : Fin numSquares → MvPolynomial (Fin n) ℚ
  /-- Exact polynomial identity checked in `MvPolynomial`. -/
  identity : p = ∑ i, square i ^ 2

namespace SOSCertificate

/-- Every checked rational SOS certificate evaluates to a nonnegative real
number at every point. -/
theorem eval_nonneg
    {p : MvPolynomial (Fin n) ℚ} (cert : SOSCertificate p)
    (x : Fin n → ℝ) :
    0 ≤ ratMvPolynomialEval p x := by
  rw [ratMvPolynomialEval_eq_eval₂Hom, cert.identity, map_sum]
  exact Finset.sum_nonneg fun i hi ↦ by
    rw [map_pow]
    exact sq_nonneg _

/-- An SOS certificate also proves ordinary real-polynomial evaluation
nonnegative after coefficients have been mapped to `ℝ`. -/
theorem eval_map_nonneg
    {p : MvPolynomial (Fin n) ℚ} (cert : SOSCertificate p)
    (x : Fin n → ℝ) :
    0 ≤ MvPolynomial.eval x
      (MvPolynomial.map (algebraMap ℚ ℝ) p) := by
  simpa [ratMvPolynomialEval] using cert.eval_nonneg x

end SOSCertificate

/-! ## Strict homogeneous margins -/

/-- A checked strict homogeneous margin
`p - ε ρ^k = ∑ i, sᵢ^2`.

The square roots are themselves certified homogeneous of degree `k`.  Thus
the identity is an identity of forms of degree `2k`, in addition to carrying
the positivity information used analytically. -/
structure StrictHomogeneousMarginCertificate
    (p : MvPolynomial (Fin n) ℚ) (k : ℕ) where
  /-- Strict rational margin. -/
  epsilon : ℚ
  /-- The margin is genuinely positive. -/
  epsilon_pos : 0 < epsilon
  /-- SOS representation after subtracting the radial margin. -/
  sos : SOSCertificate
    (p - C epsilon * (rhoPolynomial (n := n)) ^ k)
  /-- Each square root has the expected homogeneous degree. -/
  square_homogeneous :
    ∀ i, (sos.square i).IsHomogeneous k

namespace StrictHomogeneousMarginCertificate

variable {p : MvPolynomial (Fin n) ℚ} {k : ℕ}

/-- The real image of the rational margin is positive. -/
theorem real_epsilon_pos
    (cert : StrictHomogeneousMarginCertificate p k) :
    0 < (cert.epsilon : ℝ) := by
  exact_mod_cast cert.epsilon_pos

/-- The SOS side of a homogeneous margin identity is homogeneous of degree
`2k`. -/
theorem sos_isHomogeneous
    (cert : StrictHomogeneousMarginCertificate p k) :
    (p - C cert.epsilon * (rhoPolynomial (n := n)) ^ k).IsHomogeneous
      (2 * k) := by
  rw [cert.sos.identity]
  apply IsHomogeneous.sum Finset.univ
    (fun i ↦ cert.sos.square i ^ 2) (2 * k)
  intro i hi
  convert (cert.square_homogeneous i).pow 2 using 1
  omega

/-- A strict homogeneous margin certificate in particular verifies that
`p` itself is homogeneous of degree `2k`. -/
theorem target_isHomogeneous
    (cert : StrictHomogeneousMarginCertificate p k) :
    p.IsHomogeneous (2 * k) := by
  have hrho :
      ((rhoPolynomial (n := n)) ^ k).IsHomogeneous (2 * k) :=
    (rhoPolynomial_isHomogeneous (n := n)).pow k
  have hmargin :
      (C cert.epsilon * (rhoPolynomial (n := n)) ^ k).IsHomogeneous
        (2 * k) :=
    hrho.C_mul cert.epsilon
  rw [show p =
      (p - C cert.epsilon * (rhoPolynomial (n := n)) ^ k) +
        C cert.epsilon * (rhoPolynomial (n := n)) ^ k by ring]
  exact cert.sos_isHomogeneous.add hmargin

/-- Exact evaluation of the polynomial whose SOS representation is stored
in a strict margin certificate. -/
theorem eval_sub_margin
    (cert : StrictHomogeneousMarginCertificate p k)
    (x : Fin n → ℝ) :
    ratMvPolynomialEval
        (p - C cert.epsilon * (rhoPolynomial (n := n)) ^ k) x =
      ratMvPolynomialEval p x -
        (cert.epsilon : ℝ) * normSq x ^ k := by
  simp only [ratMvPolynomialEval_eq_eval₂Hom, map_sub, map_mul, map_pow,
    eval₂Hom_C]
  rw [eval₂Hom_rhoPolynomial]
  norm_num

/-- The fundamental real lower bound certified by a strict homogeneous
margin. -/
theorem eval_lower_bound
    (cert : StrictHomogeneousMarginCertificate p k)
    (x : Fin n → ℝ) :
    (cert.epsilon : ℝ) * normSq x ^ k ≤
      ratMvPolynomialEval p x := by
  have hsos := cert.sos.eval_nonneg x
  rw [cert.eval_sub_margin] at hsos
  linarith

/-- A strict homogeneous margin makes the target positive at every nonzero
real point. -/
theorem eval_pos_of_ne_zero
    (cert : StrictHomogeneousMarginCertificate p k)
    {x : Fin n → ℝ} (hx : x ≠ 0) :
    0 < ratMvPolynomialEval p x := by
  exact lt_of_lt_of_le
    (mul_pos cert.real_epsilon_pos
      (pow_pos (normSq_pos_of_ne_zero hx) k))
    (cert.eval_lower_bound x)

/-- Forgetting the strict margin yields nonnegativity of the target itself. -/
theorem eval_nonneg
    (cert : StrictHomogeneousMarginCertificate p k)
    (x : Fin n → ℝ) :
    0 ≤ ratMvPolynomialEval p x := by
  exact le_trans
    (mul_nonneg cert.real_epsilon_pos.le
      (pow_nonneg (normSq_nonneg x) k))
    (cert.eval_lower_bound x)

end StrictHomogeneousMarginCertificate

/-! ## Certificates specialized to rational Lyapunov functions -/

/-- The natural strict margin for a numerator `p` used in
`V = p / ρ^r`: its radial exponent is `r+1`, so division leaves a quadratic
lower bound. -/
abbrev LyapunovValueMarginCertificate
    (p : MvPolynomial (Fin n) ℚ) (r : ℕ) :=
  StrictHomogeneousMarginCertificate p (r + 1)

namespace LyapunovValueMarginCertificate

/-- Away from the origin, a margin
`p ≥ ε ρ^(r+1)` becomes the quadratic Lyapunov bound
`V ≥ ε ρ` after division by `ρ^r`. -/
theorem value_lower_bound_of_ne_zero
    {p : MvPolynomial (Fin n) ℚ} {r : ℕ}
    (cert : LyapunovValueMarginCertificate p r)
    {x : Fin n → ℝ} (hx : x ≠ 0) :
    (cert.epsilon : ℝ) * normSq x ≤
      rationalLyapunovValue p r x := by
  have hρ : 0 < normSq x := normSq_pos_of_ne_zero hx
  rw [rationalLyapunovValue]
  apply (le_div_iff₀ (pow_pos hρ r)).mpr
  calc
    (cert.epsilon : ℝ) * normSq x * normSq x ^ r =
        (cert.epsilon : ℝ) * normSq x ^ (r + 1) := by
      rw [pow_succ]
      ring
    _ ≤ ratMvPolynomialEval p x := cert.eval_lower_bound x

/-- Consequently, the rational Lyapunov value is positive away from the
origin. -/
theorem value_pos_of_ne_zero
    {p : MvPolynomial (Fin n) ℚ} {r : ℕ}
    (cert : LyapunovValueMarginCertificate p r)
    {x : Fin n → ℝ} (hx : x ≠ 0) :
    0 < rationalLyapunovValue p r x := by
  exact lt_of_lt_of_le
    (mul_pos cert.real_epsilon_pos (normSq_pos_of_ne_zero hx))
    (cert.value_lower_bound_of_ne_zero hx)

end LyapunovValueMarginCertificate

/-! ## Certificates specialized to Lyapunov decay numerators -/

/-- An SOS certificate for the polynomial numerator representing `-V̇`. -/
abbrev DecayNumeratorSOSCertificate
    (F : PolynomialField n) (p : MvPolynomial (Fin n) ℚ) (r : ℕ) :=
  SOSCertificate (rationalLyapunovNumerator F p r)

/-- A strict homogeneous radial margin for the polynomial numerator
representing `-V̇`. -/
abbrev StrictDecayMarginCertificate
    (F : PolynomialField n) (p : MvPolynomial (Fin n) ℚ)
    (r k : ℕ) :=
  StrictHomogeneousMarginCertificate
    (rationalLyapunovNumerator F p r) k

namespace DecayNumeratorSOSCertificate

/-- A checked numerator SOS certificate supplies the numerator
nonnegativity hypothesis of `rationalCertificate_gas`. -/
theorem numerator_nonneg
    {F : PolynomialField n} {p : MvPolynomial (Fin n) ℚ} {r : ℕ}
    (cert : DecayNumeratorSOSCertificate F p r)
    (x : Fin n → ℝ) :
    0 ≤ ratMvPolynomialEval
      (rationalLyapunovNumerator F p r) x :=
  cert.eval_nonneg x

/-- Consequently, a checked numerator SOS certificate proves that the
analytic decay quotient is nonnegative. -/
theorem decay_nonneg
    {F : PolynomialField n} {p : MvPolynomial (Fin n) ℚ} {r : ℕ}
    (cert : DecayNumeratorSOSCertificate F p r)
    (x : Fin n → ℝ) :
    0 ≤ rationalLyapunovDecay F p r x :=
  rationalLyapunovDecay_nonneg F p r x (cert.numerator_nonneg x)

end DecayNumeratorSOSCertificate

namespace StrictDecayMarginCertificate

/-- The explicit radial lower bound carried by a strict decay-numerator
margin. -/
theorem numerator_lower_bound
    {F : PolynomialField n} {p : MvPolynomial (Fin n) ℚ}
    {r k : ℕ}
    (cert : StrictDecayMarginCertificate F p r k)
    (x : Fin n → ℝ) :
    (cert.epsilon : ℝ) * normSq x ^ k ≤
      ratMvPolynomialEval
        (rationalLyapunovNumerator F p r) x :=
  cert.eval_lower_bound x

/-- A strict numerator margin supplies numerator nonnegativity. -/
theorem numerator_nonneg
    {F : PolynomialField n} {p : MvPolynomial (Fin n) ℚ}
    {r k : ℕ}
    (cert : StrictDecayMarginCertificate F p r k)
    (x : Fin n → ℝ) :
    0 ≤ ratMvPolynomialEval
      (rationalLyapunovNumerator F p r) x :=
  cert.eval_nonneg x

/-- A margin with exponent exactly `r+1` directly supplies the scaled
superlevel estimate expected by `rationalCertificate_gas`.

The estimate is actually global and independent of `η`; the theorem retains
the superlevel-shaped interface so it can be passed to the soundness theorem
without further algebra. -/
theorem numerator_level
    {F : PolynomialField n} {p : MvPolynomial (Fin n) ℚ}
    {r : ℕ}
    (cert : StrictDecayMarginCertificate F p r (r + 1)) :
    ∀ η : ℝ, 0 < η →
      ∃ d : ℝ, 0 < d ∧ ∀ x : Fin n → ℝ,
        η ≤ rationalLyapunovValue p r x →
          d * normSq x ^ (r + 1) ≤
            ratMvPolynomialEval
              (rationalLyapunovNumerator F p r) x := by
  intro η hη
  exact ⟨(cert.epsilon : ℝ), cert.real_epsilon_pos,
    fun x hx ↦ cert.eval_lower_bound x⟩

/-- A strict decay margin of any exponent `k ≥ r+1` supplies the
superlevel estimate needed by `rationalCertificate_gas`, provided the
Lyapunov value has a quadratic upper bound.

This is the form relevant to a homogeneous field of degree greater than
one.  Its decay numerator generally has degree strictly larger than
`2(r+1)`, so a global lower bound by a fixed multiple of `ρ^(r+1)` would
be dimensionally impossible near the origin.  On a positive Lyapunov
superlevel, however, `V ≤ Bρ` gives the missing positive lower bound on
`ρ`; the extra power can then be absorbed into the constant `d`. -/
theorem numerator_level_of_upper
    {F : PolynomialField n} {p : MvPolynomial (Fin n) ℚ}
    {r k : ℕ}
    (cert : StrictDecayMarginCertificate F p r k)
    (hrk : r + 1 ≤ k)
    {B : ℝ} (hB : 0 < B)
    (hupper : ∀ x : Fin n → ℝ,
      rationalLyapunovValue p r x ≤ B * normSq x) :
    ∀ η : ℝ, 0 < η →
      ∃ d : ℝ, 0 < d ∧ ∀ x : Fin n → ℝ,
        η ≤ rationalLyapunovValue p r x →
          d * normSq x ^ (r + 1) ≤
            ratMvPolynomialEval
              (rationalLyapunovNumerator F p r) x := by
  intro η hη
  let extra : ℕ := k - (r + 1)
  let d : ℝ :=
    (cert.epsilon : ℝ) * (η / B) ^ extra
  have hetaB : 0 < η / B := div_pos hη hB
  have hd : 0 < d :=
    mul_pos cert.real_epsilon_pos (pow_pos hetaB extra)
  refine ⟨d, hd, ?_⟩
  intro x hx
  have hηrho : η ≤ B * normSq x :=
    hx.trans (hupper x)
  have hrho : η / B ≤ normSq x := by
    exact (div_le_iff₀ hB).mpr (by simpa [mul_comm] using hηrho)
  have hrho_nonneg : 0 ≤ normSq x :=
    normSq_nonneg x
  have hextra :
      (η / B) ^ extra ≤ normSq x ^ extra :=
    pow_le_pow_left₀ hetaB.le hrho extra
  have hfactor :
      d * normSq x ^ (r + 1) ≤
        (cert.epsilon : ℝ) * normSq x ^ k := by
    have hk : k = (r + 1) + extra := by
      dsimp only [extra]
      omega
    have hpow :
        normSq x ^ k =
          normSq x ^ (r + 1) * normSq x ^ extra := by
      rw [hk, pow_add]
    dsimp only [d]
    have hepsilon_nonneg := cert.real_epsilon_pos.le
    calc
      (cert.epsilon : ℝ) * (η / B) ^ extra *
            normSq x ^ (r + 1) =
          ((cert.epsilon : ℝ) * normSq x ^ (r + 1)) *
            (η / B) ^ extra := by ring
      _ ≤ ((cert.epsilon : ℝ) * normSq x ^ (r + 1)) *
            normSq x ^ extra :=
        mul_le_mul_of_nonneg_left hextra
          (mul_nonneg hepsilon_nonneg
            (pow_nonneg hrho_nonneg (r + 1)))
      _ = (cert.epsilon : ℝ) *
            (normSq x ^ (r + 1) * normSq x ^ extra) := by ring
      _ = (cert.epsilon : ℝ) * normSq x ^ k := by rw [hpow]
  exact hfactor.trans (cert.eval_lower_bound x)

/-- A strict decay margin makes the numerator positive away from the
origin. -/
theorem numerator_pos_of_ne_zero
    {F : PolynomialField n} {p : MvPolynomial (Fin n) ℚ}
    {r k : ℕ}
    (cert : StrictDecayMarginCertificate F p r k)
    {x : Fin n → ℝ} (hx : x ≠ 0) :
    0 < ratMvPolynomialEval
      (rationalLyapunovNumerator F p r) x :=
  cert.eval_pos_of_ne_zero hx

end StrictDecayMarginCertificate

end

end HGAS
