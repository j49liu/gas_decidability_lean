import HGAS.Lyapunov.GridRationalCertificateSoundness
import HGAS.Lyapunov.RationalLyapunovPerturbation
import Mathlib.Tactic

/-!
# Completeness bridge for exact-grid rational Lyapunov certificates

The homogeneous converse theorem naturally produces a polynomial numerator
with real coefficients.  The executable exact-grid checker accepts sparse
rational codes.  This file proves the entire bridge between those two
statements:

1. strict unit-sphere positivity of a homogeneous real numerator and its
   decay numerator survives a sufficiently small rational coefficient
   perturbation;
2. unit-sphere positivity of a homogeneous rational form propagates to
   every nonzero point;
3. every rational polynomial has a finite sparse code; and
4. the exact-grid completeness theorem supplies finite accepted
   resolutions for both forms.

Consequently the only remaining upper-bound input is the analytic
homogeneous converse-Lyapunov theorem itself.  The last declarations make
that boundary explicit without postulating it as an axiom.
-/

namespace HGAS

open MvPolynomial

noncomputable section

variable {n : ℕ}

/-- Positivity on the ordinary unit sphere propagates along every nonzero
ray for a homogeneous polynomial. -/
theorem ratMvPolynomialEval_pos_of_isHomogeneous_of_unitSphere_pos
    {p : MvPolynomial (Fin n) ℚ} {D : ℕ}
    (hp : p.IsHomogeneous D)
    (hunit : ∀ x : Fin n → ℝ, ‖x‖ = 1 →
      0 < ratMvPolynomialEval p x) :
    ∀ x : Fin n → ℝ, x ≠ 0 →
      0 < ratMvPolynomialEval p x := by
  intro x hx
  let y : Fin n → ℝ := ‖x‖⁻¹ • x
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hynorm : ‖y‖ = 1 := by
    simp [y, norm_smul, hxnorm.ne']
  have hxy : ‖x‖ • y = x := by
    simp [y, smul_smul, hxnorm.ne']
  rw [ratMvPolynomialEval_eq_eval₂Hom]
  calc
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x p =
        MvPolynomial.eval₂Hom
          (algebraMap ℚ ℝ) (‖x‖ • y) p := by rw [hxy]
    _ = ‖x‖ ^ D *
        MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) y p :=
      MvPolynomial.IsHomogeneous.eval₂Hom_smul
        hp (algebraMap ℚ ℝ) y ‖x‖
    _ > 0 := mul_pos (pow_pos hxnorm D) (by
      rw [← ratMvPolynomialEval_eq_eval₂Hom]
      exact hunit y hynorm)

/-- Exact data returned by the analytic rational homogeneous converse
theorem before rationalizing coefficients. -/
structure RealRationalLyapunovWitness
    (F : PolynomialField n) where
  denominatorExponent : ℕ
  numerator : MvPolynomial (Fin n) ℝ
  numerator_isHomogeneous :
    numerator.IsHomogeneous (2 * (denominatorExponent + 1))
  value_positive_on_unitSphere :
    ∀ x : Fin n → ℝ, ‖x‖ = 1 →
      0 < MvPolynomial.eval x numerator
  decay_positive_on_unitSphere :
    ∀ x : Fin n → ℝ, ‖x‖ = 1 →
      0 < MvPolynomial.eval x
        (realRationalLyapunovNumerator
          (realPolynomialFieldOfRational F)
          numerator denominatorExponent)

/-- Rationalize a real converse witness and produce an accepted finite
exact-grid certificate. -/
theorem hasGridRationalLyapunov_of_realWitness
    {d : ℕ} (F : PolynomialFieldCode n)
    (hF : ∀ i : Fin n,
      (PolynomialCode.decode (F i)).IsHomogeneous d)
    (L : RealRationalLyapunovWitness
      (PolynomialFieldCode.decode F)) :
    HasGridRationalLyapunov d F := by
  obtain ⟨pQ, hpQ, hpQunit, hqQunit⟩ :=
    exists_rational_homogeneous_lyapunov_perturbation
      (PolynomialFieldCode.decode F)
      L.numerator L.denominatorExponent
      (2 * (L.denominatorExponent + 1))
      L.numerator_isHomogeneous
      L.value_positive_on_unitSphere
      L.decay_positive_on_unitSphere
  let pCode : PolynomialCode n := PolynomialCode.encode pQ
  have hpCode :
      (PolynomialCode.decode pCode).IsHomogeneous
        (2 * (L.denominatorExponent + 1)) := by
    simpa [pCode] using hpQ
  have hpOff :
      ∀ x : Fin n → ℝ, x ≠ 0 →
        0 < ratMvPolynomialEval
          (PolynomialCode.decode pCode) x := by
    simpa [pCode] using
      ratMvPolynomialEval_pos_of_isHomogeneous_of_unitSphere_pos
        hpQ hpQunit
  have hqHom :
      (rationalLyapunovNumerator
        (PolynomialFieldCode.decode F) pQ
        L.denominatorExponent).IsHomogeneous
          (2 * L.denominatorExponent + d + 3) := by
    exact rationalLyapunovNumerator_isHomogeneous
      (PolynomialFieldCode.decode F) pQ
      L.denominatorExponent hF (by
        convert hpQ using 1)
  have hqOff :
      ∀ x : Fin n → ℝ, x ≠ 0 →
        0 < ratMvPolynomialEval
          (rationalLyapunovNumerator
            (PolynomialFieldCode.decode F)
            (PolynomialCode.decode pCode)
            L.denominatorExponent) x := by
    simpa [pCode] using
      ratMvPolynomialEval_pos_of_isHomogeneous_of_unitSphere_pos
        hqHom hqQunit
  obtain ⟨c, _hr, _hp, hc⟩ :=
    exists_checkGridRationalLyapunov_of_semantic
      F pCode hF hpCode hpOff hqOff
  exact ⟨c, hc⟩

/-- The exact analytic property still required from a homogeneous converse
Lyapunov theorem in dimension `n` and degree `d`. -/
def HasRealRationalHomogeneousConverse (n d : ℕ) : Prop :=
  ∀ F : PolynomialFieldCode n,
    PolynomialFieldCode.homogeneous d F = true →
    GloballyAsymptoticallyStable
      (PolynomialFieldCode.realize F) 0 →
    Nonempty
      (RealRationalLyapunovWitness
        (PolynomialFieldCode.decode F))

/-- Under the real homogeneous converse theorem, the exact-grid witness
language is extensionally equal to homogeneous GAS. -/
theorem hgasQ_iff_hasGridRationalLyapunov
    {n d : ℕ} (hd : 0 < d)
    (hconverse : HasRealRationalHomogeneousConverse n d)
    (F : PolynomialFieldCode n) :
    HGASQ n d F ↔ HasGridRationalLyapunov d F := by
  constructor
  · rintro ⟨hvalid, hgas⟩
    obtain ⟨L⟩ := hconverse F hvalid hgas
    exact hasGridRationalLyapunov_of_realWitness F
      ((PolynomialFieldCode.homogeneous_eq_true_iff d F).mp hvalid) L
  · rintro ⟨c, hc⟩
    exact hgasQ_of_checkGridRationalLyapunov hd F c hc

/-- Hence the fixed-dimension, fixed-degree GAS language is recursively
enumerable as soon as the analytic homogeneous converse theorem is
available. -/
theorem hgasQ_re_of_realRationalHomogeneousConverse
    (n d : ℕ) (hd : 0 < d)
    (hconverse : HasRealRationalHomogeneousConverse n d) :
    REPred (HGASQ n d) := by
  apply REPred.of_eq (hasGridRationalLyapunov_re n d)
  intro F
  exact (hgasQ_iff_hasGridRationalLyapunov hd hconverse F).symm

end

end HGAS
