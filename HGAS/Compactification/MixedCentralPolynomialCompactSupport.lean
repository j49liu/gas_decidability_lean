import HGAS.Compactification.MixedCentralPolynomialGlobalTangency
import Mathlib.Tactic

/-!
# Homogenization of compactly supported source coordinates

The scaled-chart identity for mixed central compactification is usually
written at points whose affine coordinates have the form `x_j = w_b z_j`.
At an equator `w_b = 0`, an arbitrary ambient affine coordinate need not
have that form.  This causes no difficulty for a source polynomial which
does not use any affine variable: its homogenization is simply the
original polynomial in the compact variables multiplied by the common
slowdown.

This file proves that statement directly on sparse terms, without
division by a chart coordinate.  It then packages the useful geometric
consequence: if the source components belonging to an already compact
block use no affine variables, denominator clearing preserves their dot
product up to the common scalar slowdown at every ambient point,
including every equator and projective corner.
-/

namespace HGAS

open _root_.MvPolynomial
open scoped BigOperators

noncomputable section

namespace MixedCentralPolynomialCode

variable {n k l : ℕ}

/-- A source term has no exponent in any affine block. -/
def AffineDegreeZero
    (layout : Fin n → Fin k ⊕ Fin l)
    (e : ExponentCode n) : Prop :=
  ∀ b, affineBlockDegree layout e b = 0

/-- A sparse source polynomial uses no affine-block variable. -/
def TermsAffineDegreeZero
    (layout : Fin n → Fin k ⊕ Fin l)
    (p : PolynomialCode n) : Prop :=
  ∀ t ∈ p, AffineDegreeZero layout t.1

/-- Direct arbitrary-chart evaluation of one homogenized term which uses
only already compact variables.  Unlike the usual scaled-chart theorem,
this identity remains applicable when a chart weight is zero. -/
theorem eval₂Hom_decodeTerm_liftTerm_chartPoint_of_affineDegreeZero
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (t : ExponentCode n × RationalCode)
    (ht : AffineDegreeZero layout t.1)
    (x : Fin n → R) (w : Fin k → R) :
    eval₂Hom (algebraMap ℚ R) (chartPoint x w)
        (PolynomialCode.decodeTerm (liftTerm layout M t)) =
      slowdown M w *
        eval₂Hom (algebraMap ℚ R) x
          (PolynomialCode.decodeTerm t) := by
  simp only [PolynomialCode.decodeTerm, liftTerm, eval₂Hom_monomial]
  rw [Finsupp.prod_of_support_subset
      (ExponentCode.decode (liftExponent layout M t.1))
      (Finset.subset_univ _) _ (by simp),
    Finsupp.prod_of_support_subset
      (ExponentCode.decode t.1)
      (Finset.subset_univ _) _ (by simp)]
  simp only [ExponentCode.decode]
  rw [← finSumFinEquiv.prod_comp, Fintype.prod_sum_type]
  simp only [ne_eq, Finsupp.coe_mk]
  simp only [chartPoint, MultiCentralPolynomialCode.chartPoint,
    liftExponent, Equiv.symm_apply_apply]
  unfold AffineDegreeZero at ht
  simp_rw [ht, Nat.sub_zero]
  unfold slowdown
  ring

/-- Arbitrary-chart evaluation of a complete homogenized polynomial whose
terms use only already compact variables. -/
theorem eval₂Hom_homogenize_chartPoint_of_termsAffineDegreeZero
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (p : PolynomialCode n)
    (hp : TermsAffineDegreeZero layout p)
    (x : Fin n → R) (w : Fin k → R) :
    eval₂Hom (algebraMap ℚ R) (chartPoint x w)
        (PolynomialCode.decode (homogenize layout M p)) =
      slowdown M w *
        eval₂Hom (algebraMap ℚ R) x
          (PolynomialCode.decode p) := by
  induction p with
  | nil => simp [homogenize]
  | cons t p ih =>
      have ht : AffineDegreeZero layout t.1 :=
        hp t (by simp)
      have hp' : TermsAffineDegreeZero layout p := by
        intro u hu
        exact hp u (by simp [hu])
      simp only [homogenize, List.map_cons,
        PolynomialCode.decode_cons, map_add]
      rw [
        eval₂Hom_decodeTerm_liftTerm_chartPoint_of_affineDegreeZero
          layout M t ht x w]
      change
        slowdown M w *
              eval₂Hom (algebraMap ℚ R) x
                (PolynomialCode.decodeTerm t) +
            eval₂Hom (algebraMap ℚ R) (chartPoint x w)
              (PolynomialCode.decode (homogenize layout M p)) =
          slowdown M w *
            (eval₂Hom (algebraMap ℚ R) x
                (PolynomialCode.decodeTerm t) +
              eval₂Hom (algebraMap ℚ R) x
                (PolynomialCode.decode p))
      rw [ih hp']
      ring

/-- Denominator clearing multiplies the dot product in an already compact
block by the common slowdown, provided precisely the source components
occurring in that block use no affine variables. -/
theorem compactBlockDot_clearedSourceVelocity_of_termsAffineDegreeZero
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (P : PolynomialFieldCode n)
    (x : Fin n → ℝ) (w : Fin k → ℝ) (c : Fin l)
    (hP :
      ∀ j, layout j = Sum.inr c →
        TermsAffineDegreeZero layout (P j)) :
    compactBlockDot layout x
        (clearedSourceVelocity layout M P (chartPoint x w)) c =
      slowdown M w *
        compactBlockDot layout x
          (PolynomialFieldCode.realize P x) c := by
  unfold compactBlockDot
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : layout j = Sum.inr c
  · simp only [hj, ↓reduceIte, clearedSourceVelocity,
      PolynomialFieldCode.realize_apply]
    rw [
      eval₂Hom_homogenize_chartPoint_of_termsAffineDegreeZero
        layout M (P j) (hP j hj) x w]
    ring
  · simp [hj]

/-- In particular, an exactly tangent compact block stays tangent after
mixed denominator clearing, globally and without a nonzero-weight
hypothesis. -/
theorem compactBlockDot_clearedSourceVelocity_eq_zero
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (P : PolynomialFieldCode n)
    (x : Fin n → ℝ) (w : Fin k → ℝ) (c : Fin l)
    (hP :
      ∀ j, layout j = Sum.inr c →
        TermsAffineDegreeZero layout (P j))
    (htangent :
      compactBlockDot layout x
        (PolynomialFieldCode.realize P x) c = 0) :
    compactBlockDot layout x
        (clearedSourceVelocity layout M P (chartPoint x w)) c = 0 := by
  rw [
    compactBlockDot_clearedSourceVelocity_of_termsAffineDegreeZero
      layout M P x w c hP,
    htangent,
    mul_zero]

end MixedCentralPolynomialCode

end

end HGAS
