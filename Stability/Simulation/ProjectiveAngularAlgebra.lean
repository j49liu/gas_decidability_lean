import Stability.Simulation.ProjectivePolynomialCode
import HGAS.Algebra.HomogeneousEvaluation
import HGAS.Veronese.SourceAngularFlow

/-!
# Angular and radial identities for the projective field

On the Euclidean unit sphere the radial reward is exactly the homogenized
output, and the angular field is the tangential projection of the
homogenized source. These identities concern the actual compiled field.
-/

namespace Stability.ProjectivePolynomialCode

open HGAS HGAS.Veronese MvPolynomial
open scoped BigOperators

noncomputable section

variable {n : ℕ}

theorem contDiff_realize_fieldCode (ell : ℕ) (P : PolynomialFieldCode n) (b : PolynomialCode n) :
    ContDiff ℝ ⊤ (PolynomialFieldCode.realize (fieldCode ell P b)) := by
  rw [contDiff_pi]
  intro i
  exact HGAS.contDiff_eval₂Hom_rational_real_fintype _

theorem scalesAsDegree_realize_fieldCode (ell : ℕ) (hell : 1 ≤ ell)
    (P : PolynomialFieldCode n) (b : PolynomialCode n)
    (hP : ∀ i, PolynomialCode.TermsDegreeLE ell (P i))
    (hb : PolynomialCode.TermsDegreeLE (ell - 1) b) :
    ScalesAsDegree ℝ (ell + 2) (PolynomialFieldCode.realize (fieldCode ell P b)) :=
  fun c x ↦ HGAS.evalPolynomialField_smul _ (isHomogeneous_fieldCode ell hell P b hP hb) c x

theorem realize_fieldCode_eq (ell : ℕ) (P : PolynomialFieldCode n) (b : PolynomialCode n)
    (y : Fin (n + 1) → ℝ) :
    PolynomialFieldCode.realize (fieldCode ell P b) y =
      HGAS.normSq y • PolynomialFieldCode.realize (augmentedFieldCode ell P) y -
      HGAS.dot y (PolynomialFieldCode.realize (augmentedFieldCode ell P) y) • y +
      (HGAS.normSq y *
        eval₂Hom (algebraMap ℚ ℝ) y (PolynomialCode.decode (radialRateCode ell b))) • y := by
  funext i
  exact realize_fieldCode ell P b y i

theorem realize_fieldCode_zero (ell : ℕ) (P : PolynomialFieldCode n) (b : PolynomialCode n) :
    PolynomialFieldCode.realize (fieldCode ell P b) 0 = 0 := by
  rw [realize_fieldCode_eq]
  simp

private theorem dot_sub_right (y v w : Fin (n + 1) → ℝ) :
    HGAS.dot y (v - w) = HGAS.dot y v - HGAS.dot y w := by
  simp [HGAS.dot, mul_sub, Finset.sum_sub_distrib]

theorem radialReward_fieldCode_on_sphere (ell : ℕ) (P : PolynomialFieldCode n)
    (b : PolynomialCode n) (y : Fin (n + 1) → ℝ) (hy : sourceRadiusSq y = 1) :
    HGAS.radialReward (PolynomialFieldCode.realize (fieldCode ell P b)) y =
      eval₂Hom (algebraMap ℚ ℝ) y (PolynomialCode.decode (radialRateCode ell b)) := by
  have hnorm : HGAS.normSq y = 1 := by rw [HGAS.normSq_eq_sourceRadiusSq, hy]
  have hdot : HGAS.dot y y = 1 := hnorm
  rw [HGAS.radialReward, realize_fieldCode_eq, HGAS.dot_add_right, dot_sub_right]
  simp only [HGAS.dot_smul_right, hnorm, hdot, one_mul, mul_one, sub_self, zero_add]

theorem angularField_fieldCode_on_sphere (ell : ℕ) (P : PolynomialFieldCode n)
    (b : PolynomialCode n) (y : Fin (n + 1) → ℝ) (hy : sourceRadiusSq y = 1) :
    HGAS.angularField (PolynomialFieldCode.realize (fieldCode ell P b)) y =
      PolynomialFieldCode.realize (augmentedFieldCode ell P) y -
        HGAS.dot y (PolynomialFieldCode.realize (augmentedFieldCode ell P) y) • y := by
  have hnorm : HGAS.normSq y = 1 := by rw [HGAS.normSq_eq_sourceRadiusSq, hy]
  change PolynomialFieldCode.realize (fieldCode ell P b) y -
    HGAS.radialReward (PolynomialFieldCode.realize (fieldCode ell P b)) y • y = _
  rw [radialReward_fieldCode_on_sphere ell P b y hy,
    realize_fieldCode_eq, hnorm]
  simp only [one_smul, one_mul, add_sub_cancel_right]

theorem angularField_fieldCode_last (ell : ℕ) (P : PolynomialFieldCode n)
    (b : PolynomialCode n) (y : Fin (n + 1) → ℝ) (hy : sourceRadiusSq y = 1) :
    HGAS.angularField (PolynomialFieldCode.realize (fieldCode ell P b)) y (Fin.last n) =
      -HGAS.dot y (PolynomialFieldCode.realize (augmentedFieldCode ell P) y) * y (Fin.last n) := by
  rw [angularField_fieldCode_on_sphere ell P b y hy]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, realize_augmentedFieldCode_last]
  ring

theorem angularField_fieldCode_equator (ell : ℕ) (P : PolynomialFieldCode n)
    (b : PolynomialCode n)
    (hP : ∀ i t, t ∈ P i → ExponentCode.totalDegree t.1 < ell)
    (hb : ∀ t ∈ b, ExponentCode.totalDegree t.1 < ell - 1)
    (y : Fin (n + 1) → ℝ) (hy : y (Fin.last n) = 0) :
    HGAS.angularField (PolynomialFieldCode.realize (fieldCode ell P b)) y = 0 := by
  funext i
  change PolynomialFieldCode.realize (fieldCode ell P b) y i -
    HGAS.dot y (PolynomialFieldCode.realize (fieldCode ell P b) y) * y i = 0
  rw [realize_fieldCode_equator ell P b hP hb y hy]
  simp

/-- The actual angular differential equation gives the expected source
equation in the quotient chart. The time factor is not assumed. -/
theorem hasDerivAt_quotient_chart (ell : ℕ) (hell : 1 ≤ ell)
    (P : PolynomialFieldCode n) (b : PolynomialCode n)
    (hP : ∀ i, PolynomialCode.TermsDegreeLE ell (P i))
    {y : ℝ → Fin (n + 1) → ℝ} {t : ℝ}
    (hderiv : HasDerivAt y
      (HGAS.angularField (PolynomialFieldCode.realize (fieldCode ell P b)) (y t)) t)
    (hsphere : sourceRadiusSq (y t) = 1) (hz : y t (Fin.last n) ≠ 0) :
    HasDerivAt (fun r i ↦ y r i.castSucc / y r (Fin.last n))
      (y t (Fin.last n) ^ (ell - 1) • PolynomialFieldCode.realize P
        (fun i ↦ y t i.castSucc / y t (Fin.last n))) t := by
  apply hasDerivAt_pi.mpr
  intro i
  have hcoord := (hasDerivAt_pi.mp hderiv) i.castSucc
  have hlast := (hasDerivAt_pi.mp hderiv) (Fin.last n)
  rw [angularField_fieldCode_on_sphere ell P b (y t) hsphere] at hcoord
  rw [angularField_fieldCode_last ell P b (y t) hsphere] at hlast
  have hquotient := hcoord.div hlast hz
  convert hquotient using 1
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
  have hpow : y t (Fin.last n) ^ ell = y t (Fin.last n) ^ (ell - 1) * y t (Fin.last n) := by
    conv_lhs => rw [← Nat.sub_add_cancel hell, pow_succ]
  rw [realize_augmentedFieldCode_quotient ell P hP (y t) hz i, hpow]
  generalize PolynomialFieldCode.realize P
    (fun j ↦ y t j.castSucc / y t (Fin.last n)) i = value
  field_simp
  ring

end

end Stability.ProjectivePolynomialCode
