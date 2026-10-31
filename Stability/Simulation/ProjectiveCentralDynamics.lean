import Stability.Simulation.ProjectiveCentralChart
import Stability.Simulation.ProjectiveAngularAlgebra

/-!
# Lifting finite polynomial trajectories to the angular field

In the positive central chart, the angular field runs at speed
`c^(ell-1)` relative to the affine polynomial field. The radial output
has the same factor. Reversing that speed therefore preserves the output
integral, as required for the converse projective reduction.
-/

namespace Stability.ProjectivePolynomialCode

open HGAS HGAS.Veronese MvPolynomial
open scoped BigOperators

noncomputable section

variable {n : ℕ}

theorem realize_augmentedFieldCode_centralLift (ell : ℕ) (P : PolynomialFieldCode n)
    (hP : ∀ i, PolynomialCode.TermsDegreeLE ell (P i)) (x : Fin n → ℝ) :
    PolynomialFieldCode.realize (augmentedFieldCode ell P) (centralLift x) =
      centralScale x ^ ell • Fin.lastCases 0 (PolynomialFieldCode.realize P x) := by
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp only [realize_augmentedFieldCode_last, Pi.smul_apply, smul_eq_mul,
      Fin.lastCases_last, mul_zero]
  · rw [realize_augmentedFieldCode_quotient ell P hP _
      (by simpa only [centralLift_last] using (centralScale_pos x).ne') j]
    rw [centralLift_quotient]
    simp only [centralLift_last, Pi.smul_apply,
      smul_eq_mul, Fin.lastCases_castSucc]

theorem dot_centralLift_lastCases (x v : Fin n → ℝ) :
    HGAS.dot (centralLift x) (Fin.lastCases 0 v) = centralScale x * HGAS.dot x v := by
  unfold HGAS.dot
  rw [Fin.sum_univ_castSucc]
  simp only [centralLift_last, centralLift_castSucc, Fin.lastCases_last,
    Fin.lastCases_castSucc, mul_zero, add_zero, Finset.mul_sum, mul_assoc]

theorem centralLift_hasDerivAt_angular (ell : ℕ) (hell : 1 ≤ ell)
    (P : PolynomialFieldCode n) (b : PolynomialCode n)
    (hP : ∀ i, PolynomialCode.TermsDegreeLE ell (P i))
    {x : ℝ → Fin n → ℝ} {t : ℝ}
    (hx : HasDerivAt x (PolynomialFieldCode.realize P (x t)) t) :
    HasDerivAt (fun s ↦ centralLift (x s))
      ((centralScale (x t) ^ (ell - 1))⁻¹ •
        HGAS.angularField (PolynomialFieldCode.realize (fieldCode ell P b))
          (centralLift (x t))) t := by
  have hc : centralScale (x t) ^ (ell - 1) ≠ 0 :=
    pow_ne_zero _ (centralScale_pos (x t)).ne'
  have hp : centralScale (x t) ^ ell =
      centralScale (x t) ^ (ell - 1) * centralScale (x t) := by
    rw [← pow_succ, Nat.sub_add_cancel hell]
  convert centralLift_hasDerivAt hx using 1
  rw [angularField_fieldCode_on_sphere ell P b _ (sourceRadiusSq_centralLift _),
    realize_augmentedFieldCode_centralLift ell P hP, HGAS.dot_smul_right,
    dot_centralLift_lastCases, hp]
  funext i
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  field_simp [hc]

theorem centralLift_weighted_radialReward (ell : ℕ) (P : PolynomialFieldCode n)
    (b : PolynomialCode n) (hb : PolynomialCode.TermsDegreeLE (ell - 1) b)
    (x : Fin n → ℝ) :
    (centralScale x ^ (ell - 1))⁻¹ *
        HGAS.radialReward (PolynomialFieldCode.realize (fieldCode ell P b)) (centralLift x) =
      eval₂Hom (algebraMap ℚ ℝ) x (PolynomialCode.decode b) := by
  rw [radialReward_fieldCode_on_sphere ell P b _ (sourceRadiusSq_centralLift _),
    eval_radialRateCode_quotient ell b hb _
      (by simpa only [centralLift_last] using (centralScale_pos x).ne')]
  rw [centralLift_quotient, centralLift_last, ← mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero _ (centralScale_pos x).ne'), one_mul]

end

end Stability.ProjectivePolynomialCode
