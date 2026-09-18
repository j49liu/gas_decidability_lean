import HGAS.Wrapper.UnitSphereWrapperFlowCertificate
import HGAS.Wrapper.InvariantAverage
import Mathlib.Tactic

/-!
# The concrete wrapper reward observable

The semantic product-sphere theorem asks for an ambient observable `α`
whose radius-weighted wrapper reward agrees with the radial reward of the
final homogeneous field.  Here `α` is simply the normalized chart reward.

All equalities are literal:

* the certificate radii are the scaled block radii;
* `rewardObservable α` is the raw coded wrapper reward;
* parity homogenization does not change that reward on the unit sphere;
* the radial part of `F = Y + A x` is exactly `A`.

Thus this file discharges the semantic theorem's `hreward` obligation for
the concrete finite-code compiler.
-/

namespace HGAS

open Function Metric Set
open scoped BigOperators BoundedContinuousFunction RealInnerProductSpace

noncomputable section

namespace UnitSpherePolynomialWrapper

variable {n k : ℕ}

/-- Evaluation of any sparse rational polynomial code is continuous. -/
theorem continuous_eval_polynomialCode
    (p : PolynomialCode (n + 1)) :
    Continuous (fun x : RawWrapperSpace n ↦
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode p)) := by
  have h :=
    (contDiff_ratMvPolynomialEval
      (PolynomialCode.decode p)).continuous
  convert h using 1
  funext x
  simp [ratMvPolynomialEval, MvPolynomial.eval_map]

/-- The normalized chart reward, bundled on the Euclidean unit sphere. -/
noncomputable def chartRewardBCF
    (D : ℕ) (a : PolynomialCode n) :
    EuclideanUnitSphere (EuclideanWrapperSpace n) →ᵇ ℝ := by
  exact BoundedContinuousFunction.mkOfCompact
    ⟨fun u ↦
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (wrapperEuclideanEquiv.symm u.1)
        (PolynomialCode.decode (chartRewardCode k D a)),
      (continuous_eval_polynomialCode
        (chartRewardCode k D a)).comp
          (wrapperEuclideanEquiv.symm.continuous.comp
            continuous_subtype_val)⟩

@[simp]
theorem chartRewardBCF_apply
    (D : ℕ) (a : PolynomialCode n)
    (u : EuclideanUnitSphere (EuclideanWrapperSpace n)) :
    chartRewardBCF (k := k) D a u =
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (wrapperEuclideanEquiv.symm u.1)
        (PolynomialCode.decode (chartRewardCode k D a)) :=
  rfl

@[simp]
theorem radiusCleanupFlowCertificate_radii_apply
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n)
    (b : Fin (k + 1))
    (u : EuclideanUnitSphere (EuclideanWrapperSpace n)) :
    (radiusCleanupFlowCertificate sourceBlock D P a).radii b u =
      scaledBlockRadius sourceBlock
        (wrapperEuclideanEquiv.symm u.1) b :=
  rfl

/-- Pointwise identification of the semantic wrapper observable with the
raw sparse wrapper-reward code. -/
theorem rewardObservable_chartRewardBCF_apply
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n)
    (u : EuclideanUnitSphere (EuclideanWrapperSpace n)) :
    (radiusCleanupFlowCertificate sourceBlock D P a).rewardObservable
        (chartRewardBCF (k := k) D a) u =
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (wrapperEuclideanEquiv.symm u.1)
        (PolynomialCode.decode
          (rawWrapperRewardCode sourceBlock D a)) := by
  rw [RadiusCleanupFlowCertificate.rewardObservable_apply,
    eval_rawWrapperRewardCode]
  rfl

/-- The chart-wrapper observable is exactly the Euclidean radial reward of
the final compiled field. -/
theorem rewardObservable_eq_euclideanUnitRadialReward
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n) :
    (radiusCleanupFlowCertificate sourceBlock D P a).rewardObservable
        (chartRewardBCF (k := k) D a) =
      euclideanUnitRadialReward
        (euclideanFinalField sourceBlock D P a)
        ((contDiff_euclideanFinalField
          sourceBlock D P a).of_le (by norm_num)) := by
  ext u
  let x : RawWrapperSpace n :=
    wrapperEuclideanEquiv.symm u.1
  have hx : normSq x = 1 :=
    normSq_wrapperEuclideanEquiv_symm_sphere u
  have hnorm : ‖u.1‖ = 1 := by
    have hu := u.property
    change dist u.1 0 = 1 at hu
    rw [dist_zero_right] at hu
    exact hu
  rw [rewardObservable_chartRewardBCF_apply]
  rw [← eval_homogeneousRewardCode_of_normSq_one
    sourceBlock D a x hx]
  rw [← radialReward_finalFieldCode_of_normSq_one
    sourceBlock D P a x hx]
  change
    radialReward
        (PolynomialFieldCode.realize
          (finalFieldCode sourceBlock D P a)) x =
      boundedCutoffInnerRadialReward
        (euclideanFinalField sourceBlock D P a)
        ((contDiff_euclideanFinalField
          sourceBlock D P a).of_le (by norm_num)) u.1
  rw [boundedCutoffInnerRadialReward_apply,
    cutoffInnerRadialReward_eq_of_norm_eq_one
      (euclideanFinalField sourceBlock D P a) u.1 hnorm]
  symm
  simpa only [euclideanFinalField, x, wrapperEuclideanEquiv] using
    Veronese.innerRadialReward_conjugateField_sourceEuclideanEquiv
      (PolynomialFieldCode.realize
        (finalFieldCode sourceBlock D P a)) x

end UnitSpherePolynomialWrapper

end

end HGAS
