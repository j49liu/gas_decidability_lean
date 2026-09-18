import HGAS.Wrapper.UnitSphereWrapperFixedFace
import HGAS.Wrapper.SemanticProductSphere
import Mathlib.Tactic

/-!
# Concrete semantic GAS theorem for the finite-code wrapper

This file instantiates every algebraic, regularity, radius-cleanup, reward,
and proper-face hypothesis of `semanticProductSphereWrapper_gas_iff`.

Only the genuinely source-dynamical statements remain as inputs:

1. invariance of the full two-sheet product-sphere stratum; and
2. identification of its maximal chart-reward average with the chosen
   source maximum `β`.

Those two hypotheses are kept explicit.  Everything else is now supplied
by the executable sparse compiler.
-/

namespace HGAS

open Function Metric Set
open scoped BigOperators BoundedContinuousFunction RealInnerProductSpace

noncomputable section

namespace UnitSpherePolynomialWrapper

variable {n k : ℕ}

/-- The realized raw compiler output scales with its advertised target
degree. -/
theorem scalesAsDegree_realize_finalFieldCode
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (hD : 3 ≤ D) (hDodd : D % 2 = 1)
    (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE D (P j))
    (a : PolynomialCode n)
    (ha : PolynomialCode.TermsDegreeLE (D - 1) a) :
    ScalesAsDegree ℝ (targetDegree k D)
      (PolynomialFieldCode.realize
        (finalFieldCode sourceBlock D P a)) := by
  intro c x
  exact evalPolynomialField_smul
    (PolynomialFieldCode.decode
      (finalFieldCode sourceBlock D P a))
    (finalFieldCode_isHomogeneous_of_degreeBounds
      sourceBlock D hD hDodd P hP a ha) c x

/-- The Euclidean-normalized compiler output has the same homogeneity
degree. -/
theorem scalesAsDegree_euclideanFinalField
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (hD : 3 ≤ D) (hDodd : D % 2 = 1)
    (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE D (P j))
    (a : PolynomialCode n)
    (ha : PolynomialCode.TermsDegreeLE (D - 1) a) :
    ScalesAsDegree ℝ (targetDegree k D)
      (euclideanFinalField sourceBlock D P a) :=
  scalesAsDegree_conjugateField wrapperEuclideanEquiv
    (scalesAsDegree_realize_finalFieldCode
      sourceBlock D hD hDodd P hP a ha)

/-- The target degree is positive under the wrapper's standard degree
hypothesis. -/
theorem targetDegree_pos
    (D : ℕ) (hD : 3 ≤ D) :
    0 < targetDegree k D := by
  unfold targetDegree
  omega

/-- A positive-degree homogeneous Euclidean wrapper field fixes the
origin. -/
theorem euclideanFinalField_zero
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (hD : 3 ≤ D) (hDodd : D % 2 = 1)
    (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE D (P j))
    (a : PolynomialCode n)
    (ha : PolynomialCode.TermsDegreeLE (D - 1) a) :
    euclideanFinalField sourceBlock D P a 0 = 0 := by
  have hscale :=
    scalesAsDegree_euclideanFinalField
      sourceBlock D hD hDodd P hP a ha
      (0 : ℝ) (0 : EuclideanWrapperSpace n)
  simpa [zero_pow (targetDegree_pos (k := k) D hD).ne'] using hscale

/-- The advertised target degree is the successor required by the angular
GAS theorem. -/
theorem targetDegree_sub_one_add_one
    (D : ℕ) (hD : 3 ≤ D) :
    targetDegree k D - 1 + 1 = targetDegree k D :=
  Nat.sub_add_cancel (targetDegree_pos (k := k) D hD)

/-- Fully concrete Euclidean GAS equivalence, conditional only on the two
source-dynamical full-stratum statements. -/
theorem euclideanFinalField_gas_iff_of_fullStratumMaximum
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (hD : 3 ≤ D) (hDodd : D % 2 = 1)
    (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE D (P j))
    (a : PolynomialCode n)
    (ha : PolynomialCode.TermsDegreeLE (D - 1) a)
    (i : Fin k)
    (β : ℝ)
    (hfullInvariant :
      IsInvariant
        (euclideanUnitAngularFlow
          (euclideanFinalField sourceBlock D P a)
          ((contDiff_euclideanFinalField
            sourceBlock D P a).of_le (by norm_num)))
        (radiusCleanupFlowCertificate
          sourceBlock D P a).fullStratum)
    (hsource :
      (radiusCleanupFlowCertificate sourceBlock D P a).FullStratumMaximum
        (chartRewardBCF (k := k) D a) β) :
    GloballyAsymptoticallyStable
      (euclideanFinalField sourceBlock D P a) 0 ↔
      β < 0 := by
  let F := euclideanFinalField sourceBlock D P a
  let hF2 : ContDiff ℝ 2 F :=
    (contDiff_euclideanFinalField
      sourceBlock D P a).of_le (by norm_num)
  have hhom :
      ScalesAsDegree ℝ
        ((targetDegree k D - 1) + 1) F := by
    simpa only [F, targetDegree_sub_one_add_one (k := k) D hD] using
      scalesAsDegree_euclideanFinalField
        sourceBlock D hD hDodd P hP a ha
  exact semanticProductSphereWrapper_gas_iff
    F (targetDegree k D - 1)
    hhom hF2
    (euclideanFinalField_zero
      sourceBlock D hD hDodd P hP a ha)
    (radiusCleanupFlowCertificate sourceBlock D P a)
    (chartRewardBCF (k := k) D a) β
    hfullInvariant hsource
    (exists_properFace_fixedPoint
      sourceBlock D P a hP i)
    (rewardObservable_eq_euclideanUnitRadialReward
      sourceBlock D P a)

/-- The same theorem in the raw finite-code coordinate space used by the
decision language. -/
theorem realize_finalFieldCode_gas_iff_of_fullStratumMaximum
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (hD : 3 ≤ D) (hDodd : D % 2 = 1)
    (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE D (P j))
    (a : PolynomialCode n)
    (ha : PolynomialCode.TermsDegreeLE (D - 1) a)
    (i : Fin k)
    (β : ℝ)
    (hfullInvariant :
      IsInvariant
        (euclideanUnitAngularFlow
          (euclideanFinalField sourceBlock D P a)
          ((contDiff_euclideanFinalField
            sourceBlock D P a).of_le (by norm_num)))
        (radiusCleanupFlowCertificate
          sourceBlock D P a).fullStratum)
    (hsource :
      (radiusCleanupFlowCertificate sourceBlock D P a).FullStratumMaximum
        (chartRewardBCF (k := k) D a) β) :
    GloballyAsymptoticallyStable
        (PolynomialFieldCode.realize
          (finalFieldCode sourceBlock D P a)) 0 ↔
      β < 0 := by
  rw [← globallyAsymptoticallyStable_conjugateField_iff
    wrapperEuclideanEquiv
    (PolynomialFieldCode.realize
      (finalFieldCode sourceBlock D P a))]
  exact euclideanFinalField_gas_iff_of_fullStratumMaximum
    sourceBlock D hD hDodd P hP a ha i β
    hfullInvariant hsource

end UnitSpherePolynomialWrapper

end

end HGAS
