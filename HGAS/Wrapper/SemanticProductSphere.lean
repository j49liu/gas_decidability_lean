import HGAS.Wrapper.AngularAverageGAS
import HGAS.Wrapper.InvariantAverage
import HGAS.Wrapper.ParityHomogenization
import Mathlib.Tactic

/-!
# The semantic product-sphere wrapper theorem

This file composes the two completed halves:

* radius cleanup plus the exact `max {β,-1}` invariant-average identity;
* GAS iff negativity of the maximal Euclidean angular radial average.

The theorem is deliberately explicit about the remaining construction
obligations.  Its `RadiusCleanupFlowCertificate` contains the integrated
radius Lyapunov identity, and `hreward` identifies the concrete
homogeneous field's angular radial reward with the wrapper reward.
`FullStratumMaximum` records the exact source maximum on the intended
stratum.  Once an actual polynomial chart/homogenization supplies these
objects, no further dynamical or measure-theoretic argument is needed.
-/

namespace HGAS

open Set
open scoped BoundedContinuousFunction RealInnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

/-- The final angular maximal average has the manuscript's exact value
`max β (-1)`. -/
theorem semanticProductSphereWrapper_maximalAverage
    (F : E → E) (hF1 : ContDiff ℝ 1 F)
    {blocks : ℕ}
    (certificate :
      RadiusCleanupFlowCertificate
        (euclideanUnitAngularFlow F hF1) blocks)
    (α : EuclideanUnitSphere E →ᵇ ℝ) (β : ℝ)
    (hfullInvariant :
      IsInvariant (euclideanUnitAngularFlow F hF1)
        certificate.fullStratum)
    (hsource :
      certificate.FullStratumMaximum α β)
    (hproperFixed :
      ∃ x : EuclideanUnitSphere E,
        x ∈ certificate.properFace ∧
          Dynamics.InvariantProbabilityMeasure.IsFlowFixedPoint
            (euclideanUnitAngularFlow F hF1) x)
    (hreward :
      certificate.rewardObservable α =
        euclideanUnitRadialReward F hF1) :
    Dynamics.maximalInvariantAverage
        (euclideanUnitAngularFlow F hF1)
        (euclideanUnitRadialReward F hF1) =
      max β (-1) := by
  rw [← hreward]
  exact certificate.maximalInvariantAverage_reward_eq_max
    α β hfullInvariant hsource hproperFixed

/-- **Semantic product-sphere wrapper theorem.**

For any concrete homogeneous field whose unit-sphere angular system
realizes the certified radius cleanup and wrapper reward, GAS is equivalent
to strict negativity of the source maximal invariant average. -/
theorem semanticProductSphereWrapper_gas_iff
    (F : E → E) (k : ℕ)
    (hFhom : ScalesAsDegree ℝ (k + 1) F)
    (hF : ContDiff ℝ 2 F)
    (hzero : F 0 = 0)
    {blocks : ℕ}
    (certificate :
      RadiusCleanupFlowCertificate
        (euclideanUnitAngularFlow F (hF.of_le (by norm_num))) blocks)
    (α : EuclideanUnitSphere E →ᵇ ℝ) (β : ℝ)
    (hfullInvariant :
      IsInvariant
        (euclideanUnitAngularFlow F (hF.of_le (by norm_num)))
        certificate.fullStratum)
    (hsource :
      certificate.FullStratumMaximum α β)
    (hproperFixed :
      ∃ x : EuclideanUnitSphere E,
        x ∈ certificate.properFace ∧
          Dynamics.InvariantProbabilityMeasure.IsFlowFixedPoint
            (euclideanUnitAngularFlow F (hF.of_le (by norm_num))) x)
    (hreward :
      certificate.rewardObservable α =
        euclideanUnitRadialReward F (hF.of_le (by norm_num))) :
    GloballyAsymptoticallyStable F 0 ↔ β < 0 := by
  rw [globallyAsymptoticallyStable_iff_maximalAngularAverage_neg
    F k hFhom hF hzero]
  rw [semanticProductSphereWrapper_maximalAverage
    F (hF.of_le (by norm_num)) certificate α β
    hfullInvariant hsource hproperFixed hreward]
  simp

end

end HGAS
