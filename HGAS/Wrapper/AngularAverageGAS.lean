import HGAS.Dynamics.EuclideanAngularBlockGAS
import HGAS.Dynamics.UniformNegativeBlocks
import Mathlib.Tactic

/-!
# GAS as negativity of the maximal Euclidean angular average

The existing GAS criterion is phrased using one common negative orbit
block on the ambient cutoff angular flow.  The invariant-measure theorem
is phrased for a flow on a compact space.  This file supplies the missing
literal bridge: restrict the cutoff flow and reward to the Euclidean unit
sphere, prove that the two block predicates agree, and compose the two
criteria.

This theorem is independent of the product-sphere construction and is
reusable for every homogeneous finite-dimensional vector field.
-/

namespace HGAS

open Metric Set
open scoped BoundedContinuousFunction RealInnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The Euclidean unit sphere as a compact phase type. -/
abbrev EuclideanUnitSphere (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  Metric.sphere (0 : E) 1

noncomputable instance euclideanUnitSphereMeasurableSpace :
    MeasurableSpace (EuclideanUnitSphere E) :=
  borel (EuclideanUnitSphere E)

instance euclideanUnitSphereBorelSpace :
    BorelSpace (EuclideanUnitSphere E) :=
  ⟨rfl⟩

noncomputable instance euclideanUnitSphereNonempty
    [Nontrivial E] : Nonempty (EuclideanUnitSphere E) :=
  (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype

/-- The cutoff Euclidean angular flow restricted to the invariant unit
sphere. -/
noncomputable def euclideanUnitAngularFlow
    (F : E → E) (hF : ContDiff ℝ 1 F) :
    Flow ℝ (EuclideanUnitSphere E) :=
  (euclideanAngularFlow F hF).restrict (by
    intro t x hx
    have hnorm :
        ‖euclideanAngularFlow F hF t x‖ = 1 :=
      euclideanAngularFlow_preserves_norm F hF x
        (by simpa [EuclideanUnitSphere, Metric.mem_sphere,
          dist_zero_right] using hx) t
    simpa [EuclideanUnitSphere, Metric.mem_sphere,
      dist_zero_right] using hnorm)

/-- The bounded radial reward restricted to the unit sphere. -/
noncomputable def euclideanUnitRadialReward
    (F : E → E) (hF : ContDiff ℝ 1 F) :
    EuclideanUnitSphere E →ᵇ ℝ :=
  (boundedCutoffInnerRadialReward F hF).compContinuous
    ⟨Subtype.val, continuous_subtype_val⟩

@[simp]
theorem euclideanUnitRadialReward_apply
    (F : E → E) (hF : ContDiff ℝ 1 F)
    (u : EuclideanUnitSphere E) :
    euclideanUnitRadialReward F hF u =
      boundedCutoffInnerRadialReward F hF u :=
  rfl

/-- Restricting the angular flow does not alter an orbit integral that
starts on the sphere. -/
theorem orbitIntegral_euclideanUnit_eq
    (F : E → E) (hF : ContDiff ℝ 1 F)
    (T : ℝ) (u : EuclideanUnitSphere E) :
    Dynamics.orbitIntegral
        (euclideanUnitAngularFlow F hF)
        (euclideanUnitRadialReward F hF) T u =
      Dynamics.orbitIntegral
        (euclideanAngularFlow F hF)
        (boundedCutoffInnerRadialReward F hF) T u := by
  apply intervalIntegral.integral_congr
  intro t _
  rfl

/-- The paper's ambient formulation of a uniform negative angular block is
identical to the compact-sphere flow formulation. -/
theorem uniformNegativeEuclideanAngularBlock_iff_unitSphere
    (F : E → E) (hF : ContDiff ℝ 1 F) :
    HasUniformNegativeEuclideanAngularBlock F hF ↔
      Dynamics.HasUniformNegativeBlock
        (euclideanUnitAngularFlow F hF)
        (euclideanUnitRadialReward F hF) := by
  constructor
  · rintro ⟨T, c, hT, hc, hblock⟩
    refine ⟨T, c, hT, hc, ?_⟩
    intro u
    rw [orbitIntegral_euclideanUnit_eq]
    exact hblock u (by
      have hu := u.property
      simp only [EuclideanUnitSphere, Metric.mem_sphere,
        dist_zero_right] at hu
      exact hu)
  · rintro ⟨T, c, hT, hc, hblock⟩
    refine ⟨T, c, hT, hc, ?_⟩
    intro u hu
    let us : EuclideanUnitSphere E :=
      ⟨u, by
        simpa [EuclideanUnitSphere, Metric.mem_sphere,
          dist_zero_right] using hu⟩
    simpa [us, orbitIntegral_euclideanUnit_eq] using hblock us

/-- **Maximal-angular-average criterion for homogeneous GAS.**

For a nontrivial finite-dimensional real inner-product space and a `C²`
field homogeneous of positive degree, GAS of the origin is equivalent to
strict negativity of the attained maximal invariant radial average on the
unit angular sphere. -/
theorem globallyAsymptoticallyStable_iff_maximalAngularAverage_neg
    [Nontrivial E]
    (F : E → E) (k : ℕ)
    (hFhom : ScalesAsDegree ℝ (k + 1) F)
    (hF : ContDiff ℝ 2 F)
    (hzero : F 0 = 0) :
    GloballyAsymptoticallyStable F 0 ↔
      Dynamics.maximalInvariantAverage
        (euclideanUnitAngularFlow F (hF.of_le (by norm_num)))
        (euclideanUnitRadialReward F (hF.of_le (by norm_num))) < 0 := by
  rw [globallyAsymptoticallyStable_iff_uniformNegativeEuclideanAngularBlock
    F k hFhom hF hzero]
  rw [uniformNegativeEuclideanAngularBlock_iff_unitSphere]
  exact
    (Dynamics.maximalInvariantAverage_neg_iff_uniformNegativeBlock
      (euclideanUnitAngularFlow F (hF.of_le (by norm_num)))
      (euclideanUnitRadialReward F
        (hF.of_le (by norm_num)))).symm

end

end HGAS
