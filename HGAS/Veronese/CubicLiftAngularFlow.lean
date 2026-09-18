import HGAS.Veronese.CoordinateFieldSmoothness
import HGAS.Veronese.CubicLiftStabilizationBounds
import HGAS.Veronese.WeightedAngularFlow
import Mathlib.Tactic

/-!
# The angular flow of the stabilized cubic lift

This module joins the algebraic cubicizer and its quantitative bounds to
the general weighted-angular flow construction.

For stabilization data `b`, the rational polynomial
`stabilizedCubicField F b.K` evaluates to a smooth real cubic vector field.
We therefore obtain:

* a global ambient angular flow;
* its restriction to the compact ellipsoid `Q=1`;
* the exact derivative of the toric penalty along every orbit;
* the already-proved uniform negative derivative estimate inside the tube;
* the already-proved radial-reward estimate outside the tube.

No new geometric hypothesis is introduced here.
-/

namespace HGAS.Veronese

open Set
open scoped Topology NNReal

noncomputable section

variable {n k : ℕ} {F : HGAS.PolynomialField n}

/-- Real evaluation of the rational stabilized cubic field selected by
the quantitative package `b`. -/
def evaluatedStabilizedCubicField
    (b : CubicLiftStabilizationBounds F k) :
    RealVeroneseSpace n k → RealVeroneseSpace n k :=
  fun y ↦
    evalCoordinateField
      (stabilizedCubicField (k := k) F b.K) y

/-- The evaluated stabilized cubic field is smooth. -/
theorem contDiff_evaluatedStabilizedCubicField
    (b : CubicLiftStabilizationBounds F k) :
    ContDiff ℝ 1 (evaluatedStabilizedCubicField b) := by
  exact
    (contDiff_evalCoordinateField_real
      (stabilizedCubicField (k := k) F b.K)).of_le
      (by norm_num)

/-- Ambient global angular flow of the stabilized cubic field. -/
noncomputable def stabilizedCubicAmbientAngularFlow
    (b : CubicLiftStabilizationBounds F k) :
    Flow ℝ (RealVeroneseSpace n k) :=
  weightedAngularFlow
    (evaluatedStabilizedCubicField b)
    (contDiff_evaluatedStabilizedCubicField b)

/-- The continuous angular flow on the compact weighted unit sphere. -/
noncomputable def stabilizedCubicAngularFlow
    (b : CubicLiftStabilizationBounds F k) :
    Flow ℝ (weightedUnitSphere n k) :=
  weightedUnitSphereFlow
    (evaluatedStabilizedCubicField b)
    (contDiff_evaluatedStabilizedCubicField b)

theorem stabilizedCubicAmbientAngularFlow_preserves_Q
    (b : CubicLiftStabilizationBounds F k)
    (y : RealVeroneseSpace n k) (hy : Q y = 1) :
    ∀ t, Q (stabilizedCubicAmbientAngularFlow b t y) = 1 :=
  weightedAngularFlow_preserves_Q
    (evaluatedStabilizedCubicField b)
    (contDiff_evaluatedStabilizedCubicField b) y hy

/-- Ambient orbits starting on `Q=1` solve the uncut angular ODE of the
stabilized cubic field. -/
theorem stabilizedCubicAmbientAngularFlow_isIntegralCurve
    (b : CubicLiftStabilizationBounds F k)
    (y : RealVeroneseSpace n k) (hy : Q y = 1) :
    IsIntegralCurve
      (fun t ↦ stabilizedCubicAmbientAngularFlow b t y)
      (fun _ ↦ weightedAngularField
        (evaluatedStabilizedCubicField b)) :=
  weightedAngularFlow_isIntegralCurve
    (evaluatedStabilizedCubicField b)
    (contDiff_evaluatedStabilizedCubicField b) y hy

/-- Exact infinitesimal evolution of the toric penalty along a stabilized
cubic angular orbit. -/
theorem stabilizedCubicAmbientAngularFlow_hasDerivAt_penalty
    (b : CubicLiftStabilizationBounds F k)
    (y : RealVeroneseSpace n k) (hy : Q y = 1)
    (t : ℝ) :
    HasDerivAt
      (fun s ↦
        completeToricEnergy
          (stabilizedCubicAmbientAngularFlow b s y))
      (penaltyLieDerivative
        (weightedAngularField
          (evaluatedStabilizedCubicField b))
        (stabilizedCubicAmbientAngularFlow b t y)) t := by
  exact
    HGAS.Veronese.HasDerivAt.toricPenalty_comp_eq_weightedInner
      (stabilizedCubicAmbientAngularFlow_isIntegralCurve b y hy t)

/-- Inside the stabilization tube, the derivative along the actual angular
flow obeys the quantitative negative bound. -/
theorem stabilizedCubicAngular_penaltyDerivative_le
    (b : CubicLiftStabilizationBounds F k)
    (y : RealVeroneseSpace n k)
    (hy : Q y = 1)
    (hTube : completeToricEnergy y ≤ b.η) :
    penaltyLieDerivative
        (weightedAngularField
          (evaluatedStabilizedCubicField b)) y ≤
      -((b.K : ℝ) * b.c - b.C) *
        completeToricEnergy y := by
  exact
    b.evaluatedStabilized_angularPenaltyLieDerivative_le
      y hy hTube

/-- The decay coefficient in the preceding estimate is strictly positive. -/
theorem cubicLiftStabilization_decayRate_pos
    (b : CubicLiftStabilizationBounds F k) :
    0 < (b.K : ℝ) * b.c - b.C :=
  sub_pos.mpr b.angularGain

/-- Outside the stabilization tube, the radial reward of the actual
stabilized cubic field is at most `-1`. -/
theorem stabilizedCubicAngular_radialReward_le_neg_one
    (b : CubicLiftStabilizationBounds F k)
    (y : RealVeroneseSpace n k)
    (hy : Q y = 1)
    (hOutside : b.η ≤ completeToricEnergy y) :
    weightedRadialReward
        (evaluatedStabilizedCubicField b) y ≤ -1 :=
  b.evaluatedStabilized_radialReward_le_neg_one
    y hy hOutside

end

end HGAS.Veronese
