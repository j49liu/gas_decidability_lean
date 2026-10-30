import HGAS.Veronese.CubicLiftStabilizationBounds
import Mathlib.Tactic

/-!
# Quantitative data for the Lyapunov half of the cubicization theorem

The stabilization package `CubicLiftStabilizationBounds` suffices for
global asymptotic stability.  For Lyapunov stability the paper uses, in
addition, a Lipschitz constant `L` of the angular field and of the radial
rate of the unstabilized cubic lift on the weighted unit sphere, and the
stronger gain condition `2L + 1 ≤ K c - C`, which makes the transverse
contraction rate `λ = K c - C` dominate twice the rate at which the
angular flow of the lift separates nearby orbits.

The Lipschitz estimates are stated for the sup norm of the coordinate
space `RealVeroneseSpace n k`.
-/

namespace HGAS.Veronese

noncomputable section

variable {n k : ℕ}

/-- The stabilization package together with a Lipschitz constant of the
unstabilized angular field and radial rate on `Q = 1`, and the shadowing
gain condition. -/
structure CubicLiftShadowingBounds
    (F : HGAS.PolynomialField n) (k : ℕ)
    extends CubicLiftStabilizationBounds F k where
  L : ℝ
  L_nonneg : 0 ≤ L
  angularLipschitz :
    ∀ y y' : RealVeroneseSpace n k, Q y = 1 → Q y' = 1 →
      ‖weightedAngularField (evaluatedCubicLift (k := k) F) y -
          weightedAngularField (evaluatedCubicLift (k := k) F) y'‖ ≤
        L * ‖y - y'‖
  radialLipschitz :
    ∀ y y' : RealVeroneseSpace n k, Q y = 1 → Q y' = 1 →
      |weightedRadialReward (evaluatedCubicLift (k := k) F) y -
          weightedRadialReward (evaluatedCubicLift (k := k) F) y'| ≤
        L * ‖y - y'‖
  shadowGain : 2 * L + 1 ≤ (K : ℝ) * c - C

end

end HGAS.Veronese
