import HGAS.Modular.ClosedUnaryHorocycleChart
import HGAS.Modular.ClosedUnaryHorocycleExactAmplitude
import HGAS.Modular.CanonicalLambdaLocal

/-!
# Exact amplitude in a closed unary horocycle chart

`ClosedUnaryHorocycleChart` remembers the integral completion which turns
a periodic level-two horocycle into a literal horizontal line.  The
weight-two theta transformation law then removes the projective ambiguity
in the unary quartics.  This file packages that last step in the form used
by the moment selector.

Suppose `T` is a differentiable canonical-lambda lift of a unary modular
trajectory and `c` is a closed chart for `T`.  Write

```text
  a = c.horizontalization.cuspNormalized.upperLeft,
  s = a² c.orbitSpeed.
```

Then the common quartic amplitude is exactly `s` at the infinity cusp
and exactly `-s` at the zero and one cusps.  In particular it is a
nonzero real constant, not a time-dependent fourth-root choice.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I

noncomputable section

namespace ClosedUnaryHorocycleChart

variable {z : ℝ → UnaryModularState ℂ}
  {T : ℝ → UpperHalfPlane}

/-- A differentiable canonical-lambda trajectory in a closed chart has
the exact signed cusp amplitude dictated by the horizontal speed. -/
theorem hasCuspQuarticAmplitude
    (c : ClosedUnaryHorocycleChart z T)
    (hz :
      IsScaledUnaryModularTrajectory
        modularIndependentVariableClock z)
    (hB : ∀ t, UnaryModularState.B (z t) ≠ 0)
    (hlambda :
      ∀ t,
        UnaryModularState.lambdaCoordinate (z t) =
          canonicalLambda (T t))
    (hTdiff :
      ∀ t, ∃ v : ℂ,
        HasDerivAt (fun u : ℝ ↦ (T u : ℂ)) v t)
    (t : ℝ) :
    HasCuspQuarticAmplitude c.cuspLabel
      (z t) (c.horizontalModulus t)
      (cuspQuarticAmplitude c.cuspLabel
        (c.horizontalization.cuspNormalized.upperLeft ^ 2 *
          c.orbitSpeed)) := by
  let h := c.horizontalization
  let h' := h.cuspNormalized
  let x := h'.upperLeft * h'.upperRight
  let y := h'.upperLeft ^ 2
  let s := h'.upperLeft ^ 2 * c.orbitSpeed
  have hy : 0 < y := by
    exact sq_pos_of_ne_zero h'.upperLeft_ne_zero
  have hs : s ≠ 0 := by
    exact c.horizontalSpeed_ne_zero
  have hline :
      ∀ u,
        h'.completion • T u =
          horizontalLine x y s hy u := by
    intro u
    simpa only [h, h', x, y, s, horizontalModulus] using
      c.horizontalModulus_eq u
  have hderiv :
      HasDerivAt
        (fun u : ℝ ↦ (T u : ℂ))
        (unaryComparisonV z
          (fun u ↦ canonicalUnaryTheta (T u)) t) t :=
    canonicalLambdaLift_hasDerivAt_comparisonV
      hz hB hlambda hTdiff t
  simpa only [h, h', x, y, s, horizontalModulus] using
    hasCuspQuarticAmplitude_of_horizontalized_comparison
      c.cuspLabel h'.completion
      h.reduce_cuspNormalized_completion
      z T hB hlambda x y s hy hs hline t hderiv

end ClosedUnaryHorocycleChart

end

end HGAS.Modular
