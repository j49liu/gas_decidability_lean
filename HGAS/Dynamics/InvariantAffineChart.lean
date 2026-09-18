import HGAS.Dynamics.FlowDerivativeCocycle
import HGAS.Dynamics.InvariantFullMeasureRestriction

/-!
# The invariant affine-chart drift obstruction

This module composes two reusable facts:

1. an invariant probability giving full mass to an invariant measurable
   chart pulls back to an invariant probability on that chart; and
2. a stationary finite affine cocycle has zero mean drift.

It is the abstract core of the compact-accumulator argument.  The geometric
compactification module only needs to exhibit its finite chart, its affine
coordinate, and the time-integrated increment identity.
-/

noncomputable section

open MeasureTheory Set
open scoped BoundedContinuousFunction Interval

namespace HGAS.Dynamics

variable {X : Type*} [TopologicalSpace X]
  [MeasurableSpace X] [BorelSpace X]

namespace InvariantProbabilityMeasure

variable {ϕ : Flow ℝ X}

/-- A full-measure invariant affine chart has zero mean in every coordinate
of its bounded continuous drift.  The affine coordinate itself may be
unbounded. -/
theorem coordinateIntegral_eq_zero_on_fullMeasureAffineChart
    (μ : InvariantProbabilityMeasure ϕ)
    {s : Set X} (hs : MeasurableSet s)
    (hfull : (μ.measure : Measure X) s = 1)
    (hinv : IsInvariant ϕ s)
    {m : ℕ}
    (z : s → (Fin m → ℝ)) (hz : Continuous z)
    (g : s →ᵇ (Fin m → ℝ))
    (hincrement :
      ∀ x i,
        z ((ϕ.restrict hinv) 1 x) i - z x i =
          ∫ t in (0 : ℝ)..1,
            g ((ϕ.restrict hinv) t x) i) :
    ∀ i : Fin m,
      (∫ x, g x i
        ∂((μ.restrictToFullMeasureInvariant hs hfull hinv).measure :
          Measure s)) = 0 := by
  let ν := μ.restrictToFullMeasureInvariant hs hfull hinv
  exact ν.coordinateIntegral_eq_zero_of_flowIntegral_increment
    z hz g hincrement

/-- Scalar specialization of
`coordinateIntegral_eq_zero_on_fullMeasureAffineChart`. -/
theorem integral_eq_zero_on_fullMeasureAffineChart
    (μ : InvariantProbabilityMeasure ϕ)
    {s : Set X} (hs : MeasurableSet s)
    (hfull : (μ.measure : Measure X) s = 1)
    (hinv : IsInvariant ϕ s)
    (z : s → ℝ) (hz : Continuous z)
    (g : s →ᵇ ℝ)
    (hincrement :
      ∀ x,
        z ((ϕ.restrict hinv) 1 x) - z x =
          ∫ t in (0 : ℝ)..1,
            g ((ϕ.restrict hinv) t x)) :
    (∫ x, g x
      ∂((μ.restrictToFullMeasureInvariant hs hfull hinv).measure :
        Measure s)) = 0 := by
  let ν := μ.restrictToFullMeasureInvariant hs hfull hinv
  exact ν.integral_eq_zero_of_flowIntegral_increment
    z hz g hincrement

/-- ODE-facing form of the finite-dimensional affine-chart obstruction.
It derives the time-one cocycle identity from the coordinate derivatives
by the fundamental theorem of calculus. -/
theorem coordinateIntegral_eq_zero_on_fullMeasureAffineChart_of_hasDerivAt
    (μ : InvariantProbabilityMeasure ϕ)
    {s : Set X} (hs : MeasurableSet s)
    (hfull : (μ.measure : Measure X) s = 1)
    (hinv : IsInvariant ϕ s)
    {m : ℕ}
    (z : s → (Fin m → ℝ)) (hz : Continuous z)
    (g : s →ᵇ (Fin m → ℝ))
    (hderiv :
      ∀ x i t,
        HasDerivAt
          (fun r ↦ z ((ϕ.restrict hinv) r x) i)
          (g ((ϕ.restrict hinv) t x) i) t) :
    ∀ i : Fin m,
      (∫ x, g x i
        ∂((μ.restrictToFullMeasureInvariant hs hfull hinv).measure :
          Measure s)) = 0 := by
  apply μ.coordinateIntegral_eq_zero_on_fullMeasureAffineChart
    hs hfull hinv z hz g
  exact flow_coordinateIncrement_eq_intervalIntegral
    (ϕ.restrict hinv) z g hderiv g.continuous

end InvariantProbabilityMeasure

end HGAS.Dynamics

end
