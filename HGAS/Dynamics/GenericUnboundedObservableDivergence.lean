import HGAS.Modular.GammaTwoOrbitEquidistributionReduction
import Mathlib.Tactic

/-!
# Divergence of unbounded observables along generic orbits

Genericity is usually stated for compactly supported continuous test
functions.  Cusp exclusion, however, needs an unbounded nonnegative
observable such as a reciprocal projective speed.

This file isolates the elementary bridge.  Let `R ≥ 0` be continuous.  If
for every real threshold `B` there is a compactly supported continuous
minorant `f ≤ R` whose mean exceeds `B`, then every point generic for the
underlying probability has time average of `R` tending to `+∞`.

The statement deliberately packages the measure-theoretic exhaustion by
compactly supported minorants as a separate hypothesis.  Constructing
those minorants from a concrete modular cusp chart is independent of the
orbit argument and can therefore be audited separately.
-/

namespace HGAS.Dynamics

open Filter Function _root_.MeasureTheory Set Topology
open scoped BoundedContinuousFunction CompactlySupported Interval

noncomputable section

variable {X : Type*}
  [TopologicalSpace X] [MeasurableSpace X]

/-- The positive integer-horizon average of an arbitrary continuous real
observable.  Unlike `HGAS.Modular.forwardOrbitAverage`, the observable is
not required to be bounded. -/
def forwardContinuousOrbitAverage
    (ϕ : Flow ℝ X) (R : C(X, ℝ))
    (n : ℕ) (x : X) : ℝ :=
  (n + 1 : ℝ)⁻¹ *
    ∫ t in (0 : ℝ)..(n + 1 : ℝ), R (ϕ t x)

omit [MeasurableSpace X] in
/-- A compactly supported pointwise minorant gives a lower bound for every
positive integer-horizon average. -/
theorem forwardOrbitAverage_le_forwardContinuousOrbitAverage
    (ϕ : Flow ℝ X) (R : C(X, ℝ))
    (f : C_c(X, ℝ))
    (hf : ∀ x, f x ≤ R x)
    (n : ℕ) (x : X) :
    HGAS.Modular.forwardOrbitAverage ϕ f n x ≤
      forwardContinuousOrbitAverage ϕ R n x := by
  have htime : (0 : ℝ) ≤ (n + 1 : ℝ) := by positivity
  have hfcont :
      Continuous
        (fun t : ℝ ↦
          f.toBoundedContinuousFunction (ϕ t x)) :=
    f.toBoundedContinuousFunction.continuous.comp
      (ϕ.continuous continuous_id continuous_const)
  have hRcont :
      Continuous (fun t : ℝ ↦ R (ϕ t x)) :=
    R.continuous.comp
      (ϕ.continuous continuous_id continuous_const)
  have hintegral :
      HGAS.Dynamics.orbitIntegral ϕ
          f.toBoundedContinuousFunction (n + 1 : ℝ) x ≤
        ∫ t in (0 : ℝ)..(n + 1 : ℝ), R (ϕ t x) := by
    unfold HGAS.Dynamics.orbitIntegral
    exact
      intervalIntegral.integral_mono_on htime
        (hfcont.intervalIntegrable _ _)
        (hRcont.intervalIntegrable _ _)
        (fun t _ ↦ hf (ϕ t x))
  unfold HGAS.Modular.forwardOrbitAverage
    forwardContinuousOrbitAverage
  exact
    mul_le_mul_of_nonneg_left hintegral (by positivity)

/-- **Generic-orbit divergence criterion.**

If compactly supported continuous minorants of `R` have arbitrarily large
means, then the integer-horizon time averages of `R` tend to `+∞` along
every point generic for the probability. -/
theorem forwardContinuousOrbitAverage_tendsto_atTop_of_generic
    (ϕ : Flow ℝ X)
    (μ : ProbabilityMeasure X)
    (R : C(X, ℝ))
    (hminorants :
      ∀ B : ℝ, ∃ f : C_c(X, ℝ),
        (∀ x, 0 ≤ f x) ∧
        (∀ x, f x ≤ R x) ∧
        B < ∫ x, f x ∂(μ : Measure X))
    {x : X}
    (hx : HGAS.Modular.IsForwardGenericFor ϕ μ x) :
    Tendsto
      (fun n ↦ forwardContinuousOrbitAverage ϕ R n x)
      atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro B
  obtain ⟨f, _hfnonneg, hfR, hB⟩ :=
    hminorants B
  have hgeneric := hx f
  have hevent :
      ∀ᶠ n in atTop,
        B <
          HGAS.Modular.forwardOrbitAverage ϕ f n x :=
    (tendsto_order.1 hgeneric).1
      _ hB
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  refine ⟨N, ?_⟩
  intro n hn
  exact
    (hN n hn).le.trans
      (forwardOrbitAverage_le_forwardContinuousOrbitAverage
        ϕ R f hfR n x)

end

end HGAS.Dynamics
