import HGAS.Compactification.StereographicDynamics
import HGAS.Dynamics.InvariantAffineChart
import HGAS.Dynamics.InvariantPositiveRestriction

/-!
# Nonzero mean drift excludes the finite compact-accumulator chart

This is the composed theorem used by the lower-bound reduction.  A compact
flow has an invariant measurable region on which its accumulator lies in
the finite stereographic chart.  If an invariant probability gives that
region full mass and the accumulator satisfies the compactified translation
equations, then every coordinate of the mean drift is zero.

Equivalently, any nonzero mean drift rules out a stationary lift supported
in the finite chart.  The proof is short because the reusable layers have
already isolated:

* restriction of a full-measure invariant probability to the chart;
* differentiation of the stereographic chart coordinate;
* the fundamental theorem of calculus; and
* the clipped-coboundary stationary-cocycle lemma.
-/

noncomputable section

open MeasureTheory Set
open scoped BoundedContinuousFunction

namespace HGAS

variable {X : Type*} [TopologicalSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- Whole-space form of the compact-accumulator obstruction. -/
theorem Dynamics.InvariantProbabilityMeasure.coordinateIntegral_eq_zero_compactAccumulator
    {ϕ : Flow ℝ X}
    (μ : Dynamics.InvariantProbabilityMeasure ϕ)
    {m : ℕ}
    (q : X → FiniteAccumulatorChart m)
    (hq : Continuous q)
    (g : X →ᵇ FinVector m ℝ)
    (hU :
      ∀ x i t,
        HasDerivAt
          (fun r ↦ (q (ϕ r x)).1.1.1 i)
          (accumulatorUField
            (q (ϕ t x)).1.1.1
            (q (ϕ t x)).1.1.2
            (g (ϕ t x)) i) t)
    (hW :
      ∀ x t,
        HasDerivAt
          (fun r ↦ (q (ϕ r x)).1.1.2)
          (accumulatorWField
            (q (ϕ t x)).1.1.1
            (q (ϕ t x)).1.1.2
            (g (ϕ t x))) t) :
    ∀ i : Fin m,
      (∫ x, g x i ∂(μ.measure : Measure X)) = 0 := by
  apply μ.coordinateIntegral_eq_zero_of_flowIntegral_increment
    (fun x ↦ accumulatorChartCoordinate (q x))
    (continuous_accumulatorChartCoordinate.comp hq)
    g
  exact flow_coordinateIncrement_eq_intervalIntegral
    ϕ
    (fun x ↦ accumulatorChartCoordinate (q x))
    g
    (fun x i t ↦
      accumulatorChartCoordinate_hasDerivAt
        (fun r ↦ q (ϕ r x))
        (fun r ↦ g (ϕ r x))
        t (fun j ↦ hU x j t) (hW x t) i)
    g.continuous

/-- Whole-space factor form: the pushed-forward base marginal of a compact
accumulator has zero mean drift. -/
theorem Dynamics.InvariantProbabilityMeasure.coordinateBaseIntegral_eq_zero_compactAccumulator
    {ϕ : Flow ℝ X}
    (μ : Dynamics.InvariantProbabilityMeasure ϕ)
    {B : Type*} [TopologicalSpace B]
    [MeasurableSpace B] [BorelSpace B]
    {ψ : Flow ℝ B}
    (π : X → B) (hπ : Continuous π)
    (hequiv : ∀ t : ℝ, Function.Semiconj π (ϕ t) (ψ t))
    {m : ℕ}
    (q : X → FiniteAccumulatorChart m)
    (hq : Continuous q)
    (gb : B →ᵇ FinVector m ℝ)
    (hU :
      ∀ x i t,
        HasDerivAt
          (fun r ↦ (q (ϕ r x)).1.1.1 i)
          (accumulatorUField
            (q (ϕ t x)).1.1.1
            (q (ϕ t x)).1.1.2
            (gb (π (ϕ t x))) i) t)
    (hW :
      ∀ x t,
        HasDerivAt
          (fun r ↦ (q (ϕ r x)).1.1.2)
          (accumulatorWField
            (q (ϕ t x)).1.1.1
            (q (ϕ t x)).1.1.2
            (gb (π (ϕ t x)))) t) :
    ∀ i : Fin m,
      (∫ b, gb b i
        ∂((μ.mapEquivariant π hπ hequiv).measure :
          Measure B)) = 0 := by
  let g : X →ᵇ FinVector m ℝ :=
    gb.compContinuous ⟨π, hπ⟩
  have hzero :
      ∀ i : Fin m,
        (∫ x, g x i ∂(μ.measure : Measure X)) = 0 := by
    apply μ.coordinateIntegral_eq_zero_compactAccumulator
      q hq g
    · simpa only [g,
        BoundedContinuousFunction.compContinuous_apply,
        ContinuousMap.coe_mk] using hU
    · simpa only [g,
        BoundedContinuousFunction.compContinuous_apply,
        ContinuousMap.coe_mk] using hW
  intro i
  rw [Dynamics.InvariantProbabilityMeasure.mapEquivariant_measure]
  change
    (∫ b, gb b i
      ∂Measure.map π (μ.measure : Measure X)) = 0
  rw [integral_map (f := fun b : B ↦ gb b i)
    hπ.measurable.aemeasurable
    ((continuous_apply i).comp gb.continuous).aestronglyMeasurable]
  simpa only [g,
    BoundedContinuousFunction.compContinuous_apply,
    ContinuousMap.coe_mk] using hzero i

/-- **Compact accumulator finite-chart obstruction.** -/
theorem Dynamics.InvariantProbabilityMeasure.coordinateIntegral_eq_zero_of_compactAccumulator
    {ϕ : Flow ℝ X}
    (μ : Dynamics.InvariantProbabilityMeasure ϕ)
    {s : Set X} (hs : MeasurableSet s)
    (hfull : (μ.measure : Measure X) s = 1)
    (hinv : IsInvariant ϕ s)
    {m : ℕ}
    (q : s → FiniteAccumulatorChart m)
    (hq : Continuous q)
    (g : s →ᵇ FinVector m ℝ)
    (hU :
      ∀ x i t,
        HasDerivAt
          (fun r ↦
            (q ((ϕ.restrict hinv) r x)).1.1.1 i)
          (accumulatorUField
            (q ((ϕ.restrict hinv) t x)).1.1.1
            (q ((ϕ.restrict hinv) t x)).1.1.2
            (g ((ϕ.restrict hinv) t x)) i) t)
    (hW :
      ∀ x t,
        HasDerivAt
          (fun r ↦
            (q ((ϕ.restrict hinv) r x)).1.1.2)
          (accumulatorWField
            (q ((ϕ.restrict hinv) t x)).1.1.1
            (q ((ϕ.restrict hinv) t x)).1.1.2
            (g ((ϕ.restrict hinv) t x))) t) :
    ∀ i : Fin m,
      (∫ x, g x i
        ∂((μ.restrictToFullMeasureInvariant hs hfull hinv).measure :
          Measure s)) = 0 := by
  apply
    μ.coordinateIntegral_eq_zero_on_fullMeasureAffineChart_of_hasDerivAt
      hs hfull hinv
      (fun x ↦ accumulatorChartCoordinate (q x))
      (continuous_accumulatorChartCoordinate.comp hq)
      g
  intro x i t
  exact accumulatorChartCoordinate_hasDerivAt
    (fun r ↦ q ((ϕ.restrict hinv) r x))
    (fun r ↦ g ((ϕ.restrict hinv) r x))
    t (fun j ↦ hU x j t) (hW x t) i

/-- Factor form of the compact-accumulator obstruction.

If the drift is pulled back from an equivariant base factor, then the mean
drift of the pushed-forward base probability is zero.  This is the exact
interface used after fixing an ergodic base marginal. -/
theorem Dynamics.InvariantProbabilityMeasure.coordinateBaseIntegral_eq_zero_of_compactAccumulator
    {ϕ : Flow ℝ X}
    (μ : Dynamics.InvariantProbabilityMeasure ϕ)
    {s : Set X} (hs : MeasurableSet s)
    (hfull : (μ.measure : Measure X) s = 1)
    (hinv : IsInvariant ϕ s)
    {B : Type*} [TopologicalSpace B]
    [MeasurableSpace B] [BorelSpace B]
    {ψ : Flow ℝ B}
    (π : s → B) (hπ : Continuous π)
    (hequiv :
      ∀ t : ℝ,
        Function.Semiconj π ((ϕ.restrict hinv) t) (ψ t))
    {m : ℕ}
    (q : s → FiniteAccumulatorChart m)
    (hq : Continuous q)
    (gb : B →ᵇ FinVector m ℝ)
    (hU :
      ∀ x i t,
        HasDerivAt
          (fun r ↦
            (q ((ϕ.restrict hinv) r x)).1.1.1 i)
          (accumulatorUField
            (q ((ϕ.restrict hinv) t x)).1.1.1
            (q ((ϕ.restrict hinv) t x)).1.1.2
            (gb (π ((ϕ.restrict hinv) t x))) i) t)
    (hW :
      ∀ x t,
        HasDerivAt
          (fun r ↦
            (q ((ϕ.restrict hinv) r x)).1.1.2)
          (accumulatorWField
            (q ((ϕ.restrict hinv) t x)).1.1.1
            (q ((ϕ.restrict hinv) t x)).1.1.2
            (gb (π ((ϕ.restrict hinv) t x)))) t) :
    let ν := μ.restrictToFullMeasureInvariant hs hfull hinv
    let η := ν.mapEquivariant π hπ hequiv
    ∀ i : Fin m,
      (∫ b, gb b i ∂(η.measure : Measure B)) = 0 := by
  dsimp only
  let ν := μ.restrictToFullMeasureInvariant hs hfull hinv
  let g : s →ᵇ FinVector m ℝ :=
    gb.compContinuous ⟨π, hπ⟩
  have hzero :
      ∀ i : Fin m,
        (∫ x, g x i ∂(ν.measure : Measure s)) = 0 := by
    apply μ.coordinateIntegral_eq_zero_of_compactAccumulator
      hs hfull hinv q hq g
    · simpa only [g,
        BoundedContinuousFunction.compContinuous_apply,
        ContinuousMap.coe_mk] using hU
    · simpa only [g,
        BoundedContinuousFunction.compContinuous_apply,
        ContinuousMap.coe_mk] using hW
  intro i
  rw [Dynamics.InvariantProbabilityMeasure.mapEquivariant_measure]
  change
    (∫ b, gb b i
      ∂Measure.map π (ν.measure : Measure s)) = 0
  rw [integral_map (f := fun b : B ↦ gb b i)
    hπ.measurable.aemeasurable
    ((continuous_apply i).comp gb.continuous).aestronglyMeasurable]
  simpa only [g,
    BoundedContinuousFunction.compContinuous_apply,
    ContinuousMap.coe_mk] using hzero i

/-- If every positive finite-chart conditional has a nonzero base drift,
then the original invariant probability assigns the finite chart zero
mass.  In applications, ergodicity of the prescribed base marginal supplies
the conditional-marginal hypothesis. -/
theorem Dynamics.InvariantProbabilityMeasure.finiteChart_measure_eq_zero
    {ϕ : Flow ℝ X}
    (μ : Dynamics.InvariantProbabilityMeasure ϕ)
    {s : Set X} (hs : MeasurableSet s)
    (hinv : IsInvariant ϕ s)
    {B : Type*} [TopologicalSpace B]
    [MeasurableSpace B] [BorelSpace B]
    {ψ : Flow ℝ B}
    (π : s → B) (hπ : Continuous π)
    (hequiv :
      ∀ t : ℝ,
        Function.Semiconj π ((ϕ.restrict hinv) t) (ψ t))
    {m : ℕ}
    (q : s → FiniteAccumulatorChart m)
    (hq : Continuous q)
    (gb : B →ᵇ FinVector m ℝ)
    (hU :
      ∀ x i t,
        HasDerivAt
          (fun r ↦
            (q ((ϕ.restrict hinv) r x)).1.1.1 i)
          (accumulatorUField
            (q ((ϕ.restrict hinv) t x)).1.1.1
            (q ((ϕ.restrict hinv) t x)).1.1.2
            (gb (π ((ϕ.restrict hinv) t x))) i) t)
    (hW :
      ∀ x t,
        HasDerivAt
          (fun r ↦
            (q ((ϕ.restrict hinv) r x)).1.1.2)
          (accumulatorWField
            (q ((ϕ.restrict hinv) t x)).1.1.1
            (q ((ϕ.restrict hinv) t x)).1.1.2
            (gb (π ((ϕ.restrict hinv) t x)))) t)
    (hnonzero :
      ∀ hpos : (μ.measure : Measure X) s ≠ 0,
        let ν := μ.restrictToPositiveInvariant hs hpos hinv
        ∃ i : Fin m,
          (∫ b, gb b i
            ∂((ν.mapEquivariant π hπ hequiv).measure :
              Measure B)) ≠ 0) :
    (μ.measure : Measure X) s = 0 := by
  by_contra hpos
  let ν := μ.restrictToPositiveInvariant hs hpos hinv
  obtain ⟨i, hi⟩ := hnonzero hpos
  apply hi
  exact ν.coordinateBaseIntegral_eq_zero_compactAccumulator
    π hπ hequiv q hq gb hU hW i

end HGAS

end
