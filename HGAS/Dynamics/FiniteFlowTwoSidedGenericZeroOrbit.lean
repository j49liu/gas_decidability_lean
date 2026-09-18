import HGAS.Dynamics.FiniteFlowGenericZeroOrbit
import Mathlib.Tactic

/-!
# A two-sided generic point on an invariant zero locus

For a two-sided flow, invariance and ergodicity are unchanged when time is
reversed.  Hence the full-measure sets supplied by the pointwise ergodic
theorem for the forward and reversed flows may be intersected.

This module packages that elementary observation together with the
rational-time argument of `FiniteFlowGenericZeroOrbit`.  The selected
point is:

* forward recurrent;
* forward generic for a prescribed finite family;
* backward generic for the same family; and
* carried for all real times by the zero locus of a nonnegative
  zero-mean observable.

The backward speed average is the extra fact needed to invert an
unmodified state clock on the whole real line.
-/

namespace HGAS.Dynamics

open Filter MeasureTheory Set Topology
open scoped BoundedContinuousFunction

noncomputable section

variable {X : Type*}
  [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {ϕ : Flow ℝ X}

/-- An invariant probability for a flow is invariant for the reversed
flow, with the same underlying probability measure. -/
def InvariantProbabilityMeasure.reverse
    (μ : InvariantProbabilityMeasure ϕ) :
    InvariantProbabilityMeasure ϕ.reverse where
  measure := μ.measure
  invariant := by
    intro t
    simpa only [Flow.reverse] using μ.invariant (-t)

@[simp]
theorem InvariantProbabilityMeasure.reverse_measure
    (μ : InvariantProbabilityMeasure ϕ) :
    μ.reverse.measure = μ.measure :=
  rfl

/-- Ergodicity is unchanged by reversing a real flow. -/
theorem IsErgodicInvariantProbability.reverse
    {μ : ProbabilityMeasure X}
    (hμ : IsErgodicInvariantProbability ϕ μ) :
    IsErgodicInvariantProbability ϕ.reverse μ := by
  refine ⟨?_, ?_⟩
  · intro t
    simpa only [Flow.reverse] using hμ.invariant (-t)
  · intro A hA hinv
    apply hμ.zero_or_one hA
    intro t
    simpa only [Flow.reverse, neg_neg] using hinv (-t)

variable [SecondCountableTopology X]

/-- One recurrent point is simultaneously generic for a finite family in
both time directions and lies on the complete orbit of a nonnegative
zero-mean observable's zero set. -/
theorem
    IsErgodicInvariantProbability.exists_recurrent_twoSidedGenericPoint_fin_zeroOrbit
    (μ : InvariantProbabilityMeasure ϕ)
    (hμ : IsErgodicInvariantProbability ϕ μ.measure)
    {m : ℕ} (f : Fin m → X →ᵇ ℝ)
    (g : X →ᵇ ℝ)
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_zero :
      (∫ x, g x ∂(μ.measure : Measure X)) = 0) :
    ∃ x : X,
      ForwardRecurrentAt (fun t : ℝ ↦ ϕ t x) 0 ∧
        (∀ t : ℝ, g (ϕ t x) = 0) ∧
        (∀ i : Fin m,
          Tendsto
            (fun n : ℕ ↦
              integerOrbitAverageObservable
                ϕ (f i) (n + 1) x)
            atTop
            (𝓝 (∫ y, f i y
              ∂(μ.measure : Measure X)))) ∧
        ∀ i : Fin m,
          Tendsto
            (fun n : ℕ ↦
              integerOrbitAverageObservable
                ϕ.reverse (f i) (n + 1) x)
            atTop
            (𝓝 (∫ y, f i y
              ∂(μ.measure : Measure X))) := by
  have hg_integrable :
      Integrable g (μ.measure : Measure X) :=
    μ.integrable_boundedContinuous g
  have hg_ae :
      g =ᵐ[(μ.measure : Measure X)] 0 :=
    (integral_eq_zero_iff_of_nonneg
      hg_nonneg hg_integrable).mp hg_zero
  have hg_rational :
      ∀ q : ℚ,
        ∀ᵐ x ∂(μ.measure : Measure X),
          g (ϕ (q : ℝ) x) = 0 := by
    intro q
    have hpre :=
      (μ.measurePreservingTime (q : ℝ)).quasiMeasurePreserving.ae hg_ae
    simpa only [Function.comp_apply, Pi.zero_apply] using hpre
  have hg_all_rational :
      ∀ᵐ x ∂(μ.measure : Measure X),
        ∀ q : ℚ, g (ϕ (q : ℝ) x) = 0 :=
    ae_all_iff.mpr hg_rational
  have hrec :
      ∀ᵐ x ∂(μ.measure : Measure X),
        ForwardRecurrentAt (fun t : ℝ ↦ ϕ t x) 0 :=
    μ.ae_forwardRecurrentAt_zero
  have havg :
      ∀ i : Fin m,
        ∀ᵐ x ∂(μ.measure : Measure X),
          Tendsto
            (fun n : ℕ ↦
              integerOrbitAverageObservable
                ϕ (f i) (n + 1) x)
            atTop
            (𝓝 (∫ y, f i y
              ∂(μ.measure : Measure X))) :=
    fun i ↦ hμ.ae_tendsto_integerOrbitAverage μ (f i)
  have havg_all :
      ∀ᵐ x ∂(μ.measure : Measure X),
        ∀ i : Fin m,
          Tendsto
            (fun n : ℕ ↦
              integerOrbitAverageObservable
                ϕ (f i) (n + 1) x)
            atTop
            (𝓝 (∫ y, f i y
              ∂(μ.measure : Measure X))) :=
    ae_all_iff.mpr havg
  let μrev : InvariantProbabilityMeasure ϕ.reverse := μ.reverse
  have hμrev :
      IsErgodicInvariantProbability ϕ.reverse μrev.measure := by
    simpa only [μrev, InvariantProbabilityMeasure.reverse_measure] using
      hμ.reverse
  have havgReverse :
      ∀ i : Fin m,
        ∀ᵐ x ∂(μ.measure : Measure X),
          Tendsto
            (fun n : ℕ ↦
              integerOrbitAverageObservable
                ϕ.reverse (f i) (n + 1) x)
            atTop
            (𝓝 (∫ y, f i y
              ∂(μ.measure : Measure X))) := by
    intro i
    have hi :=
      hμrev.ae_tendsto_integerOrbitAverage μrev (f i)
    simpa only [μrev, InvariantProbabilityMeasure.reverse_measure] using hi
  have havgReverse_all :
      ∀ᵐ x ∂(μ.measure : Measure X),
        ∀ i : Fin m,
          Tendsto
            (fun n : ℕ ↦
              integerOrbitAverageObservable
                ϕ.reverse (f i) (n + 1) x)
            atTop
            (𝓝 (∫ y, f i y
              ∂(μ.measure : Measure X))) :=
    ae_all_iff.mpr havgReverse
  obtain ⟨x, hxrec, hxrat, hxavg, hxavgReverse⟩ :=
    (hrec.and
      (hg_all_rational.and
        (havg_all.and havgReverse_all))).exists
  refine ⟨x, hxrec, ?_, hxavg, hxavgReverse⟩
  have horbit :
      (fun t : ℝ ↦ g (ϕ t x)) = fun _ ↦ 0 := by
    exact
      Rat.isDenseEmbedding_coe_real.dense.equalizer
        (continuous_orbitObservable ϕ g x)
        continuous_const
        (funext hxrat)
  intro t
  exact congrFun horbit t

/-- Zero-mean specialization for the finite family in both directions. -/
theorem
    IsErgodicInvariantProbability.exists_recurrent_twoSidedZeroMeanPoint_fin_zeroOrbit
    (μ : InvariantProbabilityMeasure ϕ)
    (hμ : IsErgodicInvariantProbability ϕ μ.measure)
    {m : ℕ} (f : Fin m → X →ᵇ ℝ)
    (hzero :
      ∀ i : Fin m,
        (∫ y, f i y
          ∂(μ.measure : Measure X)) = 0)
    (g : X →ᵇ ℝ)
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_zero :
      (∫ x, g x ∂(μ.measure : Measure X)) = 0) :
    ∃ x : X,
      ForwardRecurrentAt (fun t : ℝ ↦ ϕ t x) 0 ∧
        (∀ t : ℝ, g (ϕ t x) = 0) ∧
        (∀ i : Fin m,
          Tendsto
            (fun n : ℕ ↦
              integerOrbitAverageObservable
                ϕ (f i) (n + 1) x)
            atTop (𝓝 0)) ∧
        ∀ i : Fin m,
          Tendsto
            (fun n : ℕ ↦
              integerOrbitAverageObservable
                ϕ.reverse (f i) (n + 1) x)
            atTop (𝓝 0) := by
  obtain ⟨x, hxrec, hxzero, hxavg, hxavgReverse⟩ :=
    hμ.exists_recurrent_twoSidedGenericPoint_fin_zeroOrbit
      μ f g hg_nonneg hg_zero
  refine ⟨x, hxrec, hxzero, ?_, ?_⟩
  · intro i
    simpa only [hzero i] using hxavg i
  · intro i
    simpa only [hzero i] using hxavgReverse i

end

end HGAS.Dynamics
