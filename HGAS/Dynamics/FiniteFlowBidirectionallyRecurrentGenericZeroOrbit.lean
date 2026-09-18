import HGAS.Dynamics.FiniteFlowTwoSidedGenericZeroOrbit
import Mathlib.Tactic

/-!
# A generic zero-locus point recurrent in both time directions

Forward recurrence is not, in general, inherited by the reversed orbit.
That distinction matters when a trajectory must later be rescaled by a
negative constant.  Fortunately, for an invariant probability measure,
Poincare recurrence applies independently to the original flow and to
its reversal.  Both recurrent sets have full measure, so they may be
intersected with the forward-generic, backward-generic, and zero-locus
sets used by the existing selector.

The result in this file deliberately records the two recurrence
certificates separately.  This makes sign-changing time
reparametrizations safe at later compiler stages.
-/

namespace HGAS.Dynamics

open Filter MeasureTheory Set Topology
open scoped BoundedContinuousFunction

noncomputable section

variable {X : Type*}
  [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {ϕ : Flow ℝ X}

variable [SecondCountableTopology X]

/-- A point which is recurrent for both the original and reversed
flows, generic for a finite family in both directions, and whose entire
orbit lies in a prescribed nonnegative zero-mean zero locus. -/
theorem IsErgodicInvariantProbability.exists_birecurrent_twoSidedGenericPoint_fin_zeroOrbit
    (μ : InvariantProbabilityMeasure ϕ)
    (hμ : IsErgodicInvariantProbability ϕ μ.measure)
    {m : ℕ} (f : Fin m → X →ᵇ ℝ)
    (g : X →ᵇ ℝ)
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_zero :
      (∫ x, g x ∂(μ.measure : Measure X)) = 0) :
    ∃ x : X,
      ForwardRecurrentAt (fun t : ℝ ↦ ϕ t x) 0 ∧
        ForwardRecurrentAt (fun t : ℝ ↦ ϕ.reverse t x) 0 ∧
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
  have hrecReverse :
      ∀ᵐ x ∂(μ.measure : Measure X),
        ForwardRecurrentAt (fun t : ℝ ↦ ϕ.reverse t x) 0 := by
    have hrecReverse' :
        ∀ᵐ x ∂(μrev.measure : Measure X),
          ForwardRecurrentAt (fun t : ℝ ↦ ϕ.reverse t x) 0 :=
      μrev.ae_forwardRecurrentAt_zero
    simpa only [μrev, InvariantProbabilityMeasure.reverse_measure] using
      hrecReverse'
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
  obtain
      ⟨x, hxrec, hxrecReverse, hxrat, hxavg, hxavgReverse⟩ :=
    (hrec.and
      (hrecReverse.and
        (hg_all_rational.and
          (havg_all.and havgReverse_all)))).exists
  refine
    ⟨x, hxrec, hxrecReverse, ?_, hxavg, hxavgReverse⟩
  have horbit :
      (fun t : ℝ ↦ g (ϕ t x)) = fun _ ↦ 0 := by
    exact
      Rat.isDenseEmbedding_coe_real.dense.equalizer
        (continuous_orbitObservable ϕ g x)
        continuous_const
        (funext hxrat)
  intro t
  exact congrFun horbit t

/-- Zero-mean specialization of the bidirectionally recurrent selector. -/
theorem IsErgodicInvariantProbability.exists_birecurrent_twoSidedZeroMeanPoint_fin_zeroOrbit
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
        ForwardRecurrentAt (fun t : ℝ ↦ ϕ.reverse t x) 0 ∧
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
  obtain
      ⟨x, hxrec, hxrecReverse, hxzero, hxavg, hxavgReverse⟩ :=
    hμ.exists_birecurrent_twoSidedGenericPoint_fin_zeroOrbit
      μ f g hg_nonneg hg_zero
  refine
    ⟨x, hxrec, hxrecReverse, hxzero, ?_, ?_⟩
  · intro i
    simpa only [hzero i] using hxavg i
  · intro i
    simpa only [hzero i] using hxavgReverse i

end

end HGAS.Dynamics
