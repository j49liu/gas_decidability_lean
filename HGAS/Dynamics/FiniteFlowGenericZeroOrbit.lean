import HGAS.Dynamics.FiniteFlowGenericPoint
import Mathlib.Tactic

/-!
# A recurrent generic point lying on an invariant zero locus

For a nonnegative continuous observable, zero invariant mean implies
vanishing almost everywhere.  Invariance then implies vanishing after
every rational time-map.  Intersecting these countably many full-measure
sets and using continuity in time gives one orbit on which the observable
vanishes at every real time.

This is the precise bridge needed by residual-energy arguments: a zero
mean of a sum of squares must put the selected trajectory on the residual
variety pointwise, rather than merely make its Cesàro average zero.
-/

namespace HGAS.Dynamics

open Filter MeasureTheory Topology
open scoped BoundedContinuousFunction

noncomputable section

variable {X : Type*}
  [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]
  {ϕ : Flow ℝ X}

/-- One point is recurrent and generic for a finite family, while an
additional nonnegative zero-mean observable vanishes along its entire
real orbit. -/
theorem IsErgodicInvariantProbability.exists_recurrent_genericPoint_fin_zeroOrbit
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
        ∀ i : Fin m,
          Tendsto
            (fun n : ℕ ↦
              integerOrbitAverageObservable
                ϕ (f i) (n + 1) x)
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
  obtain ⟨x, hxrec, hxrat, hxavg⟩ :=
    (hrec.and (hg_all_rational.and havg_all)).exists
  refine ⟨x, hxrec, ?_, hxavg⟩
  have horbit :
      (fun t : ℝ ↦ g (ϕ t x)) = fun _ ↦ 0 := by
    exact
      Rat.isDenseEmbedding_coe_real.dense.equalizer
        (continuous_orbitObservable ϕ g x)
        continuous_const
        (funext hxrat)
  intro t
  exact congrFun horbit t

/-- Zero-mean specialization for the finite generic family. -/
theorem IsErgodicInvariantProbability.exists_recurrent_zeroMeanPoint_fin_zeroOrbit
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
        ∀ i : Fin m,
          Tendsto
            (fun n : ℕ ↦
              integerOrbitAverageObservable
                ϕ (f i) (n + 1) x)
            atTop (𝓝 0) := by
  obtain ⟨x, hxrec, hxzero, hxavg⟩ :=
    hμ.exists_recurrent_genericPoint_fin_zeroOrbit
      μ f g hg_nonneg hg_zero
  refine ⟨x, hxrec, hxzero, ?_⟩
  intro i
  simpa only [hzero i] using hxavg i

end

end HGAS.Dynamics
