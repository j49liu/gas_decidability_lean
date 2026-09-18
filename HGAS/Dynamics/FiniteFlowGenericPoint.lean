import HGAS.Dynamics.FlowPointwiseErgodic
import HGAS.Dynamics.PoincareRecurrence

/-!
# One recurrent generic point for finitely many flow observables

The all-state selector uses only finitely many real observables: one
nonnegative validity energy, the real and imaginary parts of seven complex
moments in each block, and the two real detector coordinates.  Applying a
pointwise ergodic theorem separately to those coordinates is not quite
enough: the later trajectory classification must use one and the same
initial point and one and the same orbit.

This file packages the elementary finite-intersection argument.  For an
ergodic invariant probability of a continuous real flow, there is one point
which

* is forward recurrent at time zero; and
* is generic, along every positive integral time horizon, for every member
  of an arbitrary finite family of bounded continuous real observables.

The result is deliberately independent of the modular/Jacobi construction.
It is useful whenever finitely many moment constraints must be imposed on
one recurrent trajectory.
-/

namespace HGAS.Dynamics

open Filter MeasureTheory Topology
open scoped BoundedContinuousFunction

noncomputable section

variable {X : Type*}
  [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]
  {ϕ : Flow ℝ X}

/-- One point is simultaneously recurrent and Birkhoff-generic for every
observable in a finite family.

The time averages are the continuous-time averages over `[0,n+1]` encoded
by `integerOrbitAverageObservable`; no observable-dependent subsequence is
introduced. -/
theorem IsErgodicInvariantProbability.exists_recurrent_genericPoint_fin
    (μ : InvariantProbabilityMeasure ϕ)
    (hμ : IsErgodicInvariantProbability ϕ μ.measure)
    {m : ℕ} (f : Fin m → X →ᵇ ℝ) :
    ∃ x : X,
      ForwardRecurrentAt (fun t : ℝ ↦ ϕ t x) 0 ∧
        ∀ i : Fin m,
          Tendsto
            (fun n : ℕ ↦
              integerOrbitAverageObservable
                ϕ (f i) (n + 1) x)
            atTop
            (𝓝 (∫ y, f i y
              ∂(μ.measure : Measure X))) := by
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
  have hall :
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
  obtain ⟨x, hxrec, hxavg⟩ := (hrec.and hall).exists
  exact ⟨x, hxrec, hxavg⟩

/-- Zero-mean specialization.  This is the form consumed by the drift
selector after assuming that the entire finite drift vector has zero
invariant average. -/
theorem IsErgodicInvariantProbability.exists_recurrent_zeroMeanPoint_fin
    (μ : InvariantProbabilityMeasure ϕ)
    (hμ : IsErgodicInvariantProbability ϕ μ.measure)
    {m : ℕ} (f : Fin m → X →ᵇ ℝ)
    (hzero :
      ∀ i : Fin m,
        (∫ y, f i y
          ∂(μ.measure : Measure X)) = 0) :
    ∃ x : X,
      ForwardRecurrentAt (fun t : ℝ ↦ ϕ t x) 0 ∧
        ∀ i : Fin m,
          Tendsto
            (fun n : ℕ ↦
              integerOrbitAverageObservable
                ϕ (f i) (n + 1) x)
            atTop (𝓝 0) := by
  obtain ⟨x, hxrec, hxavg⟩ :=
    hμ.exists_recurrent_genericPoint_fin μ f
  refine ⟨x, hxrec, ?_⟩
  intro i
  simpa only [hzero i] using hxavg i

end

end HGAS.Dynamics
