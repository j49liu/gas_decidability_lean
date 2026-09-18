import HGAS.Dynamics.FlowPointwiseErgodic
import HGAS.Modular.GammaTwoCcToC0Equidistribution

/-!
# The abstract horocycle generic-point alternative

The pointwise ergodic theorem supplies almost-everywhere convergence for
each bounded continuous observable.  On a second-countable locally
compact space, a countable dense family in `C₀` lets us choose one point
where all canonical tests converge; the contraction estimate for orbit
averages extends convergence to every compactly supported continuous
test.

Applied to the level-two horocycle flow, this produces a generic point
for every ergodic invariant probability.  If that point is periodic,
the elementary periodic-orbit averaging theorem identifies the measure
with normalized arclength on the closed horocycle.  Otherwise the point
is the nonperiodic generic witness.  Thus
`GammaTwoErgodicGenericPointAlternative` is proved without an external
ergodic-theory axiom.
-/

namespace HGAS.Modular

open Filter Function _root_.MeasureTheory Set Topology
open scoped BoundedContinuousFunction CompactlySupported ZeroAtInfty

noncomputable section

variable {X : Type*}
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [T2Space X] [SecondCountableTopology X]
  [LocallyCompactSpace X]
  [TopologicalSpace.PseudoMetrizableSpace X]

omit [TopologicalSpace.PseudoMetrizableSpace X] in
/-- Every ergodic invariant probability of a continuous real flow has a
forward-generic point for every compactly supported continuous
observable. -/
theorem exists_isForwardGenericFor
    (ϕ : Flow ℝ X)
    (μ : HGAS.Dynamics.InvariantProbabilityMeasure ϕ)
    (hμ :
      HGAS.Dynamics.IsErgodicInvariantProbability ϕ μ.measure) :
    ∃ x : X, IsForwardGenericFor ϕ μ.measure x := by
  have htests :
      ∀ j : ℕ,
        ∀ᵐ x ∂(μ.measure : Measure X),
          Tendsto
            (fun n : ℕ ↦
              HGAS.Dynamics.integerOrbitAverageObservable
                ϕ (HGAS.Dynamics.c0DenseTest (X := X) j).toBCF
                (n + 1) x)
            atTop
            (𝓝 (∫ y,
              HGAS.Dynamics.c0DenseTest (X := X) j y
                ∂(μ.measure : Measure X))) :=
    fun j ↦ hμ.ae_tendsto_integerOrbitAverage μ
      (HGAS.Dynamics.c0DenseTest (X := X) j).toBCF
  have hall :
      ∀ᵐ x ∂(μ.measure : Measure X), ∀ j : ℕ,
        Tendsto
          (fun n : ℕ ↦
            HGAS.Dynamics.integerOrbitAverageObservable
              ϕ (HGAS.Dynamics.c0DenseTest (X := X) j).toBCF
              (n + 1) x)
          atTop
          (𝓝 (∫ y,
            HGAS.Dynamics.c0DenseTest (X := X) j y
              ∂(μ.measure : Measure X))) :=
    ae_all_iff.mpr htests
  obtain ⟨x, hx⟩ := hall.exists
  refine ⟨x, ?_⟩
  intro f
  let f₀ : C₀(X, ℝ) :=
    HGAS.Dynamics.compactlySupportedToC0 f
  have hforward (n : ℕ) :
      forwardOrbitAverage ϕ f n x =
        HGAS.Dynamics.integerOrbitAverageObservable
          ϕ f₀.toBCF (n + 1) x := by
    rw [forwardOrbitAverage,
      HGAS.Dynamics.integerOrbitAverageObservable_apply]
    simp only [Nat.cast_add, Nat.cast_one]
    rfl
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨j, hj⟩ :=
    (Metric.denseRange_iff.mp
      (HGAS.Dynamics.denseRange_c0DenseTest (X := X)))
      f₀ (ε / 3) (by positivity)
  have hj' :
      dist (HGAS.Dynamics.c0DenseTest (X := X) j) f₀ < ε / 3 := by
    simpa only [dist_comm] using hj
  obtain ⟨N, hN⟩ :=
    (Metric.tendsto_atTop.mp (hx j)) (ε / 3) (by positivity)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [hforward]
  change
    dist
      (HGAS.Dynamics.integerOrbitAverageObservable
        ϕ f₀.toBCF (n + 1) x)
      (∫ y, f₀ y ∂(μ.measure : Measure X)) < ε
  let g : C₀(X, ℝ) := HGAS.Dynamics.c0DenseTest (X := X) j
  have hA :
      dist
        (HGAS.Dynamics.integerOrbitAverageObservable
          ϕ f₀.toBCF (n + 1) x)
        (HGAS.Dynamics.integerOrbitAverageObservable
          ϕ g.toBCF (n + 1) x) < ε / 3 :=
    (HGAS.Dynamics.dist_integerOrbitAverageObservable_apply_le
      ϕ f₀.toBCF g.toBCF (Nat.succ_pos n) x).trans_lt <| by
        simpa only [ZeroAtInftyContinuousMap.dist_toBCF_eq_dist,
          dist_comm] using hj'
  have hB :
      dist
        (HGAS.Dynamics.integerOrbitAverageObservable
          ϕ g.toBCF (n + 1) x)
        (∫ y, g y ∂(μ.measure : Measure X)) < ε / 3 := by
    exact hN n hn
  have hC :
      dist
        (∫ y, g y ∂(μ.measure : Measure X))
        (∫ y, f₀ y ∂(μ.measure : Measure X)) < ε / 3 :=
    (HGAS.Dynamics.dist_integral_c0_le μ.measure g f₀).trans_lt hj'
  calc
    dist
        (HGAS.Dynamics.integerOrbitAverageObservable
          ϕ f₀.toBCF (n + 1) x)
        (∫ y, f₀ y ∂(μ.measure : Measure X)) ≤
      dist
          (HGAS.Dynamics.integerOrbitAverageObservable
            ϕ f₀.toBCF (n + 1) x)
          (HGAS.Dynamics.integerOrbitAverageObservable
            ϕ g.toBCF (n + 1) x) +
        dist
          (HGAS.Dynamics.integerOrbitAverageObservable
            ϕ g.toBCF (n + 1) x)
          (∫ y, f₀ y ∂(μ.measure : Measure X)) :=
      dist_triangle _ _ _
    _ ≤
      dist
          (HGAS.Dynamics.integerOrbitAverageObservable
            ϕ f₀.toBCF (n + 1) x)
          (HGAS.Dynamics.integerOrbitAverageObservable
            ϕ g.toBCF (n + 1) x) +
        (dist
            (HGAS.Dynamics.integerOrbitAverageObservable
              ϕ g.toBCF (n + 1) x)
            (∫ y, g y ∂(μ.measure : Measure X)) +
          dist
            (∫ y, g y ∂(μ.measure : Measure X))
            (∫ y, f₀ y ∂(μ.measure : Measure X))) := by
      gcongr
      exact dist_triangle _ _ _
    _ < ε / 3 + (ε / 3 + ε / 3) :=
      add_lt_add hA (add_lt_add hB hC)
    _ = ε := by ring

/-- A periodic horocycle point is forward generic for its normalized
closed-orbit probability. -/
theorem isForwardGenericFor_closedHorocycleInvariantProbability
    (q : GammaTwoFrameQuotient) {T : ℝ} (hT : 0 < T)
    (hperiod :
      scaledGammaTwoHorocycleFlow 1 T q = q) :
    IsForwardGenericFor gammaTwoHorocycleFlow
      (closedHorocycleInvariantProbability
        1 q hT hperiod).measure q := by
  intro f
  have h :=
    HGAS.Dynamics.tendsto_integerOrbitAverage_of_periodic
      (scaledGammaTwoHorocycleFlow 1)
      f.toBoundedContinuousFunction q hT hperiod
  simpa only [forwardOrbitAverage,
    HGAS.Dynamics.integerOrbitAverageObservable_apply,
    closedHorocycleInvariantProbability,
    scaledGammaTwoHorocycleFlow_one,
    Nat.cast_add, Nat.cast_one] using h

/-- The abstract generic-point alternative for the level-two horocycle
flow is a theorem, not an external input. -/
theorem gammaTwoErgodicGenericPointAlternative :
    GammaTwoErgodicGenericPointAlternative := by
  intro μ hμ
  let μi :
      HGAS.Dynamics.InvariantProbabilityMeasure
        gammaTwoHorocycleFlow :=
    ⟨μ, hμ.invariant⟩
  obtain ⟨q, hqgeneric⟩ :=
    exists_isForwardGenericFor
      gammaTwoHorocycleFlow μi hμ
  by_cases hperiodic : IsPeriodicHorocyclePoint 1 q
  · obtain ⟨T, hT, hperiod⟩ := hperiodic
    let νq : ProbabilityMeasure GammaTwoFrameQuotient :=
      (closedHorocycleInvariantProbability
        1 q hT hperiod).measure
    have hqν :
        IsForwardGenericFor gammaTwoHorocycleFlow νq q := by
      simpa only [νq] using
        isForwardGenericFor_closedHorocycleInvariantProbability
          q hT hperiod
    have hμν : μ = νq :=
      hqgeneric.probability_eq hqν
    exact Or.inl <| by
      rw [hμν]
      exact closedHorocycleInvariantProbability_isClosed
        1 q hT hperiod
  · exact Or.inr ⟨q, hperiodic, hqgeneric⟩

/-- The pointwise nonperiodic-orbit theorem now implies the ergodic
measure dichotomy with no separate generic-point assumption. -/
theorem gammaTwoErgodicHorocycleDichotomy_of_pointwiseEquidistribution'
    (hpointwise : GammaTwoPointwiseHorocycleEquidistribution) :
    GammaTwoErgodicHorocycleDichotomy :=
  gammaTwoErgodicHorocycleDichotomy_of_pointwiseEquidistribution
    hpointwise gammaTwoErgodicGenericPointAlternative

/-- Consequently the sole remaining input to the full Dani--Smillie
classification is the geometric nonperiodic-orbit equidistribution
theorem itself. -/
theorem gammaTwoDaniSmillieTheorem_of_pointwiseEquidistribution'
    (hpointwise : GammaTwoPointwiseHorocycleEquidistribution) :
    GammaTwoDaniSmillieTheorem :=
  gammaTwoDaniSmillieTheorem_of_pointwiseEquidistribution
    hpointwise gammaTwoErgodicGenericPointAlternative

end

end HGAS.Modular
