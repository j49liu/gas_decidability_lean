import HGAS.Dynamics.PeriodicOrbitAverages
import HGAS.Modular.CountableC0Tests
import HGAS.Modular.GammaTwoFiniteVolumeConsequences

/-!
# A countable-test generic-point reduction for the horocycle flow

The usual proof that orbit equidistribution implies classification invokes
the pointwise ergodic theorem.  For the present application one can use a
strictly smaller abstract input.

For each member of one fixed countable measure-determining family in
`C₀(X, ℝ)`, the continuous-time mean ergodic theorem supplies an almost
everywhere convergent subsequence.  Countable intersection gives one point
at which all these (observable-dependent) subsequences converge.  There is
no need to diagonalize the subsequences:

* on a nonperiodic horocycle, full orbit equidistribution identifies every
  subsequential limit with Haar measure;
* on a periodic horocycle, the elementary periodic-average theorem
  identifies every subsequential limit with normalized arclength.

Equality on the fixed dense family then identifies the probability
measure.  This argument proves all of the generic-point reduction in the
Lean kernel while leaving only the geometric nonperiodic-orbit theorem as
an external boundary.
-/

namespace HGAS.Modular

open Filter Function _root_.MeasureTheory Set Topology
open scoped BoundedContinuousFunction ZeroAtInfty

noncomputable section

/-! ## The reusable countable-test generic point -/

variable {X : Type*}
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [T2Space X] [SecondCountableTopology X]
  [LocallyCompactSpace X]
  [TopologicalSpace.PseudoMetrizableSpace X]

/-- A point has the expected subsequential averages on the canonical
countable dense family in `C₀(X, ℝ)`.  The subsequence may depend on the
observable. -/
def IsC0DenseSubsequentiallyGenericFor
    (ϕ : Flow ℝ X) (μ : ProbabilityMeasure X) (x : X) : Prop :=
  ∀ j : ℕ,
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      Tendsto
        (fun i : ℕ ↦
          HGAS.Dynamics.integerOrbitAverageObservable
            ϕ (HGAS.Dynamics.c0DenseTest (X := X) j).toBCF
            (ns i + 1) x)
        atTop
        (𝓝 (∫ y,
          HGAS.Dynamics.c0DenseTest (X := X) j y
            ∂(μ : Measure X)))

omit [TopologicalSpace.PseudoMetrizableSpace X] in
/-- Every ergodic invariant probability has a point which is
subsequentially generic on the canonical countable `C₀` test family. -/
theorem exists_isC0DenseSubsequentiallyGenericFor
    (ϕ : Flow ℝ X)
    (μ : HGAS.Dynamics.InvariantProbabilityMeasure ϕ)
    (hμ :
      HGAS.Dynamics.IsErgodicInvariantProbability
        ϕ μ.measure) :
    ∃ x : X,
      IsC0DenseSubsequentiallyGenericFor ϕ μ.measure x := by
  choose ns hns hconv using
    fun j : ℕ ↦
      hμ.exists_subsequence_ae_tendsto_integerAverage
        μ (HGAS.Dynamics.c0DenseTest (X := X) j).toBCF
  have hall :
      ∀ᵐ x ∂(μ.measure : Measure X), ∀ j : ℕ,
        Tendsto
          (fun i : ℕ ↦
            HGAS.Dynamics.integerOrbitAverageObservable
              ϕ (HGAS.Dynamics.c0DenseTest (X := X) j).toBCF
              (ns j i + 1) x)
          atTop
          (𝓝 (∫ y,
            HGAS.Dynamics.c0DenseTest (X := X) j y
              ∂(μ.measure : Measure X))) :=
    ae_all_iff.mpr hconv
  obtain ⟨x, hx⟩ := hall.exists
  refine ⟨x, fun j ↦ ⟨ns j, hns j, ?_⟩⟩
  exact hx j

/-! ## The exact nonperiodic input and its classification consequence -/

/-- The `C₀` form of nonperiodic horocycle equidistribution for a chosen
probability `ν`. -/
def GammaTwoNonperiodicOrbitC0Equidistribution
    (ν : ProbabilityMeasure GammaTwoFrameQuotient) : Prop :=
  ∀ q : GammaTwoFrameQuotient,
    ¬ IsPeriodicHorocyclePoint 1 q →
      ∀ f : C₀(GammaTwoFrameQuotient, ℝ),
        Tendsto
          (fun n : ℕ ↦
            HGAS.Dynamics.integerOrbitAverageObservable
              gammaTwoHorocycleFlow f.toBCF (n + 1) q)
          atTop
          (𝓝 (∫ y, f y
            ∂(ν : Measure GammaTwoFrameQuotient)))

/-- The countable-test argument converts nonperiodic orbit
equidistribution directly into the ergodic periodic-or-Haar dichotomy. -/
theorem ergodicHorocycleDichotomy_of_c0Equidistribution
    (ν : ProbabilityMeasure GammaTwoFrameQuotient)
    (hν : GammaTwoNonperiodicOrbitC0Equidistribution ν)
    (μ : ProbabilityMeasure GammaTwoFrameQuotient)
    (hμ :
      HGAS.Dynamics.IsErgodicInvariantProbability
        gammaTwoHorocycleFlow μ) :
    IsClosedHorocycleProbability 1 μ ∨ μ = ν := by
  let μi :
      HGAS.Dynamics.InvariantProbabilityMeasure
        gammaTwoHorocycleFlow :=
    ⟨μ, hμ.invariant⟩
  obtain ⟨q, hq⟩ :=
    exists_isC0DenseSubsequentiallyGenericFor
      gammaTwoHorocycleFlow μi hμ
  by_cases hperiodic : IsPeriodicHorocyclePoint 1 q
  · obtain ⟨T, hT, hperiod⟩ := hperiodic
    let νq : ProbabilityMeasure GammaTwoFrameQuotient :=
      (closedHorocycleInvariantProbability
        1 q hT hperiod).measure
    have hμνq : μ = νq := by
      apply HGAS.Dynamics.probability_eq_of_integral_c0DenseTest_eq
      intro j
      obtain ⟨ns, hns, hμsub⟩ := hq j
      have hperiodicFull :=
        HGAS.Dynamics.tendsto_integerOrbitAverage_of_periodic
          (scaledGammaTwoHorocycleFlow 1)
          (HGAS.Dynamics.c0DenseTest
            (X := GammaTwoFrameQuotient) j).toBCF
          q hT hperiod
      have hperiodicFull' :
          Tendsto
            (fun n : ℕ ↦
              HGAS.Dynamics.integerOrbitAverageObservable
                gammaTwoHorocycleFlow
                (HGAS.Dynamics.c0DenseTest
                  (X := GammaTwoFrameQuotient) j).toBCF
                (n + 1) q)
            atTop
            (𝓝 (∫ y,
              HGAS.Dynamics.c0DenseTest
                (X := GammaTwoFrameQuotient) j y
                ∂(νq : Measure GammaTwoFrameQuotient))) := by
        simpa only [νq, closedHorocycleInvariantProbability,
          scaledGammaTwoHorocycleFlow_one] using
            hperiodicFull
      have hperiodicSub :=
        hperiodicFull'.comp hns.tendsto_atTop
      exact tendsto_nhds_unique hμsub hperiodicSub
    exact Or.inl <| by
      rw [hμνq]
      exact closedHorocycleInvariantProbability_isClosed
        1 q hT hperiod
  · have hμν : μ = ν := by
      apply HGAS.Dynamics.probability_eq_of_integral_c0DenseTest_eq
      intro j
      obtain ⟨ns, hns, hμsub⟩ := hq j
      have hνfull :=
        hν q hperiodic
          (HGAS.Dynamics.c0DenseTest
            (X := GammaTwoFrameQuotient) j)
      have hνsub := hνfull.comp hns.tendsto_atTop
      exact tendsto_nhds_unique hμsub hνsub
    exact Or.inr hμν

/-- A normalization-independent `C₀` version of pointwise horocycle
equidistribution. -/
def GammaTwoPointwiseHorocycleC0Equidistribution : Prop :=
  ∀ ν : ProbabilityMeasure GammaTwoFrameQuotient,
    IsRightInvariantFrameProbability ν →
      GammaTwoNonperiodicOrbitC0Equidistribution ν

/-- The geometric `C₀` orbit theorem implies the exact dichotomy
interface consumed by the finite-volume development. -/
theorem gammaTwoErgodicHorocycleDichotomy_of_c0Equidistribution
    (hpointwise :
      GammaTwoPointwiseHorocycleC0Equidistribution) :
    GammaTwoErgodicHorocycleDichotomy := by
  intro ν hν μ hμ
  exact ergodicHorocycleDichotomy_of_c0Equidistribution
    ν (hpointwise ν hν) μ hμ

/-- Consequently the geometric `C₀` orbit theorem supplies the full
Dani--Smillie classification object used elsewhere in the project. -/
theorem gammaTwoDaniSmillieTheorem_of_c0Equidistribution
    (hpointwise :
      GammaTwoPointwiseHorocycleC0Equidistribution) :
    GammaTwoDaniSmillieTheorem :=
  gammaTwoDaniSmillieTheorem_of_ergodicHorocycleDichotomy
    (gammaTwoErgodicHorocycleDichotomy_of_c0Equidistribution
      hpointwise)

end

end HGAS.Modular
