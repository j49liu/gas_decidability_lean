import HGAS.Dynamics.TightOrbitOccupations
import HGAS.Modular.GammaTwoCcToC0Equidistribution

/-!
# The occupation-measure endgame for the level-two horocycle flow

This file formalizes the last compactness argument in the
Dani--Smillie/Hubbard--Miller proof.

For a nonperiodic point `q`, let `mₙ(q)` be normalized Lebesgue measure on
the horocycle segment of length `n + 1`.  Three geometric/ergodic facts
finish the pointwise theorem:

* the family `mₙ(q)` is tight (no escape of mass into a cusp);
* every weak accumulation probability gives zero mass to the union of
  periodic horocycles;
* Haar is the only invariant probability with zero mass on that union.

The theorem below proves in Lean that these three inputs imply convergence
of every nonperiodic horocycle to Haar, and hence imply the exact
`GammaTwoDaniSmillieTheorem` interface used downstream.

This decomposition follows the proof in:

* J. H. Hubbard and R. L. Miller, *Equidistribution of horocyclic flows on
  complete hyperbolic surfaces of finite area*, arXiv:0712.1300,
  Sections 7--8;
* S. G. Dani and J. Smillie, *Uniform distribution of horocycle orbits for
  Fuchsian groups*, Duke Math. J. 51 (1984), 185--194.

No one of the three inputs is silently assumed here: each is a named
proposition and an explicit argument of the reduction theorem.
-/

namespace HGAS.Modular

open Filter Function _root_.MeasureTheory Set Topology
open scoped BoundedContinuousFunction CompactlySupported

noncomputable section

/-!
The quotient is second countable, locally compact, and Hausdorff, hence
metrizable.  We choose one compatible metric only to use Mathlib's
Lévy--Prokhorov metrization and sequential form of Prokhorov compactness.
None of the definitions or conclusions depends on which compatible metric
is chosen.
-/

local instance gammaTwoFrameQuotientMetricSpace :
    MetricSpace GammaTwoFrameQuotient :=
  TopologicalSpace.metrizableSpaceMetric GammaTwoFrameQuotient

/-- The union of all periodic unit-speed horocycles, expressed as the set
of their points. -/
def gammaTwoPeriodicHorocycleSet :
    Set GammaTwoFrameQuotient :=
  {q | IsPeriodicHorocyclePoint 1 q}

/-- Nonescape of mass for every nonperiodic horocycle, in the exact tight
form used by Prokhorov's theorem. -/
def GammaTwoNonperiodicOccupationTightness : Prop :=
  ∀ q : GammaTwoFrameQuotient,
    ¬ IsPeriodicHorocyclePoint 1 q →
      IsTightMeasureSet
        {((m : ProbabilityMeasure GammaTwoFrameQuotient) :
            Measure GammaTwoFrameQuotient) |
          m ∈ Set.range
            (HGAS.Dynamics.integerOrbitOccupationProbability
              gammaTwoHorocycleFlow q)}

/-- Every accumulation probability of a nonperiodic horocycle gives zero
mass to the union of periodic horocycles. -/
def GammaTwoNonperiodicOccupationLimitsAvoidPeriodic : Prop :=
  ∀ q : GammaTwoFrameQuotient,
    ¬ IsPeriodicHorocyclePoint 1 q →
      HGAS.Dynamics.EveryOrbitOccupationLimitSatisfies
        gammaTwoHorocycleFlow q
        (fun μ ↦
          (μ : Measure GammaTwoFrameQuotient)
            gammaTwoPeriodicHorocycleSet = 0)

/-- Haar uniqueness among invariant probabilities which do not charge the
periodic horocycles.

This is the measure-uniqueness proposition proved from the good-return-time
lemma in the classical elementary proof.  Ergodicity of the candidate
measure is not assumed and is not needed. -/
def GammaTwoInvariantProbabilityOffPeriodicUnique
    (ν : ProbabilityMeasure GammaTwoFrameQuotient) : Prop :=
  ∀ μ : ProbabilityMeasure GammaTwoFrameQuotient,
    HGAS.Dynamics.IsInvariantProbability
      gammaTwoHorocycleFlow μ →
    (μ : Measure GammaTwoFrameQuotient)
        gammaTwoPeriodicHorocycleSet = 0 →
    μ = ν

/-- Weak convergence of integer occupation probabilities is exactly the
forward-genericity statement used by the pointwise horocycle theorem. -/
theorem isForwardGenericFor_of_tendsto_integerOrbitOccupation
    (q : GammaTwoFrameQuotient)
    (ν : ProbabilityMeasure GammaTwoFrameQuotient)
    (h :
      Tendsto
        (HGAS.Dynamics.integerOrbitOccupationProbability
          gammaTwoHorocycleFlow q)
        atTop (𝓝 ν)) :
    IsForwardGenericFor gammaTwoHorocycleFlow ν q := by
  intro f
  have hf :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp h)
      f.toBoundedContinuousFunction
  simpa only [forwardOrbitAverage,
    HGAS.Dynamics.integral_integerOrbitOccupationProbability]
    using hf

/-- The three classical endgame inputs imply pointwise equidistribution of
every nonperiodic level-two horocycle. -/
theorem gammaTwoPointwiseHorocycleEquidistribution_of_occupation_inputs
    (ν : ProbabilityMeasure GammaTwoFrameQuotient)
    (htight : GammaTwoNonperiodicOccupationTightness)
    (havoid :
      GammaTwoNonperiodicOccupationLimitsAvoidPeriodic)
    (hunique :
      GammaTwoInvariantProbabilityOffPeriodicUnique ν) :
    GammaTwoNonperiodicOrbitEquidistribution ν := by
  intro q hq
  apply isForwardGenericFor_of_tendsto_integerOrbitOccupation
  exact
    HGAS.Dynamics.tendsto_integerOrbitOccupation_of_tight_of_unique
      gammaTwoHorocycleFlow q ν
      (fun μ ↦
        (μ : Measure GammaTwoFrameQuotient)
          gammaTwoPeriodicHorocycleSet = 0)
      (htight q hq) (havoid q hq) hunique

/-- Normalization-independent pointwise form of the preceding reduction. -/
theorem gammaTwoPointwiseHorocycleEquidistribution_of_occupation_inputs'
    (htight : GammaTwoNonperiodicOccupationTightness)
    (havoid :
      GammaTwoNonperiodicOccupationLimitsAvoidPeriodic)
    (hunique :
      ∀ ν : ProbabilityMeasure GammaTwoFrameQuotient,
        IsRightInvariantFrameProbability ν →
          GammaTwoInvariantProbabilityOffPeriodicUnique ν) :
    GammaTwoPointwiseHorocycleEquidistribution := by
  intro ν hν
  exact
    gammaTwoPointwiseHorocycleEquidistribution_of_occupation_inputs
      ν htight havoid (hunique ν hν)

/-- Consequently the three endgame inputs, together with the already
formalized pointwise-to-classification reduction, supply the complete
Dani--Smillie classification proposition. -/
theorem gammaTwoDaniSmillieTheorem_of_occupation_inputs
    (htight : GammaTwoNonperiodicOccupationTightness)
    (havoid :
      GammaTwoNonperiodicOccupationLimitsAvoidPeriodic)
    (hunique :
      ∀ ν : ProbabilityMeasure GammaTwoFrameQuotient,
        IsRightInvariantFrameProbability ν →
          GammaTwoInvariantProbabilityOffPeriodicUnique ν) :
    GammaTwoDaniSmillieTheorem :=
  gammaTwoDaniSmillieTheorem_of_nonperiodicEquidistribution
    (gammaTwoPointwiseHorocycleEquidistribution_of_occupation_inputs'
      htight havoid hunique)

end

end HGAS.Modular
