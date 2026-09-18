import HGAS.MeasureTheory.TightSingletonSigmaCompact
import HGAS.Modular.GammaTwoHaarErgodic
import HGAS.Modular.GammaTwoPeriodicMassExclusion

/-!
# Haar measure does not charge periodic level-two horocycles

This module combines two previously independent pieces of the geometric
argument.

* A right-invariant probability is unchanged by every positive diagonal
  right translation.  Its family of discrete geodesic pushforwards is
  therefore the singleton consisting of the original measure, hence is
  tight.
* Positive diagonal translation contracts every positive horocycle
  period, while compact subsets of `Γ(2) \ SL(2,ℝ)` have a positive
  period systole.

The abstract renormalized periodic-mass exclusion theorem then says that
Haar measure gives zero mass to the union of periodic horocycles.  This
argument avoids any smooth-volume or codimension calculation and works
directly with the intrinsic right-invariance characterization of Haar
probability.
-/

namespace HGAS.Modular

open Filter Function Matrix _root_.MeasureTheory Set Topology
open scoped MatrixGroups

noncomputable section

local instance gammaTwoFrameQuotientMetricSpaceForHaarPeriodicNull :
    MetricSpace GammaTwoFrameQuotient :=
  TopologicalSpace.metrizableSpaceMetric GammaTwoFrameQuotient

/-- The discrete positive-geodesic pushforwards of a right-invariant
probability form a tight family: every pushforward is the original
probability. -/
theorem
    IsRightInvariantFrameProbability.hasTightDiscreteGeodesicRenormalizationFamily
    {ν : ProbabilityMeasure GammaTwoFrameQuotient}
    (hν : IsRightInvariantFrameProbability ν) :
    HGAS.Dynamics.HasTightRenormalizationFamily ν
      gammaTwoDiscreteGeodesicRenormalizer := by
  have hpush :
      ∀ n : ℕ,
        HGAS.Dynamics.continuousPushforwardMeasure ν
            (gammaTwoDiscreteGeodesicRenormalizer n) =
          (ν : Measure GammaTwoFrameQuotient) := by
    intro n
    change
      Measure.map
          (gammaTwoFrameRightMul
            (gammaTwoGeodesicDiagonal (n : ℝ)))
          (ν : Measure GammaTwoFrameQuotient) =
        (ν : Measure GammaTwoFrameQuotient)
    exact
      congrArg ProbabilityMeasure.toMeasure
        (hν (gammaTwoGeodesicDiagonal (n : ℝ)))
  rw [HGAS.Dynamics.HasTightRenormalizationFamily]
  simpa only [hpush, Set.range_const] using
    (HGAS.MeasureTheory.isTightMeasureSet_singleton_of_sigmaCompact
      (ν : Measure GammaTwoFrameQuotient))

/-- Every right-invariant probability on the level-two frame quotient
assigns measure zero to the union of periodic positive horocycles. -/
theorem
    IsRightInvariantFrameProbability.periodicHorocycleSet_measure_zero
    {ν : ProbabilityMeasure GammaTwoFrameQuotient}
    (hν : IsRightInvariantFrameProbability ν) :
    (ν : Measure GammaTwoFrameQuotient)
        gammaTwoPeriodicHorocycleSet = 0 := by
  have hzero :=
    HGAS.Dynamics.measure_periodicPointSet_eq_zero_of_tight_renormalization
      gammaTwoHorocycleFlow ν
      gammaTwoDiscreteGeodesicRenormalizer
      gammaTwoDiscretePeriodContraction
      gammaTwoHorocycleCompactPeriodSystole
      gammaTwoDiscreteGeodesicRenormalizer_period
      gammaTwoDiscretePeriodContraction_pos
      (fun ε hε ↦
        exists_gammaTwoDiscretePeriodContraction_lt hε)
      hν.hasTightDiscreteGeodesicRenormalizationFamily
  rwa [periodicPointSet_gammaTwoHorocycleFlow] at hzero

end

end HGAS.Modular
