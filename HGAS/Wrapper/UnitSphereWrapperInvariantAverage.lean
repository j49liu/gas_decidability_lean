import HGAS.Dynamics.InvariantComponentAverage
import HGAS.Wrapper.UnitSphereWrapperSourceFlow
import Mathlib.Tactic

/-!
# Invariant-average transfer for the concrete two-sheet wrapper

This file closes the measure-theoretic part of the concrete product-sphere
wrapper.  On each normalized sheet:

1. the explicit chart is a homeomorphism from the compact source product;
2. the restricted wrapper flow pulls back to the canonical source flow;
3. the chart reward pulls back to the source polynomial reward.

Therefore invariant probabilities and their averages correspond exactly.
The full stratum is the disjoint union of the positive and negative
sheets, and the two pulled-back source flows are equal.  Splitting an
ambient invariant probability between the two sheets proves that the
full-stratum maximum is precisely the source maximum.
-/

namespace HGAS

open Function MeasureTheory Metric Set
open scoped BigOperators BoundedContinuousFunction

noncomputable section

namespace UnitSpherePolynomialWrapper

variable {n k : ℕ}

/-- The positive sheet is ambiently measurable. -/
theorem measurableSet_positiveFullSheet
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n) :
    MeasurableSet (positiveFullSheet sourceBlock D P a) := by
  have hcoord :
      Measurable
        (fun u : EuclideanUnitSphere (EuclideanWrapperSpace n) ↦
          wrapperEuclideanEquiv.symm u.1 0) :=
    ((continuous_apply 0).comp
      (wrapperEuclideanEquiv.symm.continuous.comp
        continuous_subtype_val)).measurable
  exact
    (radiusCleanupFlowCertificate
      sourceBlock D P a).measurableSet_fullStratum.inter
      (hcoord measurableSet_Ioi)

/-- The negative sheet is ambiently measurable. -/
theorem measurableSet_negativeFullSheet
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n) :
    MeasurableSet (negativeFullSheet sourceBlock D P a) := by
  have hcoord :
      Measurable
        (fun u : EuclideanUnitSphere (EuclideanWrapperSpace n) ↦
          wrapperEuclideanEquiv.symm u.1 0) :=
    ((continuous_apply 0).comp
      (wrapperEuclideanEquiv.symm.continuous.comp
        continuous_subtype_val)).measurable
  exact
    (radiusCleanupFlowCertificate
      sourceBlock D P a).measurableSet_fullStratum.inter
      (hcoord measurableSet_Iio)

/-- A probability concentrated on the positive sheet has chart-reward
average bounded by the canonical source maximum. -/
theorem chartReward_average_le_sourceMaximum_of_ae_positive
    (sourceBlock : Fin n → Fin k)
    [Nonempty (SourceProductSphere sourceBlock)]
    (D : ℕ) (hDodd : D % 2 = 1)
    (P : PolynomialFieldCode n)
    (a : PolynomialCode n)
    (ha : PolynomialCode.TermsDegreeLE (D - 1) a)
    (μ : Dynamics.InvariantProbabilityMeasure
      (wrapperUnitFlow sourceBlock D P a))
    (hmem :
      ∀ᵐ u ∂(μ.measure :
        Measure (EuclideanUnitSphere (EuclideanWrapperSpace n))),
        u ∈ positiveFullSheet sourceBlock D P a) :
    Dynamics.observableAverage
        (chartRewardBCF (k := k) D a) μ.measure ≤
      Dynamics.maximalInvariantAverage
        (positiveSourceFlow sourceBlock D P a)
        (sourceRewardBCF sourceBlock a) := by
  let s := positiveFullSheet sourceBlock D P a
  have hs : MeasurableSet s :=
    measurableSet_positiveFullSheet sourceBlock D P a
  have hfull :
      (μ.measure :
        Measure (EuclideanUnitSphere (EuclideanWrapperSpace n))) s = 1 := by
    have heq :=
      (ae_mem_iff_measure_eq hs.nullMeasurableSet).mp hmem
    simpa only [measure_univ] using heq
  let μs :=
    μ.restrictToFullMeasureInvariant
      hs hfull
      (isInvariant_positiveFullSheet sourceBlock D P a)
  let e := positiveSheetHomeomorph sourceBlock D P a
  let μsource :=
    Dynamics.InvariantProbabilityMeasure.comapHomeomorph
      e (positiveSheetFlow sourceBlock D P a) μs
  have hle :
      Dynamics.observableAverage
          (sourceRewardBCF sourceBlock a) μsource.measure ≤
        Dynamics.maximalInvariantAverage
          (positiveSourceFlow sourceBlock D P a)
          (sourceRewardBCF sourceBlock a) :=
    Dynamics.invariantAverage_le_maximalInvariantAverage
      (positiveSourceFlow sourceBlock D P a)
      (sourceRewardBCF sourceBlock a)
      μsource.measure μsource.invariant
  calc
    Dynamics.observableAverage
        (chartRewardBCF (k := k) D a) μ.measure =
      Dynamics.observableAverage
        (Dynamics.subtypeObservable
          (chartRewardBCF (k := k) D a) s)
        μs.measure := by
          symm
          exact
            Dynamics.observableAverage_restrictToFullMeasureInvariant
              μ hs hfull
                (isInvariant_positiveFullSheet
                  sourceBlock D P a)
              (chartRewardBCF (k := k) D a)
    _ =
      Dynamics.observableAverage
        (sourceRewardBCF sourceBlock a) μsource.measure := by
          rw [← Dynamics.observableAverage_comapHomeomorph
            e (positiveSheetFlow sourceBlock D P a)
            (Dynamics.subtypeObservable
              (chartRewardBCF (k := k) D a) s) μs]
          rw [show
            Dynamics.pullbackObservable e
                (Dynamics.subtypeObservable
                  (chartRewardBCF (k := k) D a) s) =
              sourceRewardBCF sourceBlock a by
            simpa only [s, e, Dynamics.subtypeObservable] using
              pullback_chartRewardBCF_positive
                sourceBlock D hDodd P a ha]
    _ ≤ _ := hle

/-- The analogous upper bound on the negative sheet. -/
theorem chartReward_average_le_sourceMaximum_of_ae_negative
    (sourceBlock : Fin n → Fin k)
    [Nonempty (SourceProductSphere sourceBlock)]
    (D : ℕ) (hDodd : D % 2 = 1)
    (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE D (P j))
    (a : PolynomialCode n)
    (ha : PolynomialCode.TermsDegreeLE (D - 1) a)
    (htangent :
      ∀ y : SourceProductSphere sourceBlock,
        SourceTangentAt sourceBlock y.1
          (PolynomialFieldCode.realize P y.1))
    (μ : Dynamics.InvariantProbabilityMeasure
      (wrapperUnitFlow sourceBlock D P a))
    (hmem :
      ∀ᵐ u ∂(μ.measure :
        Measure (EuclideanUnitSphere (EuclideanWrapperSpace n))),
        u ∈ negativeFullSheet sourceBlock D P a) :
    Dynamics.observableAverage
        (chartRewardBCF (k := k) D a) μ.measure ≤
      Dynamics.maximalInvariantAverage
        (positiveSourceFlow sourceBlock D P a)
        (sourceRewardBCF sourceBlock a) := by
  let s := negativeFullSheet sourceBlock D P a
  have hs : MeasurableSet s :=
    measurableSet_negativeFullSheet sourceBlock D P a
  have hfull :
      (μ.measure :
        Measure (EuclideanUnitSphere (EuclideanWrapperSpace n))) s = 1 := by
    have heq :=
      (ae_mem_iff_measure_eq hs.nullMeasurableSet).mp hmem
    simpa only [measure_univ] using heq
  let μs :=
    μ.restrictToFullMeasureInvariant
      hs hfull
      (isInvariant_negativeFullSheet sourceBlock D P a)
  let e := negativeSheetHomeomorph sourceBlock D P a
  let μsource :=
    Dynamics.InvariantProbabilityMeasure.comapHomeomorph
      e (negativeSheetFlow sourceBlock D P a) μs
  have hle :
      Dynamics.observableAverage
          (sourceRewardBCF sourceBlock a) μsource.measure ≤
        Dynamics.maximalInvariantAverage
          (negativeSourceFlow sourceBlock D P a)
          (sourceRewardBCF sourceBlock a) :=
    Dynamics.invariantAverage_le_maximalInvariantAverage
      (negativeSourceFlow sourceBlock D P a)
      (sourceRewardBCF sourceBlock a)
      μsource.measure μsource.invariant
  calc
    Dynamics.observableAverage
        (chartRewardBCF (k := k) D a) μ.measure =
      Dynamics.observableAverage
        (Dynamics.subtypeObservable
          (chartRewardBCF (k := k) D a) s)
        μs.measure := by
          symm
          exact
            Dynamics.observableAverage_restrictToFullMeasureInvariant
              μ hs hfull
                (isInvariant_negativeFullSheet
                  sourceBlock D P a)
              (chartRewardBCF (k := k) D a)
    _ =
      Dynamics.observableAverage
        (sourceRewardBCF sourceBlock a) μsource.measure := by
          rw [← Dynamics.observableAverage_comapHomeomorph
            e (negativeSheetFlow sourceBlock D P a)
            (Dynamics.subtypeObservable
              (chartRewardBCF (k := k) D a) s) μs]
          rw [show
            Dynamics.pullbackObservable e
                (Dynamics.subtypeObservable
                  (chartRewardBCF (k := k) D a) s) =
              sourceRewardBCF sourceBlock a by
            simpa only [s, e, Dynamics.subtypeObservable] using
              pullback_chartRewardBCF_negative
                sourceBlock D hDodd P a ha]
    _ ≤
      Dynamics.maximalInvariantAverage
        (negativeSourceFlow sourceBlock D P a)
        (sourceRewardBCF sourceBlock a) :=
      hle
    _ =
      Dynamics.maximalInvariantAverage
        (positiveSourceFlow sourceBlock D P a)
        (sourceRewardBCF sourceBlock a) := by
          rw [positiveSourceFlow_eq_negativeSourceFlow
            sourceBlock D hDodd P hP a htangent]

/-- **Exact full-stratum maximum for the concrete wrapper.**

The value is the attained maximal average of the source polynomial reward
under the canonical source flow carried by either normalized sheet. -/
theorem fullStratumMaximum_chartReward
    (sourceBlock : Fin n → Fin k)
    [Nonempty (SourceProductSphere sourceBlock)]
    (D : ℕ) (hDodd : D % 2 = 1)
    (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE D (P j))
    (a : PolynomialCode n)
    (ha : PolynomialCode.TermsDegreeLE (D - 1) a)
    (htangent :
      ∀ y : SourceProductSphere sourceBlock,
        SourceTangentAt sourceBlock y.1
          (PolynomialFieldCode.realize P y.1)) :
    RadiusCleanupFlowCertificate.FullStratumMaximum
      (radiusCleanupFlowCertificate sourceBlock D P a)
      (chartRewardBCF (k := k) D a)
      (Dynamics.maximalInvariantAverage
        (positiveSourceFlow sourceBlock D P a)
        (sourceRewardBCF sourceBlock a)) := by
  let β :=
    Dynamics.maximalInvariantAverage
      (positiveSourceFlow sourceBlock D P a)
      (sourceRewardBCF sourceBlock a)
  constructor
  · intro μ hfull
    apply Dynamics.observableAverage_le_of_ae_mem_invariant_union
      (chartRewardBCF (k := k) D a) β
      (measurableSet_positiveFullSheet sourceBlock D P a)
      (isInvariant_positiveFullSheet sourceBlock D P a)
    · intro ν hν
      exact chartReward_average_le_sourceMaximum_of_ae_positive
        sourceBlock D hDodd P a ha ν hν
    · intro ν hν
      exact chartReward_average_le_sourceMaximum_of_ae_negative
        sourceBlock D hDodd P hP a ha htangent ν hν
    · filter_upwards [hfull] with u hu
      exact
        (mem_fullStratum_iff_mem_positive_or_negative
          sourceBlock D P a u).mp hu
  · let sourceFlow :=
      positiveSourceFlow sourceBlock D P a
    let sourceReward :=
      sourceRewardBCF sourceBlock a
    let μsource :
        Dynamics.InvariantProbabilityMeasure sourceFlow :=
      ⟨Dynamics.maximizingInvariantProbability
          sourceFlow sourceReward,
        Dynamics.maximizingInvariantProbability_invariant
          sourceFlow sourceReward⟩
    let e := positiveSheetHomeomorph sourceBlock D P a
    let μsheet :
        Dynamics.InvariantProbabilityMeasure
          (positiveSheetFlow sourceBlock D P a) :=
      Dynamics.InvariantProbabilityMeasure.mapHomeomorph
        e (positiveSheetFlow sourceBlock D P a) μsource
    let μambient :
        Dynamics.InvariantProbabilityMeasure
          (wrapperUnitFlow sourceBlock D P a) :=
      μsheet.mapSubtype
        (isInvariant_positiveFullSheet sourceBlock D P a)
    refine ⟨μambient, ?_, ?_⟩
    · change
        ∀ᵐ u ∂(μambient.measure :
          Measure (EuclideanUnitSphere (EuclideanWrapperSpace n))),
          u ∈ (radiusCleanupFlowCertificate
            sourceBlock D P a).fullStratum
      rw [show
        (μambient.measure :
          Measure (EuclideanUnitSphere (EuclideanWrapperSpace n))) =
          Measure.map
            ((↑) :
              positiveFullSheet sourceBlock D P a →
                EuclideanUnitSphere (EuclideanWrapperSpace n))
            (μsheet.measure :
              Measure (positiveFullSheet sourceBlock D P a)) by
        rfl]
      change
        ∀ᵐ u ∂Measure.map
            ((↑) :
              positiveFullSheet sourceBlock D P a →
                EuclideanUnitSphere (EuclideanWrapperSpace n))
            (μsheet.measure :
              Measure (positiveFullSheet sourceBlock D P a)),
          ∀ i,
            (radiusCleanupFlowCertificate
              sourceBlock D P a).radii i u = 1
      rw [ae_map_iff
        measurable_subtype_coe.aemeasurable
        (radiusCleanupFlowCertificate
          sourceBlock D P a).measurableSet_fullStratum]
      exact Filter.Eventually.of_forall fun u ↦ u.property.1
    · calc
        Dynamics.observableAverage
            (chartRewardBCF (k := k) D a) μambient.measure =
          Dynamics.observableAverage
            (Dynamics.subtypeObservable
              (chartRewardBCF (k := k) D a)
              (positiveFullSheet sourceBlock D P a))
            μsheet.measure := by
              exact Dynamics.observableAverage_mapSubtype
                (isInvariant_positiveFullSheet
                  sourceBlock D P a)
                μsheet (chartRewardBCF (k := k) D a)
        _ =
          Dynamics.observableAverage
            sourceReward μsource.measure := by
              rw [show μsheet =
                Dynamics.InvariantProbabilityMeasure.mapHomeomorph
                  e (positiveSheetFlow sourceBlock D P a) μsource by
                rfl]
              rw [Dynamics.observableAverage_mapHomeomorph]
              rw [show
                Dynamics.pullbackObservable e
                    (Dynamics.subtypeObservable
                      (chartRewardBCF (k := k) D a)
                      (positiveFullSheet sourceBlock D P a)) =
                  sourceReward by
                simpa only [e, sourceReward,
                  Dynamics.subtypeObservable] using
                  pullback_chartRewardBCF_positive
                    sourceBlock D hDodd P a ha]
        _ = β := rfl

end UnitSpherePolynomialWrapper

end

end HGAS
