import HGAS.Modular.TwoControllerLinkedJacobiMixedClockC1Target
import HGAS.Dynamics.InvariantProbabilityTransport
import Mathlib.Tactic

/-!
# The measure diagram for the faithful mixed clock observation

The time-change theorem first pushes a normalized density from the mixed
compact base into the ambient eight-dimensional clock-coordinate space.
That ambient probability is supported on the four literal circles.  It is
then pulled back to the clock-sphere subtype and transported through the
explicit homeomorphism to the analytic controller--phase state.

This file proves that the intermediate pullback introduces no hidden
change of measure.  The clock-sphere probability is exactly the direct
pushforward by the clock projection, and the final analytic probability is
exactly the direct pushforward by the analytic clock observation.  These
commuting-measure identities are needed when a classification theorem on
the analytic clock model is transported back to observables on the mixed
polynomial source.
-/

noncomputable section

open Function MeasureTheory Set
open scoped ENNReal NNReal

namespace HGAS.Modular.TwoControllerLinkedJacobiMixedClockMeasureDiagram

open HGAS
open HGAS.Dynamics
open HGAS.Clocks.ControllerPhaseProductC1CutoffFlow
open HGAS.Clocks.ControllerPhaseProductFlowPolynomial
open HGAS.Clocks.ControllerPhaseProductSphereFlow
open TwoControllerLinkedJacobiMixedClockC1Target
open TwoControllerLinkedJacobiMixedClockDynamics
open TwoControllerLinkedJacobiMixedClockProjection

local instance : MeasurableSpace Circle :=
  borel Circle

local instance : BorelSpace Circle :=
  ⟨rfl⟩

/-- The normalized clock-density probability on the mixed compact base,
before applying any clock observation. -/
def mixedClockDensityProbability
    (pΩ pN : RationalCode)
    (η :
      InvariantProbabilityMeasure
        (mixedBaseFlow pΩ pN))
    (a : ℝ≥0) (ha : a ≠ 0)
    (hmass :
      ∫⁻ y, (clockSlowdownBCF y : ENNReal)
          ∂(η.measure : Measure BaseSpace) =
        (a : ENNReal)) :
    ProbabilityMeasure BaseSpace :=
  normalizedDensityProbability
    (η.measure : Measure BaseSpace)
    clockSlowdownBCF a
    clockSlowdownBCF.continuous.measurable
    ha hmass

/-- Pull the ambient target invariant probability back to the literal
clock-sphere subtype. -/
def mixedClockSphereInvariant
    (pΩ pN : RationalCode)
    (hp :
      ∀ i : Fin 2,
        (1 : ℝ) <
          (RationalCode.decode (twoClockCodes pΩ pN i) : ℝ))
    (η :
      InvariantProbabilityMeasure
        (mixedBaseFlow pΩ pN))
    (a : ℝ≥0) (ha : a ≠ 0)
    (hmass :
      ∫⁻ y, (clockSlowdownBCF y : ENNReal)
          ∂(η.measure : Measure BaseSpace) =
        (a : ENNReal)) :
    InvariantProbabilityMeasure
      (clockSphereFlow
        (fun i ↦
          (RationalCode.decode (twoClockCodes pΩ pN i) : ℝ))
        hp) :=
  InvariantProbabilityMeasure.transportFlow
    (restrict_ambientClockFlow_eq_clockSphereFlow
      (twoClockCodes pΩ pN) hp)
    (InvariantProbabilityMeasure.restrictToFullMeasureInvariant
      (mixedClockTargetInvariant pΩ pN η a ha hmass)
        (measurableSet_clockSphereSet :
          MeasurableSet (clockSphereSet 2))
        (mixedClockTargetInvariant_full_clockSphereSet
          pΩ pN η a ha hmass)
        (isInvariant_clockSphereSet
          (twoClockCodes pΩ pN) hp))

/-- The mixed source observed directly as an analytic controller--phase
state. -/
def analyticClockObservation :
    BaseSpace →
      HGAS.Clocks.ControllerPhaseFlow.State (Fin 2) :=
  (analyticHomeomorph.symm ∘ clockSphereHomeomorph) ∘
    clockProjection

theorem continuous_analyticClockObservation :
    Continuous analyticClockObservation :=
  continuous_toAnalytic.comp continuous_clockProjection

/-- Analytic clock invariant obtained from the transparent clock-sphere
transport above.  It has the same dynamics as the ambient construction,
while its underlying-measure formula remains definitionally visible. -/
def diagramAnalyticClockInvariant
    (pΩ pN : RationalCode)
    (hp :
      ∀ i : Fin 2,
        (1 : ℝ) <
          (RationalCode.decode (twoClockCodes pΩ pN i) : ℝ))
    (η :
      InvariantProbabilityMeasure
        (mixedBaseFlow pΩ pN))
    (a : ℝ≥0) (ha : a ≠ 0)
    (hmass :
      ∫⁻ y, (clockSlowdownBCF y : ENNReal)
          ∂(η.measure : Measure BaseSpace) =
        (a : ENNReal)) :
    InvariantProbabilityMeasure
      (HGAS.Clocks.ControllerPhaseFlow.controllerPhaseFlow
        (fun i ↦
          (RationalCode.decode (twoClockCodes pΩ pN i) : ℝ))
        hp) :=
  (mixedClockSphereInvariant pΩ pN hp η a ha hmass).mapEquivariant
    (analyticHomeomorph.symm ∘ clockSphereHomeomorph)
    continuous_toAnalytic
    (toAnalytic_semiconj
      (fun i ↦
        (RationalCode.decode (twoClockCodes pΩ pN i) : ℝ))
      hp)

/-- The subtype-valued clock observation has underlying ambient value
equal to the raw eight-coordinate observation. -/
theorem subtypeVal_comp_clockProjection :
    ((↑) :
        ClockProductSphere 2 →
          (Fin
              TwoControllerLinkedJacobiPolynomialCode.controllerPairDimension →
            ℝ)) ∘
        clockProjection =
      rawClockObservation := by
  funext y
  rfl

/-- The probability obtained by restricting the ambient clock measure to
the literal variety is exactly the direct clock-projection pushforward of
the normalized source density. -/
theorem mixedClockSphereInvariant_measure_eq_map_clockProjection
    (pΩ pN : RationalCode)
    (hp :
      ∀ i : Fin 2,
        (1 : ℝ) <
          (RationalCode.decode (twoClockCodes pΩ pN i) : ℝ))
    (η :
      InvariantProbabilityMeasure
        (mixedBaseFlow pΩ pN))
    (a : ℝ≥0) (ha : a ≠ 0)
    (hmass :
      ∫⁻ y, (clockSlowdownBCF y : ENNReal)
          ∂(η.measure : Measure BaseSpace) =
        (a : ENNReal)) :
    ((mixedClockSphereInvariant pΩ pN hp η a ha hmass).measure :
        ProbabilityMeasure (ClockProductSphere 2)) =
      (mixedClockDensityProbability pΩ pN η a ha hmass).map
        continuous_clockProjection.measurable.aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  apply
    (MeasurableEmbedding.subtype_coe
      (measurableSet_clockSphereSet :
        MeasurableSet (clockSphereSet 2))).map_injective
  have hleft :=
    InvariantProbabilityMeasure.map_restrictToFullMeasureInvariant_measure
      (mixedClockTargetInvariant pΩ pN η a ha hmass)
      (measurableSet_clockSphereSet :
        MeasurableSet (clockSphereSet 2))
      (mixedClockTargetInvariant_full_clockSphereSet
        pΩ pN η a ha hmass)
      (isInvariant_clockSphereSet
        (twoClockCodes pΩ pN) hp)
  have hleft' :
      Measure.map ((↑) :
          ClockProductSphere 2 →
            (Fin
                TwoControllerLinkedJacobiPolynomialCode.controllerPairDimension →
              ℝ))
          ((mixedClockSphereInvariant
              pΩ pN hp η a ha hmass).measure :
            Measure (ClockProductSphere 2)) =
        ((mixedClockTargetInvariant pΩ pN η a ha hmass).measure :
          Measure
            (Fin
                TwoControllerLinkedJacobiPolynomialCode.controllerPairDimension →
              ℝ)) := by
    simpa only [mixedClockSphereInvariant,
      InvariantProbabilityMeasure.transportFlow_measure] using hleft
  calc
    Measure.map ((↑) :
        ClockProductSphere 2 →
          (Fin
              TwoControllerLinkedJacobiPolynomialCode.controllerPairDimension →
            ℝ))
        ((mixedClockSphereInvariant
            pΩ pN hp η a ha hmass).measure :
          Measure (ClockProductSphere 2)) =
        ((mixedClockTargetInvariant pΩ pN η a ha hmass).measure :
          Measure
            (Fin
                TwoControllerLinkedJacobiPolynomialCode.controllerPairDimension →
              ℝ)) := hleft'
    _ = Measure.map ((↑) :
          ClockProductSphere 2 →
            (Fin
                TwoControllerLinkedJacobiPolynomialCode.controllerPairDimension →
              ℝ))
          (((mixedClockDensityProbability pΩ pN η a ha hmass).map
              continuous_clockProjection.measurable.aemeasurable :
            ProbabilityMeasure (ClockProductSphere 2)) :
            Measure (ClockProductSphere 2)) := by
      simp only [mixedClockTargetInvariant,
        targetInvariantProbabilityOfObservedTimeChange,
        ProbabilityMeasure.toMeasure_map]
      rw [Measure.map_map
        measurable_subtype_coe
        continuous_clockProjection.measurable]
      rw [subtypeVal_comp_clockProjection]
      rfl

/-- The analytic invariant probability constructed through the ambient
cutoff target is exactly the direct pushforward of the normalized mixed
source density. -/
theorem diagramAnalyticClockInvariant_measure_eq_map_analyticClockObservation
    (pΩ pN : RationalCode)
    (hp :
      ∀ i : Fin 2,
        (1 : ℝ) <
          (RationalCode.decode (twoClockCodes pΩ pN i) : ℝ))
    (η :
      InvariantProbabilityMeasure
        (mixedBaseFlow pΩ pN))
    (a : ℝ≥0) (ha : a ≠ 0)
    (hmass :
      ∫⁻ y, (clockSlowdownBCF y : ENNReal)
          ∂(η.measure : Measure BaseSpace) =
        (a : ENNReal)) :
    (diagramAnalyticClockInvariant
        pΩ pN hp η a ha hmass).measure =
      (mixedClockDensityProbability pΩ pN η a ha hmass).map
        continuous_analyticClockObservation.measurable.aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [diagramAnalyticClockInvariant,
    InvariantProbabilityMeasure.mapEquivariant_measure,
    ProbabilityMeasure.toMeasure_map]
  change
    Measure.map
        (analyticHomeomorph.symm ∘ clockSphereHomeomorph)
        ((mixedClockSphereInvariant
            pΩ pN hp η a ha hmass).measure :
          Measure (ClockProductSphere 2)) =
      _
  rw [mixedClockSphereInvariant_measure_eq_map_clockProjection
    pΩ pN hp η a ha hmass]
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map
    continuous_toAnalytic.measurable
    continuous_clockProjection.measurable]
  rfl

end HGAS.Modular.TwoControllerLinkedJacobiMixedClockMeasureDiagram
