import HGAS.Clocks.ControllerPhaseProductC1CutoffFlow
import HGAS.Modular.TwoControllerLinkedJacobiMixedClockDynamics
import Mathlib.Tactic

/-!
# The compactly supported `C¹` target for the faithful mixed two-clock factor

The mixed linked-Jacobi compactification observes eight literal clock
coordinates.  Its derivative theorem says that these coordinates follow
the canonical two-clock polynomial field with the common, nonnegative
speed `w⁸`.  The reusable cutoff construction supplies a complete `C¹`
ODE flow on all of `ℝ⁸` whose generator agrees with that polynomial field
on the four clock circles.

This file makes the two interfaces meet.  It proves:

* the mixed clock observation is a time-changed factor of the concrete
  compactly supported ambient ODE;
* the normalized clock-density pushforward of every invariant mixed-base
  probability is an invariant probability of that ambient ODE;
* this pushforward gives full mass to the literal clock variety; and
* when both decoded parameters are greater than one, the measure therefore
  transfers to the original analytic controller--phase flow.

The full-mass proof is explicit.  It uses only that every mixed-base clock
observation satisfies the four circle equations; it does not infer support
from an informal coordinate picture.
-/

noncomputable section

open Function MeasureTheory Set
open scoped ENNReal NNReal

namespace HGAS.Modular.TwoControllerLinkedJacobiMixedClockC1Target

open HGAS
open HGAS.Dynamics
open HGAS.Clocks.ControllerPhaseProductC1CutoffFlow
open HGAS.Clocks.ControllerPhaseProductSphereFlow
open TwoControllerLinkedJacobiMixedClockDynamics

local instance : MeasurableSpace Circle :=
  borel Circle

local instance : BorelSpace Circle :=
  ⟨rfl⟩

/-- The two compiler parameters in the finite-product convention. -/
def twoClockCodes
    (pΩ pN : RationalCode) :
    Fin 2 → RationalCode :=
  ![pΩ, pN]

/-- The concrete complete ambient `C¹` ODE target for the mixed clock
observation. -/
def mixedClockC1ODEFlow
    (pΩ pN : RationalCode) :
    C1ODEFlow
      (Fin
          TwoControllerLinkedJacobiPolynomialCode.controllerPairDimension →
        ℝ) :=
  ambientClockC1ODEFlow (twoClockCodes pΩ pN)

@[simp]
theorem mixedClockC1ODEFlow_generator
    (pΩ pN : RationalCode) :
    (mixedClockC1ODEFlow pΩ pN).generator =
      cutoffClockField (twoClockCodes pΩ pN) :=
  rfl

/-- The mixed compact base observes the concrete ambient cutoff ODE with
the exact state-dependent speed `w⁸`. -/
theorem isObservedGeneratorTimeChange_mixedClockC1ODEFlow
    (pΩ pN : RationalCode) :
    IsObservedGeneratorTimeChange
      (TwoControllerLinkedJacobiMixedClockDynamics.mixedBaseFlow pΩ pN)
      (mixedClockC1ODEFlow pΩ pN)
      TwoControllerLinkedJacobiMixedClockDynamics.rawClockObservation
      TwoControllerLinkedJacobiMixedClockDynamics.clockSlowdownBCF := by
  apply
    isObservedGeneratorTimeChange_of_generator_eq_clockField
  intro z
  exact
    ambientClockC1ODEFlow_generator_eq_raw_on_sphere
      (twoClockCodes pΩ pN) z

/-- The normalized clock-density pushforward, now specialized to the
concrete complete ambient ODE target. -/
def mixedClockTargetInvariant
    (pΩ pN : RationalCode)
    (η :
      InvariantProbabilityMeasure
        (TwoControllerLinkedJacobiMixedClockDynamics.mixedBaseFlow pΩ pN))
    (a : ℝ≥0) (ha : a ≠ 0)
    (hmass :
      ∫⁻ y,
          (TwoControllerLinkedJacobiMixedClockDynamics.clockSlowdownBCF y :
            ENNReal)
          ∂(η.measure :
            Measure TwoControllerLinkedJacobiMixedClockProjection.BaseSpace) =
        (a : ENNReal)) :
    InvariantProbabilityMeasure
      (mixedClockC1ODEFlow pΩ pN).flow :=
  targetInvariantProbabilityOfObservedTimeChange
    (TwoControllerLinkedJacobiMixedClockDynamics.mixedBaseFlow pΩ pN)
    (mixedClockC1ODEFlow pΩ pN)
    TwoControllerLinkedJacobiMixedClockDynamics.rawClockObservation
    TwoControllerLinkedJacobiMixedClockDynamics.clockSlowdownBCF
    TwoControllerLinkedJacobiMixedClockDynamics.continuous_rawClockObservation
    (isObservedGeneratorTimeChange_mixedClockC1ODEFlow pΩ pN)
    η a ha hmass

/-- Any probability pushed through the mixed raw clock observation gives
the literal clock variety full mass. -/
theorem map_rawClockObservation_clockSphereSet
    (ν :
      ProbabilityMeasure
        TwoControllerLinkedJacobiMixedClockProjection.BaseSpace) :
    ((ν.map
          continuous_rawClockObservation.measurable.aemeasurable :
        ProbabilityMeasure
          (Fin
              TwoControllerLinkedJacobiPolynomialCode.controllerPairDimension →
            ℝ)) :
      Measure
        (Fin
            TwoControllerLinkedJacobiPolynomialCode.controllerPairDimension →
          ℝ))
        (clockSphereSet 2) = 1 := by
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_apply
    continuous_rawClockObservation.measurable
    measurableSet_clockSphereSet]
  have hpreimage :
      TwoControllerLinkedJacobiMixedClockDynamics.rawClockObservation ⁻¹'
          clockSphereSet 2 =
        Set.univ := by
    ext y
    simp only [Set.mem_preimage, Set.mem_univ, iff_true]
    change OnClockCircles
      (TwoControllerLinkedJacobiMixedClockProjection.clockRawPoint y)
    exact
      TwoControllerLinkedJacobiMixedClockProjection.onClockCircles_clockRawPoint
        y
  rw [hpreimage, measure_univ]

/-- The invariant probability produced by the mixed time-change theorem is
supported on the literal clock variety. -/
theorem mixedClockTargetInvariant_full_clockSphereSet
    (pΩ pN : RationalCode)
    (η :
      InvariantProbabilityMeasure
        (TwoControllerLinkedJacobiMixedClockDynamics.mixedBaseFlow pΩ pN))
    (a : ℝ≥0) (ha : a ≠ 0)
    (hmass :
      ∫⁻ y,
          (TwoControllerLinkedJacobiMixedClockDynamics.clockSlowdownBCF y :
            ENNReal)
          ∂(η.measure :
            Measure TwoControllerLinkedJacobiMixedClockProjection.BaseSpace) =
        (a : ENNReal)) :
    (((mixedClockTargetInvariant
          pΩ pN η a ha hmass).measure :
        ProbabilityMeasure
          (Fin
              TwoControllerLinkedJacobiPolynomialCode.controllerPairDimension →
            ℝ)) :
      Measure
        (Fin
            TwoControllerLinkedJacobiPolynomialCode.controllerPairDimension →
          ℝ))
        (clockSphereSet 2) = 1 := by
  exact
    map_rawClockObservation_clockSphereSet
      (normalizedDensityProbability
        (η.measure :
          Measure TwoControllerLinkedJacobiMixedClockProjection.BaseSpace)
        TwoControllerLinkedJacobiMixedClockDynamics.clockSlowdownBCF a
        TwoControllerLinkedJacobiMixedClockDynamics.clockSlowdownBCF.continuous.measurable
        ha hmass)

/-- End-to-end transfer of the mixed normalized clock-density pushforward
to the original analytic two-controller--phase flow. -/
def mixedAnalyticClockInvariant
    (pΩ pN : RationalCode)
    (hp :
      ∀ i : Fin 2,
        (1 : ℝ) <
          (RationalCode.decode (twoClockCodes pΩ pN i) : ℝ))
    (η :
      InvariantProbabilityMeasure
        (TwoControllerLinkedJacobiMixedClockDynamics.mixedBaseFlow pΩ pN))
    (a : ℝ≥0) (ha : a ≠ 0)
    (hmass :
      ∫⁻ y,
          (TwoControllerLinkedJacobiMixedClockDynamics.clockSlowdownBCF y :
            ENNReal)
          ∂(η.measure :
            Measure TwoControllerLinkedJacobiMixedClockProjection.BaseSpace) =
        (a : ENNReal)) :
    InvariantProbabilityMeasure
      (HGAS.Clocks.ControllerPhaseFlow.controllerPhaseFlow
        (fun i ↦
          (RationalCode.decode (twoClockCodes pΩ pN i) : ℝ))
        hp) :=
  analyticInvariantOfAmbient
    (twoClockCodes pΩ pN) hp
    (mixedClockTargetInvariant pΩ pN η a ha hmass)
    (mixedClockTargetInvariant_full_clockSphereSet
      pΩ pN η a ha hmass)

end HGAS.Modular.TwoControllerLinkedJacobiMixedClockC1Target

end
