import HGAS.Clocks.ControllerPhaseProductC1CutoffFlow
import HGAS.Clocks.NonergodicControllerPhaseHaar
import HGAS.Dynamics.InvariantMeasureTimeChangedFactor
import HGAS.Dynamics.InvariantProbabilityTransport
import Mathlib.Tactic

/-!
# Haar phases for observed time-changed finite clock products

This module packages the reusable abstract form of the clock argument.
Let `X` carry a continuous flow `ϕ`, let

```
                  π : X → ClockProductSphere q
```

be a continuous observation, and let `f : X → ℝ≥0` be a bounded
continuous speed.  Suppose the ambient real coordinates of `π(ϕ_t x)`
satisfy the polynomial controller--phase generator with speed `f`.

For every `ϕ`-invariant probability `η` with nonzero finite clock mass,
weighting by `f` and normalizing gives a probability whose analytic clock
observation is invariant under the ordinary controller--phase flow.  If
the controller parameters are distinct primes, the physical phase
marginal in turns is therefore Haar.

The proof deliberately does not claim that the density change preserves
ergodicity.  It uses the stronger classification theorem saying that every
invariant coupled-clock probability has Haar phase marginal.
-/

noncomputable section

open Function MeasureTheory Set
open scoped BoundedContinuousFunction ENNReal NNReal

namespace HGAS.Clocks.ObservedTimeChangedControllerPhaseHaar

open HGAS
open HGAS.Dynamics
open HGAS.Clocks.ControllerPhaseProductC1CutoffFlow
open HGAS.Clocks.ControllerPhaseProductFlowPolynomial
open HGAS.Clocks.ControllerPhaseProductSphereFlow
open HGAS.Clocks.ErgodicControllerPhaseHaar

local instance : MeasurableSpace Circle :=
  borel Circle

local instance : BorelSpace Circle :=
  ⟨rfl⟩

variable {q : ℕ}
variable {X : Type*}
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Rational finite codes for a family of natural controller parameters. -/
def primeClockCodes (p : Fin q → ℕ) :
    Fin q → RationalCode :=
  fun i ↦ RationalCode.ofNat (p i)

@[simp]
theorem decode_primeClockCodes
    (p : Fin q → ℕ) (i : Fin q) :
    (RationalCode.decode (primeClockCodes p i) : ℝ) =
      (p i : ℝ) := by
  simp [primeClockCodes, RationalCode.decode_ofNat]

/-- Prime controller parameters are strictly larger than one after
decoding their rational finite codes. -/
theorem primeClockCodes_gt_one
    (p : Fin q → ℕ)
    (hp : ∀ i, (p i).Prime) :
    ∀ i,
      (1 : ℝ) <
        (RationalCode.decode (primeClockCodes p i) : ℝ) := by
  intro i
  rw [decode_primeClockCodes]
  exact_mod_cast (hp i).one_lt

/-- The decoded-code analytic flow is the standard natural-prime analytic
flow used by the Haar theorem. -/
theorem decodedPrimeClockFlow_eq
    (p : Fin q → ℕ)
    (hp : ∀ i, (p i).Prime) :
    ControllerPhaseFlow.controllerPhaseFlow
        (fun i ↦
          (RationalCode.decode (primeClockCodes p i) : ℝ))
        (primeClockCodes_gt_one p hp) =
      ControllerPhaseFlow.controllerPhaseFlow
        (fun i ↦ (p i : ℝ))
        (primeControllerParameters_gt_one p hp) := by
  congr 2
  funext i
  exact decode_primeClockCodes p i

/-- The normalized clock-density probability on the source. -/
def sourceClockDensityProbability
    (ϕ : Flow ℝ X)
    (η : InvariantProbabilityMeasure ϕ)
    (f : X →ᵇ ℝ≥0)
    (a : ℝ≥0) (ha : a ≠ 0)
    (hmass :
      ∫⁻ x, (f x : ENNReal)
          ∂(η.measure : Measure X) =
        (a : ENNReal)) :
    ProbabilityMeasure X :=
  normalizedDensityProbability
    (η.measure : Measure X) f a
    f.continuous.measurable ha hmass

/-- Ambient real-coordinate observation associated to a clock-sphere
observation. -/
def ambientClockObservation
    (π : X → ClockProductSphere q) :
    X → ClockAmbient q :=
  fun x ↦ (π x).1

omit [MeasurableSpace X] [BorelSpace X] in
theorem continuous_ambientClockObservation
    (π : X → ClockProductSphere q)
    (hπ : Continuous π) :
    Continuous (ambientClockObservation π) :=
  continuous_subtype_val.comp hπ

/-- The direct analytic controller--phase observation. -/
def analyticClockObservation
    (π : X → ClockProductSphere q) :
    X → ControllerPhaseFlow.State (Fin q) :=
  (analyticHomeomorph.symm ∘ clockSphereHomeomorph) ∘ π

omit [MeasurableSpace X] [BorelSpace X] in
theorem continuous_analyticClockObservation
    (π : X → ClockProductSphere q)
    (hπ : Continuous π) :
    Continuous (analyticClockObservation π) :=
  continuous_toAnalytic.comp hπ

/-- The physical phase observation, converted from radians to additive
turns. -/
def phaseInTurnsObservation
    (π : X → ClockProductSphere q) :
    X → UnitAddTorus (Fin q) :=
  (HGAS.Clocks.PhaseTorusFlow.phaseTorusToTurns ∘
    phaseProjection) ∘
      analyticClockObservation π

omit [MeasurableSpace X] [BorelSpace X] in
theorem continuous_phaseInTurnsObservation
    (π : X → ClockProductSphere q)
    (hπ : Continuous π) :
    Continuous (phaseInTurnsObservation π) :=
  (HGAS.Clocks.PhaseTorusFlow.continuous_phaseTorusToTurns.comp
    continuous_phaseProjection).comp
      (continuous_analyticClockObservation π hπ)

/-- The ambient invariant probability supplied by the orbitwise
time-change theorem. -/
def ambientClockInvariant
    (ϕ : Flow ℝ X)
    (p : Fin q → ℕ)
    (π : X → ClockProductSphere q)
    (hπ : Continuous π)
    (f : X →ᵇ ℝ≥0)
    (hchange :
      IsObservedGeneratorTimeChange
        ϕ (ambientClockC1ODEFlow (primeClockCodes p))
        (ambientClockObservation π) f)
    (η : InvariantProbabilityMeasure ϕ)
    (a : ℝ≥0) (ha : a ≠ 0)
    (hmass :
      ∫⁻ x, (f x : ENNReal)
          ∂(η.measure : Measure X) =
        (a : ENNReal)) :
    InvariantProbabilityMeasure
      (ambientClockC1ODEFlow (primeClockCodes p)).flow :=
  targetInvariantProbabilityOfObservedTimeChange
    ϕ (ambientClockC1ODEFlow (primeClockCodes p))
    (ambientClockObservation π) f
    (continuous_ambientClockObservation π hπ)
    hchange η a ha hmass

/-- The normalized-density ambient pushforward gives full mass to the
literal product of clock circles. -/
theorem ambientClockInvariant_full_clockSphereSet
    (ϕ : Flow ℝ X)
    (p : Fin q → ℕ)
    (π : X → ClockProductSphere q)
    (hπ : Continuous π)
    (f : X →ᵇ ℝ≥0)
    (hchange :
      IsObservedGeneratorTimeChange
        ϕ (ambientClockC1ODEFlow (primeClockCodes p))
        (ambientClockObservation π) f)
    (η : InvariantProbabilityMeasure ϕ)
    (a : ℝ≥0) (ha : a ≠ 0)
    (hmass :
      ∫⁻ x, (f x : ENNReal)
          ∂(η.measure : Measure X) =
        (a : ENNReal)) :
    (((ambientClockInvariant
          ϕ p π hπ f hchange η a ha hmass).measure :
        ProbabilityMeasure (ClockAmbient q)) :
      Measure (ClockAmbient q))
        (clockSphereSet q) = 1 := by
  simp only [ambientClockInvariant,
    targetInvariantProbabilityOfObservedTimeChange,
    ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_apply
    (continuous_ambientClockObservation π hπ).measurable
    measurableSet_clockSphereSet]
  have hpreimage :
      ambientClockObservation π ⁻¹' clockSphereSet q =
        Set.univ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ, iff_true]
    exact (π x).2
  rw [hpreimage, measure_univ]

/-- Restrict the ambient invariant probability to the clock-sphere subtype
and transparently identify the restricted flow with the canonical compact
clock flow. -/
def clockSphereInvariant
    (ϕ : Flow ℝ X)
    (p : Fin q → ℕ)
    (hp : ∀ i, (p i).Prime)
    (π : X → ClockProductSphere q)
    (hπ : Continuous π)
    (f : X →ᵇ ℝ≥0)
    (hchange :
      IsObservedGeneratorTimeChange
        ϕ (ambientClockC1ODEFlow (primeClockCodes p))
        (ambientClockObservation π) f)
    (η : InvariantProbabilityMeasure ϕ)
    (a : ℝ≥0) (ha : a ≠ 0)
    (hmass :
      ∫⁻ x, (f x : ENNReal)
          ∂(η.measure : Measure X) =
        (a : ENNReal)) :
    InvariantProbabilityMeasure
      (clockSphereFlow
        (fun i ↦
          (RationalCode.decode (primeClockCodes p i) : ℝ))
        (primeClockCodes_gt_one p hp)) :=
  InvariantProbabilityMeasure.transportFlow
    (restrict_ambientClockFlow_eq_clockSphereFlow
      (primeClockCodes p) (primeClockCodes_gt_one p hp))
    (InvariantProbabilityMeasure.restrictToFullMeasureInvariant
      (ambientClockInvariant
        ϕ p π hπ f hchange η a ha hmass)
      measurableSet_clockSphereSet
      (ambientClockInvariant_full_clockSphereSet
        ϕ p π hπ f hchange η a ha hmass)
      (isInvariant_clockSphereSet
        (primeClockCodes p) (primeClockCodes_gt_one p hp)))

/-- The restricted sphere measure is exactly the direct source-density
pushforward by `π`. -/
theorem clockSphereInvariant_measure_eq_map
    (ϕ : Flow ℝ X)
    (p : Fin q → ℕ)
    (hp : ∀ i, (p i).Prime)
    (π : X → ClockProductSphere q)
    (hπ : Continuous π)
    (f : X →ᵇ ℝ≥0)
    (hchange :
      IsObservedGeneratorTimeChange
        ϕ (ambientClockC1ODEFlow (primeClockCodes p))
        (ambientClockObservation π) f)
    (η : InvariantProbabilityMeasure ϕ)
    (a : ℝ≥0) (ha : a ≠ 0)
    (hmass :
      ∫⁻ x, (f x : ENNReal)
          ∂(η.measure : Measure X) =
        (a : ENNReal)) :
    (clockSphereInvariant
        ϕ p hp π hπ f hchange η a ha hmass).measure =
      (sourceClockDensityProbability ϕ η f a ha hmass).map
        hπ.measurable.aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  apply
    (MeasurableEmbedding.subtype_coe
      (measurableSet_clockSphereSet :
        MeasurableSet (clockSphereSet q))).map_injective
  have hrestrict :=
    InvariantProbabilityMeasure.map_restrictToFullMeasureInvariant_measure
      (ambientClockInvariant
        ϕ p π hπ f hchange η a ha hmass)
      (measurableSet_clockSphereSet :
        MeasurableSet (clockSphereSet q))
      (ambientClockInvariant_full_clockSphereSet
        ϕ p π hπ f hchange η a ha hmass)
      (isInvariant_clockSphereSet
        (primeClockCodes p) (primeClockCodes_gt_one p hp))
  calc
    Measure.map ((↑) : ClockProductSphere q → ClockAmbient q)
        ((clockSphereInvariant
            ϕ p hp π hπ f hchange η a ha hmass).measure :
          Measure (ClockProductSphere q)) =
        ((ambientClockInvariant
            ϕ p π hπ f hchange η a ha hmass).measure :
          Measure (ClockAmbient q)) := by
      simpa only [clockSphereInvariant,
        InvariantProbabilityMeasure.transportFlow_measure] using
          hrestrict
    _ = Measure.map ((↑) : ClockProductSphere q → ClockAmbient q)
        (((sourceClockDensityProbability ϕ η f a ha hmass).map
            hπ.measurable.aemeasurable :
          ProbabilityMeasure (ClockProductSphere q)) :
          Measure (ClockProductSphere q)) := by
      simp only [ambientClockInvariant,
        targetInvariantProbabilityOfObservedTimeChange,
        ProbabilityMeasure.toMeasure_map]
      rw [Measure.map_map measurable_subtype_coe hπ.measurable]
      rfl

/-- Analytic invariant probability induced by the transparent restricted
clock-sphere probability. -/
def analyticClockInvariant
    (ϕ : Flow ℝ X)
    (p : Fin q → ℕ)
    (hp : ∀ i, (p i).Prime)
    (π : X → ClockProductSphere q)
    (hπ : Continuous π)
    (f : X →ᵇ ℝ≥0)
    (hchange :
      IsObservedGeneratorTimeChange
        ϕ (ambientClockC1ODEFlow (primeClockCodes p))
        (ambientClockObservation π) f)
    (η : InvariantProbabilityMeasure ϕ)
    (a : ℝ≥0) (ha : a ≠ 0)
    (hmass :
      ∫⁻ x, (f x : ENNReal)
          ∂(η.measure : Measure X) =
        (a : ENNReal)) :
    InvariantProbabilityMeasure
      (ControllerPhaseFlow.controllerPhaseFlow
        (fun i ↦
          (RationalCode.decode (primeClockCodes p i) : ℝ))
        (primeClockCodes_gt_one p hp)) :=
  (clockSphereInvariant
      ϕ p hp π hπ f hchange η a ha hmass).mapEquivariant
    (analyticHomeomorph.symm ∘ clockSphereHomeomorph)
    continuous_toAnalytic
    (toAnalytic_semiconj
      (fun i ↦
        (RationalCode.decode (primeClockCodes p i) : ℝ))
      (primeClockCodes_gt_one p hp))

theorem analyticClockInvariant_measure_eq_map
    (ϕ : Flow ℝ X)
    (p : Fin q → ℕ)
    (hp : ∀ i, (p i).Prime)
    (π : X → ClockProductSphere q)
    (hπ : Continuous π)
    (f : X →ᵇ ℝ≥0)
    (hchange :
      IsObservedGeneratorTimeChange
        ϕ (ambientClockC1ODEFlow (primeClockCodes p))
        (ambientClockObservation π) f)
    (η : InvariantProbabilityMeasure ϕ)
    (a : ℝ≥0) (ha : a ≠ 0)
    (hmass :
      ∫⁻ x, (f x : ENNReal)
          ∂(η.measure : Measure X) =
        (a : ENNReal)) :
    (analyticClockInvariant
        ϕ p hp π hπ f hchange η a ha hmass).measure =
      (sourceClockDensityProbability ϕ η f a ha hmass).map
        (continuous_analyticClockObservation π hπ).measurable.aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [analyticClockInvariant,
    InvariantProbabilityMeasure.mapEquivariant_measure,
    ProbabilityMeasure.toMeasure_map]
  rw [clockSphereInvariant_measure_eq_map
    ϕ p hp π hπ f hchange η a ha hmass]
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map continuous_toAnalytic.measurable hπ.measurable]
  rfl

/-- **Abstract observed-clock Haar theorem.**  A normalized positive clock
density has Haar phase marginal whenever its clock-sphere observation
follows the distinct-prime coupled generator after the corresponding
time change. -/
theorem phaseHaar_of_observedTimeChange
    (ϕ : Flow ℝ X)
    (p : Fin q → ℕ)
    (hp : ∀ i, (p i).Prime)
    (hinjective : Function.Injective p)
    (π : X → ClockProductSphere q)
    (hπ : Continuous π)
    (f : X →ᵇ ℝ≥0)
    (hchange :
      IsObservedGeneratorTimeChange
        ϕ (ambientClockC1ODEFlow (primeClockCodes p))
        (ambientClockObservation π) f)
    (η : InvariantProbabilityMeasure ϕ)
    (a : ℝ≥0) (ha : a ≠ 0)
    (hmass :
      ∫⁻ x, (f x : ENNReal)
          ∂(η.measure : Measure X) =
        (a : ENNReal)) :
    (sourceClockDensityProbability ϕ η f a ha hmass).map
        (continuous_phaseInTurnsObservation π hπ).measurable.aemeasurable =
      HGAS.Clocks.RadicalClock.torusHaarProbability := by
  let μDecoded :=
    analyticClockInvariant
      ϕ p hp π hπ f hchange η a ha hmass
  let μPrime :=
    μDecoded.transportFlow (decodedPrimeClockFlow_eq p hp)
  have hhaar :=
    HGAS.Clocks.NonergodicControllerPhaseHaar.phaseHaar_of_invariantProbability
      p hp hinjective μPrime.measure μPrime.invariant
  apply ProbabilityMeasure.toMeasure_injective
  have hhaarMeasure :=
    congrArg ProbabilityMeasure.toMeasure hhaar
  simp only [μPrime, μDecoded,
    InvariantProbabilityMeasure.transportFlow_measure] at hhaarMeasure
  simp only [ProbabilityMeasure.toMeasure_map] at hhaarMeasure ⊢
  rw [analyticClockInvariant_measure_eq_map
    ϕ p hp π hπ f hchange η a ha hmass] at hhaarMeasure
  simpa only [ProbabilityMeasure.toMeasure_map,
    Measure.map_map
      HGAS.Clocks.PhaseTorusFlow.continuous_phaseTorusToTurns.measurable
      continuous_phaseProjection.measurable,
    Measure.map_map
      (HGAS.Clocks.PhaseTorusFlow.continuous_phaseTorusToTurns.comp
        continuous_phaseProjection).measurable
      (continuous_analyticClockObservation π hπ).measurable,
    phaseInTurnsObservation] using hhaarMeasure

end HGAS.Clocks.ObservedTimeChangedControllerPhaseHaar
