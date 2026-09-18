import HGAS.Clocks.NonergodicControllerPhaseHaar
import HGAS.Dynamics.NormalizedDensityEquivalence
import HGAS.Modular.TwoControllerLinkedJacobiMixedClockEquator
import HGAS.Modular.TwoControllerLinkedJacobiMixedClockMeasureDiagram
import Mathlib.Tactic

/-!
# Haar phase marginal for the faithful mixed two-clock source

This is the end-to-end clock theorem needed by the mixed linked-Jacobi
compiler.  We fix the two controller parameters to the distinct primes
`2` and `3`, using rational finite codes.  Starting with an invariant
probability of the mixed compact base and a nonzero total clock mass:

1. reweight by the common slowdown `w⁸`;
2. transport the reweighted probability through the exact polynomial
   clock observation;
3. invoke the non-ergodic coupled-clock classification; and
4. use the commuting measure diagram to pull the conclusion back.

The resulting physical phase marginal, measured in turns, is exactly Haar
on the two-torus.  No ergodicity of the reweighted clock probability is
required.

If the original compact-base probability is ergodic, the equator theorem
also shows that the slowdown is nonzero almost everywhere.  Hence the
original and normalized-density probabilities have identical null sets.
This second conclusion is kept separate from the Haar statement because
the latter does not require source ergodicity.
-/

noncomputable section

open Function MeasureTheory Set
open scoped ENNReal NNReal

namespace HGAS.Modular.TwoControllerLinkedJacobiMixedClockHaar

open HGAS
open HGAS.Dynamics
open HGAS.Clocks
open HGAS.Clocks.ErgodicControllerPhaseHaar
open TwoControllerLinkedJacobiMixedClockC1Target
open TwoControllerLinkedJacobiMixedClockDynamics
open TwoControllerLinkedJacobiMixedClockEquator
open TwoControllerLinkedJacobiMixedClockMeasureDiagram
open TwoControllerLinkedJacobiMixedClockProjection

local instance : MeasurableSpace Circle :=
  borel Circle

local instance : BorelSpace Circle :=
  ⟨rfl⟩

/-- The two fixed controller primes. -/
def controllerPrimes : Fin 2 → ℕ :=
  ![2, 3]

theorem controllerPrimes_prime :
    ∀ i, (controllerPrimes i).Prime := by
  intro i
  fin_cases i <;> norm_num [controllerPrimes]

theorem controllerPrimes_injective :
    Function.Injective controllerPrimes := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [controllerPrimes]

/-- Rational finite code for the first prime controller. -/
def omegaPrimeCode : RationalCode :=
  RationalCode.ofNat 2

/-- Rational finite code for the second prime controller. -/
def numberPrimeCode : RationalCode :=
  RationalCode.ofNat 3

@[simp]
theorem decode_twoPrimeClockCodes
    (i : Fin 2) :
    (RationalCode.decode
        (twoClockCodes omegaPrimeCode numberPrimeCode i) : ℝ) =
      (controllerPrimes i : ℝ) := by
  fin_cases i <;>
    norm_num [twoClockCodes, omegaPrimeCode, numberPrimeCode,
      controllerPrimes, RationalCode.decode_ofNat]

/-- Both decoded rational controller parameters are greater than one. -/
theorem twoPrimeClockParameters_gt_one :
    ∀ i : Fin 2,
      (1 : ℝ) <
        (RationalCode.decode
          (twoClockCodes omegaPrimeCode numberPrimeCode i) : ℝ) := by
  intro i
  rw [decode_twoPrimeClockCodes]
  exact_mod_cast
    (controllerPrimes_prime i).one_lt

/-- Equality between the decoded-code analytic clock flow and the standard
prime-parameter form expected by the Haar-classification theorem. -/
theorem decodedClockFlow_eq_primeClockFlow :
    HGAS.Clocks.ControllerPhaseFlow.controllerPhaseFlow
        (fun i ↦
          (RationalCode.decode
            (twoClockCodes omegaPrimeCode numberPrimeCode i) : ℝ))
        twoPrimeClockParameters_gt_one =
      HGAS.Clocks.ControllerPhaseFlow.controllerPhaseFlow
        (fun i ↦ (controllerPrimes i : ℝ))
        (primeControllerParameters_gt_one
          controllerPrimes controllerPrimes_prime) := by
  congr 2
  funext i
  exact decode_twoPrimeClockCodes i

/-- Read the two physical phase circles of a mixed source point in additive
turn coordinates. -/
def mixedClockPhaseInTurns :
    TwoControllerLinkedJacobiMixedClockProjection.BaseSpace →
      UnitAddTorus (Fin 2) :=
  (HGAS.Clocks.PhaseTorusFlow.phaseTorusToTurns ∘
    phaseProjection) ∘
      analyticClockObservation

theorem continuous_mixedClockPhaseInTurns :
    Continuous mixedClockPhaseInTurns :=
  (HGAS.Clocks.PhaseTorusFlow.continuous_phaseTorusToTurns.comp
    continuous_phaseProjection).comp
      continuous_analyticClockObservation

/-- The direct phase pushforward of the normalized mixed-source density is
the phase marginal of the analytic clock invariant. -/
theorem map_mixedClockPhaseInTurns_eq_analyticPhaseMarginal
    (η :
      InvariantProbabilityMeasure
        (mixedBaseFlow omegaPrimeCode numberPrimeCode))
    (a : ℝ≥0) (ha : a ≠ 0)
    (hmass :
      ∫⁻ y, (clockSlowdownBCF y : ENNReal)
          ∂(η.measure :
            Measure
              TwoControllerLinkedJacobiMixedClockProjection.BaseSpace) =
        (a : ENNReal)) :
    (mixedClockDensityProbability
        omegaPrimeCode numberPrimeCode η a ha hmass).map
        continuous_mixedClockPhaseInTurns.measurable.aemeasurable =
      (((diagramAnalyticClockInvariant
          omegaPrimeCode numberPrimeCode
          twoPrimeClockParameters_gt_one
          η a ha hmass).measure.map
        continuous_phaseProjection.measurable.aemeasurable).map
          (HGAS.Clocks.PhaseTorusFlow.continuous_phaseTorusToTurns.measurable.aemeasurable)) := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [diagramAnalyticClockInvariant_measure_eq_map_analyticClockObservation
    omegaPrimeCode numberPrimeCode
    twoPrimeClockParameters_gt_one η a ha hmass]
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map
    HGAS.Clocks.PhaseTorusFlow.continuous_phaseTorusToTurns.measurable
    continuous_phaseProjection.measurable]
  rw [Measure.map_map
    (HGAS.Clocks.PhaseTorusFlow.continuous_phaseTorusToTurns.comp
      continuous_phaseProjection).measurable
    continuous_analyticClockObservation.measurable]
  rfl

/-- **Weighted mixed-clock Haar theorem.**  For every invariant mixed-base
probability with nonzero total slowdown, its normalized `w⁸`-density has
Haar physical phase marginal in turns. -/
theorem mixedClockDensity_phaseHaar
    (η :
      InvariantProbabilityMeasure
        (mixedBaseFlow omegaPrimeCode numberPrimeCode))
    (a : ℝ≥0) (ha : a ≠ 0)
    (hmass :
      ∫⁻ y, (clockSlowdownBCF y : ENNReal)
          ∂(η.measure :
            Measure
              TwoControllerLinkedJacobiMixedClockProjection.BaseSpace) =
        (a : ENNReal)) :
    (mixedClockDensityProbability
        omegaPrimeCode numberPrimeCode η a ha hmass).map
        continuous_mixedClockPhaseInTurns.measurable.aemeasurable =
      HGAS.Clocks.RadicalClock.torusHaarProbability := by
  let μDecoded :=
    diagramAnalyticClockInvariant
      omegaPrimeCode numberPrimeCode
      twoPrimeClockParameters_gt_one
      η a ha hmass
  let μPrime :=
    μDecoded.transportFlow decodedClockFlow_eq_primeClockFlow
  have hhaar :=
    HGAS.Clocks.NonergodicControllerPhaseHaar.phaseHaar_of_invariantProbability
        controllerPrimes controllerPrimes_prime
        controllerPrimes_injective
        μPrime.measure μPrime.invariant
  rw [map_mixedClockPhaseInTurns_eq_analyticPhaseMarginal
    η a ha hmass]
  simpa only [μPrime, μDecoded,
    InvariantProbabilityMeasure.transportFlow_measure] using hhaar

/-- For an ergodic mixed-base probability of nonzero clock mass, the
original probability and its normalized clock-density probability satisfy
exactly the same almost-everywhere propositions. -/
theorem ae_mixedClockDensityProbability_iff
    (η :
      InvariantProbabilityMeasure
        (mixedBaseFlow omegaPrimeCode numberPrimeCode))
    (hη :
      IsErgodicInvariantProbability
        (mixedBaseFlow omegaPrimeCode numberPrimeCode) η.measure)
    (a : ℝ≥0) (ha : a ≠ 0)
    (hmass :
      ∫⁻ y, (clockSlowdownBCF y : ENNReal)
          ∂(η.measure :
            Measure
              TwoControllerLinkedJacobiMixedClockProjection.BaseSpace) =
        (a : ENNReal))
    (p :
      TwoControllerLinkedJacobiMixedClockProjection.BaseSpace → Prop) :
    (∀ᵐ y ∂
        ((mixedClockDensityProbability
            omegaPrimeCode numberPrimeCode η a ha hmass :
          ProbabilityMeasure
            TwoControllerLinkedJacobiMixedClockProjection.BaseSpace) :
          Measure
            TwoControllerLinkedJacobiMixedClockProjection.BaseSpace), p y) ↔
      ∀ᵐ y ∂(η.measure :
        Measure
          TwoControllerLinkedJacobiMixedClockProjection.BaseSpace), p y := by
  apply ae_normalizedDensityProbability_iff
  have hraw :=
    clockSlowdown_ae_ne_zero_of_mass_ne_zero
      omegaPrimeCode numberPrimeCode η.measure hη a ha hmass
  filter_upwards [hraw] with y hy
  simpa only [clockSlowdownBCF_apply, ne_eq, NNReal.eq_iff,
    clockSlowdownNNReal_coe, NNReal.coe_zero] using hy

end HGAS.Modular.TwoControllerLinkedJacobiMixedClockHaar
