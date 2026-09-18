import HGAS.Clocks.ErgodicControllerPhaseHaar
import HGAS.Dynamics.ErgodicFactor
import Mathlib.Tactic

/-!
# Locked radical clocks inside an arbitrary ergodic joining

The controller--phase theorem classifies ergodic invariant probabilities
of the literal coupled clock flow itself.  In the final source the clocks
occur as one factor of a larger joining with modular, Jacobi, oscillator,
and accumulator coordinates.

This file supplies the reusable factor bridge.  A continuous equivariant
observation of an ergodic invariant probability is again ergodic and
invariant.  Applying the coupled-clock classification to that pushforward
selects one locked controller-sign tuple and proves Haar measure for the
physical phase marginal in turns.  No product decomposition or
independence of the unobserved coordinates is assumed.
-/

noncomputable section

open Complex Filter Function MeasureTheory Set

namespace HGAS.Clocks.ErgodicControllerPhaseFactorHaar

local instance : MeasurableSpace Circle :=
  borel Circle

local instance : BorelSpace Circle :=
  ⟨rfl⟩

variable {d X : Type*} [Finite d] [Fintype d]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

abbrev ClockState (d : Type*) :=
  HGAS.Clocks.ControllerPhaseFlow.State d

/-- Full joining-robust locked-clock theorem.  The conclusion is stated for
the observed clock marginal `ν`; because `ν` is literally the pushforward
of `μ`, every assertion is automatically an assertion about the clock
factor of the original joining. -/
theorem exists_lockedController_sign_and_phaseHaar_of_factor
    (Φ : Flow ℝ X)
    (p : d → ℕ)
    (hp : ∀ i : d, (p i).Prime)
    (hinjective : Function.Injective p)
    (π : X → ClockState d)
    (hπ : Continuous π)
    (hequiv :
      ∀ t : ℝ,
        Function.Semiconj π (Φ t)
          (HGAS.Clocks.ControllerPhaseFlow.controllerPhaseFlow
            (fun i ↦ (p i : ℝ))
            (HGAS.Clocks.ErgodicControllerPhaseHaar.primeControllerParameters_gt_one
              p hp) t))
    (μ : ProbabilityMeasure X)
    (hμ : HGAS.Dynamics.IsErgodicInvariantProbability Φ μ) :
    let ν : ProbabilityMeasure (ClockState d) :=
      μ.map hπ.measurable.aemeasurable
    ∃ (x : d → Circle) (sign : d → ℤ),
      (∀ i,
        x i ∈ HGAS.Clocks.ControllerFlow.controllerEquilibria
          (p i : ℝ)) ∧
      ν.map
          (HGAS.Clocks.ErgodicControllerPhaseHaar.continuous_controllerProjection
            (d := d)).measurable.aemeasurable =
        MeasureTheory.diracProba x ∧
      (∀ᵐ z ∂(ν : Measure (ClockState d)), z.1 = x) ∧
      (∀ i, sign i = 1 ∨ sign i = -1) ∧
      (fun i ↦ (p i : ℝ) * (x i : ℂ).re) =
        HGAS.Clocks.RadicalIndependence.signedPrimeSqrtFrequency
          p sign ∧
      (ν.map
          (HGAS.Clocks.ErgodicControllerPhaseHaar.continuous_phaseProjection
            (d := d)).measurable.aemeasurable).map
          (HGAS.Clocks.PhaseTorusFlow.continuous_phaseTorusToTurns
            |>.measurable.aemeasurable) =
        HGAS.Clocks.RadicalClock.torusHaarProbability := by
  let ν : ProbabilityMeasure (ClockState d) :=
    μ.map hπ.measurable.aemeasurable
  have hν :
      HGAS.Dynamics.IsErgodicInvariantProbability
        (HGAS.Clocks.ControllerPhaseFlow.controllerPhaseFlow
          (fun i ↦ (p i : ℝ))
          (HGAS.Clocks.ErgodicControllerPhaseHaar.primeControllerParameters_gt_one
            p hp))
        ν := by
    exact hμ.mapEquivariant π hπ hequiv
  exact
    HGAS.Clocks.ErgodicControllerPhaseHaar.exists_lockedController_sign_and_phaseHaar
      p hp hinjective ν hν

omit [Fintype d] in
/-- The selected joint controller equality can also be pulled all the way
back to the original joining.  This is often the most convenient form
when simplifying other source coordinates almost everywhere. -/
theorem ae_controller_eq_of_factor_locked
    (π : X → ClockState d)
    (hπ : Continuous π)
    (μ : ProbabilityMeasure X)
    (x : d → Circle)
    (hae :
      ∀ᵐ z ∂((μ.map hπ.measurable.aemeasurable :
        ProbabilityMeasure (ClockState d)) :
          Measure (ClockState d)), z.1 = x) :
    ∀ᵐ y ∂(μ : Measure X), (π y).1 = x := by
  exact ae_of_ae_map hπ.measurable.aemeasurable hae

end HGAS.Clocks.ErgodicControllerPhaseFactorHaar
