import HGAS.Clocks.ObservedTimeChangedControllerPhaseHaar
import HGAS.Dynamics.CanonicalBoundedDensity
import Mathlib.Tactic

/-!
# Canonically normalized observed-clock Haar theorem

`ObservedTimeChangedControllerPhaseHaar` states the complete abstract
clock theorem with an explicit normalizing constant and mass identity.
Those parameters are convenient for algebraic bookkeeping, but they are
not independent data.  For a bounded continuous nonnegative clock on a
probability space, finite mass is automatic; if the clock is nonzero
almost everywhere, its mass is automatically positive.

The theorem below is therefore a normalization-parameter-free public
interface: the only density hypothesis is the dynamically meaningful one

```
                         f ≠ 0  almost everywhere.
```

All normalization data are constructed canonically.
-/

noncomputable section

open Function MeasureTheory
open scoped BoundedContinuousFunction ENNReal NNReal

namespace HGAS.Clocks.ObservedTimeChangedControllerPhaseCanonicalHaar

open HGAS
open HGAS.Dynamics
open HGAS.Clocks.ControllerPhaseProductC1CutoffFlow
open HGAS.Clocks.ControllerPhaseProductSphereFlow
open HGAS.Clocks.ObservedTimeChangedControllerPhaseHaar

variable {q : ℕ}
variable {X : Type*}
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **Canonical abstract observed-clock Haar theorem.**  An observed
time-changed product of distinct prime clocks has Haar physical phase
marginal after weighting the source invariant probability by its clock
density.  The normalizing mass is constructed from the density itself. -/
theorem phaseHaar_of_observedTimeChange_canonical
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
    (hpositive :
      ∀ᵐ x ∂(η.measure : Measure X), f x ≠ 0) :
    (canonicalNormalizedDensityProbability
        η.measure f hpositive).map
        (continuous_phaseInTurnsObservation π hπ).measurable.aemeasurable =
      HGAS.Clocks.RadicalClock.torusHaarProbability := by
  let a : ℝ≥0 := boundedDensityMass η.measure f
  have ha : a ≠ 0 :=
    boundedDensityMass_ne_zero_of_ae η.measure f hpositive
  have hmass :
      ∫⁻ x, (f x : ENNReal)
          ∂(η.measure : Measure X) =
        (a : ENNReal) :=
    (coe_boundedDensityMass η.measure f).symm
  have hhaar :=
    phaseHaar_of_observedTimeChange
      ϕ p hp hinjective π hπ f hchange η a ha hmass
  simpa only [canonicalNormalizedDensityProbability,
    sourceClockDensityProbability, a, ha, hmass] using hhaar

end HGAS.Clocks.ObservedTimeChangedControllerPhaseCanonicalHaar
