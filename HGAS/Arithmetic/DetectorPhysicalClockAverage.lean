import HGAS.Arithmetic.DetectorInvariantAverage
import HGAS.Clocks.PhaseTorusFlow

/-!
# The detector average driven by literal physical phase circles

`DetectorInvariantAverage` requires a uniquely Haar additive-torus factor.
The polynomial clock, on the other hand, is naturally expressed as a product
of complex unit circles rotating with angular velocities in radians.

This module composes the two verified bridges.  Distinct prime controllers
give signed radical angular velocities; inverse angle coordinates divide
them by `2π`; common rescaling preserves nonresonance; and hence every
invariant joining has Haar detector marginal.  The negative detector's
maximal average is therefore strictly negative exactly for a solvable DQL
instance.
-/

noncomputable section

open Function MeasureTheory
open scoped BoundedContinuousFunction

namespace HGAS

variable {eqs vars : ℕ}

/-- Detector-to-maximal-average theorem with the Haar hypothesis discharged
by literal signed-radical physical phase clocks. -/
theorem maximalInvariantAverage_neg_halfDetector_physicalClocks_iff_solvable
    {X : Type*}
    [MetricSpace X] [CompactSpace X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X]
    (ϕ : Flow ℝ X)
    (primes : DetectorPhase eqs vars → ℕ)
    (hprime : ∀ i, (primes i).Prime)
    (hdistinct : Function.Injective primes)
    (sign : DetectorPhase eqs vars → ℤ)
    (hsign : ∀ i, sign i = 1 ∨ sign i = -1)
    (physicalPhase :
      X → (DetectorPhase eqs vars → Circle))
    (hphysicalPhase : Continuous physicalPhase)
    (hequivariant : ∀ t : ℝ,
      Function.Semiconj physicalPhase (ϕ t)
        (Clocks.PhaseTorusFlow.phaseTorusFlow
          (Clocks.RadicalIndependence.signedPrimeSqrtFrequency
            primes sign) t))
    (I : DQLSystem eqs vars) :
    Dynamics.maximalInvariantAverage ϕ
        ((-halfExpandedDetectorRealBCF I).compContinuous
          ⟨Clocks.PhaseTorusFlow.phaseTorusToTurns ∘ physicalPhase,
            Clocks.PhaseTorusFlow.continuous_phaseTorusToTurns.comp
              hphysicalPhase⟩) < 0 ↔
      I.Solvable := by
  let omega :
      DetectorPhase eqs vars → ℝ :=
    Clocks.PhaseTorusFlow.turnsFrequency
      (Clocks.RadicalIndependence.signedPrimeSqrtFrequency
        primes sign)
  let phase :
      X → UnitAddTorus (DetectorPhase eqs vars) :=
    Clocks.PhaseTorusFlow.phaseTorusToTurns ∘ physicalPhase
  have hphase : Continuous phase :=
    Clocks.PhaseTorusFlow.continuous_phaseTorusToTurns.comp
      hphysicalPhase
  have hphaseEquivariant :
      ∀ t : ℝ,
        Function.Semiconj phase (ϕ t)
          (Clocks.RadicalClock.torusTranslationFlow omega t) := by
    intro t
    exact
      (Clocks.PhaseTorusFlow.phaseTorusToTurns_semiconj _ t).comp_left
        (hequivariant t)
  have hHaar :
      ∀ μ : Dynamics.InvariantProbabilityMeasure ϕ,
        (μ.mapEquivariant phase hphase hphaseEquivariant).measure =
          Clocks.RadicalClock.torusHaarProbability := by
    intro μ
    exact
      Clocks.PhaseTorusFlow.physicalSignedRadicalPhase_equivariantMarginal_eq_haar
        primes hprime hdistinct sign hsign μ physicalPhase
        hphysicalPhase hequivariant
  simpa only [phase] using
    (maximalInvariantAverage_neg_halfDetector_iff_solvable
      ϕ omega phase hphase hphaseEquivariant hHaar I)

end HGAS
