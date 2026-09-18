import HGAS.Arithmetic.DetectorPhysicalClockAverage
import HGAS.Arithmetic.UnconditionalFixedDetectorInvariantAverage

/-!
# Universal halting detector with physical radical clocks

This is the fixed-resource specialization of
`DetectorPhysicalClockAverage`.  The detector phase type is constant across
all inputs; distinct prime physical circles discharge the unique-Haar
marginal once and for all.  Only the detector coefficients depend on the
encoded universal-machine input.
-/

noncomputable section

open Function MeasureTheory
open scoped BoundedContinuousFunction

namespace HGAS

/-- Universal-halting maximal-average theorem with the phase-factor
hypothesis stated directly for literal complex circle rotations. -/
theorem
    maximalInvariantAverage_unconditionalUniversalHalting_physicalClocks_iff
    {X : Type*}
    [MetricSpace X] [CompactSpace X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X]
    (ϕ : Flow ℝ X)
    (primes : UniversalHaltingFixedDetectorPhase → ℕ)
    (hprime : ∀ i, (primes i).Prime)
    (hdistinct : Function.Injective primes)
    (sign : UniversalHaltingFixedDetectorPhase → ℤ)
    (hsign : ∀ i, sign i = 1 ∨ sign i = -1)
    (physicalPhase :
      X → (UniversalHaltingFixedDetectorPhase → Circle))
    (hphysicalPhase : Continuous physicalPhase)
    (hequivariant : ∀ t : ℝ,
      Function.Semiconj physicalPhase (ϕ t)
        (Clocks.PhaseTorusFlow.phaseTorusFlow
          (Clocks.RadicalIndependence.signedPrimeSqrtFrequency
            primes sign) t))
    (input : ℕ) :
    Dynamics.maximalInvariantAverage ϕ
        ((unconditionalUniversalHaltingNegHalfDetectorBCF input)
          |>.compContinuous
            ⟨Clocks.PhaseTorusFlow.phaseTorusToTurns ∘ physicalPhase,
              Clocks.PhaseTorusFlow.continuous_phaseTorusToTurns.comp
                hphysicalPhase⟩) < 0 ↔
      UniversalHalting.Predicate input := by
  have hdetector :=
    maximalInvariantAverage_neg_halfDetector_physicalClocks_iff_solvable
      ϕ primes hprime hdistinct sign hsign physicalPhase
      hphysicalPhase hequivariant
      (UniversalHalting.unconditionalUniversalHaltingFixedDQL input)
  have hdetector' :
      Dynamics.maximalInvariantAverage ϕ
          ((unconditionalUniversalHaltingNegHalfDetectorBCF input)
            |>.compContinuous
              ⟨Clocks.PhaseTorusFlow.phaseTorusToTurns ∘ physicalPhase,
                Clocks.PhaseTorusFlow.continuous_phaseTorusToTurns.comp
                  hphysicalPhase⟩) < 0 ↔
        (UniversalHalting.unconditionalUniversalHaltingFixedDQL input).Solvable := by
    simpa only [
      unconditionalUniversalHaltingNegHalfDetectorBCF] using hdetector
  exact hdetector'.trans
    (UniversalHalting.unconditionalUniversalHaltingFixedDQL_solvable_iff
      input)

end HGAS
