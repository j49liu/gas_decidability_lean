import HGAS.Arithmetic.DetectorInvariantAverage
import HGAS.Arithmetic.UnconditionalFixedDQL

/-!
# Universal halting as a maximal detector average

`DetectorInvariantAverage` proves the arithmetic-to-dynamics statement for
an arbitrary diagonal--quadratic--linear system.  This file specializes it
to the unconditional fixed-resource universal-halting family.

The crucial resource fact is that the phase torus below has one fixed
dimension: the encoded program/input changes coefficients of the DQL
system, but not its numbers of rows or variables.  Thus one compact source
flow, one detector-phase factor map, and one frequency vector can serve all
inputs.

The dynamical realization remains explicit in the hypotheses.  We assume a
compact source flow, a continuous equivariant map to the detector torus,
and that every invariant probability has normalized Haar phase marginal.
Under exactly these assumptions, strict negativity of the maximal average
of the negative half-detector is equivalent to halting of the encoded
universal program.
-/

namespace HGAS

open Function MeasureTheory
open scoped BoundedContinuousFunction

noncomputable section

/-- The one fixed phase-index type used by every member of the
fixed-resource universal-halting detector family. -/
abbrev UniversalHaltingFixedDetectorPhase :=
  DetectorPhase
    UniversalHalting.unconditionalFixedDQLEquationCount
    UniversalHalting.unconditionalFixedDQLVariableCount

/-- Negative real half-detector for the fixed-resource DQL instance
encoding `input`.  Its domain is independent of `input`. -/
def unconditionalUniversalHaltingNegHalfDetectorBCF
    (input : ℕ) :
    UnitAddTorus UniversalHaltingFixedDetectorPhase →ᵇ ℝ :=
  -halfExpandedDetectorRealBCF
    (UniversalHalting.unconditionalUniversalHaltingFixedDQL input)

@[simp]
theorem unconditionalUniversalHaltingNegHalfDetectorBCF_apply
    (input : ℕ)
    (phase : UnitAddTorus UniversalHaltingFixedDetectorPhase) :
    unconditionalUniversalHaltingNegHalfDetectorBCF input phase =
      -(expandedDetector (1 / 2 : ℝ) (1 / 2 : ℝ)
        (UniversalHalting.unconditionalUniversalHaltingFixedDQL input)
        phase).re :=
  rfl

/-- **Fixed-resource universal-halting detector theorem.**

For a compact source realization whose detector-phase marginal is Haar for
every invariant probability, the maximal invariant average of the negative
half-detector is strictly negative exactly when the encoded universal
program/input halts.

All dynamical assumptions are parameters: this theorem does not claim that
the polynomial source realization has already been constructed. -/
theorem
    maximalInvariantAverage_unconditionalUniversalHaltingNegHalfDetector_iff
    {X : Type*}
    [MetricSpace X] [CompactSpace X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X]
    (ϕ : Flow ℝ X)
    (ω : UniversalHaltingFixedDetectorPhase → ℝ)
    (phase :
      X → UnitAddTorus UniversalHaltingFixedDetectorPhase)
    (hphase : Continuous phase)
    (hequiv :
      ∀ t : ℝ,
        Function.Semiconj phase (ϕ t)
          (Clocks.RadicalClock.torusTranslationFlow ω t))
    (hHaar :
      ∀ μ : Dynamics.InvariantProbabilityMeasure ϕ,
        (μ.mapEquivariant phase hphase hequiv).measure =
          Clocks.RadicalClock.torusHaarProbability)
    (input : ℕ) :
    Dynamics.maximalInvariantAverage ϕ
        ((unconditionalUniversalHaltingNegHalfDetectorBCF input)
          |>.compContinuous ⟨phase, hphase⟩) < 0 ↔
      UniversalHalting.Predicate input := by
  have hdetector :=
    maximalInvariantAverage_neg_halfDetector_iff_solvable
      ϕ ω phase hphase hequiv hHaar
      (UniversalHalting.unconditionalUniversalHaltingFixedDQL input)
  have hdetector' :
      Dynamics.maximalInvariantAverage ϕ
          ((unconditionalUniversalHaltingNegHalfDetectorBCF input)
            |>.compContinuous ⟨phase, hphase⟩) < 0 ↔
        (UniversalHalting.unconditionalUniversalHaltingFixedDQL
          input).Solvable := by
    simpa only [
      unconditionalUniversalHaltingNegHalfDetectorBCF]
      using hdetector
  exact hdetector'.trans
    (UniversalHalting.unconditionalUniversalHaltingFixedDQL_solvable_iff
      input)

/-- Consequently, for any one source realization satisfying the displayed
factor hypotheses, the strict-negativity predicate of its fixed-dimensional
detector family is not computable. -/
theorem
    maximalInvariantAverage_unconditionalUniversalHaltingNegHalfDetector_not_computable
    {X : Type*}
    [MetricSpace X] [CompactSpace X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X]
    (ϕ : Flow ℝ X)
    (ω : UniversalHaltingFixedDetectorPhase → ℝ)
    (phase :
      X → UnitAddTorus UniversalHaltingFixedDetectorPhase)
    (hphase : Continuous phase)
    (hequiv :
      ∀ t : ℝ,
        Function.Semiconj phase (ϕ t)
          (Clocks.RadicalClock.torusTranslationFlow ω t))
    (hHaar :
      ∀ μ : Dynamics.InvariantProbabilityMeasure ϕ,
        (μ.mapEquivariant phase hphase hequiv).measure =
          Clocks.RadicalClock.torusHaarProbability) :
    ¬ComputablePred
      (fun input : ℕ ↦
        Dynamics.maximalInvariantAverage ϕ
            ((unconditionalUniversalHaltingNegHalfDetectorBCF input)
              |>.compContinuous ⟨phase, hphase⟩) < 0) := by
  intro hcomputable
  apply UniversalHalting.predicate_not_computable
  exact
    ComputablePred.of_eq hcomputable fun input ↦
      maximalInvariantAverage_unconditionalUniversalHaltingNegHalfDetector_iff
        ϕ ω phase hphase hequiv hHaar input

end

end HGAS
