import HGAS.Dynamics.UniformNonescapeOccupationTightness
import HGAS.Modular.GammaTwoHaarPeriodicNull
import HGAS.Modular.GammaTwoUniformNonescape

/-!
# Unconditional occupation inputs for the level-two horocycle flow

The occupation-measure proof of the Dani--Smillie theorem was separated
in `GammaTwoOccupationReduction` into three inputs:

1. tightness of all integer occupation probabilities of a nonperiodic
   orbit;
2. zero periodic-horocycle mass for every occupation limit;
3. uniqueness of the invariant probability away from periodic
   horocycles.

The cusp-excursion proof in `GammaTwoUniformNonescape` now supplies the
first two inputs unconditionally.  This file records the import-chain all
the way to the pointwise and classification endpoints.  Its final
theorems deliberately retain exactly one hypothesis: the classical
good-return-time uniqueness statement.
-/

namespace HGAS.Modular

open _root_.MeasureTheory

noncomputable section

local instance gammaTwoFrameQuotientMetricSpaceForOccupationInputs :
    MetricSpace GammaTwoFrameQuotient :=
  TopologicalSpace.metrizableSpaceMetric GammaTwoFrameQuotient

/-- Every nonperiodic level-two horocycle has a tight family of integer
occupation probabilities.  This is the Prokhorov form of cusp
nonescape used by the occupation-measure endgame. -/
theorem gammaTwoNonperiodicOccupationTightness_unconditional :
    GammaTwoNonperiodicOccupationTightness := by
  intro q hq
  let occupations : ℕ →
      ProbabilityMeasure GammaTwoFrameQuotient :=
    HGAS.Dynamics.integerOrbitOccupationProbability
      gammaTwoHorocycleFlow q
  have hset :
      {μ : Measure GammaTwoFrameQuotient |
        ∃ m ∈ Set.range occupations, (m : Measure _) = μ} =
        Set.range
          (fun n ↦ (occupations n : Measure _)) := by
    ext μ
    constructor
    · rintro ⟨m, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨occupations n, ⟨n, rfl⟩, rfl⟩
  rw [hset]
  simpa only [occupations] using
    HGAS.Dynamics.isTight_integerOrbitOccupation_range_of_uniformRealOccupationNonescape
      gammaTwoHorocycleFlow
      (fun z ↦ ¬ IsPeriodicHorocyclePoint 1 z)
      gammaTwoUniformNonperiodicRealOccupationNonescape
      q hq

/-- For a chosen right-invariant probability, the sole remaining
occupation-measure input is uniqueness among invariant probabilities
which do not charge periodic horocycles. -/
theorem
    gammaTwoNonperiodicOrbitEquidistribution_of_offPeriodicUnique
    (ν : ProbabilityMeasure GammaTwoFrameQuotient)
    (hunique :
      GammaTwoInvariantProbabilityOffPeriodicUnique ν) :
    GammaTwoNonperiodicOrbitEquidistribution ν :=
  gammaTwoPointwiseHorocycleEquidistribution_of_occupation_inputs
    ν
    gammaTwoNonperiodicOccupationTightness_unconditional
    gammaTwoNonperiodicOccupationLimitsAvoidPeriodic_unconditional
    hunique

/-- Normalization-independent pointwise horocycle equidistribution,
reduced to the sole remaining good-return-time uniqueness input. -/
theorem
    gammaTwoPointwiseHorocycleEquidistribution_of_offPeriodicUnique
    (hunique :
      ∀ ν : ProbabilityMeasure GammaTwoFrameQuotient,
        IsRightInvariantFrameProbability ν →
          GammaTwoInvariantProbabilityOffPeriodicUnique ν) :
    GammaTwoPointwiseHorocycleEquidistribution :=
  gammaTwoPointwiseHorocycleEquidistribution_of_occupation_inputs'
    gammaTwoNonperiodicOccupationTightness_unconditional
    gammaTwoNonperiodicOccupationLimitsAvoidPeriodic_unconditional
    hunique

/-- Uniqueness relative to the chosen Haar probability automatically
gives the normalization-independent uniqueness input.  Indeed every
right-invariant probability is horocycle invariant and, by geodesic
renormalization, gives zero mass to periodic horocycles. -/
theorem gammaTwoOffPeriodicUnique_of_chosenHaar
    (hunique :
      GammaTwoInvariantProbabilityOffPeriodicUnique
        gammaTwoFrameHaarProbability) :
    ∀ ν : ProbabilityMeasure GammaTwoFrameQuotient,
      IsRightInvariantFrameProbability ν →
        GammaTwoInvariantProbabilityOffPeriodicUnique ν := by
  intro ν hν μ hμInvariant hμAvoidsPeriodic
  have hμHaar :
      μ = gammaTwoFrameHaarProbability :=
    hunique μ hμInvariant hμAvoidsPeriodic
  have hνHaar :
      ν = gammaTwoFrameHaarProbability :=
    hunique ν hν.horocycleInvariant
      hν.periodicHorocycleSet_measure_zero
  exact hμHaar.trans hνHaar.symm

/-- The complete Dani--Smillie classification now follows from exactly
the off-periodic invariant-probability uniqueness proposition.  Finite
Haar volume and all cusp-nonescape and periodic-mass inputs are already
unconditional in the import chain. -/
theorem gammaTwoDaniSmillieTheorem_of_offPeriodicUnique
    (hunique :
      ∀ ν : ProbabilityMeasure GammaTwoFrameQuotient,
        IsRightInvariantFrameProbability ν →
          GammaTwoInvariantProbabilityOffPeriodicUnique ν) :
    GammaTwoDaniSmillieTheorem :=
  gammaTwoDaniSmillieTheorem_of_occupation_inputs
    gammaTwoNonperiodicOccupationTightness_unconditional
    gammaTwoNonperiodicOccupationLimitsAvoidPeriodic_unconditional
    hunique

/-- Strongest chosen-normalization endpoint: Hubbard--Miller
Proposition 11 for the already constructed Haar probability is the sole
remaining hypothesis for the complete Dani--Smillie theorem. -/
theorem
    gammaTwoDaniSmillieTheorem_of_chosenHaar_offPeriodicUnique
    (hunique :
      GammaTwoInvariantProbabilityOffPeriodicUnique
        gammaTwoFrameHaarProbability) :
    GammaTwoDaniSmillieTheorem :=
  gammaTwoDaniSmillieTheorem_of_offPeriodicUnique
    (gammaTwoOffPeriodicUnique_of_chosenHaar hunique)

end

end HGAS.Modular
