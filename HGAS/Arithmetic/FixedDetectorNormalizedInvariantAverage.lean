import HGAS.Arithmetic.DetectorInvariantAverage
import HGAS.Arithmetic.UnconditionalFixedDQL

/-!
# The invariant-average theorem at the compiled detector normalization

The polynomial detector uses two numerical normalizations:

* its fourth-root gauge satisfies
  `G_j^4 = (1 / 256) χ_j`; and
* its Poisson reciprocal blocks use `η = 1 / 2`, hence the visible
  factor `1 - η² = 3 / 4`.

The older convenience observable `halfExpandedDetectorRealBCF` sets both
analytic parameters to `1 / 2`.  Its arithmetic sign theorem is correct,
but that observable is not literally the one represented by the compiled
fourth-root gauge.  This file records the matching observable

```
  phase ↦ -Re(expandedDetector (1/256) (1/2) I phase)
```

as a bounded continuous function and proves the exact maximal-invariant-
average criterion.  The last section specializes the result to the fixed
universal-halting DQL family.
-/

namespace HGAS

open Function MeasureTheory
open scoped BoundedContinuousFunction

noncomputable section

/-! Use the same explicit normalized Haar realization as the Fourier and
invariant-average modules.  Writing it locally prevents an unrelated
default `MeasureSpace` instance on `AddCircle` from changing the meaning
of `volume` in the displayed integrals. -/

local instance fixedDetectorNormalizedMeasureSpaceUnitAddCircle :
    MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance fixedDetectorNormalizedIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs
    (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance fixedDetectorNormalizedIsProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs
    (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {eqs vars : ℕ}

/-! ## The normalization-matched bounded observable -/

/-- Theta-series parameter represented by the compiled fourth-root gauge. -/
abbrev fixedDetectorThetaParameter : ℝ := 1 / 256

/-- Poisson parameter represented by the compiled reciprocal blocks. -/
abbrev fixedDetectorPoissonParameter : ℝ := 1 / 2

/-- Real part of the expanded arithmetic detector at the exact parameters
used by the polynomial compiler. -/
def fixedDetectorExpandedRealBCF
    (I : DQLSystem eqs vars) :
    UnitAddTorus (DetectorPhase eqs vars) →ᵇ ℝ :=
  expandedDetectorRealBCF
    (lambda := fixedDetectorThetaParameter)
    (eta := fixedDetectorPoissonParameter)
    (by norm_num [fixedDetectorThetaParameter])
    (by norm_num [fixedDetectorThetaParameter])
    (by norm_num [fixedDetectorPoissonParameter])
    (by norm_num [fixedDetectorPoissonParameter])
    I

@[simp]
theorem fixedDetectorExpandedRealBCF_apply
    (I : DQLSystem eqs vars)
    (phase : UnitAddTorus (DetectorPhase eqs vars)) :
    fixedDetectorExpandedRealBCF I phase =
      (expandedDetector (1 / 256 : ℝ) (1 / 2 : ℝ)
        I phase).re :=
  rfl

/-- The strict-sign reward used downstream: the negative real part of the
normalization-matched detector. -/
def fixedDetectorRewardBCF
    (I : DQLSystem eqs vars) :
    UnitAddTorus (DetectorPhase eqs vars) →ᵇ ℝ :=
  -fixedDetectorExpandedRealBCF I

@[simp]
theorem fixedDetectorRewardBCF_apply
    (I : DQLSystem eqs vars)
    (phase : UnitAddTorus (DetectorPhase eqs vars)) :
    fixedDetectorRewardBCF I phase =
      -(expandedDetector (1 / 256 : ℝ) (1 / 2 : ℝ)
        I phase).re :=
  rfl

/-! ## Haar average and arithmetic sign -/

/-- Haar averaging the reward gives the negative real detector integral.
This equality fixes the normalization before any dynamical factor map is
introduced. -/
theorem observableAverage_fixedDetectorRewardBCF_torusHaar
    (I : DQLSystem eqs vars) :
    Dynamics.observableAverage
        (fixedDetectorRewardBCF I)
        (Clocks.RadicalClock.torusHaarProbability
          (d := DetectorPhase eqs vars)) =
      -(∫ phase : UnitAddTorus (DetectorPhase eqs vars),
        expandedDetector (1 / 256 : ℝ) (1 / 2 : ℝ)
          I phase).re := by
  calc
    Dynamics.observableAverage
        (fixedDetectorRewardBCF I)
        (Clocks.RadicalClock.torusHaarProbability
          (d := DetectorPhase eqs vars)) =
      -Dynamics.observableAverage
        (fixedDetectorExpandedRealBCF I)
        (Clocks.RadicalClock.torusHaarProbability
          (d := DetectorPhase eqs vars)) := by
            unfold Dynamics.observableAverage
            change
              (∫ phase :
                  UnitAddTorus (DetectorPhase eqs vars),
                -(fixedDetectorExpandedRealBCF I phase) ∂volume) =
              -(∫ phase :
                  UnitAddTorus (DetectorPhase eqs vars),
                fixedDetectorExpandedRealBCF I phase ∂volume)
            rw [integral_neg]
    _ = -(∫ phase :
          UnitAddTorus (DetectorPhase eqs vars),
        expandedDetector (1 / 256 : ℝ) (1 / 2 : ℝ)
          I phase).re := by
            congr 1
            simpa [fixedDetectorExpandedRealBCF,
              fixedDetectorThetaParameter,
              fixedDetectorPoissonParameter] using
              (observableAverage_expandedDetectorRealBCF_torusHaar
                (lambda := (1 / 256 : ℝ))
                (eta := (1 / 2 : ℝ))
                (show (0 : ℝ) ≤ 1 / 256 by norm_num)
                (show (1 / 256 : ℝ) < 1 by norm_num)
                (show (0 : ℝ) ≤ 1 / 2 by norm_num)
                (show (1 / 2 : ℝ) < 1 by norm_num)
                I)

/-- **Normalization-correct detector-to-maximal-average bridge.**

If every invariant source probability has Haar detector-phase marginal,
then strict negativity of the maximal average of the compiled detector
reward is equivalent to solvability of the DQL system. -/
theorem maximalInvariantAverage_fixedDetectorReward_iff_solvable
    {X : Type*}
    [MetricSpace X] [CompactSpace X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X]
    (ϕ : Flow ℝ X)
    (ω : DetectorPhase eqs vars → ℝ)
    (phase : X → UnitAddTorus (DetectorPhase eqs vars))
    (hphase : Continuous phase)
    (hequiv :
      ∀ t : ℝ,
        Function.Semiconj phase (ϕ t)
          (Clocks.RadicalClock.torusTranslationFlow ω t))
    (hHaar :
      ∀ μ : Dynamics.InvariantProbabilityMeasure ϕ,
        (μ.mapEquivariant phase hphase hequiv).measure =
          Clocks.RadicalClock.torusHaarProbability)
    (I : DQLSystem eqs vars) :
    Dynamics.maximalInvariantAverage ϕ
        ((fixedDetectorRewardBCF I).compContinuous
          ⟨phase, hphase⟩) < 0 ↔
      I.Solvable := by
  rw [
    Dynamics.maximalInvariantAverage_compContinuous_eq_of_uniqueFactorMarginal
      phase hphase hequiv
      (Clocks.RadicalClock.torusHaarProbability
        (d := DetectorPhase eqs vars))
      hHaar
      (fixedDetectorRewardBCF I)]
  rw [observableAverage_fixedDetectorRewardBCF_torusHaar,
    neg_lt_zero]
  exact
    integral_expandedDetector_re_pos_iff_solvable
      (lambda := (1 / 256 : ℝ))
      (eta := (1 / 2 : ℝ))
      (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) I

/-! ## Fixed-resource universal-halting specialization -/

/-- One fixed detector phase type for the unconditional universal DQL
family. -/
abbrev UniversalHaltingNormalizedFixedDetectorPhase :=
  DetectorPhase
    UniversalHalting.unconditionalFixedDQLEquationCount
    UniversalHalting.unconditionalFixedDQLVariableCount

/-- Normalization-matched detector reward for the fixed DQL instance
encoding `input`. -/
def unconditionalUniversalHaltingFixedDetectorRewardBCF
    (input : ℕ) :
    UnitAddTorus UniversalHaltingNormalizedFixedDetectorPhase →ᵇ ℝ :=
  fixedDetectorRewardBCF
    (UniversalHalting.unconditionalUniversalHaltingFixedDQL input)

@[simp]
theorem unconditionalUniversalHaltingFixedDetectorRewardBCF_apply
    (input : ℕ)
    (phase :
      UnitAddTorus UniversalHaltingNormalizedFixedDetectorPhase) :
    unconditionalUniversalHaltingFixedDetectorRewardBCF input phase =
      -(expandedDetector (1 / 256 : ℝ) (1 / 2 : ℝ)
        (UniversalHalting.unconditionalUniversalHaltingFixedDQL input)
        phase).re :=
  rfl

/-- For any one compact realization satisfying the displayed Haar-factor
hypothesis, the normalization-matched maximal-average predicate is exactly
the fixed universal-halting predicate. -/
theorem
    maximalInvariantAverage_unconditionalUniversalHaltingFixedDetectorReward_iff
    {X : Type*}
    [MetricSpace X] [CompactSpace X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X]
    (ϕ : Flow ℝ X)
    (ω : UniversalHaltingNormalizedFixedDetectorPhase → ℝ)
    (phase :
      X → UnitAddTorus UniversalHaltingNormalizedFixedDetectorPhase)
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
        ((unconditionalUniversalHaltingFixedDetectorRewardBCF input)
          |>.compContinuous ⟨phase, hphase⟩) < 0 ↔
      UniversalHalting.Predicate input := by
  have hdetector :=
    maximalInvariantAverage_fixedDetectorReward_iff_solvable
      ϕ ω phase hphase hequiv hHaar
      (UniversalHalting.unconditionalUniversalHaltingFixedDQL input)
  have hdetector' :
      Dynamics.maximalInvariantAverage ϕ
          ((unconditionalUniversalHaltingFixedDetectorRewardBCF input)
            |>.compContinuous ⟨phase, hphase⟩) < 0 ↔
        (UniversalHalting.unconditionalUniversalHaltingFixedDQL
          input).Solvable := by
    simpa only [
      unconditionalUniversalHaltingFixedDetectorRewardBCF]
      using hdetector
  exact hdetector'.trans
    (UniversalHalting.unconditionalUniversalHaltingFixedDQL_solvable_iff
      input)

/-- Therefore the fixed-dimensional normalization-matched detector
maximal-average predicate is not computable. -/
theorem
    maximalInvariantAverage_unconditionalUniversalHaltingFixedDetectorReward_not_computable
    {X : Type*}
    [MetricSpace X] [CompactSpace X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X]
    (ϕ : Flow ℝ X)
    (ω : UniversalHaltingNormalizedFixedDetectorPhase → ℝ)
    (phase :
      X → UnitAddTorus UniversalHaltingNormalizedFixedDetectorPhase)
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
            ((unconditionalUniversalHaltingFixedDetectorRewardBCF input)
              |>.compContinuous ⟨phase, hphase⟩) < 0) := by
  intro hcomputable
  apply UniversalHalting.predicate_not_computable
  exact
    ComputablePred.of_eq hcomputable fun input ↦
      maximalInvariantAverage_unconditionalUniversalHaltingFixedDetectorReward_iff
        ϕ ω phase hphase hequiv hHaar input

end

end HGAS
