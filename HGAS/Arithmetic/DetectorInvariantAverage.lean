import HGAS.Arithmetic.DetectorFourier
import HGAS.Clocks.RadicalClock
import HGAS.Dynamics.UniqueFactorAverage
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The arithmetic detector as an invariant-average observable

`DetectorFourier` proves that the Haar integral of the expanded detector is
positive exactly for a solvable DQL instance.  This module packages its real
part as a bounded continuous observable and combines that calculation with
the unique-factor-marginal lemma.

The final theorem is deliberately abstract about the source realization:
whenever a compact source flow has the detector phase torus as an equivariant
factor and every invariant probability has Haar phase marginal, the maximal
invariant average of the *negative* detector is strictly negative exactly
when the DQL instance is solvable.  The remaining source compiler must prove
those factor hypotheses for its polynomial realization.
-/

namespace HGAS

open Function MeasureTheory
open scoped BoundedContinuousFunction

noncomputable section

local instance detectorInvariantAverageMeasureSpaceUnitAddCircle :
    MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance detectorInvariantAverageIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs
    (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance detectorInvariantAverageIsProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs
    (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {eqs vars : ℕ}

/-- Real part of the absolutely convergent detector, bundled as a bounded
continuous function on its compact phase torus. -/
def expandedDetectorRealBCF
    {lambda eta : ℝ}
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda < 1)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    (I : DQLSystem eqs vars) :
    UnitAddTorus (DetectorPhase eqs vars) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun phase ↦ (expandedDetector lambda eta I phase).re,
      Complex.continuous_re.comp
        (continuous_expandedDetector
          hlambda0 hlambda1 heta0 heta1 I)⟩

@[simp]
theorem expandedDetectorRealBCF_apply
    {lambda eta : ℝ}
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda < 1)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    (I : DQLSystem eqs vars)
    (phase : UnitAddTorus (DetectorPhase eqs vars)) :
    expandedDetectorRealBCF
        hlambda0 hlambda1 heta0 heta1 I phase =
      (expandedDetector lambda eta I phase).re :=
  rfl

/-- Haar averaging the bundled real observable recovers the real part of
the complex detector integral. -/
theorem observableAverage_expandedDetectorRealBCF_torusHaar
    {lambda eta : ℝ}
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda < 1)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    (I : DQLSystem eqs vars) :
    Dynamics.observableAverage
        (expandedDetectorRealBCF
          hlambda0 hlambda1 heta0 heta1 I)
        (Clocks.RadicalClock.torusHaarProbability
          (d := DetectorPhase eqs vars)) =
      (∫ phase : UnitAddTorus (DetectorPhase eqs vars),
        expandedDetector lambda eta I phase).re := by
  let f : UnitAddTorus (DetectorPhase eqs vars) →ᵇ ℂ :=
    BoundedContinuousFunction.mkOfCompact
      ⟨expandedDetector lambda eta I,
        continuous_expandedDetector
          hlambda0 hlambda1 heta0 heta1 I⟩
  have hf :
      Integrable
        (expandedDetector lambda eta I)
        (volume :
          Measure (UnitAddTorus (DetectorPhase eqs vars))) := by
    simpa only [f] using
      f.integrable
        (volume :
          Measure (UnitAddTorus (DetectorPhase eqs vars)))
  unfold Dynamics.observableAverage
  rw [Clocks.RadicalClock.torusHaarProbability_toMeasure]
  simpa [expandedDetectorRealBCF] using
    (integral_re hf)

/-- Fixed half-parameter real detector observable. -/
def halfExpandedDetectorRealBCF
    (I : DQLSystem eqs vars) :
    UnitAddTorus (DetectorPhase eqs vars) →ᵇ ℝ :=
  expandedDetectorRealBCF
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) < 1 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) < 1 by norm_num)
    I

/-- **Detector-to-maximal-average bridge.**

For any compact realization with a uniquely Haar detector-phase marginal,
the negative detector has strictly negative maximal invariant average
exactly for a solvable DQL instance. -/
theorem maximalInvariantAverage_neg_halfDetector_iff_solvable
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
        ((-halfExpandedDetectorRealBCF I).compContinuous
          ⟨phase, hphase⟩) < 0 ↔
      I.Solvable := by
  rw [Dynamics.maximalInvariantAverage_compContinuous_eq_of_uniqueFactorMarginal
    phase hphase hequiv
    (Clocks.RadicalClock.torusHaarProbability
      (d := DetectorPhase eqs vars))
    hHaar
    (-halfExpandedDetectorRealBCF I)]
  have haverage :
      Dynamics.observableAverage
          (-halfExpandedDetectorRealBCF I)
          (Clocks.RadicalClock.torusHaarProbability
            (d := DetectorPhase eqs vars)) =
        -(∫ phase :
            UnitAddTorus (DetectorPhase eqs vars),
          expandedDetector (1 / 2 : ℝ) (1 / 2 : ℝ)
            I phase).re := by
    calc
      Dynamics.observableAverage
          (-halfExpandedDetectorRealBCF I)
          (Clocks.RadicalClock.torusHaarProbability
            (d := DetectorPhase eqs vars)) =
        -Dynamics.observableAverage
          (halfExpandedDetectorRealBCF I)
          (Clocks.RadicalClock.torusHaarProbability
            (d := DetectorPhase eqs vars)) := by
              unfold Dynamics.observableAverage
              change
                (∫ x :
                    UnitAddTorus (DetectorPhase eqs vars),
                  -(halfExpandedDetectorRealBCF I x) ∂volume) =
                -(∫ x :
                    UnitAddTorus (DetectorPhase eqs vars),
                  halfExpandedDetectorRealBCF I x ∂volume)
              rw [integral_neg]
      _ = -(∫ phase :
            UnitAddTorus (DetectorPhase eqs vars),
          expandedDetector (1 / 2 : ℝ) (1 / 2 : ℝ)
            I phase).re := by
              congr 1
              simpa [halfExpandedDetectorRealBCF] using
                (observableAverage_expandedDetectorRealBCF_torusHaar
                  (lambda := (1 / 2 : ℝ))
                  (eta := (1 / 2 : ℝ))
                  (show (0 : ℝ) ≤ 1 / 2 by norm_num)
                  (show (1 / 2 : ℝ) < 1 by norm_num)
                  (show (0 : ℝ) ≤ 1 / 2 by norm_num)
                  (show (1 / 2 : ℝ) < 1 by norm_num)
                  I)
  rw [haverage, neg_lt_zero]
  exact integral_expandedDetector_re_pos_iff_solvable
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) I

end

end HGAS
