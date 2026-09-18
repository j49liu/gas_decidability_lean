import HGAS.Analysis.TorusFourierCesaroArbitraryHorizon
import HGAS.Arithmetic.DetectorFourier
import Mathlib.Tactic

/-!
# Arbitrary-horizon Cesàro averages of the arithmetic detector

The arithmetic detector is an absolutely convergent Fourier series on a
finite torus.  On a nonresonant linear torus orbit, its time average along
*every* sequence of horizons tending to infinity is therefore its Haar
constant term, independently of the initial phase.

This module deliberately separates that reusable analytic fact from the
later, construction-specific task of identifying the phase curve carried
by a selected compact-source trajectory.
-/

noncomputable section

open Filter MeasureTheory Topology

namespace HGAS

/-! We use normalized Haar probability on each additive circle, exactly
as in `DetectorFourier`. -/

local instance detectorCesaroMeasureSpaceUnitAddCircle :
    MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance detectorCesaroIsAddHaarMeasureUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs
    (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance detectorCesaroIsProbabilityMeasureUnitAddCircle :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs
    (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {eqs vars : ℕ}

/-- On a nonresonant detector-phase translation, arbitrary-horizon
Cesàro averages of the expanded detector converge to its normalized Haar
integral. -/
theorem cesaroMeanAt_expandedDetector_translation_tendsto_integral
    {lambda eta : ℝ}
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda < 1)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    (I : DQLSystem eqs vars)
    (ω : DetectorPhase eqs vars → ℝ)
    (hnonresonant :
      ∀ a : DetectorPhase eqs vars → ℤ,
        Clocks.RadicalClock.frequencyPairing a ω = 0 → a = 0)
    (phase₀ : UnitAddTorus (DetectorPhase eqs vars))
    {T : ℕ → ℝ}
    (hT : Tendsto T atTop atTop) :
    Tendsto
      (fun q ↦
        Analysis.cesaroMeanAt
          (fun t ↦
            expandedDetector lambda eta I
              (Clocks.RadicalClock.torusTranslationFlow
                ω t phase₀))
          (T q))
      atTop
      (𝓝
        (∫ phase : UnitAddTorus (DetectorPhase eqs vars),
          expandedDetector lambda eta I phase)) := by
  have haverage :=
    Analysis.cesaroMeanAt_torusFourierSeries_nonresonant_translation_tendsto
      (detectorCoefficient lambda eta)
      (detectorExponent I)
      (summable_norm_detectorCoefficient
        (vars := vars) hlambda0 hlambda1 heta0 heta1)
      ω hnonresonant phase₀ hT
  rw [integral_expandedDetector_eq_zeroExponentSeries
    hlambda0 hlambda1 heta0 heta1 I]
  simpa only [expandedDetector] using haverage

/-- In the solvable case the limiting detector constant term in the
preceding theorem is nonzero (indeed, it has strictly positive real
part). -/
theorem integral_expandedDetector_ne_zero_of_solvable
    {lambda eta : ℝ}
    (hlambda0 : 0 < lambda) (hlambda1 : lambda < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (I : DQLSystem eqs vars)
    (hsolvable : I.Solvable) :
    (∫ phase : UnitAddTorus (DetectorPhase eqs vars),
      expandedDetector lambda eta I phase) ≠ 0 := by
  have hpositive :
      0 <
        (∫ phase : UnitAddTorus (DetectorPhase eqs vars),
          expandedDetector lambda eta I phase).re :=
    (integral_expandedDetector_re_pos_iff_solvable
      hlambda0 hlambda1 heta0 heta1 I).2 hsolvable
  intro hzero
  rw [hzero] at hpositive
  norm_num at hpositive

/-- Combined form used in the compact-source contradiction: the physical
detector averages tend to a nonzero Haar constant term whenever the DQL
instance is solvable. -/
theorem
    cesaroMeanAt_expandedDetector_translation_tendsto_nonzero_integral_of_solvable
    {lambda eta : ℝ}
    (hlambda0 : 0 < lambda) (hlambda1 : lambda < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (I : DQLSystem eqs vars)
    (hsolvable : I.Solvable)
    (ω : DetectorPhase eqs vars → ℝ)
    (hnonresonant :
      ∀ a : DetectorPhase eqs vars → ℤ,
        Clocks.RadicalClock.frequencyPairing a ω = 0 → a = 0)
    (phase₀ : UnitAddTorus (DetectorPhase eqs vars))
    {T : ℕ → ℝ}
    (hT : Tendsto T atTop atTop) :
    Tendsto
      (fun q ↦
        Analysis.cesaroMeanAt
          (fun t ↦
            expandedDetector lambda eta I
              (Clocks.RadicalClock.torusTranslationFlow
                ω t phase₀))
          (T q))
      atTop
      (𝓝
        (∫ phase : UnitAddTorus (DetectorPhase eqs vars),
          expandedDetector lambda eta I phase)) ∧
      (∫ phase : UnitAddTorus (DetectorPhase eqs vars),
        expandedDetector lambda eta I phase) ≠ 0 := by
  exact
    ⟨cesaroMeanAt_expandedDetector_translation_tendsto_integral
        hlambda0.le hlambda1 heta0.le heta1 I
        ω hnonresonant phase₀ hT,
      integral_expandedDetector_ne_zero_of_solvable
        hlambda0 hlambda1 heta0 heta1 I hsolvable⟩

end HGAS
