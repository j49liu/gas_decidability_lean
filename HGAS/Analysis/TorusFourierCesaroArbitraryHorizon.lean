import HGAS.Analysis.CesaroExponentialSeriesArbitraryHorizon
import HGAS.Analysis.TorusCohomologicalPrimitive
import Mathlib.Tactic

/-!
# Cesàro averages of torus Fourier series on arbitrary horizons

An absolutely convergent Fourier series restricted to a linear torus
orbit is an absolutely convergent exponential series.  Consequently its
Cesàro averages along *any* sequence of horizons tending to infinity
retain precisely the resonant characters.

The nonresonant specialization below is the form used by the detector:
when the frequency vector has no nontrivial integral relation, the time
average is the Haar constant coefficient, independently of the initial
torus phase.
-/

noncomputable section

open Filter MeasureTheory Topology

namespace HGAS.Analysis

open HGAS.Clocks

variable {d ι : Type*} [Fintype d] [Countable ι]

/-- Fourier coefficients after fixing the initial point of a translation
orbit. -/
def translatedTorusCoefficient
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (x₀ : UnitAddTorus d)
    (i : ι) : ℂ :=
  coefficient i * UnitAddTorus.mFourier (exponent i) x₀

/-- Real angular frequency of one torus character. -/
def torusRealFrequency
    (exponent : ι → d → ℤ)
    (ω : d → ℝ)
    (i : ι) : ℝ :=
  2 * Real.pi *
    RadicalClock.frequencyPairing (exponent i) ω

omit [Countable ι] in
theorem norm_translatedTorusCoefficient
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (x₀ : UnitAddTorus d)
    (i : ι) :
    ‖translatedTorusCoefficient coefficient exponent x₀ i‖ =
      ‖coefficient i‖ := by
  simp [translatedTorusCoefficient, UnitAddTorus.mFourier,
    fourier_apply]

omit [Countable ι] in
/-- Restricting a torus Fourier series to a translation orbit gives the
literal exponential series with the preceding coefficients and
frequencies. -/
theorem torusFourierSeries_translation_eq_exponentialSeries
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (ω : d → ℝ)
    (x₀ : UnitAddTorus d)
    (t : ℝ) :
    torusFourierSeries coefficient exponent
        (RadicalClock.torusTranslationFlow ω t x₀) =
      exponentialSeries
        (translatedTorusCoefficient coefficient exponent x₀)
        (torusRealFrequency exponent ω) t := by
  unfold torusFourierSeries exponentialSeries
  apply tsum_congr
  intro i
  unfold torusSeriesTerm exponentialSeriesTerm
  rw [RadicalClock.torusTranslationFlow_apply,
    RadicalClock.mFourier_add_point,
    RadicalClock.mFourier_torusDisplacement]
  unfold translatedTorusCoefficient torusRealFrequency
    realFrequencyExponential
  have harg :
      2 * (Real.pi : ℂ) * Complex.I *
          ((t : ℂ) *
            (RadicalClock.frequencyPairing
              (exponent i) ω : ℂ)) =
        ((2 * Real.pi *
            RadicalClock.frequencyPairing
              (exponent i) ω : ℝ) : ℂ) *
          Complex.I * (t : ℂ) := by
    push_cast
    ring
  rw [harg]
  ring

/-- Arbitrary-horizon time averaging retains exactly the resonant
characters. -/
theorem cesaroMeanAt_torusFourierSeries_translation_tendsto
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (hsum : Summable fun i ↦ ‖coefficient i‖)
    (ω : d → ℝ)
    (x₀ : UnitAddTorus d)
    {T : ℕ → ℝ}
    (hT : Tendsto T atTop atTop) :
    Tendsto
      (fun q ↦
        cesaroMeanAt
          (fun t ↦
            torusFourierSeries coefficient exponent
              (RadicalClock.torusTranslationFlow ω t x₀))
          (T q))
      atTop
      (𝓝
        (∑' i,
          if RadicalClock.frequencyPairing (exponent i) ω = 0 then
            translatedTorusCoefficient coefficient exponent x₀ i
          else 0)) := by
  have htranslated :
      Summable fun i ↦
        ‖translatedTorusCoefficient coefficient exponent x₀ i‖ := by
    simpa only [
      norm_translatedTorusCoefficient] using hsum
  have hseries :=
    cesaroMeanAt_exponentialSeries_tendsto
      (translatedTorusCoefficient coefficient exponent x₀)
      (torusRealFrequency exponent ω)
      htranslated hT
  have hfunctions :
      (fun t ↦
        torusFourierSeries coefficient exponent
          (RadicalClock.torusTranslationFlow ω t x₀)) =
        exponentialSeries
          (translatedTorusCoefficient coefficient exponent x₀)
          (torusRealFrequency exponent ω) := by
    funext t
    exact
      torusFourierSeries_translation_eq_exponentialSeries
        coefficient exponent ω x₀ t
  rw [hfunctions]
  convert hseries using 1
  congr 1
  apply tsum_congr
  intro i
  have hfreq :
      torusRealFrequency exponent ω i = 0 ↔
        RadicalClock.frequencyPairing (exponent i) ω = 0 := by
    unfold torusRealFrequency
    constructor
    · intro h
      rcases mul_eq_zero.mp h with htwoPi | hpair
      · exfalso
        exact
          (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0)
            Real.pi_ne_zero) htwoPi
      · exact hpair
    · intro h
      rw [h]
      ring
  by_cases hpair :
      RadicalClock.frequencyPairing (exponent i) ω = 0
  · have hreal : torusRealFrequency exponent ω i = 0 :=
      hfreq.mpr hpair
    simp [hpair, hreal]
  · have hreal : torusRealFrequency exponent ω i ≠ 0 :=
      fun hzero ↦ hpair (hfreq.mp hzero)
    simp [hpair, hreal]

/-- For a nonresonant translation, the time average is independent of
the initial point and equals the zero-exponent subseries. -/
theorem
    cesaroMeanAt_torusFourierSeries_nonresonant_translation_tendsto
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (hsum : Summable fun i ↦ ‖coefficient i‖)
    (ω : d → ℝ)
    (hnonresonant :
      ∀ a : d → ℤ,
        RadicalClock.frequencyPairing a ω = 0 → a = 0)
    (x₀ : UnitAddTorus d)
    {T : ℕ → ℝ}
    (hT : Tendsto T atTop atTop) :
    Tendsto
      (fun q ↦
        cesaroMeanAt
          (fun t ↦
            torusFourierSeries coefficient exponent
              (RadicalClock.torusTranslationFlow ω t x₀))
          (T q))
      atTop
      (𝓝 (∑' i,
        if exponent i = 0 then coefficient i else 0)) := by
  have h :=
    cesaroMeanAt_torusFourierSeries_translation_tendsto
      coefficient exponent hsum ω x₀ hT
  convert h using 1
  congr 1
  apply tsum_congr
  intro i
  by_cases hi : exponent i = 0
  · simp [hi, translatedTorusCoefficient,
      RadicalClock.frequencyPairing,
      UnitAddTorus.mFourier_zero]
  · have hpair :
        RadicalClock.frequencyPairing (exponent i) ω ≠ 0 := by
      intro hzero
      exact hi (hnonresonant (exponent i) hzero)
    simp [hi, hpair]

end HGAS.Analysis
