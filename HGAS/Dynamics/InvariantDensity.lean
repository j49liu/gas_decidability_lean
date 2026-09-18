import HGAS.Dynamics.InvariantProbability
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-!
# Normalized changes of density

The compactification argument in the paper repeatedly changes an invariant
probability by a positive time-change factor.  The dynamical invariance
statement belongs to the ODE/time-reparametrization layer, but the measure
normalization and integral bookkeeping are completely general.  This file
isolates that reusable part.

If `f : X → ℝ≥0` has positive finite integral `a`, then

```
                    dν = (f / a) dμ
```

is again a probability measure.  Integration against `ν` is integration
against `μ` with the factor `f / a`.  The final theorem is the exact
algebraic drift identity used in equation (10.8) of the manuscript.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace HGAS.Dynamics

variable {X E : Type*} [MeasurableSpace X]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The ordinary measure obtained by multiplying `μ` by the nonnegative
density `f / a`. -/
def normalizedDensityMeasure
    (μ : Measure X) (f : X → ℝ≥0) (a : ℝ≥0) : Measure X :=
  μ.withDensity fun x ↦ (f x / a : ℝ≥0)

/-- A positive finite density, divided by its integral, has total mass one. -/
theorem normalizedDensityMeasure_apply_univ
    (μ : Measure X) (f : X → ℝ≥0) (a : ℝ≥0)
    (hf : Measurable f)
    (ha : a ≠ 0)
    (hmass : ∫⁻ x, (f x : ENNReal) ∂μ = (a : ENNReal)) :
    normalizedDensityMeasure μ f a Set.univ = 1 := by
  rw [normalizedDensityMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  have hpoint :
      (fun x ↦ ((f x / a : ℝ≥0) : ENNReal)) =
        fun x ↦ (a : ENNReal)⁻¹ * (f x : ENNReal) := by
    funext x
    rw [ENNReal.coe_div ha, ENNReal.div_eq_inv_mul]
  rw [hpoint, lintegral_const_mul _ hf.coe_nnreal_ennreal, hmass]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast ha) ENNReal.coe_ne_top

/-- Package the normalized density as a probability measure. -/
def normalizedDensityProbability
    (μ : Measure X) (f : X → ℝ≥0) (a : ℝ≥0)
    (hf : Measurable f)
    (ha : a ≠ 0)
    (hmass : ∫⁻ x, (f x : ENNReal) ∂μ = (a : ENNReal)) :
    ProbabilityMeasure X :=
  ⟨normalizedDensityMeasure μ f a,
    isProbabilityMeasure_iff.mpr
      (normalizedDensityMeasure_apply_univ μ f a hf ha hmass)⟩

@[simp]
theorem normalizedDensityProbability_toMeasure
    (μ : Measure X) (f : X → ℝ≥0) (a : ℝ≥0)
    (hf : Measurable f)
    (ha : a ≠ 0)
    (hmass : ∫⁻ x, (f x : ENNReal) ∂μ = (a : ENNReal)) :
    ((normalizedDensityProbability μ f a hf ha hmass :
        ProbabilityMeasure X) : Measure X) =
      normalizedDensityMeasure μ f a :=
  rfl

/-- Integration after normalization is weighted integration before
normalization.  This equality remains valid even when either side is
non-integrable, because Mathlib's Bochner integral uses the conventional
value zero in that case. -/
theorem integral_normalizedDensityProbability
    (μ : Measure X) (f : X → ℝ≥0) (a : ℝ≥0)
    (hf : Measurable f)
    (ha : a ≠ 0)
    (hmass : ∫⁻ x, (f x : ENNReal) ∂μ = (a : ENNReal))
    (g : X → E) :
    (∫ x, g x ∂
        (normalizedDensityProbability μ f a hf ha hmass :
          ProbabilityMeasure X)) =
      ∫ x, (f x / a) • g x ∂μ := by
  exact integral_withDensity_eq_integral_smul
    (hf.div_const a) g

/-- Real scalar form of the normalized-density formula. -/
theorem integral_normalizedDensityProbability_real
    (μ : Measure X) (f : X → ℝ≥0) (a : ℝ≥0)
    (hf : Measurable f)
    (ha : a ≠ 0)
    (hmass : ∫⁻ x, (f x : ENNReal) ∂μ = (a : ENNReal))
    (g : X → ℝ) :
    (∫ x, g x ∂
        (normalizedDensityProbability μ f a hf ha hmass :
          ProbabilityMeasure X)) =
      ∫ x, ((f x : ℝ) / (a : ℝ)) * g x ∂μ := by
  rw [integral_normalizedDensityProbability μ f a hf ha hmass g]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [NNReal.smul_def]

/-- Exact drift bookkeeping for a normalized time-change density.

If `ν = (f/a) μ`, then the `μ`-average of `κ f h` is `κ a` times the
`ν`-average of `h`.  Mathlib's integral convention and the nonzero
normalizing constant make the identity valid without separate
integrability hypotheses. -/
theorem integral_density_drift_identity
    (μ : Measure X) (f : X → ℝ≥0) (a : ℝ≥0)
    (hf : Measurable f)
    (ha : a ≠ 0)
    (hmass : ∫⁻ x, (f x : ENNReal) ∂μ = (a : ENNReal))
    (κ : ℝ) (h : X → ℝ) :
    (∫ x, κ * (f x : ℝ) * h x ∂μ) =
      κ * (a : ℝ) *
        ∫ x, h x ∂
          (normalizedDensityProbability μ f a hf ha hmass :
            ProbabilityMeasure X) := by
  rw [integral_normalizedDensityProbability_real μ f a hf ha hmass h]
  have hareal : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  calc
    (∫ x, κ * (f x : ℝ) * h x ∂μ) =
        κ * ∫ x, (f x : ℝ) * h x ∂μ := by
      simpa only [mul_assoc] using
        MeasureTheory.integral_const_mul κ
          (fun x ↦ (f x : ℝ) * h x)
    _ = κ *
        ((a : ℝ) *
          ∫ x, ((f x : ℝ) / (a : ℝ)) * h x ∂μ) := by
      congr 1
      rw [← MeasureTheory.integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      field_simp
    _ = κ * (a : ℝ) *
        ∫ x, ((f x : ℝ) / (a : ℝ)) * h x ∂μ := by
      rw [mul_assoc]

end HGAS.Dynamics
