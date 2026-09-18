import HGAS.Dynamics.GeneratorInvariantMeasure
import HGAS.Dynamics.InvariantDensity
import Mathlib.Tactic

/-!
# Invariant probabilities under positive changes of time

Suppose two complete `C¹` flows on a finite-dimensional real vector space
have generators

```
  Y(x) = f(x) X(x),       f(x) > 0.
```

The two flows have the same oriented orbits but generally not the same
invariant probabilities.  Their invariant measures are related by the
standard reciprocal density rule:

* a `Y`-invariant probability `η` gives the `X`-invariant probability
  `dμ = f dη / ∫ f dη`;
* an `X`-invariant probability `μ` gives a `Y`-invariant probability
  `dη = f⁻¹ dμ / ∫ f⁻¹ dμ`, provided the reciprocal is integrable.

Unlike a common paper proof that invokes a generator characterization
without justification, this file derives both directions from the
kernel-checked generator criterion in
`HGAS.Dynamics.GeneratorInvariantMeasure`.
-/

noncomputable section

open Function MeasureTheory Set
open scoped ENNReal NNReal

namespace HGAS.Dynamics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The generator relation for the positive state-dependent time change
`Y = f X`. -/
def IsGeneratorTimeChange
    (Φ Ψ : C1ODEFlow E) (f : E → ℝ≥0) : Prop :=
  ∀ x, Ψ.generator x = (f x : ℝ) • Φ.generator x

/-- A `Y = fX` invariant probability becomes `X` invariant after weighting
by `f` and normalizing. -/
theorem invariantProbability_normalizedDensity_of_timeChange
    (Φ Ψ : C1ODEFlow E) (f : E → ℝ≥0)
    (hf : Continuous f)
    (hchange : IsGeneratorTimeChange Φ Ψ f)
    (η : InvariantProbabilityMeasure Ψ.flow)
    (a : ℝ≥0) (ha : a ≠ 0)
    (hmass :
      ∫⁻ x, (f x : ENNReal) ∂(η.measure : Measure E) =
        (a : ENNReal)) :
    IsInvariantProbability Φ.flow
      (normalizedDensityProbability
        (η.measure : Measure E) f a hf.measurable ha hmass) := by
  apply
    (isInvariantProbability_iff_isGeneratorInvariant Φ _).2
  intro φ hφ hφs
  rw [integral_normalizedDensityProbability_real
    (η.measure : Measure E) f a hf.measurable ha hmass
    (lieDerivative Φ.generator φ)]
  have hzero :
      (∫ x, (f x : ℝ) *
          lieDerivative Φ.generator φ x
          ∂(η.measure : Measure E)) = 0 := by
    have hη := η.isGeneratorInvariant Ψ
    have hraw := hη φ hφ hφs
    rw [show
        (fun x ↦ lieDerivative Ψ.generator φ x) =
          fun x ↦ (f x : ℝ) *
            lieDerivative Φ.generator φ x by
      funext x
      simp only [lieDerivative, hchange x,
        map_smul, smul_eq_mul]] at hraw
    exact hraw
  calc
    (∫ x, ((f x : ℝ) / (a : ℝ)) *
        lieDerivative Φ.generator φ x
        ∂(η.measure : Measure E)) =
        (a : ℝ)⁻¹ *
          ∫ x, (f x : ℝ) *
            lieDerivative Φ.generator φ x
            ∂(η.measure : Measure E) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [div_eq_mul_inv]
      ring
    _ = 0 := by rw [hzero, mul_zero]

/-- Pointwise reciprocal of a nonnegative speed. -/
def reciprocalSpeed (f : E → ℝ≥0) : E → ℝ≥0 :=
  fun x ↦ (f x)⁻¹

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
@[simp]
theorem reciprocalSpeed_apply (f : E → ℝ≥0) (x : E) :
    reciprocalSpeed f x = (f x)⁻¹ :=
  rfl

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
/-- A continuous strictly positive speed has a continuous reciprocal. -/
theorem continuous_reciprocalSpeed
    {f : E → ℝ≥0} (hf : Continuous f)
    (hpos : ∀ x, f x ≠ 0) :
    Continuous (reciprocalSpeed f) := by
  exact hf.inv₀ hpos

/-- An `X`-invariant probability becomes `Y = fX` invariant after weighting
by `f⁻¹` and normalizing, whenever that reciprocal density has finite
positive mass. -/
theorem invariantProbability_normalizedReciprocalDensity_of_timeChange
    (Φ Ψ : C1ODEFlow E) (f : E → ℝ≥0)
    (hf : Continuous f) (hpos : ∀ x, f x ≠ 0)
    (hchange : IsGeneratorTimeChange Φ Ψ f)
    (μ : InvariantProbabilityMeasure Φ.flow)
    (Z : ℝ≥0) (hZ : Z ≠ 0)
    (hmass :
      ∫⁻ x, (reciprocalSpeed f x : ENNReal)
          ∂(μ.measure : Measure E) =
        (Z : ENNReal)) :
    IsInvariantProbability Ψ.flow
      (normalizedDensityProbability
        (μ.measure : Measure E) (reciprocalSpeed f) Z
        (continuous_reciprocalSpeed hf hpos).measurable
        hZ hmass) := by
  apply
    (isInvariantProbability_iff_isGeneratorInvariant Ψ _).2
  intro φ hφ hφs
  rw [integral_normalizedDensityProbability_real
    (μ.measure : Measure E) (reciprocalSpeed f) Z
    (continuous_reciprocalSpeed hf hpos).measurable
    hZ hmass (lieDerivative Ψ.generator φ)]
  have hzero :
      (∫ x, lieDerivative Φ.generator φ x
          ∂(μ.measure : Measure E)) = 0 :=
    (μ.isGeneratorInvariant Φ) φ hφ hφs
  calc
    (∫ x,
        ((reciprocalSpeed f x : ℝ) / (Z : ℝ)) *
          lieDerivative Ψ.generator φ x
        ∂(μ.measure : Measure E)) =
        (Z : ℝ)⁻¹ *
          ∫ x, lieDerivative Φ.generator φ x
            ∂(μ.measure : Measure E) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [lieDerivative, hchange x, map_smul,
        smul_eq_mul, reciprocalSpeed, NNReal.coe_inv]
      have hfreal : (f x : ℝ) ≠ 0 := by
        exact_mod_cast hpos x
      field_simp
    _ = 0 := by rw [hzero, mul_zero]

/-- Package the source-time invariant probability obtained from a slowed
invariant probability. -/
def sourceInvariantProbabilityOfTimeChange
    (Φ Ψ : C1ODEFlow E) (f : E → ℝ≥0)
    (hf : Continuous f)
    (hchange : IsGeneratorTimeChange Φ Ψ f)
    (η : InvariantProbabilityMeasure Ψ.flow)
    (a : ℝ≥0) (ha : a ≠ 0)
    (hmass :
      ∫⁻ x, (f x : ENNReal) ∂(η.measure : Measure E) =
        (a : ENNReal)) :
    InvariantProbabilityMeasure Φ.flow where
  measure :=
    normalizedDensityProbability
      (η.measure : Measure E) f a hf.measurable ha hmass
  invariant :=
    invariantProbability_normalizedDensity_of_timeChange
      Φ Ψ f hf hchange η a ha hmass

/-- Package the slowed-time invariant probability obtained from a source
invariant probability with integrable reciprocal speed. -/
def slowedInvariantProbabilityOfTimeChange
    (Φ Ψ : C1ODEFlow E) (f : E → ℝ≥0)
    (hf : Continuous f) (hpos : ∀ x, f x ≠ 0)
    (hchange : IsGeneratorTimeChange Φ Ψ f)
    (μ : InvariantProbabilityMeasure Φ.flow)
    (Z : ℝ≥0) (hZ : Z ≠ 0)
    (hmass :
      ∫⁻ x, (reciprocalSpeed f x : ENNReal)
          ∂(μ.measure : Measure E) =
        (Z : ENNReal)) :
    InvariantProbabilityMeasure Ψ.flow where
  measure :=
    normalizedDensityProbability
      (μ.measure : Measure E) (reciprocalSpeed f) Z
      (continuous_reciprocalSpeed hf hpos).measurable
      hZ hmass
  invariant :=
    invariantProbability_normalizedReciprocalDensity_of_timeChange
      Φ Ψ f hf hpos hchange μ Z hZ hmass

omit [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Exact cocycle-average bookkeeping in the direction used by projective
compactification:

```
  dμ = (f/a) dη
  ⟹  ∫ κ f h dη = κ a ∫ h dμ.
```
-/
theorem timeChange_drift_identity
    (η : Measure E) (f : E → ℝ≥0) (a : ℝ≥0)
    (hf : Measurable f) (ha : a ≠ 0)
    (hmass : ∫⁻ x, (f x : ENNReal) ∂η = (a : ENNReal))
    (κ : ℝ) (h : E → ℝ) :
    (∫ x, κ * (f x : ℝ) * h x ∂η) =
      κ * (a : ℝ) *
        ∫ x, h x ∂
          (normalizedDensityProbability η f a hf ha hmass :
            ProbabilityMeasure E) :=
  integral_density_drift_identity η f a hf ha hmass κ h

end HGAS.Dynamics
