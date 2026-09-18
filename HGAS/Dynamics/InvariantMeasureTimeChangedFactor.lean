import HGAS.Dynamics.GeneratorInvariantMeasure
import HGAS.Dynamics.InvariantDensity
import Mathlib.Tactic

/-!
# Invariant measures for time-changed factors

This module treats a situation which is slightly more general than a time
change on one phase space.  Let `ϕ` be a continuous flow on a space `X`,
let `Φ` be a complete `C¹` ODE flow on a finite-dimensional real vector
space `E`, and let

```
                         π : X → E
```

be a continuous observation.  Suppose that observed source trajectories
satisfy

```
  d/dt π(ϕ t x) = f(ϕ t x) • Φ.generator (π(ϕ t x)).
```

Thus `π` is a factor map after a state-dependent change of clock, although
it need not intertwine equal time parameters.  If `η` is `ϕ`-invariant,
then the normalized `f`-density of `η`, pushed through `π`, is invariant
for `Φ`.

The proof does not put a manifold or vector-space structure on `X`.  This
is important for applications where `X` is a compact product of spheres or
an invariant subtype.  Instead, the derivative hypothesis is stated
directly along observed orbits.  For every compactly supported `C¹` target
test function, the chain rule identifies its derivative along a source
orbit with a bounded continuous observable on `X`.  The fundamental
theorem of calculus and source invariance show that this observable has
mean zero.  Mathlib's normalized-density formula and the already proved
target generator criterion then give genuine invariance under every target
time map.

No ergodicity assertion is made here.  Ergodicity under a time-changed
factor additionally requires an orbit-partition argument (and appropriate
strict positivity of the clock); it does not follow from the equal-time
factor theorem because `π` is generally not an equal-time semiconjugacy.
-/

noncomputable section

open Function MeasureTheory Set
open scoped BoundedContinuousFunction ENNReal NNReal Interval

namespace HGAS.Dynamics

variable {X E : Type*}
  [TopologicalSpace X]
  [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Orbitwise form of the generator relation for a time-changed
observation.

This formulation deliberately asks for derivatives of the actual observed
curves, not for a derivative of `π` on the source phase space.  It therefore
applies unchanged when the source is a subtype or a compact manifold for
which no ambient `C¹` structure has been installed in Lean. -/
def IsObservedGeneratorTimeChange
    (ϕ : Flow ℝ X) (Φ : C1ODEFlow E)
    (π : X → E) (f : X → ℝ≥0) : Prop :=
  ∀ x t,
    HasDerivAt
      (fun s : ℝ ↦ π (ϕ s x))
      ((f (ϕ t x) : ℝ) •
        Φ.generator (π (ϕ t x))) t

/-- The target Lie derivative, pulled back by a time-changed observation
and multiplied by the clock density, is a bounded continuous source
observable. -/
def observedWeightedLieDerivativeBCF
    (Φ : C1ODEFlow E) (π : X → E) (f : X →ᵇ ℝ≥0)
    (hπ : Continuous π)
    (φ : E → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hφs : HasCompactSupport φ) :
    X →ᵇ ℝ :=
  (f.comp ((↑) : ℝ≥0 → ℝ)
      NNReal.isometry_coe.lipschitz) *
    ((lieDerivativeBCF
        Φ.generator φ Φ.continuous_generator hφ hφs).compContinuous
      ⟨π, hπ⟩)

omit [MeasurableSpace X] [BorelSpace X]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp]
theorem observedWeightedLieDerivativeBCF_apply
    (Φ : C1ODEFlow E) (π : X → E) (f : X →ᵇ ℝ≥0)
    (hπ : Continuous π)
    (φ : E → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hφs : HasCompactSupport φ)
    (x : X) :
    observedWeightedLieDerivativeBCF
        Φ π f hπ φ hφ hφs x =
      (f x : ℝ) *
        lieDerivative Φ.generator φ (π x) :=
  rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Source invariance forces every observed weighted target Lie derivative
to have mean zero. -/
theorem integral_observedWeightedLieDerivative_eq_zero
    (ϕ : Flow ℝ X) (Φ : C1ODEFlow E)
    (π : X → E) (f : X →ᵇ ℝ≥0)
    (hπ : Continuous π)
    (hchange : IsObservedGeneratorTimeChange ϕ Φ π f)
    (η : InvariantProbabilityMeasure ϕ)
    (φ : E → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hφs : HasCompactSupport φ) :
    (∫ x,
        (f x : ℝ) *
          lieDerivative Φ.generator φ (π x)
        ∂(η.measure : Measure X)) = 0 := by
  let b : X →ᵇ ℝ :=
    observedWeightedLieDerivativeBCF
      Φ π f hπ φ hφ hφs
  let φb : E →ᵇ ℝ :=
    ofCompactSupport φ hφ.continuous hφs
  let c : X →ᵇ ℝ :=
    φb.compContinuous ⟨π, hπ⟩
  have hderiv :
      ∀ x t,
        HasDerivAt
          (fun s : ℝ ↦ φ (π (ϕ s x)))
          (b (ϕ t x)) t := by
    intro x t
    have hφat :
        HasFDerivAt φ
          (fderiv ℝ φ (π (ϕ t x)))
          (π (ϕ t x)) :=
      (hφ.differentiable one_ne_zero _).hasFDerivAt
    have hchain :=
      hφat.comp_hasDerivAt t (hchange x t)
    simpa only [b, observedWeightedLieDerivativeBCF_apply,
      lieDerivative, map_smul, smul_eq_mul] using hchain
  have hincrement :
      ∀ x,
        φ (π (ϕ 1 x)) - φ (π x) =
          orbitIntegral ϕ b 1 x := by
    intro x
    have hint :
        IntervalIntegrable
          (fun t : ℝ ↦ b (ϕ t x)) volume 0 1 :=
      (continuous_orbitObservable ϕ b x).intervalIntegrable 0 1
    symm
    simpa only [orbitIntegral, ϕ.map_zero_apply] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ ↦ hderiv x t) hint
  have hleft :
      (∫ x, φ (π (ϕ 1 x)) - φ (π x)
          ∂(η.measure : Measure X)) = 0 := by
    rw [integral_sub]
    · exact sub_eq_zero.mpr (by
        simpa only [c, φb] using η.integral_comp_time 1 c)
    · exact
        (c.compContinuous
          ⟨ϕ 1, ϕ.continuous_toFun 1⟩).integrable
          (η.measure : Measure X)
    · exact c.integrable (η.measure : Measure X)
  have hintegral :
      (∫ x, φ (π (ϕ 1 x)) - φ (π x)
          ∂(η.measure : Measure X)) =
        ∫ x, orbitIntegral ϕ b 1 x
          ∂(η.measure : Measure X) :=
    integral_congr_ae (ae_of_all _ hincrement)
  have horbit :
      (∫ x, orbitIntegral ϕ b 1 x
          ∂(η.measure : Measure X)) =
        ∫ x, b x ∂(η.measure : Measure X) := by
    simpa using integral_orbitIntegral_eq ϕ b η 1
  rw [hleft, horbit] at hintegral
  simpa only [b, observedWeightedLieDerivativeBCF_apply] using
    hintegral.symm

/-- A normalized clock-density pushforward of a source invariant
probability is invariant for the observed target ODE flow. -/
theorem invariantProbability_map_normalizedDensity_of_observedTimeChange
    (ϕ : Flow ℝ X) (Φ : C1ODEFlow E)
    (π : X → E) (f : X →ᵇ ℝ≥0)
    (hπ : Continuous π)
    (hchange : IsObservedGeneratorTimeChange ϕ Φ π f)
    (η : InvariantProbabilityMeasure ϕ)
    (a : ℝ≥0) (ha : a ≠ 0)
    (hmass :
      ∫⁻ x, (f x : ENNReal)
          ∂(η.measure : Measure X) =
        (a : ENNReal)) :
    IsInvariantProbability Φ.flow
      ((normalizedDensityProbability
          (η.measure : Measure X) f a
          f.continuous.measurable ha hmass).map
        hπ.measurable.aemeasurable) := by
  apply (isInvariantProbability_iff_isGeneratorInvariant Φ _).2
  intro φ hφ hφs
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [integral_map
    hπ.measurable.aemeasurable
    ((continuous_lieDerivative
      Φ.continuous_generator hφ).measurable.aestronglyMeasurable)]
  rw [integral_normalizedDensityProbability_real
    (η.measure : Measure X) f a
    f.continuous.measurable ha hmass
    (fun x ↦
      lieDerivative Φ.generator φ (π x))]
  have hzero :=
    integral_observedWeightedLieDerivative_eq_zero
      ϕ Φ π f hπ hchange η φ hφ hφs
  calc
    (∫ x,
        ((f x : ℝ) / (a : ℝ)) *
          lieDerivative Φ.generator φ (π x)
        ∂(η.measure : Measure X)) =
        (a : ℝ)⁻¹ *
          ∫ x,
            (f x : ℝ) *
              lieDerivative Φ.generator φ (π x)
            ∂(η.measure : Measure X) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [div_eq_mul_inv]
      ring
    _ = 0 := by rw [hzero, mul_zero]

/-- Bundled target invariant probability produced by the time-changed
factor construction. -/
def targetInvariantProbabilityOfObservedTimeChange
    (ϕ : Flow ℝ X) (Φ : C1ODEFlow E)
    (π : X → E) (f : X →ᵇ ℝ≥0)
    (hπ : Continuous π)
    (hchange : IsObservedGeneratorTimeChange ϕ Φ π f)
    (η : InvariantProbabilityMeasure ϕ)
    (a : ℝ≥0) (ha : a ≠ 0)
    (hmass :
      ∫⁻ x, (f x : ENNReal)
          ∂(η.measure : Measure X) =
        (a : ENNReal)) :
    InvariantProbabilityMeasure Φ.flow where
  measure :=
    (normalizedDensityProbability
      (η.measure : Measure X) f a
      f.continuous.measurable ha hmass).map
        hπ.measurable.aemeasurable
  invariant :=
    invariantProbability_map_normalizedDensity_of_observedTimeChange
      ϕ Φ π f hπ hchange η a ha hmass

end HGAS.Dynamics
