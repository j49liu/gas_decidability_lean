import HGAS.Dynamics.InvariantProbability
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Finite-time averages along a continuous flow

For a continuous real flow `ϕ` on `K` and a bounded continuous observable
`a`, set

```
A(T,x) = ∫ t in 0..T, a (ϕ t x).
```

This module records the elementary analytic facts used on both sides of the
uniform-negative-block lemma:

* `A(T,·)` is continuous (and hence is itself a bounded continuous
  observable when `K` is compact);
* finite-time integrals satisfy the exact cocycle identity;
* a common negative block iterates to every integral number of blocks;
* every finite-time integral is controlled by `‖a‖ |T|`.

The compactness/empirical-measure argument that produces a common negative
block from negativity of all invariant averages is kept in a later module.
-/

noncomputable section

open Function MeasureTheory Set
open scoped BoundedContinuousFunction Interval

namespace HGAS.Dynamics

variable {K : Type*} [TopologicalSpace K]

/-- The unnormalized integral of `a` along the orbit segment from time zero
to time `T`.  The oriented interval integral also gives the natural
definition when `T < 0`. -/
def orbitIntegral (ϕ : Flow ℝ K) (a : K →ᵇ ℝ)
    (T : ℝ) (x : K) : ℝ :=
  ∫ t in (0 : ℝ)..T, a (ϕ t x)

/-- Joint continuity of the orbit integrand in initial state and time. -/
theorem continuous_uncurry_orbitObservable
    (ϕ : Flow ℝ K) (a : K →ᵇ ℝ) :
    Continuous (uncurry fun x t ↦ a (ϕ t x)) := by
  exact a.continuous.comp
    (ϕ.continuous continuous_snd continuous_fst)

/-- A finite-time orbit integral depends continuously on the initial
state. -/
theorem continuous_orbitIntegral
    (ϕ : Flow ℝ K) (a : K →ᵇ ℝ) (T : ℝ) :
    Continuous (orbitIntegral ϕ a T) := by
  apply
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact continuous_uncurry_orbitObservable ϕ a

/-- On a compact phase space, a finite-time orbit integral is again a
bounded continuous observable. -/
def orbitIntegralBCF [CompactSpace K]
    (ϕ : Flow ℝ K) (a : K →ᵇ ℝ) (T : ℝ) : K →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨orbitIntegral ϕ a T, continuous_orbitIntegral ϕ a T⟩

@[simp]
theorem orbitIntegralBCF_apply [CompactSpace K]
    (ϕ : Flow ℝ K) (a : K →ᵇ ℝ) (T : ℝ) (x : K) :
    orbitIntegralBCF ϕ a T x = orbitIntegral ϕ a T x :=
  rfl

@[simp]
theorem orbitIntegral_zero
    (ϕ : Flow ℝ K) (a : K →ᵇ ℝ) (x : K) :
    orbitIntegral ϕ a 0 x = 0 := by
  simp [orbitIntegral]

/-- The integrand along every fixed orbit is continuous. -/
theorem continuous_orbitObservable
    (ϕ : Flow ℝ K) (a : K →ᵇ ℝ) (x : K) :
    Continuous (fun t : ℝ ↦ a (ϕ t x)) := by
  exact a.continuous.comp
    (ϕ.continuous continuous_id continuous_const)

/-- The additive orbit integral has derivative equal to the observable at
its moving right endpoint. -/
theorem hasDerivAt_orbitIntegral
    (ϕ : Flow ℝ K) (a : K →ᵇ ℝ) (x : K) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ orbitIntegral ϕ a s x)
      (a (ϕ t x)) t := by
  have hcontinuous :=
    continuous_orbitObservable ϕ a x
  unfold orbitIntegral
  exact
    intervalIntegral.integral_hasDerivAt_right
      (hcontinuous.intervalIntegrable 0 t)
      hcontinuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      hcontinuous.continuousAt

/-- Exact additive-cocycle identity for finite-time orbit integrals. -/
theorem orbitIntegral_add
    (ϕ : Flow ℝ K) (a : K →ᵇ ℝ) (S T : ℝ) (x : K) :
    orbitIntegral ϕ a (S + T) x =
      orbitIntegral ϕ a S x + orbitIntegral ϕ a T (ϕ S x) := by
  let f : ℝ → ℝ := fun t ↦ a (ϕ t x)
  have hf : Continuous f := continuous_orbitObservable ϕ a x
  have hfirst : IntervalIntegrable f volume 0 S :=
    hf.intervalIntegrable 0 S
  have hsecond : IntervalIntegrable f volume S (S + T) :=
    hf.intervalIntegrable S (S + T)
  rw [orbitIntegral, orbitIntegral, orbitIntegral]
  rw [← intervalIntegral.integral_add_adjacent_intervals hfirst hsecond]
  congr 1
  symm
  calc
    (∫ t in (0 : ℝ)..T, a (ϕ t (ϕ S x))) =
        ∫ t in (0 : ℝ)..T, f (t + S) := by
          apply intervalIntegral.integral_congr
          intro t _
          simp only [f, ϕ.map_add]
    _ = ∫ t in (0 : ℝ) + S..T + S, f t := by
          exact intervalIntegral.integral_comp_add_right f S
    _ = ∫ t in S..S + T, f t := by
          rw [zero_add, add_comm T S]

/-- Splitting off one final block of length `T`. -/
theorem orbitIntegral_natSucc_mul
    (ϕ : Flow ℝ K) (a : K →ᵇ ℝ) (n : ℕ) (T : ℝ) (x : K) :
    orbitIntegral ϕ a ((n + 1 : ℕ) * T) x =
      orbitIntegral ϕ a (n * T) x +
        orbitIntegral ϕ a T (ϕ (n * T) x) := by
  have hsum : ((n + 1 : ℕ) : ℝ) * T = (n : ℝ) * T + T := by
    push_cast
    ring
  rw [hsum, orbitIntegral_add]

/-- A strict common negative block remains negative after every positive
integral number of blocks. -/
theorem orbitIntegral_nat_mul_le
    (ϕ : Flow ℝ K) (a : K →ᵇ ℝ) {T c : ℝ}
    (hblock : ∀ x : K, orbitIntegral ϕ a T x ≤ -c)
    (n : ℕ) (x : K) :
    orbitIntegral ϕ a (n * T) x ≤ -(n : ℝ) * c := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [orbitIntegral_natSucc_mul]
      calc
        orbitIntegral ϕ a (n * T) x +
              orbitIntegral ϕ a T (ϕ (n * T) x) ≤
            (-(n : ℝ) * c) + (-c) :=
          add_le_add ih (hblock _)
        _ = -(n + 1 : ℕ) * c := by
          push_cast
          ring

/-- The elementary uniform bound
`|∫₀ᵀ a(ϕₜx)dt| ≤ ‖a‖ |T|`. -/
theorem norm_orbitIntegral_le
    (ϕ : Flow ℝ K) (a : K →ᵇ ℝ) (T : ℝ) (x : K) :
    ‖orbitIntegral ϕ a T x‖ ≤ ‖a‖ * |T| := by
  simpa only [orbitIntegral, sub_zero] using
    (intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := T) (C := ‖a‖)
      (f := fun t ↦ a (ϕ t x)) fun t _ ↦
        a.norm_coe_le_norm (ϕ t x))

section InvariantMeasure

variable [MeasurableSpace K] [BorelSpace K]

/-- The jointly continuous orbit observable is integrable on a bounded time
interval times any probability space.  This is the precise Fubini
hypothesis needed below. -/
theorem integrable_uncurry_orbitObservable_uIoc
    (ϕ : Flow ℝ K) (a : K →ᵇ ℝ) (μ : ProbabilityMeasure K)
    (T : ℝ) :
    Integrable (uncurry fun t x ↦ a (ϕ t x))
      ((volume.restrict (uIoc 0 T)).prod (μ : Measure K)) := by
  have hcontinuous :
      Continuous (uncurry fun t x ↦ a (ϕ t x)) := by
    exact a.continuous.comp
      (ϕ.continuous continuous_fst continuous_snd)
  rcases le_total 0 T with hT | hT
  · haveI :
        IsFiniteMeasure (volume.restrict (uIoc 0 T)) := by
      simpa only [uIoc_of_le hT] using
        (inferInstance :
          IsFiniteMeasure (volume.restrict (Ioc 0 T)))
    apply Integrable.of_bound hcontinuous.aestronglyMeasurable ‖a‖
    exact ae_of_all _ fun z ↦ a.norm_coe_le_norm (ϕ z.1 z.2)
  · haveI :
        IsFiniteMeasure (volume.restrict (uIoc 0 T)) := by
      simpa only [uIoc_of_ge hT] using
        (inferInstance :
          IsFiniteMeasure (volume.restrict (Ioc T 0)))
    apply Integrable.of_bound hcontinuous.aestronglyMeasurable ‖a‖
    exact ae_of_all _ fun z ↦ a.norm_coe_le_norm (ϕ z.1 z.2)

/-- Integrating a finite orbit segment against an invariant probability
equals the length of the segment times the invariant average. -/
theorem integral_orbitIntegral_eq
    (ϕ : Flow ℝ K) (a : K →ᵇ ℝ)
    (μ : InvariantProbabilityMeasure ϕ) (T : ℝ) :
    (∫ x, orbitIntegral ϕ a T x ∂(μ.measure : Measure K)) =
      T * ∫ x, a x ∂(μ.measure : Measure K) := by
  calc
    (∫ x, orbitIntegral ϕ a T x ∂(μ.measure : Measure K)) =
        ∫ t in (0 : ℝ)..T,
          ∫ x, a (ϕ t x) ∂(μ.measure : Measure K) := by
      symm
      exact intervalIntegral_integral_swap
        (integrable_uncurry_orbitObservable_uIoc
          ϕ a μ.measure T)
    _ = ∫ t in (0 : ℝ)..T,
          ∫ x, a x ∂(μ.measure : Measure K) := by
      apply intervalIntegral.integral_congr
      intro t _
      exact μ.integral_comp_time t a
    _ = T * ∫ x, a x ∂(μ.measure : Measure K) := by
      simp

/-- The elementary direction of the uniform-negative-block principle:
a common block bounded by `-c` forces every invariant average to be at most
`-c/T`. -/
theorem invariantAverage_le_of_uniformBlock
    [CompactSpace K]
    (ϕ : Flow ℝ K) (a : K →ᵇ ℝ)
    (μ : InvariantProbabilityMeasure ϕ)
    {T c : ℝ} (hT : 0 < T)
    (hblock : ∀ x : K, orbitIntegral ϕ a T x ≤ -c) :
    (∫ x, a x ∂(μ.measure : Measure K)) ≤ -c / T := by
  have horbitIntegrable :
      Integrable (orbitIntegral ϕ a T) (μ.measure : Measure K) :=
    (orbitIntegralBCF ϕ a T).integrable (μ.measure : Measure K)
  have hconstantIntegrable :
      Integrable (fun _ : K ↦ -c) (μ.measure : Measure K) :=
    integrable_const _
  have hintegral :
      (∫ x, orbitIntegral ϕ a T x ∂(μ.measure : Measure K)) ≤
        ∫ _ : K, -c ∂(μ.measure : Measure K) := by
    exact integral_mono horbitIntegrable hconstantIntegrable
      hblock
  rw [integral_orbitIntegral_eq ϕ a μ T] at hintegral
  simp only [integral_const] at hintegral
  rw [ProbabilityMeasure.measureReal_eq_coe_coeFn] at hintegral
  norm_num [ProbabilityMeasure.coeFn_univ] at hintegral
  apply (le_div_iff₀ hT).2
  simpa only [mul_comm] using hintegral

end InvariantMeasure

end HGAS.Dynamics
