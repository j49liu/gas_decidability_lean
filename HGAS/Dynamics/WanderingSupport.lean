import HGAS.Dynamics.InvariantProbability
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic

/-!
# Wandering sets carry no invariant probability

This module isolates the measure-theoretic argument used repeatedly in the
paper to exclude heteroclinic and escaping pieces of a flow.

If the integer-time translates of a measurable set are pairwise disjoint,
invariance gives every translate the same mass.  A finite invariant
probability cannot contain countably many disjoint copies of a set of
positive mass, so the set is null.  A countable union of such wandering
sets is null as well.

The result is stated for an arbitrary continuous real flow and is reusable
for controller arcs, affine escape branches, and projective charts.
-/

noncomputable section

open Function MeasureTheory Set
open scoped ENNReal

namespace HGAS.Dynamics

variable {K : Type*} [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K]

/-- The `n`-th inverse translate of a set by a fixed time step.  Inverse
images are convenient because the invariant-measure API gives their mass
directly. -/
def inverseTimeTranslate
    (ϕ : Flow ℝ K) (step : ℝ) (A : Set K) (n : ℕ) : Set K :=
  (ϕ ((n : ℝ) * step)) ⁻¹' A

/-- Every inverse translate of a measurable set is measurable. -/
theorem measurableSet_inverseTimeTranslate
    (ϕ : Flow ℝ K) (step : ℝ) {A : Set K}
    (hA : MeasurableSet A) (n : ℕ) :
    MeasurableSet (inverseTimeTranslate ϕ step A n) := by
  exact hA.preimage (ϕ.continuous_toFun _).measurable

/-- An invariant probability assigns the original mass to every inverse
time translate. -/
theorem measure_inverseTimeTranslate
    {ϕ : Flow ℝ K} (μ : InvariantProbabilityMeasure ϕ)
    (step : ℝ) {A : Set K} (hA : MeasurableSet A) (n : ℕ) :
    (μ.measure : Measure K) (inverseTimeTranslate ϕ step A n) =
      (μ.measure : Measure K) A := by
  have h := congrArg (fun r : NNReal ↦ (r : ENNReal))
    (μ.measure_preimage_time ((n : ℝ) * step) hA)
  simpa only [inverseTimeTranslate,
    ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using h

/-- A measurable set with pairwise disjoint nonnegative-integer time
translates has zero mass under every invariant probability. -/
theorem measure_eq_zero_of_pairwise_disjoint_translates
    {ϕ : Flow ℝ K} (μ : InvariantProbabilityMeasure ϕ)
    (step : ℝ) {A : Set K} (hA : MeasurableSet A)
    (hdisjoint :
      Pairwise (Disjoint on
        inverseTimeTranslate ϕ step A)) :
    (μ.measure : Measure K) A = 0 := by
  by_contra hpositive
  have hmeasure :
      ∀ n : ℕ,
        (μ.measure : Measure K) (inverseTimeTranslate ϕ step A n) =
          (μ.measure : Measure K) A :=
    measure_inverseTimeTranslate μ step hA
  have hunion :
      (μ.measure : Measure K)
          (⋃ n : ℕ, inverseTimeTranslate ϕ step A n) =
        ∑' n : ℕ,
          (μ.measure : Measure K)
            (inverseTimeTranslate ϕ step A n) := by
    exact measure_iUnion hdisjoint
      (measurableSet_inverseTimeTranslate ϕ step hA)
  have htop :
      (∑' n : ℕ,
        (μ.measure : Measure K)
          (inverseTimeTranslate ϕ step A n)) = ∞ := by
    rw [show (fun n : ℕ ↦
        (μ.measure : Measure K)
          (inverseTimeTranslate ϕ step A n)) =
          (fun _ : ℕ ↦ (μ.measure : Measure K) A) by
      funext n
      exact hmeasure n]
    exact ENNReal.tsum_const_eq_top_of_ne_zero hpositive
  have hfinite :
      (μ.measure : Measure K) (⋃ n : ℕ,
        inverseTimeTranslate ϕ step A n) ≠ ∞ :=
    measure_ne_top (μ.measure : Measure K) _
  exact hfinite (hunion.trans htop)

/-- A countable union of measurable wandering sets is null. -/
theorem measure_iUnion_eq_zero_of_pairwise_disjoint_translates
    {ϕ : Flow ℝ K} (μ : InvariantProbabilityMeasure ϕ)
    (step : ℕ → ℝ) (A : ℕ → Set K)
    (hA : ∀ m, MeasurableSet (A m))
    (hwandering : ∀ m,
      Pairwise (Disjoint on
        inverseTimeTranslate ϕ (step m) (A m))) :
    (μ.measure : Measure K) (⋃ m, A m) = 0 := by
  exact measure_iUnion_null fun m ↦
    measure_eq_zero_of_pairwise_disjoint_translates
      μ (step m) (hA m) (hwandering m)

/-- If a measurable set is contained in a countable union of wandering
sets, it is null. -/
theorem measure_eq_zero_of_subset_iUnion_wandering
    {ϕ : Flow ℝ K} (μ : InvariantProbabilityMeasure ϕ)
    (U : Set K) (step : ℕ → ℝ) (A : ℕ → Set K)
    (hsubset : U ⊆ ⋃ m, A m)
    (hA : ∀ m, MeasurableSet (A m))
    (hwandering : ∀ m,
      Pairwise (Disjoint on
        inverseTimeTranslate ϕ (step m) (A m))) :
    (μ.measure : Measure K) U = 0 := by
  apply nonpos_iff_eq_zero.mp
  calc
    (μ.measure : Measure K) U ≤
        (μ.measure : Measure K) (⋃ m, A m) :=
      measure_mono hsubset
    _ = 0 :=
      measure_iUnion_eq_zero_of_pairwise_disjoint_translates
        μ step A hA hwandering

end HGAS.Dynamics
