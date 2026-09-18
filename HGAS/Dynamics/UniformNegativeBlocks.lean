import HGAS.Dynamics.TimeAverages
import HGAS.Dynamics.InvariantProbabilityCompact
import HGAS.Dynamics.KrylovBogolyubov

/-!
# Uniform negative orbit blocks

This file proves the uniform-negative-block principle used in the paper.
For a continuous real flow `ϕ` on a nonempty compact metric space and a
bounded continuous observable `a`, the following conditions are equivalent:

* every invariant probability has strictly negative average of `a`;
* there are `T > 0` and `c > 0` such that every orbit segment of length
  `T` has integral at most `-c`.

The easy direction integrates the pointwise block estimate against an
invariant probability.  For the converse, assume no such block exists.
For every integer length `n+1`, choose an orbit segment whose integral is
greater than `-1`, and put normalized Lebesgue measure on that segment.
Compactness gives a weak limit of these occupation probabilities.  The
endpoint error under any fixed time shift is `O(1/(n+1))`, so the limit is
invariant.  Its `a`-average is nonnegative, a contradiction.
-/

noncomputable section

open Function MeasureTheory Set Filter Topology
open scoped BoundedContinuousFunction ENNReal Interval

namespace HGAS.Dynamics

variable {K : Type*} [MetricSpace K] [MeasurableSpace K] [BorelSpace K]

/-- Normalized Lebesgue measure on the interval `(0,T]`, for `T > 0`. -/
def positiveIntervalProbability (T : ℝ) (hT : 0 < T) :
    ProbabilityMeasure ℝ :=
  ⟨(ENNReal.ofReal T)⁻¹ • volume.restrict (Ioc 0 T), by
    constructor
    simp only [Measure.smul_apply,
      Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
    exact ENNReal.inv_mul_cancel
      (ENNReal.ofReal_ne_zero_iff.mpr hT)
      ENNReal.ofReal_ne_top⟩

/-- The occupation probability of the orbit segment
`{ϕ t x | 0 < t ≤ T}`, with normalized Lebesgue time. -/
def orbitOccupationProbability
    (ϕ : Flow ℝ K) (x : K) (T : ℝ) (hT : 0 < T) :
    ProbabilityMeasure K :=
  (positiveIntervalProbability T hT).map
    (f := fun t : ℝ ↦ ϕ t x)
    (ϕ.continuous continuous_id continuous_const).measurable.aemeasurable

/-- Integration against an occupation probability is the normalized
finite-time orbit integral. -/
theorem integral_orbitOccupationProbability
    (ϕ : Flow ℝ K) (a : K →ᵇ ℝ) (x : K)
    (T : ℝ) (hT : 0 < T) :
    (∫ y, a y ∂(orbitOccupationProbability ϕ x T hT : Measure K)) =
      T⁻¹ * orbitIntegral ϕ a T x := by
  rw [orbitOccupationProbability, ProbabilityMeasure.toMeasure_map,
    integral_map (φ := fun t : ℝ ↦ ϕ t x) (by fun_prop) (by fun_prop)]
  change
    (∫ t, a (ϕ t x) ∂
      (ENNReal.ofReal T)⁻¹ • volume.restrict (Ioc 0 T)) =
      T⁻¹ * orbitIntegral ϕ a T x
  rw [integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hT.le,
    ← intervalIntegral.integral_of_le hT.le]
  simp only [smul_eq_mul, orbitIntegral]

omit [MeasurableSpace K] [BorelSpace K] in
/-- Shifting the initial point by time `s` changes a length-`T` orbit
integral only through two endpoint pieces of length `s`. -/
theorem orbitIntegral_shift_sub
    (ϕ : Flow ℝ K) (a : K →ᵇ ℝ) (T s : ℝ) (x : K) :
    orbitIntegral ϕ a T (ϕ s x) - orbitIntegral ϕ a T x =
      orbitIntegral ϕ a s (ϕ T x) - orbitIntegral ϕ a s x := by
  have h₁ := orbitIntegral_add ϕ a s T x
  have h₂ := orbitIntegral_add ϕ a T s x
  rw [add_comm s T] at h₁
  linarith

/-- Exact endpoint formula for the change in an occupation average after a
fixed time shift. -/
theorem integral_timePushforward_orbitOccupation_sub
    (ϕ : Flow ℝ K) (f : K →ᵇ ℝ) (x : K)
    (T : ℝ) (hT : 0 < T) (s : ℝ) :
    (∫ y, f y ∂
        (timePushforward ϕ (orbitOccupationProbability ϕ x T hT) s :
          Measure K)) -
        (∫ y, f y ∂
          (orbitOccupationProbability ϕ x T hT : Measure K)) =
      T⁻¹ *
        (orbitIntegral ϕ f s (ϕ T x) - orbitIntegral ϕ f s x) := by
  let fs : K →ᵇ ℝ :=
    f.compContinuous (flowTimeContinuousMap ϕ s)
  have hshift :
      orbitIntegral ϕ fs T x =
        orbitIntegral ϕ f T (ϕ s x) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only [fs,
      BoundedContinuousFunction.compContinuous_apply,
      flowTimeContinuousMap_apply]
    rw [← ϕ.map_add s t x, ← ϕ.map_add t s x, add_comm]
  rw [timePushforward, ProbabilityMeasure.toMeasure_map,
    integral_map (φ := ϕ s) (by fun_prop) (by fun_prop)]
  change
    (∫ y, fs y ∂
      (orbitOccupationProbability ϕ x T hT : Measure K)) -
        (∫ y, f y ∂
          (orbitOccupationProbability ϕ x T hT : Measure K)) = _
  rw [integral_orbitOccupationProbability,
    integral_orbitOccupationProbability, hshift, ← mul_sub,
    orbitIntegral_shift_sub]

/-- For orbit segments of lengths `n+1`, the effect of any fixed time shift
on the integral of a bounded continuous test function tends to zero,
uniformly in the chosen initial points. -/
theorem tendsto_occupation_timePushforward_integral_sub
    (ϕ : Flow ℝ K) (f : K →ᵇ ℝ) (x : ℕ → K) (s : ℝ) :
    Tendsto
      (fun n ↦
        (∫ y, f y ∂
          (timePushforward ϕ
            (orbitOccupationProbability ϕ (x n) (n + 1 : ℝ) (by positivity))
            s : Measure K)) -
          ∫ y, f y ∂
            (orbitOccupationProbability ϕ (x n) (n + 1 : ℝ) (by positivity) :
              Measure K))
      atTop (𝓝 0) := by
  have hbounded :
      ∀ n : ℕ,
        |orbitIntegral ϕ f s (ϕ (n + 1 : ℝ) (x n)) -
            orbitIntegral ϕ f s (x n)| ≤
          2 * (‖f‖ * |s|) := by
    intro n
    calc
      |orbitIntegral ϕ f s (ϕ (n + 1 : ℝ) (x n)) -
          orbitIntegral ϕ f s (x n)| ≤
          |orbitIntegral ϕ f s (ϕ (n + 1 : ℝ) (x n))| +
            |orbitIntegral ϕ f s (x n)| := abs_sub _ _
      _ ≤ (‖f‖ * |s|) + (‖f‖ * |s|) := by
        exact add_le_add
          (norm_orbitIntegral_le ϕ f s _)
          (norm_orbitIntegral_le ϕ f s _)
      _ = 2 * (‖f‖ * |s|) := by ring
  have hzero :
      Tendsto
        (fun n : ℕ ↦
          (orbitIntegral ϕ f s (ϕ (n + 1 : ℝ) (x n)) -
              orbitIntegral ϕ f s (x n)) *
            (n + 1 : ℝ)⁻¹)
        atTop (𝓝 0) := by
    apply bdd_le_mul_tendsto_zero' (2 * (‖f‖ * |s|))
    · exact Eventually.of_forall hbounded
    · simpa only [one_div] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  convert hzero using 1
  funext n
  rw [integral_timePushforward_orbitOccupation_sub]
  exact mul_comm _ _

/-- Occupation probabilities of orbit segments whose lengths tend through
the positive integers have an invariant weak subsequential limit.

The initial point may vary arbitrarily with the length.  This flexibility
is exactly what is needed in the compactness contradiction for uniform
negative blocks. -/
theorem exists_invariantProbability_limit_of_occupations
    [CompactSpace K] (ϕ : Flow ℝ K) (x : ℕ → K) :
    ∃ (μ : ProbabilityMeasure K) (ψ : ℕ → ℕ),
      StrictMono ψ ∧
      Tendsto
        ((fun n ↦
          orbitOccupationProbability ϕ (x n) (n + 1 : ℝ) (by positivity)) ∘ ψ)
        atTop (𝓝 μ) ∧
      IsInvariantProbability ϕ μ := by
  let occupation : ℕ → ProbabilityMeasure K :=
    fun n ↦
      orbitOccupationProbability ϕ (x n) (n + 1 : ℝ) (by positivity)
  obtain ⟨μ, ψ, hψ, hμ⟩ :=
    CompactSpace.tendsto_subseq occupation
  have hψ_top : Tendsto ψ atTop atTop :=
    hψ.tendsto_atTop
  have hinvariant : IsInvariantProbability ϕ μ := by
    intro s
    have hpush_to_μ :
        Tendsto
          (fun n ↦ timePushforward ϕ (occupation (ψ n)) s)
          atTop (𝓝 μ) := by
      rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
      intro f
      have hbase :
          Tendsto
            (fun n ↦ ∫ y, f y ∂(occupation (ψ n) : Measure K))
            atTop (𝓝 (∫ y, f y ∂(μ : Measure K))) :=
        (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ) f
      have hdefect :
          Tendsto
            (fun n ↦
              (∫ y, f y ∂
                (timePushforward ϕ (occupation (ψ n)) s : Measure K)) -
                ∫ y, f y ∂(occupation (ψ n) : Measure K))
            atTop (𝓝 0) := by
        simpa only [occupation, Function.comp_apply] using
          (tendsto_occupation_timePushforward_integral_sub
            ϕ f x s).comp hψ_top
      simpa only [sub_add_cancel, zero_add] using hdefect.add hbase
    have hpush_to_push :
        Tendsto
          (fun n ↦ timePushforward ϕ (occupation (ψ n)) s)
          atTop (𝓝 (timePushforward ϕ μ s)) :=
      (continuous_timePushforward ϕ s).continuousAt.tendsto.comp hμ
    exact tendsto_nhds_unique hpush_to_push hpush_to_μ
  exact ⟨μ, ψ, hψ, hμ, hinvariant⟩

/-- Long orbit segments whose unnormalized `a`-integrals stay above `-1`
produce an invariant probability with nonnegative `a`-average.

The constant `-1` is immaterial; after division by the segment length its
effect vanishes. -/
theorem exists_invariantProbability_nonnegative_average_of_long_segments
    [CompactSpace K] (ϕ : Flow ℝ K) (a : K →ᵇ ℝ) (x : ℕ → K)
    (hx : ∀ n : ℕ,
      -1 < orbitIntegral ϕ a (n + 1 : ℝ) (x n)) :
    ∃ μ : ProbabilityMeasure K,
      IsInvariantProbability ϕ μ ∧ 0 ≤ observableAverage a μ := by
  obtain ⟨μ, ψ, hψ, hμ, hinvariant⟩ :=
    exists_invariantProbability_limit_of_occupations ϕ x
  have hψ_top : Tendsto ψ atTop atTop :=
    hψ.tendsto_atTop
  have havg :
      Tendsto
        (fun n ↦
          ∫ y, a y ∂
            (orbitOccupationProbability ϕ (x (ψ n))
              (ψ n + 1 : ℝ) (by positivity) : Measure K))
        atTop (𝓝 (observableAverage a μ)) := by
    simpa only [observableAverage, Function.comp_apply] using
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ) a
  have hlower_zero :
      Tendsto (fun n : ℕ ↦ -((ψ n + 1 : ℝ)⁻¹))
        atTop (𝓝 0) := by
    simpa only [one_div, neg_zero] using
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hψ_top).neg
  have hlower :
      ∀ n : ℕ,
        -((ψ n + 1 : ℝ)⁻¹) ≤
          ∫ y, a y ∂
            (orbitOccupationProbability ϕ (x (ψ n))
              (ψ n + 1 : ℝ) (by positivity) : Measure K) := by
    intro n
    rw [integral_orbitOccupationProbability]
    have hpos : 0 < (ψ n + 1 : ℝ)⁻¹ := by positivity
    have hmul :=
      mul_lt_mul_of_pos_left (hx (ψ n)) hpos
    simpa only [mul_neg, mul_one] using hmul.le
  exact ⟨μ, hinvariant,
    le_of_tendsto_of_tendsto'
      hlower_zero havg hlower⟩

/-- A common strictly negative finite-time block. -/
def HasUniformNegativeBlock
    (ϕ : Flow ℝ K) (a : K →ᵇ ℝ) : Prop :=
  ∃ T c : ℝ, 0 < T ∧ 0 < c ∧
    ∀ x : K, orbitIntegral ϕ a T x ≤ -c

/-- The elementary implication: a uniform negative block makes the average
of `a` strictly negative for every invariant probability. -/
theorem invariantAverage_neg_of_uniformNegativeBlock
    [CompactSpace K] (ϕ : Flow ℝ K) (a : K →ᵇ ℝ)
    (hblock : HasUniformNegativeBlock ϕ a)
    (μ : InvariantProbabilityMeasure ϕ) :
    observableAverage a μ.measure < 0 := by
  obtain ⟨T, c, hT, hc, hpointwise⟩ := hblock
  have havg :=
    invariantAverage_le_of_uniformBlock
      ϕ a μ hT hpointwise
  exact havg.trans_lt
    (div_neg_of_neg_of_pos (neg_neg_of_pos hc) hT)

/-- The compactness implication: strict negativity for every invariant
probability produces one common strictly negative finite-time block.

If no block existed, then at each integer length `n+1` some segment would
have integral greater than `-1`.  The preceding occupation-measure theorem
would yield an invariant probability with nonnegative average. -/
theorem uniformNegativeBlock_of_invariantAverage_neg
    [CompactSpace K] [Nonempty K]
    (ϕ : Flow ℝ K) (a : K →ᵇ ℝ)
    (hnegative :
      ∀ μ : InvariantProbabilityMeasure ϕ,
        observableAverage a μ.measure < 0) :
    HasUniformNegativeBlock ϕ a := by
  by_contra hblock
  have hexists :
      ∀ n : ℕ, ∃ x : K,
        -1 < orbitIntegral ϕ a (n + 1 : ℝ) x := by
    intro n
    by_contra hn
    have hall :
        ∀ x : K, orbitIntegral ϕ a (n + 1 : ℝ) x ≤ -1 := by
      intro x
      exact le_of_not_gt fun hx ↦ hn ⟨x, hx⟩
    exact hblock ⟨(n + 1 : ℝ), 1, by positivity, zero_lt_one, hall⟩
  let x : ℕ → K := fun n ↦ Classical.choose (hexists n)
  have hx :
      ∀ n : ℕ, -1 < orbitIntegral ϕ a (n + 1 : ℝ) (x n) :=
    fun n ↦ Classical.choose_spec (hexists n)
  obtain ⟨μ, hinvariant, hnonnegative⟩ :=
    exists_invariantProbability_nonnegative_average_of_long_segments
      ϕ a x hx
  exact (not_lt_of_ge hnonnegative)
    (hnegative ⟨μ, hinvariant⟩)

/-- **Uniform-negative-block equivalence.**

This is the direct formal counterpart of the paper's Lemma 2.3: all
invariant averages are strictly negative if and only if one finite time
block has a uniform strict negative margin. -/
theorem invariantAverage_neg_iff_uniformNegativeBlock
    [CompactSpace K] [Nonempty K]
    (ϕ : Flow ℝ K) (a : K →ᵇ ℝ) :
    (∀ μ : InvariantProbabilityMeasure ϕ,
        observableAverage a μ.measure < 0) ↔
      HasUniformNegativeBlock ϕ a := by
  constructor
  · exact uniformNegativeBlock_of_invariantAverage_neg ϕ a
  · intro hblock μ
    exact invariantAverage_neg_of_uniformNegativeBlock
      ϕ a hblock μ

/-- A chosen invariant probability maximizing the average of `a`.

Existence follows from Krylov--Bogolyubov nonemptiness and compactness of
the invariant-probability set.  Keeping the maximizer as a reusable object
avoids introducing an extended-real supremum. -/
def maximizingInvariantProbability
    [CompactSpace K] [Nonempty K]
    (ϕ : Flow ℝ K) (a : K →ᵇ ℝ) : ProbabilityMeasure K :=
  Classical.choose <|
    maximizingInvariantSet_nonempty ϕ a
      (invariantProbabilitySet_nonempty ϕ)

/-- The chosen maximizing probability is invariant. -/
theorem maximizingInvariantProbability_invariant
    [CompactSpace K] [Nonempty K]
    (ϕ : Flow ℝ K) (a : K →ᵇ ℝ) :
    IsInvariantProbability ϕ (maximizingInvariantProbability ϕ a) := by
  have hmem :
      maximizingInvariantProbability ϕ a ∈
        maximizingInvariantSet ϕ a :=
    Classical.choose_spec <|
      maximizingInvariantSet_nonempty ϕ a
        (invariantProbabilitySet_nonempty ϕ)
  exact hmem.1

/-- The largest invariant average, represented by its attained value. -/
def maximalInvariantAverage
    [CompactSpace K] [Nonempty K]
    (ϕ : Flow ℝ K) (a : K →ᵇ ℝ) : ℝ :=
  observableAverage a (maximizingInvariantProbability ϕ a)

/-- Every invariant average is bounded above by the attained maximal
invariant average. -/
theorem invariantAverage_le_maximalInvariantAverage
    [CompactSpace K] [Nonempty K]
    (ϕ : Flow ℝ K) (a : K →ᵇ ℝ)
    (μ : ProbabilityMeasure K) (hμ : IsInvariantProbability ϕ μ) :
    observableAverage a μ ≤ maximalInvariantAverage ϕ a := by
  have hmem :
      maximizingInvariantProbability ϕ a ∈
        maximizingInvariantSet ϕ a :=
    Classical.choose_spec <|
      maximizingInvariantSet_nonempty ϕ a
        (invariantProbabilitySet_nonempty ϕ)
  exact (isMaxOn_iff.mp hmem.2) μ hμ

/-- Quantitative form of the easy direction at the attained maximum. -/
theorem maximalInvariantAverage_le_of_uniformBlock
    [CompactSpace K] [Nonempty K]
    (ϕ : Flow ℝ K) (a : K →ᵇ ℝ)
    {T c : ℝ} (hT : 0 < T)
    (hblock : ∀ x : K, orbitIntegral ϕ a T x ≤ -c) :
    maximalInvariantAverage ϕ a ≤ -c / T := by
  exact invariantAverage_le_of_uniformBlock
    ϕ a
    ⟨maximizingInvariantProbability ϕ a,
      maximizingInvariantProbability_invariant ϕ a⟩
    hT hblock

/-- **Paper-style form of Lemma 2.3.**

The (attained) maximum invariant average is strictly negative if and only
if there is a positive time and a positive uniform margin for which every
orbit block is negative. -/
theorem maximalInvariantAverage_neg_iff_uniformNegativeBlock
    [CompactSpace K] [Nonempty K]
    (ϕ : Flow ℝ K) (a : K →ᵇ ℝ) :
    maximalInvariantAverage ϕ a < 0 ↔
      HasUniformNegativeBlock ϕ a := by
  constructor
  · intro hmax
    apply uniformNegativeBlock_of_invariantAverage_neg
    intro μ
    exact (invariantAverage_le_maximalInvariantAverage
      ϕ a μ.measure μ.invariant).trans_lt hmax
  · intro hblock
    change observableAverage a
      (maximizingInvariantProbability ϕ a) < 0
    exact invariantAverage_neg_of_uniformNegativeBlock
      ϕ a hblock
      ⟨maximizingInvariantProbability ϕ a,
        maximizingInvariantProbability_invariant ϕ a⟩

/-- Fully expanded paper-facing statement of the uniform-negative-block
lemma, without the abbreviation `HasUniformNegativeBlock`. -/
theorem maximalInvariantAverage_neg_iff_exists_uniformNegativeBlock
    [CompactSpace K] [Nonempty K]
    (ϕ : Flow ℝ K) (a : K →ᵇ ℝ) :
    maximalInvariantAverage ϕ a < 0 ↔
      ∃ T c : ℝ, 0 < T ∧ 0 < c ∧
        ∀ x : K, orbitIntegral ϕ a T x ≤ -c := by
  simpa only [HasUniformNegativeBlock] using
    maximalInvariantAverage_neg_iff_uniformNegativeBlock ϕ a

end HGAS.Dynamics
