import HGAS.Dynamics.InvariantProbabilityCompact
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Topology.Bases

/-!
# Krylov--Bogolyubov construction

This file develops the empirical-measure proof that a continuous self-map
of a nonempty compact metric space admits an invariant probability measure.
It then applies the discrete theorem to increasingly fine time maps of a
continuous real flow.

The construction is explicit: the `n`-th empirical probability is the
uniform average of the first `n+1` Dirac masses along an orbit.  Compactness
of the weak probability topology supplies a convergent subsequence, and the
telescoping endpoint error proves invariance of its limit.
-/

noncomputable section

open Function MeasureTheory Set Filter Topology
open scoped BigOperators BoundedContinuousFunction ENNReal

namespace HGAS.Dynamics

variable {K : Type*} [MetricSpace K] [MeasurableSpace K] [BorelSpace K]

/-- The ordinary measure underlying the uniform empirical distribution on
the first `n+1` points of the forward orbit of `x` under `T`. -/
def empiricalOrbitMeasureRaw (T : K → K) (x : K) (n : ℕ) : Measure K :=
  (n + 1 : ℝ≥0∞)⁻¹ •
    ∑ i ∈ Finset.range (n + 1), Measure.dirac ((T^[i]) x)

omit [MetricSpace K] [BorelSpace K] in
/-- The empirical orbit measure has total mass one. -/
theorem empiricalOrbitMeasureRaw_apply_univ
    (T : K → K) (x : K) (n : ℕ) :
    empiricalOrbitMeasureRaw T x n Set.univ = 1 := by
  simp [empiricalOrbitMeasureRaw, Measure.smul_apply,
    ENNReal.inv_mul_cancel]

/-- The empirical orbit measure, bundled as a probability measure. -/
def empiricalOrbitProbability (T : K → K) (x : K) (n : ℕ) :
    ProbabilityMeasure K :=
  ⟨empiricalOrbitMeasureRaw T x n,
    ⟨empiricalOrbitMeasureRaw_apply_univ T x n⟩⟩

omit [MetricSpace K] [BorelSpace K] in
@[simp]
theorem empiricalOrbitProbability_toMeasure
    (T : K → K) (x : K) (n : ℕ) :
    (empiricalOrbitProbability T x n : Measure K) =
      empiricalOrbitMeasureRaw T x n :=
  rfl

/-- Integrating against an empirical probability is taking the finite
arithmetic mean along the orbit. -/
theorem integral_empiricalOrbitProbability
    (T : K → K) (x : K) (n : ℕ) (f : K →ᵇ ℝ) :
    (∫ y, f y ∂(empiricalOrbitProbability T x n : Measure K)) =
      (n + 1 : ℝ)⁻¹ *
        ∑ i ∈ Finset.range (n + 1), f ((T^[i]) x) := by
  rw [empiricalOrbitProbability_toMeasure]
  simp only [empiricalOrbitMeasureRaw, integral_smul_measure,
    ENNReal.toReal_inv]
  rw [integral_finsetSum_measure]
  · have hcast :
        (↑n + 1 : ℝ≥0∞).toReal = (n + 1 : ℝ) := by
      rw [show (↑n + 1 : ℝ≥0∞) = ↑(n + 1) by norm_num,
        ENNReal.toReal_natCast]
      norm_num
    simp [hcast]
  · intro i _
    exact integrable_dirac (by simp)

/-- Shifting a finite range sum by one only changes its two endpoints. -/
theorem sum_range_comp_succ_sub_sum_range
    (a : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), a (i + 1)) -
        ∑ i ∈ Finset.range (n + 1), a i =
      a (n + 1) - a 0 := by
  calc
    (∑ i ∈ Finset.range (n + 1), a (i + 1)) -
          ∑ i ∈ Finset.range (n + 1), a i =
        ((∑ i ∈ Finset.range n, a (i + 1)) + a (n + 1)) -
          (a 0 + ∑ i ∈ Finset.range n, a (i + 1)) := by
            rw [Finset.sum_range_succ, Finset.sum_range_succ']
            ring
    _ = a (n + 1) - a 0 := by ring

/-- Exact endpoint formula for the change in an empirical average after
composing the observable with the dynamics. -/
theorem empirical_average_comp_sub
    (T : K → K) (hT : Continuous T) (x : K) (n : ℕ) (f : K →ᵇ ℝ) :
    (∫ y, f (T y) ∂(empiricalOrbitProbability T x n : Measure K)) -
        (∫ y, f y ∂(empiricalOrbitProbability T x n : Measure K)) =
      (n + 1 : ℝ)⁻¹ *
        (f ((T^[n + 1]) x) - f x) := by
  let fT : K →ᵇ ℝ := f.compContinuous ⟨T, hT⟩
  change (∫ y, fT y ∂(empiricalOrbitProbability T x n : Measure K)) -
      (∫ y, f y ∂(empiricalOrbitProbability T x n : Measure K)) = _
  rw [integral_empiricalOrbitProbability, integral_empiricalOrbitProbability,
    ← mul_sub]
  congr 1
  have hshift :
      (∑ i ∈ Finset.range (n + 1), fT ((T^[i]) x)) =
        ∑ i ∈ Finset.range (n + 1), f ((T^[i + 1]) x) := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [fT, BoundedContinuousFunction.compContinuous_apply,
      ContinuousMap.coe_mk]
    change f (T ((T^[i]) x)) = f ((T^[i + 1]) x)
    rw [← Function.iterate_succ_apply' T i x]
  rw [hshift]
  simpa only [Function.iterate_zero_apply] using
    sum_range_comp_succ_sub_sum_range
      (fun i ↦ f ((T^[i]) x)) n

/-- The endpoint error in the empirical-average identity tends to zero.

The proof uses only boundedness of the observable: the numerator is bounded
uniformly by twice the sup norm, whereas the denominator is `n+1`. -/
theorem tendsto_empirical_average_comp_sub
    (T : K → K) (hT : Continuous T) (x : K) (f : K →ᵇ ℝ) :
    Tendsto
        (fun n ↦
          (∫ y, f (T y) ∂(empiricalOrbitProbability T x n : Measure K)) -
            ∫ y, f y ∂(empiricalOrbitProbability T x n : Measure K))
        atTop (𝓝 0) := by
  have hbounded :
      ∀ n : ℕ, |f ((T^[n + 1]) x) - f x| ≤ 2 * ‖f‖ := by
    intro n
    calc
      |f ((T^[n + 1]) x) - f x| ≤
          |f ((T^[n + 1]) x)| + |f x| := abs_sub _ _
      _ ≤ ‖f‖ + ‖f‖ := by
        exact add_le_add (f.norm_coe_le_norm _) (f.norm_coe_le_norm _)
      _ = 2 * ‖f‖ := by ring
  have hzero :
      Tendsto
        (fun n : ℕ ↦
          (f ((T^[n + 1]) x) - f x) * (n + 1 : ℝ)⁻¹)
        atTop (𝓝 0) := by
    apply bdd_le_mul_tendsto_zero' (2 * ‖f‖)
    · exact Filter.Eventually.of_forall hbounded
    · simpa only [one_div] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  convert hzero using 1
  funext n
  rw [empirical_average_comp_sub T hT x n f]
  exact mul_comm _ _

/-- Push a probability measure forward by a continuous self-map.

Bundling the map as a `ContinuousMap` keeps measurability witnesses out of
later statements and makes the construction convenient to reuse. -/
def continuousMapPushforward (T : C(K, K)) (μ : ProbabilityMeasure K) :
    ProbabilityMeasure K :=
  μ.map T.continuous.measurable.aemeasurable

@[simp]
theorem continuousMapPushforward_toMeasure
    (T : C(K, K)) (μ : ProbabilityMeasure K) :
    (continuousMapPushforward T μ : Measure K) =
      Measure.map T (μ : Measure K) :=
  rfl

/-- Pushforward by a continuous self-map is continuous for the topology of
weak convergence of probability measures. -/
theorem continuous_continuousMapPushforward (T : C(K, K)) :
    Continuous (continuousMapPushforward T) := by
  simpa only [continuousMapPushforward] using
    ProbabilityMeasure.continuous_map T.continuous

/-- **Discrete Krylov--Bogolyubov theorem.**

Every continuous self-map of a nonempty compact metric space fixes a Borel
probability measure.

The empirical orbit probabilities have a weakly convergent subsequence by
compactness.  Their pushforwards have the same weak limit because the
telescoping defect tends to zero.  On the other hand, continuity of
pushforward says that their limit is the pushforward of the original weak
limit.  Uniqueness of limits then gives the fixed-point identity. -/
theorem exists_probability_fixed_by_continuousMap
    [CompactSpace K] [Nonempty K] (T : C(K, K)) :
    ∃ μ : ProbabilityMeasure K, continuousMapPushforward T μ = μ := by
  let x : K := Classical.choice ‹Nonempty K›
  let empirical : ℕ → ProbabilityMeasure K :=
    fun n ↦ empiricalOrbitProbability T x n
  obtain ⟨μ, ψ, hψ, hμ⟩ :=
    CompactSpace.tendsto_subseq empirical
  have hψ_top : Tendsto ψ atTop atTop :=
    hψ.tendsto_atTop
  have hpush_to_μ :
      Tendsto
        (fun n ↦ continuousMapPushforward T (empirical (ψ n)))
        atTop (𝓝 μ) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    have hbase :
        Tendsto
          (fun n ↦ ∫ y, f y ∂(empirical (ψ n) : Measure K))
          atTop (𝓝 (∫ y, f y ∂(μ : Measure K))) :=
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ) f
    have hdefect :
        Tendsto
          (fun n ↦
            (∫ y, f (T y) ∂(empirical (ψ n) : Measure K)) -
              ∫ y, f y ∂(empirical (ψ n) : Measure K))
          atTop (𝓝 0) := by
      simpa only [empirical] using
        (tendsto_empirical_average_comp_sub
          (T := (T : K → K)) T.continuous x f).comp hψ_top
    have hcomp :
        Tendsto
          (fun n ↦ ∫ y, f (T y) ∂(empirical (ψ n) : Measure K))
          atTop (𝓝 (∫ y, f y ∂(μ : Measure K))) := by
      simpa only [sub_add_cancel, zero_add] using hdefect.add hbase
    convert hcomp using 1
    funext n
    rw [continuousMapPushforward_toMeasure,
      integral_map T.continuous.measurable.aemeasurable]
    fun_prop
  have hpush_to_push :
      Tendsto
        (fun n ↦ continuousMapPushforward T (empirical (ψ n)))
        atTop (𝓝 (continuousMapPushforward T μ)) :=
    (continuous_continuousMapPushforward T).continuousAt.tendsto.comp hμ
  exact ⟨μ, tendsto_nhds_unique hpush_to_push hpush_to_μ⟩

/-- The time-`t` map of a flow, bundled as a continuous self-map. -/
def flowTimeContinuousMap (ϕ : Flow ℝ K) (t : ℝ) : C(K, K) :=
  ⟨ϕ t, ϕ.continuous_toFun t⟩

omit [MeasurableSpace K] [BorelSpace K] in
@[simp]
theorem flowTimeContinuousMap_apply
    (ϕ : Flow ℝ K) (t : ℝ) (x : K) :
    flowTimeContinuousMap ϕ t x = ϕ t x :=
  rfl

/-- The generic continuous-map pushforward specializes to the previously
defined time pushforward for a flow. -/
theorem continuousMapPushforward_flowTime
    (ϕ : Flow ℝ K) (μ : ProbabilityMeasure K) (t : ℝ) :
    continuousMapPushforward (flowTimeContinuousMap ϕ t) μ =
      timePushforward ϕ μ t :=
  rfl

/-- Time pushforwards respect addition of times.

The order on the right reflects the convention
`ϕ (s+t) x = ϕ s (ϕ t x)`. -/
theorem timePushforward_add
    (ϕ : Flow ℝ K) (μ : ProbabilityMeasure K) (s t : ℝ) :
    timePushforward ϕ μ (s + t) =
      timePushforward ϕ (timePushforward ϕ μ t) s := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [timePushforward, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map
    (ϕ.continuous_toFun s).measurable
    (ϕ.continuous_toFun t).measurable]
  apply Measure.map_congr
  filter_upwards with x
  exact ϕ.map_add s t x

/-- Probabilities fixed by one specified time map. -/
def fixedProbabilityAtTime
    (ϕ : Flow ℝ K) (t : ℝ) : Set (ProbabilityMeasure K) :=
  {μ | timePushforward ϕ μ t = μ}

/-- The fixed probabilities for a specified time form a closed set in the
weak topology. -/
theorem isClosed_fixedProbabilityAtTime
    (ϕ : Flow ℝ K) (t : ℝ) :
    IsClosed (fixedProbabilityAtTime ϕ t) := by
  exact isClosed_eq (continuous_timePushforward ϕ t) continuous_id

/-- Every individual time map of a flow fixes at least one probability on a
nonempty compact metric state space. -/
theorem fixedProbabilityAtTime_nonempty
    [CompactSpace K] [Nonempty K] (ϕ : Flow ℝ K) (t : ℝ) :
    (fixedProbabilityAtTime ϕ t).Nonempty := by
  obtain ⟨μ, hμ⟩ :=
    exists_probability_fixed_by_continuousMap
      (flowTimeContinuousMap ϕ t)
  exact ⟨μ, by
    simpa only [fixedProbabilityAtTime,
      continuousMapPushforward_flowTime] using hμ⟩

/-- The dyadic time scale used to pass from discrete to continuous time. -/
def dyadicTime (n : ℕ) : ℝ :=
  (2 : ℝ)⁻¹ ^ n

theorem dyadicTime_pos (n : ℕ) : 0 < dyadicTime n := by
  unfold dyadicTime
  positivity

/-- Each dyadic time is twice the next, the key relation making the fixed
sets below nested. -/
theorem dyadicTime_eq_add_next (n : ℕ) :
    dyadicTime n = dyadicTime (n + 1) + dyadicTime (n + 1) := by
  simp only [dyadicTime, pow_succ]
  ring

/-- A probability fixed at the next dyadic time is fixed at the preceding
dyadic time. -/
theorem fixedProbabilityAtTime_dyadic_antitone
    (ϕ : Flow ℝ K) (n : ℕ) :
    fixedProbabilityAtTime ϕ (dyadicTime (n + 1)) ⊆
      fixedProbabilityAtTime ϕ (dyadicTime n) := by
  intro μ hμ
  change timePushforward ϕ μ (dyadicTime n) = μ
  rw [dyadicTime_eq_add_next, timePushforward_add, hμ, hμ]

/-- There is one probability measure fixed simultaneously by every dyadic
time map.

For each `n`, let `Fₙ` be the closed set of probabilities fixed at time
`2⁻ⁿ`.  The discrete theorem makes every `Fₙ` nonempty, and the doubling
identity makes this sequence decreasing.  Cantor's intersection theorem in
the compact space of probability measures then supplies a common point. -/
theorem exists_probability_fixed_at_all_dyadicTimes
    [CompactSpace K] [Nonempty K] (ϕ : Flow ℝ K) :
    ∃ μ : ProbabilityMeasure K,
      ∀ n : ℕ, timePushforward ϕ μ (dyadicTime n) = μ := by
  let F : ℕ → Set (ProbabilityMeasure K) :=
    fun n ↦ fixedProbabilityAtTime ϕ (dyadicTime n)
  have hdecreasing : ∀ n, F (n + 1) ⊆ F n := by
    intro n
    exact fixedProbabilityAtTime_dyadic_antitone ϕ n
  have hnonempty : ∀ n, (F n).Nonempty := by
    intro n
    exact fixedProbabilityAtTime_nonempty ϕ (dyadicTime n)
  have hclosed : ∀ n, IsClosed (F n) := by
    intro n
    exact isClosed_fixedProbabilityAtTime ϕ (dyadicTime n)
  have hcompact_zero : IsCompact (F 0) :=
    (hclosed 0).isCompact
  obtain ⟨μ, hμ⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      F hdecreasing hnonempty hcompact_zero hclosed
  refine ⟨μ, fun n ↦ ?_⟩
  exact mem_iInter.mp hμ n

/-- For a fixed probability, its pushforward varies continuously with the
time parameter of a continuous flow.

Weak continuity is tested against a bounded continuous observable `f`.
After the change-of-variables formula for a pushforward, the relevant
quantity is
`t ↦ ∫ x, f (ϕ t x) ∂μ`; continuity follows from the standard theorem on a
continuous parametric integral over the compact state space. -/
theorem continuous_timePushforward_in_time
    [CompactSpace K] (ϕ : Flow ℝ K) (μ : ProbabilityMeasure K) :
    Continuous (fun t : ℝ ↦ timePushforward ϕ μ t) := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuous_integral]
  intro f
  have hparam :
      Continuous (fun t : ℝ ↦
        ∫ x in (Set.univ : Set K), f (ϕ t x) ∂(μ : Measure K)) := by
    apply continuous_parametric_integral_of_continuous
    · fun_prop
    · exact isCompact_univ
  convert hparam using 1
  funext t
  simp only [Measure.restrict_univ]
  rw [timePushforward, ProbabilityMeasure.toMeasure_map,
    integral_map (ϕ.continuous_toFun t).measurable.aemeasurable]
  fun_prop

/-- For a fixed probability, the times at which it is invariant form an
additive subgroup of the real line. -/
def invariantTimeAddSubgroup
    (ϕ : Flow ℝ K) (μ : ProbabilityMeasure K) : AddSubgroup ℝ where
  carrier := {t | timePushforward ϕ μ t = μ}
  zero_mem' := InvariantProbabilityMeasure.timePushforward_zero μ
  add_mem' := by
    intro s t hs ht
    change timePushforward ϕ μ s = μ at hs
    change timePushforward ϕ μ t = μ at ht
    change timePushforward ϕ μ (s + t) = μ
    rw [timePushforward_add, ht, hs]
  neg_mem' := by
    intro t ht
    change timePushforward ϕ μ t = μ at ht
    change timePushforward ϕ μ (-t) = μ
    have h := timePushforward_add ϕ μ (-t) t
    rw [neg_add_cancel, InvariantProbabilityMeasure.timePushforward_zero, ht] at h
    exact h.symm

@[simp]
theorem mem_invariantTimeAddSubgroup
    (ϕ : Flow ℝ K) (μ : ProbabilityMeasure K) (t : ℝ) :
    t ∈ invariantTimeAddSubgroup ϕ μ ↔
      timePushforward ϕ μ t = μ :=
  Iff.rfl

/-- On a compact state space, the additive subgroup of invariant times is
closed. -/
theorem isClosed_invariantTimeAddSubgroup
    [CompactSpace K] (ϕ : Flow ℝ K) (μ : ProbabilityMeasure K) :
    IsClosed (invariantTimeAddSubgroup ϕ μ : Set ℝ) := by
  exact isClosed_eq
    (continuous_timePushforward_in_time ϕ μ) continuous_const

/-- If a probability is fixed by every dyadic time, then its subgroup of
invariant times is dense in `ℝ`.

Indeed, that subgroup contains the positive sequence `2⁻ⁿ`, which converges
to zero.  An additive subgroup of an Archimedean ordered group with
arbitrarily small positive elements is dense. -/
theorem dense_invariantTimeAddSubgroup_of_dyadic
    (ϕ : Flow ℝ K) (μ : ProbabilityMeasure K)
    (hdyadic : ∀ n : ℕ, timePushforward ϕ μ (dyadicTime n) = μ) :
    Dense (invariantTimeAddSubgroup ϕ μ : Set ℝ) := by
  apply AddSubgroup.dense_of_not_isolated_zero
  intro ε hε
  have hdyadic_zero : Tendsto dyadicTime atTop (𝓝 0) := by
    simpa only [dyadicTime] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (𝕜 := ℝ) (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num))
  obtain ⟨n, hn⟩ :=
    ((tendsto_order.mp hdyadic_zero).2 ε hε).exists
  refine ⟨dyadicTime n, ?_, ?_⟩
  · exact hdyadic n
  · exact ⟨dyadicTime_pos n, hn⟩

/-- Invariance at all dyadic times implies invariance at every real time.

The dyadic times make the invariant-time subgroup dense, while continuity
of the flow makes it closed.  A closed dense subgroup of `ℝ` is the whole
line. -/
theorem isInvariantProbability_of_dyadic
    [CompactSpace K] (ϕ : Flow ℝ K) (μ : ProbabilityMeasure K)
    (hdyadic : ∀ n : ℕ, timePushforward ϕ μ (dyadicTime n) = μ) :
    IsInvariantProbability ϕ μ := by
  let S : AddSubgroup ℝ := invariantTimeAddSubgroup ϕ μ
  have hdense : Dense (S : Set ℝ) := by
    exact dense_invariantTimeAddSubgroup_of_dyadic ϕ μ hdyadic
  have hclosed : IsClosed (S : Set ℝ) := by
    exact isClosed_invariantTimeAddSubgroup ϕ μ
  have hS : (S : Set ℝ) = Set.univ := by
    calc
      (S : Set ℝ) = closure (S : Set ℝ) := hclosed.closure_eq.symm
      _ = Set.univ := hdense.closure_eq
  intro t
  have ht : t ∈ S := by
    change t ∈ (S : Set ℝ)
    rw [hS]
    exact mem_univ t
  exact ht

/-- **Continuous-time Krylov--Bogolyubov theorem.**

Every continuous real flow on a nonempty compact metric space equipped with
its Borel measurable structure admits an invariant Borel probability
measure. -/
theorem exists_invariantProbability_krylovBogolyubov
    [CompactSpace K] [Nonempty K] (ϕ : Flow ℝ K) :
    ∃ μ : ProbabilityMeasure K, IsInvariantProbability ϕ μ := by
  obtain ⟨μ, hdyadic⟩ :=
    exists_probability_fixed_at_all_dyadicTimes ϕ
  exact ⟨μ, isInvariantProbability_of_dyadic ϕ μ hdyadic⟩

/-- Bundled form of the continuous-time Krylov--Bogolyubov theorem. -/
theorem nonempty_invariantProbabilityMeasure
    [CompactSpace K] [Nonempty K] (ϕ : Flow ℝ K) :
    Nonempty (InvariantProbabilityMeasure ϕ) := by
  obtain ⟨μ, hμ⟩ :=
    exists_invariantProbability_krylovBogolyubov ϕ
  exact ⟨⟨μ, hμ⟩⟩

/-- Set-theoretic form: the closed set of invariant probabilities is
nonempty. -/
theorem invariantProbabilitySet_nonempty
    [CompactSpace K] [Nonempty K] (ϕ : Flow ℝ K) :
    (invariantProbabilitySet ϕ).Nonempty := by
  obtain ⟨μ, hμ⟩ :=
    exists_invariantProbability_krylovBogolyubov ϕ
  exact ⟨μ, hμ⟩

end HGAS.Dynamics
