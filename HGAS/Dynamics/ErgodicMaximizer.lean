import HGAS.Dynamics.KrylovBogolyubov
import HGAS.Dynamics.ErgodicInvariantProbability
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Dynamics.Ergodic.Action.Basic
import Mathlib.Dynamics.Ergodic.Extreme
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# Ergodic maximizers for continuous flows

This file proves the compact-flow form of the elementary ``ergodic
reduction'' principle.  If a continuous real flow acts on a nonempty
compact metric space, then every bounded continuous observable attains its
largest invariant average at an ergodic invariant probability.

There are two points worth making explicit.

* Mathlib characterizes ergodic measures for one measurable self-map as
  extreme invariant probabilities, but it does not currently provide the
  corresponding existence theorem for a real flow.
* Positive measures are not a real vector space, so the Krein--Milman
  theorem cannot be applied to them directly.  We embed a probability
  measure in the real weak dual of the bounded continuous functions by
  integration.  This is a continuous affine injection.  Krein--Milman
  applies in that ambient locally convex real vector space.

The resulting definitions and lemmas are independent of the polynomial
reduction and can be reused for any continuous flow on a compact metric
space.
-/

noncomputable section

open Filter Function MeasureTheory ProbabilityTheory Set Topology
open scoped BoundedContinuousFunction ENNReal

namespace HGAS.Dynamics

variable {K : Type*} [MetricSpace K] [MeasurableSpace K] [BorelSpace K]

section WeakDualTopology

variable (E : Type*) [TopologicalSpace E] [AddCommGroup E]
  [Module ℝ E]

/-- The weak-dual coercion to a family of real coordinates, as a real
linear map. -/
def weakDualCoeLinearMap :
    WeakDual ℝ E →ₗ[ℝ] E → ℝ where
  toFun L := L
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The weak-star topology is induced by the family of evaluation
coordinates. -/
theorem isInducing_weakDualCoeLinearMap :
    IsInducing (weakDualCoeLinearMap E) := by
  simpa only [weakDualCoeLinearMap] using
    (WeakBilin.isEmbedding
      (B := topDualPairing ℝ E)
      ContinuousLinearMap.coe_injective).isInducing

/-- The real weak dual is locally convex in its weak-star topology.

Mathlib defines this topology as the one induced by the coordinate
evaluations but does not currently register the corresponding locally
convex instance. -/
instance instLocallyConvexSpaceWeakDualReal :
    LocallyConvexSpace ℝ (WeakDual ℝ E) :=
  (isInducing_weakDualCoeLinearMap E).locallyConvexSpace

end WeakDualTopology

/-- Integration against a probability measure, regarded as an element of
the real weak dual of the bounded continuous functions. -/
def probabilityIntegralWeakDual (μ : ProbabilityMeasure K) :
    WeakDual ℝ (K →ᵇ ℝ) :=
  let L : (K →ᵇ ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun f ↦ ∫ x, f x ∂(μ : Measure K)
      map_add' := fun f g ↦ integral_add (f.integrable _) (g.integrable _)
      map_smul' := fun c f ↦ by
        simpa only [BoundedContinuousFunction.coe_smul, smul_eq_mul] using
          integral_smul c (f : K → ℝ) }
  L.mkContinuous 1 fun f ↦ by
    simpa only [one_mul] using
      f.norm_integral_le_norm (μ : Measure K)

@[simp]
theorem probabilityIntegralWeakDual_apply
    (μ : ProbabilityMeasure K) (f : K →ᵇ ℝ) :
    probabilityIntegralWeakDual μ f = observableAverage f μ :=
  rfl

/-- The integration embedding is continuous for the weak topology on
probability measures and the weak-star topology on the dual. -/
theorem continuous_probabilityIntegralWeakDual :
    Continuous (probabilityIntegralWeakDual :
      ProbabilityMeasure K → WeakDual ℝ (K →ᵇ ℝ)) := by
  apply WeakDual.continuous_of_continuous_eval
  intro f
  exact continuous_observableAverage f

/-- On a compact metric space, bounded continuous functions distinguish
probability measures.  Hence the integration map into the weak dual is
injective. -/
theorem probabilityIntegralWeakDual_injective [CompactSpace K] :
    Function.Injective
      (probabilityIntegralWeakDual :
        ProbabilityMeasure K → WeakDual ℝ (K →ᵇ ℝ)) := by
  intro μ ν h
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  let fbc : K →ᵇ ℝ :=
    ContinuousMap.equivBoundedOfCompact K ℝ
      ⟨f, f.continuous⟩
  have happ := congrArg (fun L : WeakDual ℝ (K →ᵇ ℝ) ↦ L fbc) h
  exact happ

/-! ## Ergodicity for the whole real flow -/

/-- Ordinary measures which are probability measures and are preserved by
every time map of the flow.  We use ordinary measures here because their
positive-cone convex structure is the one used by Mathlib's
`extremePoints ℝ≥0∞`. -/
def flowInvariantProbabilityMeasureSet (ϕ : Flow ℝ K) :
    Set (Measure K) :=
  {μ | (∀ t : ℝ, MeasurePreserving (ϕ t) μ μ) ∧
    IsProbabilityMeasure μ}

/-- The ordinary-measure formulation agrees with the bundled formulation
used throughout the HGAS development. -/
theorem toMeasure_mem_flowInvariantProbabilityMeasureSet_iff
    (ϕ : Flow ℝ K) (μ : ProbabilityMeasure K) :
    (μ : Measure K) ∈ flowInvariantProbabilityMeasureSet ϕ ↔
      IsInvariantProbability ϕ μ := by
  constructor
  · rintro ⟨hpres, _⟩ t
    apply ProbabilityMeasure.toMeasure_injective
    simpa only [timePushforward, ProbabilityMeasure.toMeasure_map] using
      (hpres t).map_eq
  · intro hinv
    refine ⟨fun t ↦
      ⟨(ϕ.continuous_toFun t).measurable, ?_⟩, inferInstance⟩
    have h :=
      congrArg ProbabilityMeasure.toMeasure (hinv t)
    simpa only [timePushforward, ProbabilityMeasure.toMeasure_map] using h

/-- An extreme invariant probability for the full real action is
ergodic for that action.

This is the flow analogue of Mathlib's
`Ergodic.of_mem_extremePoints_measure_univ_eq`.  The proof is included
here because applying the one-map theorem to `ϕ 1` would incorrectly
replace flow ergodicity by time-one ergodicity. -/
theorem isErgodicInvariantProbability_of_mem_extremePoints
    (ϕ : Flow ℝ K) (μ : ProbabilityMeasure K)
    (hμ :
      (μ : Measure K) ∈
        extremePoints ℝ≥0∞
          (flowInvariantProbabilityMeasureSet ϕ)) :
    IsErgodicInvariantProbability ϕ μ := by
  have hpres :
      ∀ t : ℝ,
        MeasurePreserving (ϕ t)
          (μ : Measure K) (μ : Measure K) :=
    hμ.1.1
  refine
    ⟨(toMeasure_mem_flowInvariantProbabilityMeasureSet_iff ϕ μ).1 hμ.1,
      ?_⟩
  intro s hsm hfs
  have hcondMem {u : Set K}
      (hum : MeasurableSet u)
      (hfu :
        ∀ t : ℝ,
          (ϕ t) ⁻¹' u =ᵐ[(μ : Measure K)] u)
      (hμu : (μ : Measure K) u ≠ 0) :
      (1 : ℝ≥0∞) • (μ : Measure K)[|u] ∈
        flowInvariantProbabilityMeasureSet ϕ := by
    refine ⟨fun t ↦ .smul_measure (.smul_measure ?_ _) 1, ?_⟩
    · have hp := (hpres t).restrict_preimage hum
      rw [Measure.restrict_congr_set (hfu t)] at hp
      exact hp
    · simpa only [one_smul] using
        cond_isProbabilityMeasure hμu
  by_cases hs : (μ : Measure K) s = 0
  · exact Or.inl hs
  by_cases hsone : (μ : Measure K) s = 1
  · exact Or.inr hsone
  have hscompl : (μ : Measure K) sᶜ ≠ 0 := by
    intro hzero
    have hadd :=
      measure_add_measure_compl
        (μ := (μ : Measure K)) hsm
    rw [hzero, add_zero] at hadd
    exact hsone (by simpa using hadd)
  have hcond :
      (1 : ℝ≥0∞) • (μ : Measure K)[|s] =
        (μ : Measure K) := by
    apply hμ.2
      (hcondMem hsm hfs hs)
      (hcondMem hsm.compl
        (fun t ↦ by
          rw [preimage_compl]
          exact (hfs t).compl) hscompl)
    refine
      ⟨(μ : Measure K) s,
        (μ : Measure K) sᶜ,
        pos_iff_ne_zero.2 hs,
        pos_iff_ne_zero.2 hscompl, ?_, ?_⟩
    · simpa using
        (measure_add_measure_compl
          (μ := (μ : Measure K)) hsm)
    · simp [ProbabilityTheory.cond, smul_smul,
        ENNReal.mul_inv_cancel, *]
  rw [← hcond] at hscompl
  simp [ProbabilityTheory.cond_apply, hsm] at hscompl

/-! ## The compact maximizing face in the real weak dual -/

/-- The image of all flow-invariant probabilities in the real weak dual. -/
def invariantIntegralWeakDualSet (ϕ : Flow ℝ K) :
    Set (WeakDual ℝ (K →ᵇ ℝ)) :=
  probabilityIntegralWeakDual '' invariantProbabilitySet ϕ

/-- The image in the real weak dual of the invariant probabilities which
maximize the average of `f`. -/
def maximizingIntegralWeakDualSet
    (ϕ : Flow ℝ K) (f : K →ᵇ ℝ) :
    Set (WeakDual ℝ (K →ᵇ ℝ)) :=
  probabilityIntegralWeakDual '' maximizingInvariantSet ϕ f

/-- The weak-dual image of the invariant probabilities is compact. -/
theorem isCompact_invariantIntegralWeakDualSet
    [CompactSpace K] (ϕ : Flow ℝ K) :
    IsCompact (invariantIntegralWeakDualSet ϕ) :=
  (isCompact_invariantProbabilitySet ϕ).image
    continuous_probabilityIntegralWeakDual

/-- The weak-dual image of the maximizing invariant probabilities is
compact. -/
theorem isCompact_maximizingIntegralWeakDualSet
    [CompactSpace K] (ϕ : Flow ℝ K) (f : K →ᵇ ℝ) :
    IsCompact (maximizingIntegralWeakDualSet ϕ f) :=
  (isCompact_maximizingInvariantSet ϕ f).image
    continuous_probabilityIntegralWeakDual

/-- On a nonempty compact space, the weak-dual maximizing set is
nonempty. -/
theorem maximizingIntegralWeakDualSet_nonempty
    [CompactSpace K] [Nonempty K]
    (ϕ : Flow ℝ K) (f : K →ᵇ ℝ) :
    (maximizingIntegralWeakDualSet ϕ f).Nonempty := by
  obtain ⟨μ, hμ⟩ :=
    maximizingInvariantSet_nonempty ϕ f
      (invariantProbabilitySet_nonempty ϕ)
  exact ⟨probabilityIntegralWeakDual μ, μ, hμ, rfl⟩

/-- The maximizing weak-dual image is a face of the full invariant
weak-dual image.

This is the elementary affine calculation behind ergodic optimization:
if a strict convex combination has maximal `f`-average, then both
endpoints have maximal `f`-average. -/
theorem isExtreme_maximizingIntegralWeakDualSet
    (ϕ : Flow ℝ K) (f : K →ᵇ ℝ) :
    IsExtreme ℝ
      (invariantIntegralWeakDualSet ϕ)
      (maximizingIntegralWeakDualSet ϕ f) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨μ, hμ, rfl⟩
    exact ⟨μ, hμ.1, rfl⟩
  · rintro _ ⟨μ₁, hμ₁, rfl⟩
      _ ⟨μ₂, hμ₂, rfl⟩
      _ ⟨μ, hμ, rfl⟩
      ⟨a, b, ha, hb, hab, hcomb⟩
    have havgComb :=
      congrArg
        (fun L : WeakDual ℝ (K →ᵇ ℝ) ↦ L f)
        hcomb
    change
      a * observableAverage f μ₁ +
          b * observableAverage f μ₂ =
        observableAverage f μ at havgComb
    have hle₁ :
        observableAverage f μ₁ ≤ observableAverage f μ :=
      hμ.2 hμ₁
    have hle₂ :
        observableAverage f μ₂ ≤ observableAverage f μ :=
      hμ.2 hμ₂
    have havg₁ :
        observableAverage f μ₁ = observableAverage f μ := by
      apply le_antisymm hle₁
      by_contra hnot
      have hlt₁ :
          observableAverage f μ₁ < observableAverage f μ :=
        lt_of_not_ge hnot
      have hweighted :
          a * observableAverage f μ₁ +
              b * observableAverage f μ₂ <
            a * observableAverage f μ +
              b * observableAverage f μ :=
        add_lt_add_of_lt_of_le
          (mul_lt_mul_of_pos_left hlt₁ ha)
          (mul_le_mul_of_nonneg_left hle₂ hb.le)
      rw [← add_mul, hab, one_mul] at hweighted
      exact (havgComb ▸ hweighted).false
    refine ⟨μ₁, ⟨hμ₁, ?_⟩, rfl⟩
    intro ν hν
    exact (hμ.2 hν).trans_eq havg₁.symm

/-! ## Returning from the real weak dual to positive measures -/

/-- A real extreme point of the weak-dual image is an extreme point of the
positive cone of ordinary invariant probability measures.

The scalar fields differ on the two sides: Krein--Milman uses real
coefficients, while Mathlib's measure-extremality theorem uses
`ℝ≥0∞`.  The coefficients of an open segment sum to one, hence are finite;
taking their real values converts one segment representation into the
other. -/
theorem toMeasure_mem_extremePoints_of_weakDual
    [CompactSpace K]
    (ϕ : Flow ℝ K) (μ : ProbabilityMeasure K)
    (hμ :
      probabilityIntegralWeakDual μ ∈
        extremePoints ℝ (invariantIntegralWeakDualSet ϕ)) :
    (μ : Measure K) ∈
      extremePoints ℝ≥0∞
        (flowInvariantProbabilityMeasureSet ϕ) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨ν, hν, heq⟩ := hμ.1
    have hνμ : ν = μ :=
      probabilityIntegralWeakDual_injective heq
    subst ν
    exact
      (toMeasure_mem_flowInvariantProbabilityMeasureSet_iff
        ϕ μ).2 hν
  · intro ν₁ hν₁ ν₂ hν₂ hseg
    letI : IsProbabilityMeasure ν₁ := hν₁.2
    letI : IsProbabilityMeasure ν₂ := hν₂.2
    let μ₁ : ProbabilityMeasure K := ⟨ν₁, hν₁.2⟩
    let μ₂ : ProbabilityMeasure K := ⟨ν₂, hν₂.2⟩
    have hμ₁inv : μ₁ ∈ invariantProbabilitySet ϕ :=
      (toMeasure_mem_flowInvariantProbabilityMeasureSet_iff
        ϕ μ₁).1 (by simpa [μ₁] using hν₁)
    have hμ₂inv : μ₂ ∈ invariantProbabilitySet ϕ :=
      (toMeasure_mem_flowInvariantProbabilityMeasureSet_iff
        ϕ μ₂).1 (by simpa [μ₂] using hν₂)
    obtain ⟨a, b, ha, hb, hab, hmeasure⟩ := hseg
    have ha_le_one : a ≤ 1 := by
      rw [← hab]
      exact le_add_right (le_refl a)
    have hb_le_one : b ≤ 1 := by
      rw [← hab]
      exact le_add_left (le_refl b)
    have ha_top : a ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top ha_le_one
    have hb_top : b ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top hb_le_one
    have habReal : a.toReal + b.toReal = 1 := by
      rw [← ENNReal.toReal_add ha_top hb_top, hab]
      simp
    have hweakCombination :
        a.toReal • probabilityIntegralWeakDual μ₁ +
            b.toReal • probabilityIntegralWeakDual μ₂ =
          probabilityIntegralWeakDual μ := by
      apply DFunLike.ext _ _
      intro f
      change
        a.toReal * (∫ x, f x ∂(ν₁ : Measure K)) +
            b.toReal * (∫ x, f x ∂(ν₂ : Measure K)) =
          ∫ x, f x ∂(μ : Measure K)
      rw [← hmeasure]
      rw [integral_add_measure
        ((f.integrable (ν₁ : Measure K)).smul_measure ha_top)
        ((f.integrable (ν₂ : Measure K)).smul_measure hb_top)]
      simp only [integral_smul_measure, smul_eq_mul]
    have hweakSegment :
        probabilityIntegralWeakDual μ ∈
          openSegment ℝ
            (probabilityIntegralWeakDual μ₁)
            (probabilityIntegralWeakDual μ₂) :=
      ⟨a.toReal, b.toReal,
        ENNReal.toReal_pos ha.ne' ha_top,
        ENNReal.toReal_pos hb.ne' hb_top,
        habReal, hweakCombination⟩
    have heqWeak :
        probabilityIntegralWeakDual μ₁ =
          probabilityIntegralWeakDual μ :=
      hμ.2
        ⟨μ₁, hμ₁inv, rfl⟩
        ⟨μ₂, hμ₂inv, rfl⟩
        hweakSegment
    have heqProbability : μ₁ = μ :=
      probabilityIntegralWeakDual_injective heqWeak
    exact congrArg ProbabilityMeasure.toMeasure heqProbability

/-! ## Ergodic maximizers and the reduction principle -/

/-- **Ergodic maximizer theorem for continuous real flows.**

Every bounded continuous observable on a nonempty compact metric flow has
an invariant probability which is simultaneously ergodic for the whole
real action and maximizing among all invariant probabilities. -/
theorem exists_ergodicInvariantProbability_isMaxOn_average
    [CompactSpace K] [Nonempty K]
    (ϕ : Flow ℝ K) (f : K →ᵇ ℝ) :
    ∃ μ : InvariantProbabilityMeasure ϕ,
      IsErgodicInvariantProbability ϕ μ.measure ∧
        IsMaxOn (observableAverage f)
          (invariantProbabilitySet ϕ) μ.measure := by
  obtain ⟨L, hL⟩ :=
    (isCompact_maximizingIntegralWeakDualSet ϕ f)
      |>.extremePoints_nonempty
        (maximizingIntegralWeakDualSet_nonempty ϕ f)
  obtain ⟨μ, hμ, rfl⟩ := hL.1
  have hExtremeFull :
      probabilityIntegralWeakDual μ ∈
        extremePoints ℝ
          (invariantIntegralWeakDualSet ϕ) :=
    (isExtreme_maximizingIntegralWeakDualSet ϕ f)
      |>.extremePoints_subset_extremePoints hL
  have hExtremeMeasure :
      (μ : Measure K) ∈
        extremePoints ℝ≥0∞
          (flowInvariantProbabilityMeasureSet ϕ) :=
    toMeasure_mem_extremePoints_of_weakDual
      ϕ μ hExtremeFull
  refine
    ⟨⟨μ, hμ.1⟩,
      isErgodicInvariantProbability_of_mem_extremePoints
        ϕ μ hExtremeMeasure,
      hμ.2⟩

/-- A chosen invariant probability measure which is both ergodic and
maximizing. -/
def ergodicMaximizingInvariantProbabilityMeasure
    [CompactSpace K] [Nonempty K]
    (ϕ : Flow ℝ K) (f : K →ᵇ ℝ) :
    InvariantProbabilityMeasure ϕ :=
  Classical.choose
    (exists_ergodicInvariantProbability_isMaxOn_average ϕ f)

/-- The chosen maximizing invariant probability is ergodic for the whole
real flow. -/
theorem ergodicMaximizingInvariantProbabilityMeasure_ergodic
    [CompactSpace K] [Nonempty K]
    (ϕ : Flow ℝ K) (f : K →ᵇ ℝ) :
    IsErgodicInvariantProbability ϕ
      (ergodicMaximizingInvariantProbabilityMeasure ϕ f).measure :=
  (Classical.choose_spec
    (exists_ergodicInvariantProbability_isMaxOn_average ϕ f)).1

/-- The chosen ergodic probability maximizes the observable average over
all invariant probabilities. -/
theorem ergodicMaximizingInvariantProbabilityMeasure_isMaxOn
    [CompactSpace K] [Nonempty K]
    (ϕ : Flow ℝ K) (f : K →ᵇ ℝ) :
    IsMaxOn (observableAverage f)
      (invariantProbabilitySet ϕ)
      (ergodicMaximizingInvariantProbabilityMeasure ϕ f).measure :=
  (Classical.choose_spec
    (exists_ergodicInvariantProbability_isMaxOn_average ϕ f)).2

/-- To prove an upper bound for every invariant average, it is enough to
prove it for ergodic invariant probabilities.  No measurable ergodic
decomposition is needed: apply the hypothesis to one ergodic maximizer. -/
theorem invariantAverage_le_of_forall_ergodic
    [CompactSpace K] [Nonempty K]
    (ϕ : Flow ℝ K) (f : K →ᵇ ℝ) {c : ℝ}
    (hbound :
      ∀ μ : InvariantProbabilityMeasure ϕ,
        IsErgodicInvariantProbability ϕ μ.measure →
          observableAverage f μ.measure ≤ c)
    (ν : InvariantProbabilityMeasure ϕ) :
    observableAverage f ν.measure ≤ c := by
  let μ :=
    ergodicMaximizingInvariantProbabilityMeasure ϕ f
  exact
    (ergodicMaximizingInvariantProbabilityMeasure_isMaxOn
        ϕ f ν.invariant).trans
      (hbound μ
        (ergodicMaximizingInvariantProbabilityMeasure_ergodic
          ϕ f))

/-- Equivalent universal formulations of an invariant-average upper
bound: all invariant probabilities versus only the ergodic ones. -/
theorem forall_invariantAverage_le_iff_forall_ergodic
    [CompactSpace K] [Nonempty K]
    (ϕ : Flow ℝ K) (f : K →ᵇ ℝ) {c : ℝ} :
    (∀ μ : InvariantProbabilityMeasure ϕ,
        observableAverage f μ.measure ≤ c) ↔
      (∀ μ : InvariantProbabilityMeasure ϕ,
        IsErgodicInvariantProbability ϕ μ.measure →
          observableAverage f μ.measure ≤ c) := by
  constructor
  · exact fun h μ _ ↦ h μ
  · exact fun h μ ↦
      invariantAverage_le_of_forall_ergodic ϕ f h μ

end HGAS.Dynamics
