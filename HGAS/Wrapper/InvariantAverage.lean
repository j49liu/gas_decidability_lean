import HGAS.Wrapper.RadiusInvariantFaces
import HGAS.Wrapper.Reward
import HGAS.Dynamics.InvariantRestriction
import HGAS.Dynamics.UniformNegativeBlocks
import Mathlib.Tactic

/-!
# Exact invariant-average identity for the wrapper reward

This file proves the measure-theoretic `max {β,-1}` step.  The theorem is
abstract over an actual compact wrapper flow but uses the concrete
radius-cleanup and reward formulas.

The source quantity `β` is specified by a small certificate saying exactly
that it is the attained maximum among ambient invariant probabilities
concentrated on the full stratum.  A concrete two-sheet chart must later
identify this certified value with the maximal average on the original
product of spheres.  No such identification is assumed implicitly here.
-/

namespace HGAS

open Function MeasureTheory Set
open scoped BoundedContinuousFunction BigOperators ENNReal

noncomputable section

variable {K : Type*} [MetricSpace K] [MeasurableSpace K] [BorelSpace K]
  [CompactSpace K] [Nonempty K]
variable {blocks : ℕ} {ϕ : Flow ℝ K}

namespace RadiusCleanupFlowCertificate

/-- Product of the block squared-radius observables. -/
def radiusProductObservable
    (certificate : RadiusCleanupFlowCertificate ϕ blocks) :
    K →ᵇ ℝ :=
  ∏ i, certificate.radii i

/-- The continuous wrapper reward
`H * α - (1 - H)` on the compact angular phase space. -/
def rewardObservable
    (certificate : RadiusCleanupFlowCertificate ϕ blocks)
    (α : K →ᵇ ℝ) :
    K →ᵇ ℝ :=
  certificate.radiusProductObservable * α -
    (1 - certificate.radiusProductObservable)

omit [MeasurableSpace K] [BorelSpace K] [CompactSpace K] [Nonempty K] in
@[simp]
theorem radiusProductObservable_apply
    (certificate : RadiusCleanupFlowCertificate ϕ blocks)
    (x : K) :
    certificate.radiusProductObservable x =
      blockRadiusProduct (fun i ↦ certificate.radii i x) := by
  simp [radiusProductObservable, blockRadiusProduct]

omit [MeasurableSpace K] [BorelSpace K] [CompactSpace K] [Nonempty K] in
@[simp]
theorem rewardObservable_apply
    (certificate : RadiusCleanupFlowCertificate ϕ blocks)
    (α : K →ᵇ ℝ) (x : K) :
    certificate.rewardObservable α x =
      wrapperReward (fun i ↦ certificate.radii i x) (α x) := by
  simp [rewardObservable, wrapperReward]

omit [MeasurableSpace K] [BorelSpace K] [CompactSpace K] [Nonempty K] in
/-- On the full stratum the wrapper reward is the source reward. -/
theorem rewardObservable_eq_source_of_mem_fullStratum
    (certificate : RadiusCleanupFlowCertificate ϕ blocks)
    (α : K →ᵇ ℝ) {x : K}
    (hx : x ∈ certificate.fullStratum) :
    certificate.rewardObservable α x = α x := by
  rw [rewardObservable_apply]
  exact wrapperReward_eq_source _ _ hx

omit [MeasurableSpace K] [BorelSpace K] [CompactSpace K] [Nonempty K] in
/-- On every proper face the wrapper reward is exactly `-1`. -/
theorem rewardObservable_eq_neg_one_of_mem_properFace
    (certificate : RadiusCleanupFlowCertificate ϕ blocks)
    (α : K →ᵇ ℝ) {x : K}
    (hx : x ∈ certificate.properFace) :
    certificate.rewardObservable α x = -1 := by
  obtain ⟨i, hi⟩ := hx
  rw [rewardObservable_apply]
  exact wrapperReward_eq_neg_one_of_zero_coordinate _ _ hi

omit [Nonempty K] in
/-- Almost-sure reward classification for every invariant probability. -/
theorem ae_reward_eq_source_or_neg_one
    (certificate : RadiusCleanupFlowCertificate ϕ blocks)
    (α : K →ᵇ ℝ)
    (μ : Dynamics.InvariantProbabilityMeasure ϕ) :
    ∀ᵐ x ∂(μ.measure : Measure K),
      (x ∈ certificate.fullStratum ∧
          certificate.rewardObservable α x = α x) ∨
        (x ∈ certificate.properFace ∧
          certificate.rewardObservable α x = -1) := by
  filter_upwards [certificate.ae_mem_fullStratum_or_properFace μ]
    with x hx
  rcases hx with hfull | hproper
  · exact Or.inl ⟨hfull,
      certificate.rewardObservable_eq_source_of_mem_fullStratum
        α hfull⟩
  · exact Or.inr ⟨hproper,
      certificate.rewardObservable_eq_neg_one_of_mem_properFace
        α hproper⟩

omit [CompactSpace K] in
/-- The normalized restriction to a positive-mass full stratum sees the
same average for the wrapper and source rewards. -/
theorem conditionedFull_rewardAverage_eq_source
    (certificate : RadiusCleanupFlowCertificate ϕ blocks)
    (α : K →ᵇ ℝ)
    (hfullInvariant :
      IsInvariant ϕ certificate.fullStratum)
    (μ : Dynamics.InvariantProbabilityMeasure ϕ)
    (hnonzero :
      μ.measure.toFiniteMeasure.restrict
        certificate.fullStratum ≠ 0) :
    Dynamics.observableAverage
        (certificate.rewardObservable α)
        ((Dynamics.normalizeInvariantRestriction
          ϕ μ certificate.fullStratum
          certificate.measurableSet_fullStratum
          hfullInvariant hnonzero).measure) =
      Dynamics.observableAverage α
        ((Dynamics.normalizeInvariantRestriction
          ϕ μ certificate.fullStratum
          certificate.measurableSet_fullStratum
          hfullInvariant hnonzero).measure) := by
  let ν :=
    Dynamics.normalizeInvariantRestriction
      ϕ μ certificate.fullStratum
      certificate.measurableSet_fullStratum
      hfullInvariant hnonzero
  have hmem :
      ∀ᵐ x ∂(ν.measure : Measure K),
        x ∈ certificate.fullStratum :=
    Dynamics.ae_mem_normalize_restrict
      μ.measure.toFiniteMeasure
      certificate.measurableSet_fullStratum hnonzero
  unfold Dynamics.observableAverage
  apply integral_congr_ae
  filter_upwards [hmem] with x hx
  exact certificate.rewardObservable_eq_source_of_mem_fullStratum
    α hx

/-- The normalized complement of a positive-mass full stratum has wrapper
average exactly `-1`. -/
theorem conditionedFullCompl_rewardAverage_eq_neg_one
    (certificate : RadiusCleanupFlowCertificate ϕ blocks)
    (α : K →ᵇ ℝ)
    (μ : Dynamics.InvariantProbabilityMeasure ϕ)
    (hnonzero :
      μ.measure.toFiniteMeasure.restrict
        certificate.fullStratumᶜ ≠ 0) :
    Dynamics.observableAverage
        (certificate.rewardObservable α)
        ((μ.measure.toFiniteMeasure.restrict
          certificate.fullStratumᶜ).normalize) = -1 := by
  let ν : ProbabilityMeasure K :=
    (μ.measure.toFiniteMeasure.restrict
      certificate.fullStratumᶜ).normalize
  have hcompl :
      ∀ᵐ x ∂(ν : Measure K),
        x ∈ certificate.fullStratumᶜ := by
    exact Dynamics.ae_mem_normalize_restrict
      μ.measure.toFiniteMeasure
      certificate.measurableSet_fullStratum.compl hnonzero
  have hclassificationμ :
      ∀ᵐ x ∂(μ.measure : Measure K),
        x ∈ certificate.fullStratum ∨
          x ∈ certificate.properFace :=
    certificate.ae_mem_fullStratum_or_properFace μ
  have hclassificationν :
      ∀ᵐ x ∂(ν : Measure K),
        x ∈ certificate.fullStratum ∨
          x ∈ certificate.properFace := by
    change
      ∀ᵐ x ∂
        (((μ.measure.toFiniteMeasure.restrict
          certificate.fullStratumᶜ).normalize :
            ProbabilityMeasure K) : Measure K),
        x ∈ certificate.fullStratum ∨
          x ∈ certificate.properFace
    rw [(μ.measure.toFiniteMeasure.restrict
      certificate.fullStratumᶜ).toMeasure_normalize_eq_of_nonzero
        hnonzero]
    exact Measure.ae_smul_measure
      (ae_restrict_of_ae hclassificationμ) _
  have hproper :
      ∀ᵐ x ∂(ν : Measure K),
        x ∈ certificate.properFace := by
    filter_upwards [hcompl, hclassificationν] with x hxcompl hx
    exact hx.resolve_left hxcompl
  have hrewards :
      ∀ᵐ x ∂(ν : Measure K),
        certificate.rewardObservable α x = -1 := by
    filter_upwards [hproper] with x hx
    exact certificate.rewardObservable_eq_neg_one_of_mem_properFace
      α hx
  unfold Dynamics.observableAverage
  calc
    (∫ x, certificate.rewardObservable α x ∂(ν : Measure K)) =
        ∫ _ : K, (-1 : ℝ) ∂(ν : Measure K) :=
      integral_congr_ae hrewards
    _ = -1 := by simp

/-- Exact specification that `β` is the attained maximum source average
among invariant probabilities concentrated on the full stratum. -/
structure FullStratumMaximum
    (certificate : RadiusCleanupFlowCertificate ϕ blocks)
    (α : K →ᵇ ℝ) (β : ℝ) : Prop where
  upper :
    ∀ μ : Dynamics.InvariantProbabilityMeasure ϕ,
      (∀ᵐ x ∂(μ.measure : Measure K),
        x ∈ certificate.fullStratum) →
      Dynamics.observableAverage α μ.measure ≤ β
  attained :
    ∃ μ : Dynamics.InvariantProbabilityMeasure ϕ,
      (∀ᵐ x ∂(μ.measure : Measure K),
        x ∈ certificate.fullStratum) ∧
      Dynamics.observableAverage α μ.measure = β

/-- Every invariant wrapper average is bounded by `max β (-1)`. -/
theorem wrapperAverage_le_max
    (certificate : RadiusCleanupFlowCertificate ϕ blocks)
    (α : K →ᵇ ℝ) (β : ℝ)
    (hfullInvariant :
      IsInvariant ϕ certificate.fullStratum)
    (hsource : FullStratumMaximum certificate α β)
    (μ : Dynamics.InvariantProbabilityMeasure ϕ) :
    Dynamics.observableAverage
        (certificate.rewardObservable α) μ.measure ≤
      max β (-1) := by
  let core := certificate.fullStratum
  let νc : FiniteMeasure K :=
    μ.measure.toFiniteMeasure.restrict core
  let νo : FiniteMeasure K :=
    μ.measure.toFiniteMeasure.restrict coreᶜ
  have hcoreMeas : MeasurableSet core := by
    simpa only [core] using certificate.measurableSet_fullStratum
  have hsum :
      νc + νo = μ.measure.toFiniteMeasure := by
    apply FiniteMeasure.toMeasure_injective
    simpa only [νc, νo, core,
      FiniteMeasure.toMeasure_add,
      FiniteMeasure.restrict_measure_eq] using
      (Measure.restrict_add_restrict_compl hcoreMeas :
        (μ.measure : Measure K).restrict core +
          (μ.measure : Measure K).restrict coreᶜ =
        (μ.measure : Measure K))
  have hdecomp :
      (μ.measure : Measure K) =
        (νc : Measure K) + (νo : Measure K) := by
    have h := congrArg FiniteMeasure.toMeasure hsum
    exact h.symm
  have hcMeasure :
      (νc : Measure K) =
        νc.mass • (νc.normalize : Measure K) := by
    have h :=
      congrArg FiniteMeasure.toMeasure
        νc.self_eq_mass_smul_normalize
    simpa only [FiniteMeasure.toMeasure_smul] using h
  have hoMeasure :
      (νo : Measure K) =
        νo.mass • (νo.normalize : Measure K) := by
    have h :=
      congrArg FiniteMeasure.toMeasure
        νo.self_eq_mass_smul_normalize
    simpa only [FiniteMeasure.toMeasure_smul] using h
  have hνcInt :
      Integrable (certificate.rewardObservable α) (νc : Measure K) :=
    (certificate.rewardObservable α).integrable _
  have hνoInt :
      Integrable (certificate.rewardObservable α) (νo : Measure K) :=
    (certificate.rewardObservable α).integrable _
  have htotal :
      Dynamics.observableAverage
          (certificate.rewardObservable α) μ.measure =
        (νc.mass : ℝ) *
            Dynamics.observableAverage
              (certificate.rewardObservable α) νc.normalize +
          (νo.mass : ℝ) *
            Dynamics.observableAverage
              (certificate.rewardObservable α) νo.normalize := by
    unfold Dynamics.observableAverage
    calc
      (∫ x, certificate.rewardObservable α x
          ∂(μ.measure : Measure K)) =
          ∫ x, certificate.rewardObservable α x
            ∂((νc : Measure K) + (νo : Measure K)) := by
              rw [hdecomp]
      _ =
          (∫ x, certificate.rewardObservable α x
            ∂(νc : Measure K)) +
          ∫ x, certificate.rewardObservable α x
            ∂(νo : Measure K) :=
        integral_add_measure hνcInt hνoInt
      _ =
          (νc.mass : ℝ) *
              ∫ x, certificate.rewardObservable α x
                ∂(νc.normalize : Measure K) +
            (νo.mass : ℝ) *
              ∫ x, certificate.rewardObservable α x
                ∂(νo.normalize : Measure K) := by
        rw [hcMeasure, hoMeasure]
        simp only [integral_smul_nnreal_measure,
          NNReal.smul_def, smul_eq_mul]
  have hmass : (νc.mass : ℝ) + (νo.mass : ℝ) = 1 := by
    have hmassNN : νc.mass + νo.mass = 1 := by
      have htotal :
          (νc + νo).mass = 1 := by
        simpa using congrArg FiniteMeasure.mass hsum
      rw [← htotal]
      unfold FiniteMeasure.mass
      exact (congrFun (FiniteMeasure.coeFn_add νc νo) Set.univ).symm
    exact_mod_cast hmassNN
  have hcoreWeighted :
      (νc.mass : ℝ) *
          Dynamics.observableAverage
            (certificate.rewardObservable α) νc.normalize ≤
        (νc.mass : ℝ) * max β (-1) := by
    by_cases hnc : νc = 0
    · simp [hnc]
    · let μc :=
        Dynamics.normalizeInvariantRestriction
          ϕ μ certificate.fullStratum
          certificate.measurableSet_fullStratum
          hfullInvariant (by simpa only [νc, core] using hnc)
      have hmem :
          ∀ᵐ x ∂(μc.measure : Measure K),
            x ∈ certificate.fullStratum :=
        Dynamics.ae_mem_normalize_restrict
          μ.measure.toFiniteMeasure
          certificate.measurableSet_fullStratum
          (by simpa only [νc, core] using hnc)
      have hsourceBound :
          Dynamics.observableAverage α μc.measure ≤ β :=
        hsource.upper μc hmem
      have hrewardEq :
          Dynamics.observableAverage
              (certificate.rewardObservable α) μc.measure =
            Dynamics.observableAverage α μc.measure :=
        certificate.conditionedFull_rewardAverage_eq_source
          α hfullInvariant μ
          (by simpa only [νc, core] using hnc)
      have hbound :
          Dynamics.observableAverage
              (certificate.rewardObservable α) νc.normalize ≤
            max β (-1) := by
        change
          Dynamics.observableAverage
              (certificate.rewardObservable α) μc.measure ≤ _
        rw [hrewardEq]
        exact hsourceBound.trans (le_max_left _ _)
      exact mul_le_mul_of_nonneg_left hbound (NNReal.coe_nonneg _)
  have houtWeighted :
      (νo.mass : ℝ) *
          Dynamics.observableAverage
            (certificate.rewardObservable α) νo.normalize ≤
        (νo.mass : ℝ) * max β (-1) := by
    by_cases hno : νo = 0
    · simp [hno]
    · have hreward :
          Dynamics.observableAverage
              (certificate.rewardObservable α) νo.normalize = -1 := by
        simpa only [νo, core] using
          certificate.conditionedFullCompl_rewardAverage_eq_neg_one
            α μ (by simpa only [νo, core] using hno)
      have hbound :
          Dynamics.observableAverage
              (certificate.rewardObservable α) νo.normalize ≤
            max β (-1) := by
        rw [hreward]
        exact le_max_right _ _
      exact mul_le_mul_of_nonneg_left hbound (NNReal.coe_nonneg _)
  rw [htotal]
  calc
    (νc.mass : ℝ) *
          Dynamics.observableAverage
            (certificate.rewardObservable α) νc.normalize +
        (νo.mass : ℝ) *
          Dynamics.observableAverage
            (certificate.rewardObservable α) νo.normalize ≤
        (νc.mass : ℝ) * max β (-1) +
          (νo.mass : ℝ) * max β (-1) :=
      add_le_add hcoreWeighted houtWeighted
    _ = max β (-1) := by rw [← add_mul, hmass, one_mul]

/-- **Exact wrapper maximal-average identity.**

If the full stratum is invariant, its source maximum is `β`, and at least
one proper face contains a fixed point, then the wrapper's maximal
invariant average is exactly `max β (-1)`. -/
theorem maximalInvariantAverage_reward_eq_max
    (certificate : RadiusCleanupFlowCertificate ϕ blocks)
    (α : K →ᵇ ℝ) (β : ℝ)
    (hfullInvariant :
      IsInvariant ϕ certificate.fullStratum)
    (hsource : FullStratumMaximum certificate α β)
    (hproperFixed :
      ∃ x : K,
        x ∈ certificate.properFace ∧
          Dynamics.InvariantProbabilityMeasure.IsFlowFixedPoint ϕ x) :
    Dynamics.maximalInvariantAverage ϕ
        (certificate.rewardObservable α) =
      max β (-1) := by
  apply le_antisymm
  · exact certificate.wrapperAverage_le_max
      α β hfullInvariant hsource
      ⟨Dynamics.maximizingInvariantProbability ϕ
          (certificate.rewardObservable α),
        Dynamics.maximizingInvariantProbability_invariant
          ϕ (certificate.rewardObservable α)⟩
  · apply max_le
    · obtain ⟨μsource, hmem, havg⟩ := hsource.attained
      have hreward :
          Dynamics.observableAverage
              (certificate.rewardObservable α) μsource.measure =
            Dynamics.observableAverage α μsource.measure := by
        unfold Dynamics.observableAverage
        apply integral_congr_ae
        filter_upwards [hmem] with x hx
        exact
          certificate.rewardObservable_eq_source_of_mem_fullStratum
            α hx
      rw [← havg, ← hreward]
      exact Dynamics.invariantAverage_le_maximalInvariantAverage
        ϕ (certificate.rewardObservable α)
        μsource.measure μsource.invariant
    · obtain ⟨x, hxproper, hxfixed⟩ := hproperFixed
      let μx :=
        Dynamics.InvariantProbabilityMeasure.diracOfFixedPoint
          x hxfixed
      have havg :
          Dynamics.observableAverage
              (certificate.rewardObservable α) μx.measure = -1 := by
        unfold Dynamics.observableAverage
        change
          (∫ y, certificate.rewardObservable α y
            ∂Measure.dirac x) = -1
        rw [integral_dirac]
        exact
          certificate.rewardObservable_eq_neg_one_of_mem_properFace
            α hxproper
      rw [← havg]
      exact Dynamics.invariantAverage_le_maximalInvariantAverage
        ϕ (certificate.rewardObservable α)
        μx.measure μx.invariant

/-- Negativity of the wrapper maximum is exactly negativity of the source
maximum; the added proper faces contribute only `-1`. -/
theorem maximalInvariantAverage_reward_neg_iff
    (certificate : RadiusCleanupFlowCertificate ϕ blocks)
    (α : K →ᵇ ℝ) (β : ℝ)
    (hfullInvariant :
      IsInvariant ϕ certificate.fullStratum)
    (hsource : FullStratumMaximum certificate α β)
    (hproperFixed :
      ∃ x : K,
        x ∈ certificate.properFace ∧
          Dynamics.InvariantProbabilityMeasure.IsFlowFixedPoint ϕ x) :
    Dynamics.maximalInvariantAverage ϕ
        (certificate.rewardObservable α) < 0 ↔
      β < 0 := by
  rw [certificate.maximalInvariantAverage_reward_eq_max
    α β hfullInvariant hsource hproperFixed]
  simp

end RadiusCleanupFlowCertificate

end

end HGAS
