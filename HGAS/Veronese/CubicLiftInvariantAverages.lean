import HGAS.Dynamics.InvariantRestriction
import HGAS.Dynamics.UniformNegativeBlocks
import HGAS.Veronese.CubicLiftFlowConjugacy
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Tactic

/-!
# Invariant radial averages for the stabilized cubic lift

This file proves the dynamical heart of the cubic-degree reduction.
Write `a` for the source logarithmic radial reward and `ã` for the
weighted radial reward of the stabilized cubic lift.  The main theorem
is

```
HasUniformNegativeBlock sourceFlow a ↔
  HasUniformNegativeBlock stabilizedFlow ã.
```

The easy reverse implication restricts a stabilized block to the
positive Veronese sheet.  There the exact trajectory conjugacy gives

```
∫₀ᵀ ã(Φₜ(ν(u))) dt = k ∫₀ᵀ a(φₜ(u)) dt.
```

The forward implication contains the essential measure argument.
For an arbitrary invariant probability `μ` of the stabilized angular
flow:

1. the capped-penalty coboundary from
   `CubicLiftInvariantSandwich` shows that `μ` is concentrated on the
   union of the zero-penalty core and the outside-tube region;
2. the core and its complement are invariant, so `μ` may be
   conditioned on either component;
3. on the core, the signed-sheet flow factor and the exact cocycle
   identity turn a source negative block into a core negative average;
4. on the complementary component, the sandwich places almost every
   point outside the tube, where stabilization gives `ã ≤ -1`;
5. decomposing the original finite measure into its two normalized
   restrictions proves that every invariant `ã`-average is strictly
   negative;
6. compactness and the uniform-negative-block lemma produce one common
   stabilized block.

No ergodic decomposition and no lifting of invariant measures through
the signed Veronese factor is needed.
-/

namespace HGAS.Veronese

open Function MeasureTheory Set
open scoped BoundedContinuousFunction Interval Topology

noncomputable section

variable {n k : ℕ} {F : HGAS.PolynomialField n}

/-- The source radial reward, bundled on the compact source sphere. -/
noncomputable def sourceRadialRewardBCF
    (F : HGAS.PolynomialField n) :
    sourceUnitSphere n →ᵇ ℝ := by
  letI : CompactSpace (sourceUnitSphere n) :=
    isCompact_iff_compactSpace.mp isCompact_sourceUnitSphere
  exact BoundedContinuousFunction.mkOfCompact
    ⟨fun u ↦
      HGAS.radialReward (evaluatedSourceField F) u.1,
      (contDiff_sourceRadialReward
        (contDiff_evaluatedSourceField F)).continuous.comp
          continuous_subtype_val⟩

@[simp]
theorem sourceRadialRewardBCF_apply
    (F : HGAS.PolynomialField n)
    (u : sourceUnitSphere n) :
    sourceRadialRewardBCF F u =
      HGAS.radialReward (evaluatedSourceField F) u.1 :=
  rfl

/-- The weighted radial reward of the actual stabilized cubic field,
bundled on the compact weighted sphere. -/
noncomputable def stabilizedCubicRadialRewardBCF
    (b : CubicLiftStabilizationBounds F k) :
    weightedUnitSphere n k →ᵇ ℝ := by
  letI : CompactSpace (weightedUnitSphere n k) :=
    isCompact_iff_compactSpace.mp isCompact_weightedUnitSphere
  exact BoundedContinuousFunction.mkOfCompact
    ⟨fun y ↦
      weightedRadialReward
        (evaluatedStabilizedCubicField b) y.1,
      (contDiff_weightedRadialReward
        (contDiff_evaluatedStabilizedCubicField b)).continuous.comp
          continuous_subtype_val⟩

@[simp]
theorem stabilizedCubicRadialRewardBCF_apply
    (b : CubicLiftStabilizationBounds F k)
    (y : weightedUnitSphere n k) :
    stabilizedCubicRadialRewardBCF b y =
      weightedRadialReward
        (evaluatedStabilizedCubicField b) y.1 :=
  rfl

theorem weightedRadialReward_stabilized_veronese
    (b : CubicLiftStabilizationBounds F k)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F)
    (hk : 1 ≤ k)
    (u : Fin n → ℝ) (hu : sourceRadiusSq u = 1) :
    weightedRadialReward
        (evaluatedStabilizedCubicField b)
        (veroneseMap (k := k) u) =
      (k : ℝ) *
        HGAS.radialReward (evaluatedSourceField F) u := by
  have hpoint :
      evaluatedStabilizedCubicField b
          (veroneseMap (k := k) u) =
        evaluatedCubicLift (k := k) F
          (veroneseMap (k := k) u) :=
    eval_stabilizedCubicField_of_mem_toricZeroSet
      F b.K (veronese_mem_toricZeroSet u)
  unfold weightedRadialReward
  rw [hpoint]
  exact weightedRadialReward_cubicLiftField_veronese
    F hF hk u hu

theorem weightedRadialReward_stabilized_neg_veronese
    (b : CubicLiftStabilizationBounds F k)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F)
    (hk : 1 ≤ k)
    (u : Fin n → ℝ) (hu : sourceRadiusSq u = 1) :
    weightedRadialReward
        (evaluatedStabilizedCubicField b)
        (-veroneseMap (k := k) u) =
      (k : ℝ) *
        HGAS.radialReward (evaluatedSourceField F) u := by
  have hpoint :
      evaluatedStabilizedCubicField b
          (-veroneseMap (k := k) u) =
        evaluatedCubicLift (k := k) F
          (-veroneseMap (k := k) u) :=
    eval_stabilizedCubicField_of_mem_toricZeroSet
      F b.K (neg_veronese_mem_toricZeroSet u)
  unfold weightedRadialReward
  rw [hpoint]
  exact weightedRadialReward_cubicLiftField_neg_veronese
    F hF hk u hu

/-- On every core orbit, the stabilized radial cocycle is exactly `k`
times a source radial cocycle. -/
theorem exists_source_orbitIntegral_eq_of_mem_core
    (b : CubicLiftStabilizationBounds F k)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F)
    (hk : 1 ≤ k)
    (T : ℝ) (y : weightedUnitSphere n k)
    (hy : y ∈ stabilizedConeCore n k) :
    ∃ u : sourceUnitSphere n,
      HGAS.Dynamics.orbitIntegral
          (stabilizedCubicAngularFlow b)
          (stabilizedCubicRadialRewardBCF b) T y =
        (k : ℝ) *
          HGAS.Dynamics.orbitIntegral
            (polynomialSourceAngularFlow F)
            (sourceRadialRewardBCF F) T u := by
  obtain ⟨u, hu, hy' | hy'⟩ :=
    (completeToricEnergy_eq_zero_on_weightedUnitSphere_iff
      hk y.1 y.2).mp hy
  · let uS : sourceUnitSphere n := ⟨u, hu⟩
    refine ⟨uS, ?_⟩
    have hySub :
        y = positiveVeroneseSphereMap k uS := by
      apply Subtype.ext
      simpa [positiveVeroneseSphereMap, uS] using hy'
    rw [hySub]
    rw [HGAS.Dynamics.orbitIntegral,
      HGAS.Dynamics.orbitIntegral,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    have hflow :=
      positiveVeroneseSphereMap_semiconj b hF hk t uS
    change
      stabilizedCubicRadialRewardBCF b
          (stabilizedCubicAngularFlow b t
            (positiveVeroneseSphereMap k uS)) =
        (k : ℝ) * sourceRadialRewardBCF F
          (polynomialSourceAngularFlow F t uS)
    rw [← hflow]
    exact weightedRadialReward_stabilized_veronese
      b hF hk
        (polynomialSourceAngularFlow F t uS).1
        (polynomialSourceAngularFlow F t uS).2
  · let uS : sourceUnitSphere n := ⟨u, hu⟩
    refine ⟨uS, ?_⟩
    have hySub :
        y = negativeVeroneseSphereMap k uS := by
      apply Subtype.ext
      simpa [negativeVeroneseSphereMap, uS] using hy'
    rw [hySub]
    rw [HGAS.Dynamics.orbitIntegral,
      HGAS.Dynamics.orbitIntegral,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    have hflow :=
      negativeVeroneseSphereMap_semiconj b hF hk t uS
    change
      stabilizedCubicRadialRewardBCF b
          (stabilizedCubicAngularFlow b t
            (negativeVeroneseSphereMap k uS)) =
        (k : ℝ) * sourceRadialRewardBCF F
          (polynomialSourceAngularFlow F t uS)
    rw [← hflow]
    exact weightedRadialReward_stabilized_neg_veronese
      b hF hk
        (polynomialSourceAngularFlow F t uS).1
        (polynomialSourceAngularFlow F t uS).2

/-- Explicit positive-sheet form of the core cocycle identity. -/
theorem positiveVeronese_orbitIntegral_eq
    (b : CubicLiftStabilizationBounds F k)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F)
    (hk : 1 ≤ k)
    (T : ℝ) (u : sourceUnitSphere n) :
    HGAS.Dynamics.orbitIntegral
        (stabilizedCubicAngularFlow b)
        (stabilizedCubicRadialRewardBCF b) T
        (positiveVeroneseSphereMap k u) =
      (k : ℝ) *
        HGAS.Dynamics.orbitIntegral
          (polynomialSourceAngularFlow F)
          (sourceRadialRewardBCF F) T u := by
  rw [HGAS.Dynamics.orbitIntegral,
    HGAS.Dynamics.orbitIntegral,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  have hflow :=
    positiveVeroneseSphereMap_semiconj b hF hk t u
  change
    stabilizedCubicRadialRewardBCF b
        (stabilizedCubicAngularFlow b t
          (positiveVeroneseSphereMap k u)) =
      (k : ℝ) * sourceRadialRewardBCF F
        (polynomialSourceAngularFlow F t u)
  rw [← hflow]
  exact weightedRadialReward_stabilized_veronese
    b hF hk
      (polynomialSourceAngularFlow F t u).1
      (polynomialSourceAngularFlow F t u).2

/-- A uniform source block gives a uniform block, scaled by `k`, on the
entire stabilized zero-penalty core. -/
theorem core_orbitIntegral_le_of_source_block
    (b : CubicLiftStabilizationBounds F k)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F)
    (hk : 1 ≤ k)
    {T c : ℝ}
    (hblock :
      ∀ u : sourceUnitSphere n,
        HGAS.Dynamics.orbitIntegral
          (polynomialSourceAngularFlow F)
          (sourceRadialRewardBCF F) T u ≤ -c) :
    ∀ y ∈ stabilizedConeCore n k,
      HGAS.Dynamics.orbitIntegral
          (stabilizedCubicAngularFlow b)
          (stabilizedCubicRadialRewardBCF b) T y ≤
        -((k : ℝ) * c) := by
  intro y hy
  obtain ⟨u, hu⟩ :=
    exists_source_orbitIntegral_eq_of_mem_core
      b hF hk T y hy
  rw [hu]
  calc
    (k : ℝ) *
          HGAS.Dynamics.orbitIntegral
            (polynomialSourceAngularFlow F)
            (sourceRadialRewardBCF F) T u ≤
        (k : ℝ) * (-c) :=
      mul_le_mul_of_nonneg_left (hblock u) (Nat.cast_nonneg k)
    _ = -((k : ℝ) * c) := by ring

theorem isClosed_stabilizedConeCore :
    IsClosed (stabilizedConeCore n k) := by
  exact isClosed_eq
    (continuous_completeToricEnergy.comp continuous_subtype_val)
    continuous_const

theorem measurableSet_stabilizedConeCore :
    MeasurableSet (stabilizedConeCore n k) :=
  isClosed_stabilizedConeCore.measurableSet

/-- After conditioning an invariant probability on a nonzero core
component, the stabilized radial average is strictly negative whenever
the source has a uniform negative block. -/
theorem conditionedCore_radialAverage_neg
    [Nonempty (weightedUnitSphere n k)]
    (b : CubicLiftStabilizationBounds F k)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F)
    (hk : 1 ≤ k)
    (μ : HGAS.Dynamics.InvariantProbabilityMeasure
      (stabilizedCubicAngularFlow b))
    (hsource :
      HGAS.Dynamics.HasUniformNegativeBlock
        (polynomialSourceAngularFlow F)
        (sourceRadialRewardBCF F))
    (hnonzero :
      μ.measure.toFiniteMeasure.restrict
        (stabilizedConeCore n k) ≠ 0) :
    HGAS.Dynamics.observableAverage
        (stabilizedCubicRadialRewardBCF b)
        ((HGAS.Dynamics.normalizeInvariantRestriction
          (stabilizedCubicAngularFlow b) μ
          (stabilizedConeCore n k)
          measurableSet_stabilizedConeCore
          (stabilizedConeCore_isInvariant b hF hk)
          hnonzero).measure) < 0 := by
  letI : CompactSpace (weightedUnitSphere n k) :=
    isCompact_iff_compactSpace.mp isCompact_weightedUnitSphere
  obtain ⟨T, c, hT, hc, hblock⟩ := hsource
  let ν :=
    HGAS.Dynamics.normalizeInvariantRestriction
      (stabilizedCubicAngularFlow b) μ
      (stabilizedConeCore n k)
      measurableSet_stabilizedConeCore
      (stabilizedConeCore_isInvariant b hF hk)
      hnonzero
  have hcore :
      ∀ᵐ y ∂(ν.measure : Measure (weightedUnitSphere n k)),
        y ∈ stabilizedConeCore n k := by
    exact HGAS.Dynamics.ae_mem_normalize_restrict
      μ.measure.toFiniteMeasure
      measurableSet_stabilizedConeCore hnonzero
  have hpoint :
      ∀ᵐ y ∂(ν.measure : Measure (weightedUnitSphere n k)),
        HGAS.Dynamics.orbitIntegral
            (stabilizedCubicAngularFlow b)
            (stabilizedCubicRadialRewardBCF b) T y ≤
          -((k : ℝ) * c) := by
    filter_upwards [hcore] with y hy
    exact core_orbitIntegral_le_of_source_block
      b hF hk hblock y hy
  have horbitInt :
      Integrable
        (HGAS.Dynamics.orbitIntegral
          (stabilizedCubicAngularFlow b)
          (stabilizedCubicRadialRewardBCF b) T)
        (ν.measure : Measure (weightedUnitSphere n k)) :=
    (HGAS.Dynamics.orbitIntegralBCF
      (stabilizedCubicAngularFlow b)
      (stabilizedCubicRadialRewardBCF b) T).integrable _
  have hconst :
      Integrable
        (fun _ : weightedUnitSphere n k ↦ -((k : ℝ) * c))
        (ν.measure : Measure (weightedUnitSphere n k)) :=
    integrable_const _
  have hint :
      (∫ y,
          HGAS.Dynamics.orbitIntegral
            (stabilizedCubicAngularFlow b)
            (stabilizedCubicRadialRewardBCF b) T y
          ∂(ν.measure : Measure (weightedUnitSphere n k))) ≤
        ∫ _ : weightedUnitSphere n k, -((k : ℝ) * c)
          ∂(ν.measure : Measure (weightedUnitSphere n k)) :=
    integral_mono_ae horbitInt hconst hpoint
  rw [HGAS.Dynamics.integral_orbitIntegral_eq
    (stabilizedCubicAngularFlow b)
    (stabilizedCubicRadialRewardBCF b) ν T] at hint
  simp only [integral_const,
    ProbabilityMeasure.measureReal_eq_coe_coeFn] at hint
  norm_num [ProbabilityMeasure.coeFn_univ] at hint
  change
    HGAS.Dynamics.observableAverage
        (stabilizedCubicRadialRewardBCF b) ν.measure < 0
  unfold HGAS.Dynamics.observableAverage
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hkcpos : 0 < (k : ℝ) * c := mul_pos hkpos hc
  by_contra hnot
  have havg_nonneg :
      0 ≤
        ∫ y, stabilizedCubicRadialRewardBCF b y
          ∂(ν.measure : Measure (weightedUnitSphere n k)) :=
    le_of_not_gt hnot
  have hprod_nonneg :
      0 ≤ T *
        ∫ y, stabilizedCubicRadialRewardBCF b y
          ∂(ν.measure : Measure (weightedUnitSphere n k)) :=
    mul_nonneg hT.le havg_nonneg
  have hint' :
      T *
          ∫ y, stabilizedCubicRadialRewardBCF b y
            ∂(ν.measure : Measure (weightedUnitSphere n k)) ≤
        -((k : ℝ) * c) := by
    simpa only [stabilizedCubicRadialRewardBCF_apply] using hint
  linarith

/-- The complementary invariant component is almost surely in the
outside-tube region, where the stabilization gives the pointwise reward
bound `≤ -1`. -/
theorem conditionedCoreCompl_radialAverage_le_neg_one
    [Nonempty (weightedUnitSphere n k)]
    (b : CubicLiftStabilizationBounds F k)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F)
    (hk : 1 ≤ k)
    (μ : HGAS.Dynamics.InvariantProbabilityMeasure
      (stabilizedCubicAngularFlow b))
    (hnonzero :
      μ.measure.toFiniteMeasure.restrict
        (stabilizedConeCore n k)ᶜ ≠ 0) :
    HGAS.Dynamics.observableAverage
        (stabilizedCubicRadialRewardBCF b)
        ((HGAS.Dynamics.normalizeInvariantRestriction
          (stabilizedCubicAngularFlow b) μ
          (stabilizedConeCore n k)ᶜ
          measurableSet_stabilizedConeCore.compl
          (HGAS.Dynamics.isInvariant_compl_of_flow
            (stabilizedCubicAngularFlow b)
            (stabilizedConeCore_isInvariant b hF hk))
          hnonzero).measure) ≤ -1 := by
  let ν :=
    HGAS.Dynamics.normalizeInvariantRestriction
      (stabilizedCubicAngularFlow b) μ
      (stabilizedConeCore n k)ᶜ
      measurableSet_stabilizedConeCore.compl
      (HGAS.Dynamics.isInvariant_compl_of_flow
        (stabilizedCubicAngularFlow b)
        (stabilizedConeCore_isInvariant b hF hk))
      hnonzero
  have hcompl :
      ∀ᵐ y ∂(ν.measure : Measure (weightedUnitSphere n k)),
        y ∈ (stabilizedConeCore n k)ᶜ := by
    exact HGAS.Dynamics.ae_mem_normalize_restrict
      μ.measure.toFiniteMeasure
      measurableSet_stabilizedConeCore.compl hnonzero
  have hsandwichμ :
      ∀ᵐ y ∂(μ.measure : Measure (weightedUnitSphere n k)),
        y ∈ stabilizedConeCore n k ∪
          stabilizedOutsideTube b := by
    rw [ae_iff]
    change
      (μ.measure : Measure (weightedUnitSphere n k))
        ((stabilizedConeCore n k ∪
          stabilizedOutsideTube b)ᶜ) = 0
    exact invariantMeasure_compl_core_union_outside_eq_zero b μ
  have hsandwichν :
      ∀ᵐ y ∂(ν.measure : Measure (weightedUnitSphere n k)),
        y ∈ stabilizedConeCore n k ∪
          stabilizedOutsideTube b := by
    change
      ∀ᵐ y ∂
        (((μ.measure.toFiniteMeasure.restrict
          (stabilizedConeCore n k)ᶜ).normalize :
            ProbabilityMeasure (weightedUnitSphere n k)) :
              Measure (weightedUnitSphere n k)),
        y ∈ stabilizedConeCore n k ∪
          stabilizedOutsideTube b
    rw [(μ.measure.toFiniteMeasure.restrict
      (stabilizedConeCore n k)ᶜ).toMeasure_normalize_eq_of_nonzero
        hnonzero]
    exact Measure.ae_smul_measure
      (ae_restrict_of_ae hsandwichμ) _
  have houtside :
      ∀ᵐ y ∂(ν.measure : Measure (weightedUnitSphere n k)),
        y ∈ stabilizedOutsideTube b := by
    filter_upwards [hcompl, hsandwichν] with y hyc hys
    rcases hys with hcore | hout
    · exact False.elim (hyc hcore)
    · exact hout
  have hpoint :
      ∀ᵐ y ∂(ν.measure : Measure (weightedUnitSphere n k)),
        stabilizedCubicRadialRewardBCF b y ≤ -1 := by
    filter_upwards [houtside] with y hy
    exact stabilizedCubicAngular_radialReward_le_neg_one
      b y.1 y.2 hy
  have hreward :
      Integrable
        (stabilizedCubicRadialRewardBCF b)
        (ν.measure : Measure (weightedUnitSphere n k)) :=
    (stabilizedCubicRadialRewardBCF b).integrable _
  have hconst :
      Integrable
        (fun _ : weightedUnitSphere n k ↦ (-1 : ℝ))
        (ν.measure : Measure (weightedUnitSphere n k)) :=
    integrable_const _
  have hint :
      (∫ y, stabilizedCubicRadialRewardBCF b y
          ∂(ν.measure : Measure (weightedUnitSphere n k))) ≤
        ∫ _ : weightedUnitSphere n k, (-1 : ℝ)
          ∂(ν.measure : Measure (weightedUnitSphere n k)) :=
    integral_mono_ae hreward hconst hpoint
  simp only [integral_const,
    ProbabilityMeasure.measureReal_eq_coe_coeFn] at hint
  norm_num [ProbabilityMeasure.coeFn_univ] at hint
  change
    HGAS.Dynamics.observableAverage
      (stabilizedCubicRadialRewardBCF b) ν.measure ≤ -1
  exact hint

/-- **Invariant-average transfer to the stabilized cubic lift.**

If the source radial cocycle has a uniform negative block, then every
invariant probability of the stabilized cubic angular flow has strictly
negative radial average.  The proof splits the measure into its invariant
core and core-complement components. -/
theorem stabilized_invariantAverage_neg_of_source_uniformNegativeBlock
    [Nonempty (sourceUnitSphere n)]
    (b : CubicLiftStabilizationBounds F k)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F)
    (hk : 1 ≤ k)
    (hsource :
      HGAS.Dynamics.HasUniformNegativeBlock
        (polynomialSourceAngularFlow F)
        (sourceRadialRewardBCF F))
    (μ : HGAS.Dynamics.InvariantProbabilityMeasure
      (stabilizedCubicAngularFlow b)) :
    HGAS.Dynamics.observableAverage
      (stabilizedCubicRadialRewardBCF b) μ.measure < 0 := by
  let u₀ : sourceUnitSphere n :=
    Classical.choice (inferInstance : Nonempty (sourceUnitSphere n))
  letI : Nonempty (weightedUnitSphere n k) :=
    ⟨positiveVeroneseSphereMap k u₀⟩
  let core : Set (weightedUnitSphere n k) :=
    stabilizedConeCore n k
  let νc : FiniteMeasure (weightedUnitSphere n k) :=
    μ.measure.toFiniteMeasure.restrict core
  let νo : FiniteMeasure (weightedUnitSphere n k) :=
    μ.measure.toFiniteMeasure.restrict coreᶜ
  have hcoreMeas : MeasurableSet core := by
    simpa only [core] using
      (measurableSet_stabilizedConeCore :
        MeasurableSet (stabilizedConeCore n k))
  have hsum :
      νc + νo = μ.measure.toFiniteMeasure := by
    apply FiniteMeasure.toMeasure_injective
    simpa only [νc, νo, core,
      FiniteMeasure.toMeasure_add,
      FiniteMeasure.restrict_measure_eq] using
      (Measure.restrict_add_restrict_compl hcoreMeas :
        (μ.measure : Measure (weightedUnitSphere n k)).restrict core +
          (μ.measure : Measure (weightedUnitSphere n k)).restrict coreᶜ =
        (μ.measure : Measure (weightedUnitSphere n k)))
  have hdecomp :
      (μ.measure : Measure (weightedUnitSphere n k)) =
        (νc : Measure (weightedUnitSphere n k)) +
          (νo : Measure (weightedUnitSphere n k)) := by
    have h := congrArg FiniteMeasure.toMeasure hsum
    exact h.symm
  have hcMeasure :
      (νc : Measure (weightedUnitSphere n k)) =
        νc.mass •
          (νc.normalize :
            Measure (weightedUnitSphere n k)) := by
    have h :=
      congrArg FiniteMeasure.toMeasure
        (νc.self_eq_mass_smul_normalize)
    simpa only [FiniteMeasure.toMeasure_smul] using h
  have hoMeasure :
      (νo : Measure (weightedUnitSphere n k)) =
        νo.mass •
          (νo.normalize :
            Measure (weightedUnitSphere n k)) := by
    have h :=
      congrArg FiniteMeasure.toMeasure
        (νo.self_eq_mass_smul_normalize)
    simpa only [FiniteMeasure.toMeasure_smul] using h
  have hνcInt :
      Integrable (stabilizedCubicRadialRewardBCF b)
        (νc : Measure (weightedUnitSphere n k)) :=
    (stabilizedCubicRadialRewardBCF b).integrable _
  have hνoInt :
      Integrable (stabilizedCubicRadialRewardBCF b)
        (νo : Measure (weightedUnitSphere n k)) :=
    (stabilizedCubicRadialRewardBCF b).integrable _
  have htotal :
      HGAS.Dynamics.observableAverage
          (stabilizedCubicRadialRewardBCF b) μ.measure =
        (νc.mass : ℝ) *
            HGAS.Dynamics.observableAverage
              (stabilizedCubicRadialRewardBCF b) νc.normalize +
          (νo.mass : ℝ) *
            HGAS.Dynamics.observableAverage
              (stabilizedCubicRadialRewardBCF b) νo.normalize := by
    unfold HGAS.Dynamics.observableAverage
    calc
      (∫ y, stabilizedCubicRadialRewardBCF b y
          ∂(μ.measure : Measure (weightedUnitSphere n k))) =
          ∫ y, stabilizedCubicRadialRewardBCF b y
            ∂((νc : Measure (weightedUnitSphere n k)) +
              (νo : Measure (weightedUnitSphere n k))) := by
            rw [hdecomp]
      _ =
          (∫ y, stabilizedCubicRadialRewardBCF b y
            ∂(νc : Measure (weightedUnitSphere n k))) +
          ∫ y, stabilizedCubicRadialRewardBCF b y
            ∂(νo : Measure (weightedUnitSphere n k)) :=
        integral_add_measure hνcInt hνoInt
      _ =
          (νc.mass : ℝ) *
              ∫ y, stabilizedCubicRadialRewardBCF b y
                ∂(νc.normalize :
                  Measure (weightedUnitSphere n k)) +
            (νo.mass : ℝ) *
              ∫ y, stabilizedCubicRadialRewardBCF b y
                ∂(νo.normalize :
                  Measure (weightedUnitSphere n k)) := by
        rw [hcMeasure, hoMeasure]
        simp only [integral_smul_nnreal_measure,
          NNReal.smul_def, smul_eq_mul]
  by_cases hnc : νc ≠ 0
  · have hcoreNeg :
        HGAS.Dynamics.observableAverage
          (stabilizedCubicRadialRewardBCF b) νc.normalize < 0 := by
      simpa only [νc, core] using
        conditionedCore_radialAverage_neg
          b hF hk μ hsource hnc
    have hmc :
        0 < (νc.mass : ℝ) := by
      exact_mod_cast
        (pos_iff_ne_zero.mpr
          ((FiniteMeasure.mass_nonzero_iff νc).2 hnc))
    by_cases hno : νo ≠ 0
    · have houtNeg :
          HGAS.Dynamics.observableAverage
            (stabilizedCubicRadialRewardBCF b) νo.normalize < 0 := by
        have houtLe :
            HGAS.Dynamics.observableAverage
              (stabilizedCubicRadialRewardBCF b) νo.normalize ≤ -1 := by
          simpa only [νo, core] using
            conditionedCoreCompl_radialAverage_le_neg_one
              b hF hk μ hno
        linarith
      have hmo :
          0 < (νo.mass : ℝ) := by
        exact_mod_cast
          (pos_iff_ne_zero.mpr
            ((FiniteMeasure.mass_nonzero_iff νo).2 hno))
      rw [htotal]
      exact add_neg
        (mul_neg_of_pos_of_neg hmc hcoreNeg)
        (mul_neg_of_pos_of_neg hmo houtNeg)
    · have hmo0 : νo.mass = 0 := by
        rw [FiniteMeasure.mass_zero_iff]
        exact not_ne_iff.mp hno
      rw [htotal, hmo0]
      simp only [NNReal.coe_zero, zero_mul, add_zero]
      exact mul_neg_of_pos_of_neg hmc hcoreNeg
  · have hnc0 : νc = 0 := not_ne_iff.mp hnc
    have hno : νo ≠ 0 := by
      intro hno
      have hzero :
          μ.measure.toFiniteMeasure = 0 := by
        rw [← hsum, hnc0, hno]
        simp
      exact μ.measure.toFiniteMeasure_nonzero hzero
    have houtNeg :
        HGAS.Dynamics.observableAverage
          (stabilizedCubicRadialRewardBCF b) νo.normalize < 0 := by
      have houtLe :
          HGAS.Dynamics.observableAverage
            (stabilizedCubicRadialRewardBCF b) νo.normalize ≤ -1 := by
        simpa only [νo, core] using
          conditionedCoreCompl_radialAverage_le_neg_one
            b hF hk μ hno
      linarith
    have hmo :
        0 < (νo.mass : ℝ) := by
      exact_mod_cast
        (pos_iff_ne_zero.mpr
          ((FiniteMeasure.mass_nonzero_iff νo).2 hno))
    have hmc0 : νc.mass = 0 := by
      rw [FiniteMeasure.mass_zero_iff]
      exact hnc0
    rw [htotal, hmc0]
    simp only [NNReal.coe_zero, zero_mul, zero_add]
    exact mul_neg_of_pos_of_neg hmo houtNeg

/-- Compactness turns the preceding strict invariant-average statement
into a single uniform negative block for the stabilized cubic system. -/
theorem stabilized_uniformNegativeBlock_of_source_uniformNegativeBlock
    [Nonempty (sourceUnitSphere n)]
    (b : CubicLiftStabilizationBounds F k)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F)
    (hk : 1 ≤ k)
    (hsource :
      HGAS.Dynamics.HasUniformNegativeBlock
        (polynomialSourceAngularFlow F)
        (sourceRadialRewardBCF F)) :
    HGAS.Dynamics.HasUniformNegativeBlock
      (stabilizedCubicAngularFlow b)
      (stabilizedCubicRadialRewardBCF b) := by
  let u₀ : sourceUnitSphere n :=
    Classical.choice (inferInstance : Nonempty (sourceUnitSphere n))
  letI : Nonempty (weightedUnitSphere n k) :=
    ⟨positiveVeroneseSphereMap k u₀⟩
  letI : CompactSpace (weightedUnitSphere n k) :=
    isCompact_iff_compactSpace.mp isCompact_weightedUnitSphere
  apply HGAS.Dynamics.uniformNegativeBlock_of_invariantAverage_neg
  intro μ
  exact stabilized_invariantAverage_neg_of_source_uniformNegativeBlock
    b hF hk hsource μ

/-- Restricting a stabilized negative block to the positive Veronese
sheet gives a source block.  The margin is divided by the positive
integer `k`. -/
theorem source_uniformNegativeBlock_of_stabilized_uniformNegativeBlock
    (b : CubicLiftStabilizationBounds F k)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F)
    (hk : 1 ≤ k)
    (hstabilized :
      HGAS.Dynamics.HasUniformNegativeBlock
        (stabilizedCubicAngularFlow b)
        (stabilizedCubicRadialRewardBCF b)) :
    HGAS.Dynamics.HasUniformNegativeBlock
      (polynomialSourceAngularFlow F)
      (sourceRadialRewardBCF F) := by
  obtain ⟨T, c, hT, hc, hblock⟩ := hstabilized
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast hk
  refine ⟨T, c / (k : ℝ), hT, div_pos hc hkpos, ?_⟩
  intro u
  have hb := hblock (positiveVeroneseSphereMap k u)
  rw [positiveVeronese_orbitIntegral_eq b hF hk T u] at hb
  calc
    HGAS.Dynamics.orbitIntegral
          (polynomialSourceAngularFlow F)
          (sourceRadialRewardBCF F) T u ≤
        -c / (k : ℝ) := by
      apply (le_div_iff₀ hkpos).2
      simpa only [mul_comm] using hb
    _ = -(c / (k : ℝ)) := by ring

/-- The source and stabilized cubic angular radial cocycles have a
uniform negative block simultaneously.  This is the exact compact-flow
criterion underlying the GAS-preservation theorem. -/
theorem source_uniformNegativeBlock_iff_stabilized
    [Nonempty (sourceUnitSphere n)]
    (b : CubicLiftStabilizationBounds F k)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F)
    (hk : 1 ≤ k) :
    HGAS.Dynamics.HasUniformNegativeBlock
        (polynomialSourceAngularFlow F)
        (sourceRadialRewardBCF F) ↔
      HGAS.Dynamics.HasUniformNegativeBlock
        (stabilizedCubicAngularFlow b)
        (stabilizedCubicRadialRewardBCF b) := by
  constructor
  · exact stabilized_uniformNegativeBlock_of_source_uniformNegativeBlock
      b hF hk
  · exact source_uniformNegativeBlock_of_stabilized_uniformNegativeBlock
      b hF hk

end

end HGAS.Veronese
