import Mathlib.Dynamics.Ergodic.RadonNikodym
import Mathlib.Dynamics.Ergodic.Action.Basic
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.Tactic

/-!
# Uniqueness of invariant probability on a transitive space

This file proves a reusable homogeneous-space uniqueness theorem.

Let a measurable group `G` act measurably and transitively on `X`, and
let `m` be a nonzero s-finite left-invariant measure on `G`.  Then any
two `G`-invariant probability measures on `X` coincide.

The proof does not choose a measurable section of the orbit map.  Instead,
replace `m` by the finite probability `m.toFinite`, which has exactly the
same null sets.  For `x : X`, push this probability through the orbit map
`g ↦ g • x`.  Transitivity and quasi-invariance of Haar null sets show
that all such orbit probabilities have the same null sets.  Fubini then
shows that every invariant probability has those same null sets.

It follows that two invariant probabilities are mutually absolutely
continuous.  The Radon--Nikodym derivative of one with respect to the
other is invariant.  The full transitive action is ergodic, so that
derivative is almost everywhere constant; total mass one forces the
constant to be one.

The theorem is formulated for an arbitrary transitive action.  In
particular it applies to non-normal homogeneous quotients, where the
quotient is not itself a group.
-/

namespace HGAS.MeasureTheory

open Function Set Filter
open scoped ENNReal _root_.MeasureTheory Pointwise

noncomputable section

/-! ## Invariant functions for an ergodic action -/

section ErgodicFunction

variable {G X : Type*} [SMul G X] [MeasurableSpace X]

/-- A measurable `ℝ≥0∞`-valued function invariant almost everywhere
under every element of an ergodic action is almost everywhere constant.

This group-action version complements Mathlib's corresponding theorem
for a single ergodic transformation. -/
theorem _root_.ErgodicSMul.ae_eq_const_of_forall_smul_ae_eq
    {μ : _root_.MeasureTheory.Measure X}
    [ErgodicSMul G X μ]
    {f : X → ℝ≥0∞}
    (hf : Measurable f)
    (hinv : ∀ g : G, f ∘ (g • ·) =ᵐ[μ] f) :
    ∃ c : ℝ≥0∞, f =ᵐ[μ] Function.const X c := by
  refine
    exists_eventuallyEq_const_of_forall_separating
      MeasurableSet fun U hU ↦ ?_
  apply eventuallyConst_set.mp
  apply ErgodicSMul.aeconst_of_forall_preimage_smul_ae_eq
    (G := G)
  · exact hf hU
  · intro g
    filter_upwards [hinv g] with x hx
    exact congrArg (fun z : ℝ≥0∞ ↦ z ∈ U) hx

end ErgodicFunction

/-! ## Orbit probabilities and their null sets -/

section OrbitMeasure

open _root_.MeasureTheory

variable {G X : Type*}
    [Group G]
    [MeasurableSpace G]
    [MeasurableMul₂ G]
    [MeasurableInv G]
    [MeasurableSpace X]
    [MulAction G X]
    [MeasurableSMul₂ G X]
    [MulAction.IsPretransitive G X]

variable (m : Measure G) [SFinite m] [m.IsMulLeftInvariant]

/-- Push the finite probability equivalent to `m` through the orbit map
based at `x`.

When `m` is nonzero, `m.toFinite` is a probability.  We retain the
unbundled measure because only its null sets matter in the intermediate
lemmas. -/
def finiteOrbitMeasure (x : X) : Measure X :=
  Measure.map (fun g : G ↦ g • x) m.toFinite

/-- Orbit measures based at any two points have the same null sets.

If `x = a • y`, the two orbit maps differ by right multiplication by
`a`.  A left-invariant measure is quasi-invariant under right
multiplication, and `m.toFinite` has the same null sets as `m`. -/
theorem finiteOrbitMeasure_absolutelyContinuous
    (x y : X) :
    finiteOrbitMeasure m x ≪ finiteOrbitMeasure m y := by
  obtain ⟨a, rfl⟩ := MulAction.exists_smul_eq G y x
  have hqmp :
      Measure.QuasiMeasurePreserving
        (fun g : G ↦ g * a)
        m.toFinite m.toFinite :=
    (quasiMeasurePreserving_mul_right m a).mono
      (toFinite_absolutelyContinuous m)
      (absolutelyContinuous_toFinite m)
  unfold finiteOrbitMeasure
  have hcomp :
      (fun g : G ↦ g • (a • y)) =
        (fun g : G ↦ g • y) ∘ (fun g : G ↦ g * a) := by
    funext g
    simp only [Function.comp_apply, mul_smul]
  rw [hcomp]
  rw [← Measure.map_map
    (measurable_smul_const y)
    hqmp.measurable]
  exact
    hqmp.absolutelyContinuous.map
      (measurable_smul_const y)

/-- Every finite orbit measure is absolutely continuous with respect to
an invariant probability.

For a null set `A`, invariance says that every `g`-translate has zero
probability.  Fubini supplies one base point whose orbit measure gives
`A` mass zero; transitivity transfers this to every base point. -/
theorem finiteOrbitMeasure_absolutelyContinuous_invariant
    (x : X) (μ : Measure X)
    [IsProbabilityMeasure μ]
    [SMulInvariantMeasure G X μ] :
    finiteOrbitMeasure m x ≪ μ := by
  apply Measure.AbsolutelyContinuous.mk
  intro A hA hμA
  have hall :
      ∀ᵐ g ∂m.toFinite, ∀ᵐ y ∂μ, g • y ∉ A := by
    refine Filter.Eventually.of_forall fun g ↦
      measure_eq_zero_iff_ae_notMem.mp ?_
    change μ ((fun y : X ↦ g • y) ⁻¹' A) = 0
    rw [(measurePreserving_smul g μ).measure_preimage
      hA.nullMeasurableSet]
    exact hμA
  have hmeas :
      MeasurableSet {p : G × X | p.1 • p.2 ∉ A} :=
    hA.compl.preimage measurable_smul
  have hswap :
      ∀ᵐ y ∂μ, ∀ᵐ g ∂m.toFinite, g • y ∉ A :=
    (Measure.ae_ae_comm hmeas).mp hall
  obtain ⟨y, hy⟩ := hswap.exists
  apply finiteOrbitMeasure_absolutelyContinuous m x y
  unfold finiteOrbitMeasure
  rw [Measure.map_apply (measurable_smul_const y) hA]
  exact measure_eq_zero_iff_ae_notMem.mpr hy

variable [NeZero m]

/-- Conversely, an invariant probability is absolutely continuous with
respect to every finite orbit measure.

If one orbit measure gives `A` mass zero, all of them do.  A second
application of Fubini produces one group element whose preimage of `A`
has invariant-probability mass zero; invariance then gives `μ A = 0`. -/
theorem invariant_absolutelyContinuous_finiteOrbitMeasure
    (μ : Measure X) (x : X)
    [IsProbabilityMeasure μ]
    [SMulInvariantMeasure G X μ] :
    μ ≪ finiteOrbitMeasure m x := by
  apply Measure.AbsolutelyContinuous.mk
  intro A hA horbit
  have hall :
      ∀ᵐ y ∂μ, ∀ᵐ g ∂m.toFinite, g • y ∉ A := by
    refine Filter.Eventually.of_forall fun y ↦
      measure_eq_zero_iff_ae_notMem.mp ?_
    have hyzero :
        finiteOrbitMeasure m y A = 0 :=
      finiteOrbitMeasure_absolutelyContinuous m y x horbit
    unfold finiteOrbitMeasure at hyzero
    rw [Measure.map_apply
      (measurable_smul_const y) hA] at hyzero
    exact hyzero
  have hmeas :
      MeasurableSet {p : X × G | p.2 • p.1 ∉ A} :=
    hA.compl.preimage
      (measurable_smul.comp
        (measurable_snd.prodMk measurable_fst))
  have hswap :
      ∀ᵐ g ∂m.toFinite, ∀ᵐ y ∂μ, g • y ∉ A :=
    (Measure.ae_ae_comm hmeas).mp hall
  obtain ⟨g, hg⟩ := hswap.exists
  have hpre :
      μ ((fun y : X ↦ g • y) ⁻¹' A) = 0 :=
    measure_eq_zero_iff_ae_notMem.mpr hg
  rw [(measurePreserving_smul g μ).measure_preimage
    hA.nullMeasurableSet] at hpre
  exact hpre

include m in
/-- Any two invariant probabilities on a transitive measurable
`G`-space are mutually absolutely continuous. -/
theorem invariantProbability_absolutelyContinuous_of_pretransitive
    (μ ν : Measure X)
    [IsProbabilityMeasure μ]
    [SMulInvariantMeasure G X μ]
    [IsProbabilityMeasure ν]
    [SMulInvariantMeasure G X ν] :
    μ ≪ ν := by
  letI : Nonempty X :=
    nonempty_of_isProbabilityMeasure μ
  let x : X := Classical.choice inferInstance
  exact
    (invariant_absolutelyContinuous_finiteOrbitMeasure
      m μ x).trans
      (finiteOrbitMeasure_absolutelyContinuous_invariant
        m x ν)

/-! ## Ergodicity and uniqueness -/

include m in
/-- An invariant probability for a transitive measurable action is
ergodic for the full action.

The assertion concerns the full acting group, not an individual group
element. -/
theorem ergodicSMul_of_pretransitive_probability
    (μ : Measure X)
    [IsProbabilityMeasure μ]
    [SMulInvariantMeasure G X μ] :
    ErgodicSMul G X μ := by
  refine ⟨?_⟩
  intro s hs hinv
  suffices
      (∃ᵐ x ∂μ, x ∈ s) →
        ∀ᵐ x ∂μ, x ∈ s by
    simp only [eventuallyConst_set, ← not_frequently]
    exact or_not_of_imp this
  intro hfreq
  have hmeas :
      MeasurableSet
        {p : G × X |
          (p.1 • p.2 ∈ s ↔ p.2 ∈ s)} :=
    ((hs.preimage
      (measurable_smul.comp
        (measurable_fst.prodMk measurable_snd))).iff
      (hs.preimage measurable_snd))
  have hdouble :
      ∀ᵐ x ∂μ, ∀ᵐ g ∂m.toFinite,
        (g • x ∈ s ↔ x ∈ s) := by
    rw [← Measure.ae_ae_comm hmeas]
    exact Filter.Eventually.of_forall fun g ↦
      (hinv g).mem_iff
  obtain ⟨x, hxs, hx⟩ :=
    (hfreq.and_eventually hdouble).exists
  have horbit :
      ∀ᵐ y ∂finiteOrbitMeasure m x, y ∈ s := by
    unfold finiteOrbitMeasure
    exact
      (ae_map_iff
        (measurable_smul_const x).aemeasurable hs).2
          (hx.mono fun g hg ↦ hg.mpr hxs)
  exact
    (invariant_absolutelyContinuous_finiteOrbitMeasure
      m μ x).ae_le horbit

include m in
/-- **Uniqueness of invariant probability on a transitive measurable
space.**

This is the reusable homogeneous-space theorem.  No normality of a
stabilizer is assumed. -/
theorem invariantProbability_unique_of_pretransitive
    (μ ν : Measure X)
    [IsProbabilityMeasure μ]
    [SMulInvariantMeasure G X μ]
    [IsProbabilityMeasure ν]
    [SMulInvariantMeasure G X ν] :
    μ = ν := by
  letI : ErgodicSMul G X μ :=
    ergodicSMul_of_pretransitive_probability m μ
  have hac : ν ≪ μ :=
    invariantProbability_absolutelyContinuous_of_pretransitive
      m ν μ
  have hderiv :
      ∀ g : G,
        ν.rnDeriv μ ∘ (g • ·) =ᵐ[μ]
          ν.rnDeriv μ :=
    fun g ↦
      (measurePreserving_smul g ν).rnDeriv_comp_aeEq
        (measurePreserving_smul g μ)
  obtain ⟨c, hc⟩ :=
    ErgodicSMul.ae_eq_const_of_forall_smul_ae_eq
      (Measure.measurable_rnDeriv ν μ) hderiv
  have hνc : ν = c • μ := by
    calc
      ν = μ.withDensity (ν.rnDeriv μ) :=
        (Measure.withDensity_rnDeriv_eq ν μ hac).symm
      _ = μ.withDensity (fun _ : X ↦ c) :=
        withDensity_congr_ae hc
      _ = c • μ := withDensity_const c
  have hc_one : c = 1 := by
    have huniv :=
      congrArg (fun ξ : Measure X ↦ ξ Set.univ) hνc
    exact
      (by simpa using huniv :
        (1 : ℝ≥0∞) = c).symm
  rw [hνc, hc_one, one_smul]

end OrbitMeasure

end

end HGAS.MeasureTheory
