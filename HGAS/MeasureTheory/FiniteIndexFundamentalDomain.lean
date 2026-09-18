import Mathlib.GroupTheory.Complement
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Tactic

/-!
# Fundamental domains for finite-index subgroups

This file records a general construction which is useful independently of
the modular-surface application.  If a group `G` acts measure-preservingly
on a measured space and `F` is a fundamental domain for `G`, then a finite
union of translates of `F` is a fundamental domain for any finite-index
subgroup `H`.

The construction uses a left transversal `S` for `H`.  Every `g : G` has
a unique factorization `g = s h`, with `s ∈ S` and `h ∈ H`.  Consequently

```
D = ⋃ s ∈ S, s⁻¹ • F
```

meets each `H`-orbit once (up to the same null sets as `F`).  The inverses
are forced by Mathlib's convention that a fundamental domain `F` satisfies
`∃ g, g • x ∈ F`.
-/

namespace HGAS.MeasureTheory

open Function _root_.MeasureTheory Set
open scoped ENNReal Pointwise

noncomputable section

variable {G α : Type*} [Group G] [MeasurableSpace α] [MulAction G α]

/-- The canonical finite-index-subgroup domain obtained from Mathlib's
default left transversal. -/
def finiteIndexSubgroupDomain (H : Subgroup G) (F : Set α) : Set α :=
  let S : H.LeftTransversal := default
  ⋃ s : ↥(S : Set G), (s : G)⁻¹ • F

/-- Passing from a group to a finite-index subgroup preserves the existence
of a measure-theoretic fundamental domain.

The returned domain is `finiteIndexSubgroupDomain H F`; the existential
content in the theorem statement is therefore completely explicit. -/
theorem IsFundamentalDomain.finiteIndexSubgroup
    {μ : Measure α}
    [MeasurableConstSMul G α] [SMulInvariantMeasure G α μ]
    {F : Set α}
    (hF : IsFundamentalDomain G F μ)
    (H : Subgroup G) [H.FiniteIndex] :
    IsFundamentalDomain H (finiteIndexSubgroupDomain H F) μ := by
  let S : H.LeftTransversal := default
  have hSfinite : (S : Set G).Finite :=
    S.2.finite_left
  letI : Fintype ↥(S : Set G) :=
    hSfinite.fintype
  let D : Set α :=
    ⋃ s : ↥(S : Set G), (s : G)⁻¹ • F
  have hfactorInjective :
      Function.Injective
        (fun p : H × ↥(S : Set G) ↦
          (p.1 : G) * (p.2 : G)⁻¹) := by
    intro p q hpq
    have hinv :
        (p.2 : G) * (p.1 : G)⁻¹ =
          (q.2 : G) * (q.1 : G)⁻¹ := by
      simpa only [mul_inv_rev, inv_inv] using
        congrArg Inv.inv hpq
    have hpairs :
        (p.2,
            (⟨(p.1 : G)⁻¹, H.inv_mem p.1.2⟩ : H)) =
          (q.2,
            (⟨(q.1 : G)⁻¹, H.inv_mem q.1.2⟩ : H)) :=
      S.2.1 hinv
    apply Prod.ext
    · apply Subtype.ext
      apply inv_injective
      exact congrArg Subtype.val (Prod.ext_iff.mp hpairs).2
    · exact (Prod.ext_iff.mp hpairs).1
  have hDnull : NullMeasurableSet D μ := by
    apply NullMeasurableSet.iUnion
    intro s
    exact hF.nullMeasurableSet_smul (s : G)⁻¹
  have hDcovers : ∀ᵐ x ∂μ, ∃ h : H, h • x ∈ D := by
    filter_upwards [hF.ae_covers] with x hx
    obtain ⟨g, hg⟩ := hx
    let p : ↥(S : Set G) × H :=
      S.2.equiv g
    refine ⟨p.2, ?_⟩
    apply Set.mem_iUnion.2
    refine ⟨p.1, ?_⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    have hfactor :
        (p.1 : G) * (p.2 : G) = g :=
      S.2.equiv_fst_mul_equiv_snd g
    rw [← hfactor] at hg
    rw [inv_inv]
    change (p.1 : G) • ((p.2 : G) • x) ∈ F
    simpa only [smul_smul] using hg
  have hDdisjoint :
      Pairwise
        (AEDisjoint μ on fun h : H ↦ h • D) := by
    intro h₁ h₂ hne
    have htranslate (h : H) :
        (h : G) • D =
          ⋃ s : ↥(S : Set G),
            ((h : G) * (s : G)⁻¹) • F := by
      change
        (h : G) • (⋃ s : ↥(S : Set G), (s : G)⁻¹ • F) =
          ⋃ s : ↥(S : Set G),
            ((h : G) * (s : G)⁻¹) • F
      ext x
      simp only [Set.mem_smul_set_iff_inv_smul_mem,
        Set.mem_iUnion, mul_inv_rev, smul_smul]
    change
      AEDisjoint μ ((h₁ : G) • D) ((h₂ : G) • D)
    rw [htranslate h₁, htranslate h₂]
    simp only [AEDisjoint.iUnion_left_iff,
      AEDisjoint.iUnion_right_iff]
    intro s₁ s₂
    apply hF.aedisjoint
    intro heq
    apply hne
    have hpairs :
        (h₁, s₂) = (h₂, s₁) :=
      hfactorInjective (by
        simpa only using heq)
    exact congrArg Prod.fst hpairs
  change IsFundamentalDomain H D μ
  exact ⟨hDnull, hDcovers, hDdisjoint⟩

/-- The induced domain has finite mass whenever the original domain does.

This statement does not need the fundamental-domain property itself: it is
just finite subadditivity, finiteness of a left transversal, and invariance
of `μ` under each translate. -/
theorem finiteIndexSubgroupDomain_measure_ne_top
    {μ : Measure α}
    [MeasurableConstSMul G α] [SMulInvariantMeasure G α μ]
    (H : Subgroup G) [H.FiniteIndex]
    {F : Set α} (hFfinite : μ F ≠ ∞) :
    μ (finiteIndexSubgroupDomain H F) ≠ ∞ := by
  let S : H.LeftTransversal := default
  have hSfinite : (S : Set G).Finite :=
    S.2.finite_left
  have hdomain :
      finiteIndexSubgroupDomain H F =
        ⋃ g ∈ (S : Set G), g⁻¹ • F := by
    ext x
    simp only [finiteIndexSubgroupDomain, S,
      Set.mem_iUnion]
    constructor
    · rintro ⟨s, hs⟩
      exact ⟨s.1, s.2, hs⟩
    · rintro ⟨g, hg, hx⟩
      exact ⟨⟨g, hg⟩, hx⟩
  rw [hdomain]
  apply measure_biUnion_ne_top hSfinite
  intro g hg
  simpa only [measure_smul] using hFfinite

/-- Finite covolume passes from a group to every finite-index subgroup. -/
theorem IsFundamentalDomain.finiteIndexSubgroup_finite
    {μ : Measure α}
    [MeasurableConstSMul G α] [SMulInvariantMeasure G α μ]
    {F : Set α}
    (hF : IsFundamentalDomain G F μ)
    (H : Subgroup G) [H.FiniteIndex]
    (hFfinite : μ F ≠ ∞) :
    IsFundamentalDomain H
        (finiteIndexSubgroupDomain H F) μ ∧
      μ (finiteIndexSubgroupDomain H F) ≠ ∞ :=
  ⟨HGAS.MeasureTheory.IsFundamentalDomain.finiteIndexSubgroup hF H,
    finiteIndexSubgroupDomain_measure_ne_top
      H hFfinite⟩

end

end HGAS.MeasureTheory
