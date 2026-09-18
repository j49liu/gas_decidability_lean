import HGAS.Modular.CanonicalLambdaGammaTwo
import HGAS.Modular.CanonicalLambdaImaginaryAxis
import HGAS.Modular.CanonicalLambdaTargetTopology
import HGAS.Topology.FiniteOuterCoveringComposition
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# The effective level-two modular quotient

The central element `-1` acts trivially on the upper half-plane, so the
literal action of `Γ(2)` is not free.  This file replaces it by its effective
image in the permutation group of the upper half-plane.  The resulting group
is the formal counterpart of `Γ(2) / {±1}`.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I
open Complex Real ModularGroup Filter Topology
open scoped MatrixGroups CongruenceSubgroup

noncomputable section

/-- The principal level-two congruence subgroup. -/
abbrev GammaTwo := CongruenceSubgroup.Gamma 2

/-- The image of `Γ(2)` in `GL(2, ℝ)`. -/
abbrev GammaTwoGL : Subgroup (GL (Fin 2) ℝ) :=
  (↑GammaTwo : Subgroup (GL (Fin 2) ℝ))

/-- The effective deck group `Γ(2) / {±1}`, realized as the image of its
action on the upper half-plane. -/
abbrev EffectiveGammaTwo :=
  (MulAction.toPermHom GammaTwoGL ℍ).range

example : MulAction GammaTwo ℍ := inferInstance
example : ContinuousConstSMul GammaTwoGL ℍ := inferInstance
example : ProperlyDiscontinuousSMul GammaTwoGL ℍ := inferInstance
example : MulAction EffectiveGammaTwo ℍ := inferInstance

/-- Every effective deck transformation is represented by an element of the
arithmetic subgroup `GammaTwoGL`, with the same pointwise action. -/
theorem EffectiveGammaTwo.exists_representative
    (p : EffectiveGammaTwo) :
    ∃ g : GammaTwoGL, ∀ z : ℍ, p • z = g • z := by
  obtain ⟨g, hg⟩ := p.property
  refine ⟨g, fun z ↦ ?_⟩
  change p.1 z = g • z
  rw [← hg]
  rfl

instance : ContinuousConstSMul EffectiveGammaTwo ℍ where
  continuous_const_smul p := by
    obtain ⟨g, hg⟩ :=
      EffectiveGammaTwo.exists_representative p
    have hc : Continuous (g • · : ℍ → ℍ) :=
      continuous_const_smul g
    rw [funext hg]
    exact hc

instance : ProperlyDiscontinuousSMul EffectiveGammaTwo ℍ where
  finite_disjoint_inter_image {K} {L} hK hL := by
    let φ : GammaTwoGL → EffectiveGammaTwo :=
      (MulAction.toPermHom GammaTwoGL ℍ).rangeRestrict
    have hfinite :
        {g : GammaTwoGL |
          ((g • ·) '' K ∩ L).Nonempty}.Finite :=
      ProperlyDiscontinuousSMul.finite_disjoint_inter_image
        (Γ := GammaTwoGL) hK hL
    refine (hfinite.image φ).subset ?_
    intro p hp
    obtain ⟨g, hg⟩ :=
      EffectiveGammaTwo.exists_representative p
    have haction :
        (p • · : ℍ → ℍ) = (g • · : ℍ → ℍ) :=
      funext hg
    have hg_bad :
        ((g • ·) '' K ∩ L).Nonempty := by
      simpa only [← haction] using hp
    refine ⟨g, hg_bad, ?_⟩
    apply Subtype.ext
    apply Equiv.ext
    intro z
    exact (hg z).symm

/-- The only elements of `Γ(2)` fixing a point of the upper half-plane are
the two scalar matrices.  The proof moves the point into the closed standard
fundamental domain, invokes Mathlib's complete boundary-stabilizer
classification there, and eliminates every non-scalar case modulo two. -/
theorem gammaTwo_eq_one_or_neg_one_of_smul_eq
    {g : SL(2, ℤ)} (hg : g ∈ GammaTwo)
    {z : ℍ} (hfix : g • z = z) :
    g = 1 ∨ g = -1 := by
  obtain ⟨a, ha⟩ := ModularGroup.exists_smul_mem_fd z
  let k : SL(2, ℤ) := a * g * a⁻¹
  have hk_mem : k ∈ GammaTwo := by
    exact (CongruenceSubgroup.Gamma_normal 2).conj_mem
      g hg a
  have hk_fix : k • (a • z) = a • z := by
    simp only [k, mul_smul, inv_smul_smul, hfix]
  have hcases :=
    ModularGroup.cases_of_mem_fd_smul_mem_fd
      (g := k) ha (by rw [hk_fix]; exact ha)
  rcases hcases with hscalar | hT | hTi | hS |
      hTS | hTiSTi | hSTi | hST | hTST | hTiS
  · rcases hscalar with hk | hk
    · left
      have : a⁻¹ * k * a = g := by
        simp [k, mul_assoc]
      simpa [hk] using this.symm
    · right
      have : a⁻¹ * k * a = g := by
        simp [k, mul_assoc]
      simpa [hk] using this.symm
  all_goals
    rcases ‹(_ ∨ _) ∧ _›.1 with hk | hk
    · rw [hk] at hk_mem
      norm_num [GammaTwo, CongruenceSubgroup.Gamma_mem,
        ModularGroup.S, ModularGroup.T] at hk_mem
    · rw [hk] at hk_mem
      norm_num [GammaTwo, CongruenceSubgroup.Gamma_mem,
        ModularGroup.S, ModularGroup.T] at hk_mem

/-- A matrix in the real arithmetic image of `Γ(2)` has an integral
level-two representative inducing the same transformation of `ℍ`. -/
theorem GammaTwoGL.exists_integral_representative
    (g : GammaTwoGL) :
    ∃ a : SL(2, ℤ), a ∈ GammaTwo ∧
      ∀ z : ℍ, g • z = a • z := by
  obtain ⟨a, ha, hval⟩ := g.property
  refine ⟨a, ha, fun z ↦ ?_⟩
  change g.1 • z = a • z
  rw [← hval]
  rfl

/-- The effective level-two action is free. -/
theorem EffectiveGammaTwo.eq_one_of_smul_eq
    (p : EffectiveGammaTwo) (z : ℍ)
    (hfix : p • z = z) :
    p = 1 := by
  obtain ⟨g, hpg⟩ :=
    EffectiveGammaTwo.exists_representative p
  obtain ⟨a, ha, hga⟩ :=
    GammaTwoGL.exists_integral_representative g
  have ha_fix : a • z = z := by
    rw [← hga z, ← hpg z]
    exact hfix
  have ha_scalar :=
    gammaTwo_eq_one_or_neg_one_of_smul_eq ha ha_fix
  apply Subtype.ext
  apply Equiv.ext
  intro w
  change p • w = (1 : EffectiveGammaTwo) • w
  calc
    p • w = g • w := hpg w
    _ = a • w := hga w
    _ = w := by
      rcases ha_scalar with rfl | rfl
      · exact one_smul _ _
      · simp only [SL_neg_smul, one_smul]
    _ = (1 : EffectiveGammaTwo) • w :=
      (one_smul _ _).symm

instance : IsCancelSMul EffectiveGammaTwo ℍ :=
  isCancelSMul_iff_eq_one_of_smul_eq.mpr
    EffectiveGammaTwo.eq_one_of_smul_eq

/-- The effective modular quotient of the upper half-plane. -/
abbrev LambdaModularQuotient :=
  Quotient (MulAction.orbitRel EffectiveGammaTwo ℍ)

/-- The quotient projection onto the effective level-two modular quotient. -/
def lambdaModularQuotientMk :
    ℍ → LambdaModularQuotient :=
  Quotient.mk _

/-- The effective quotient projection is a quotient covering map. -/
theorem lambdaModularQuotientMk_isQuotientCoveringMap :
    IsQuotientCoveringMap lambdaModularQuotientMk
      EffectiveGammaTwo := by
  exact
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

/-- In particular, the effective quotient projection is a covering map. -/
theorem lambdaModularQuotientMk_isCoveringMap :
    IsCoveringMap lambdaModularQuotientMk :=
  lambdaModularQuotientMk_isQuotientCoveringMap.isCoveringMap

/-- The quotient projection is unchanged by every integral element of
`Γ(2)`. -/
theorem lambdaModularQuotientMk_smul_of_mem_Gamma_two
    {a : SL(2, ℤ)} (ha : a ∈ GammaTwo) (z : ℍ) :
    lambdaModularQuotientMk (a • z) =
      lambdaModularQuotientMk z := by
  let aGL : GammaTwoGL :=
    ⟨Matrix.SpecialLinearGroup.mapGL ℝ a,
      ⟨a, ha, rfl⟩⟩
  let p : EffectiveGammaTwo :=
    (MulAction.toPermHom GammaTwoGL ℍ).rangeRestrict aGL
  apply Quotient.sound
  change a • z ∈ MulAction.orbit EffectiveGammaTwo z
  refine ⟨p, ?_⟩
  rfl

/-- Every effective quotient class has a representative obtained from a
point of the closed standard fundamental domain by one of six fixed
integral transformations. -/
theorem exists_fundamentalDomain_quotient_representative
    (z : ℍ) :
    ∃ r : SL(2, ZMod 2), ∃ w : ℍ,
      w ∈ ModularGroup.fd ∧
      lambdaModularQuotientMk z =
        lambdaModularQuotientMk
          ((liftModTwo r)⁻¹ • w) ∧
      canonicalLambdaPunctured w =
        r • canonicalLambdaPunctured z := by
  obtain ⟨a, ha⟩ :=
    ModularGroup.exists_smul_mem_fd z
  let r : SL(2, ZMod 2) := reduceModTwo a
  let δ : SL(2, ℤ) := (liftModTwo r)⁻¹ * a
  have hδred : reduceModTwo δ = 1 := by
    simp [δ, r, map_mul, map_inv]
  have hδ : δ ∈ GammaTwo := by
    apply CongruenceSubgroup.Gamma_mem'.mpr
    simpa only [reduceModTwo] using hδred
  refine ⟨r, a • z, ha, ?_, ?_⟩
  · calc
      lambdaModularQuotientMk z =
          lambdaModularQuotientMk (δ • z) :=
        (lambdaModularQuotientMk_smul_of_mem_Gamma_two
          hδ z).symm
      _ = lambdaModularQuotientMk
          ((liftModTwo r)⁻¹ • (a • z)) := by
        simp only [δ, mul_smul]
  · simpa only [r] using
      canonicalLambdaPunctured_smul a z

/-- Canonical lambda is invariant under the effective deck group. -/
theorem canonicalLambdaPunctured_effective_smul
    (p : EffectiveGammaTwo) (z : ℍ) :
    canonicalLambdaPunctured (p • z) =
      canonicalLambdaPunctured z := by
  obtain ⟨g, hpg⟩ :=
    EffectiveGammaTwo.exists_representative p
  obtain ⟨a, ha, hga⟩ :=
    GammaTwoGL.exists_integral_representative g
  calc
    canonicalLambdaPunctured (p • z) =
        canonicalLambdaPunctured (g • z) := by
      rw [hpg z]
    _ = canonicalLambdaPunctured (a • z) := by
      rw [hga z]
    _ = canonicalLambdaPunctured z :=
      canonicalLambdaPunctured_smul_of_mem_Gamma_two
        ha z

/-- The map induced by canonical lambda on the effective modular quotient. -/
def canonicalLambdaOnModularQuotient :
    LambdaModularQuotient → LambdaPuncturedPlane :=
  Quotient.lift canonicalLambdaPunctured (by
    intro z w hzw
    change z ∈ MulAction.orbit EffectiveGammaTwo w at hzw
    obtain ⟨p, rfl⟩ := hzw
    exact canonicalLambdaPunctured_effective_smul p w)

@[simp]
theorem canonicalLambdaOnModularQuotient_mk
    (z : ℍ) :
    canonicalLambdaOnModularQuotient
        (lambdaModularQuotientMk z) =
      canonicalLambdaPunctured z :=
  rfl

/-- The induced quotient map is continuous. -/
theorem canonicalLambdaOnModularQuotient_continuous :
    Continuous canonicalLambdaOnModularQuotient := by
  apply canonicalLambdaPunctured_continuous.quotient_lift

/-- The induced quotient map is a local homeomorphism.  This follows by
cancelling the quotient projection from the local-homeomorphism statement
for canonical lambda. -/
theorem canonicalLambdaOnModularQuotient_isLocalHomeomorph :
    IsLocalHomeomorph canonicalLambdaOnModularQuotient := by
  have hcomp :
      canonicalLambdaOnModularQuotient ∘
          lambdaModularQuotientMk =
        canonicalLambdaPunctured := by
    funext z
    exact canonicalLambdaOnModularQuotient_mk z
  have hOn :
      IsLocalHomeomorphOn
          canonicalLambdaOnModularQuotient
          (lambdaModularQuotientMk '' Set.univ) := by
    apply
      (show IsLocalHomeomorph
          (canonicalLambdaOnModularQuotient ∘
            lambdaModularQuotientMk) by
          rw [hcomp]
          exact
            canonicalLambdaPunctured_isLocalHomeomorph).isLocalHomeomorphOn.of_comp_right
    exact
      lambdaModularQuotientMk_isCoveringMap.isLocalHomeomorph.isLocalHomeomorphOn
  have hsurj : Function.Surjective
      lambdaModularQuotientMk :=
    Quotient.mk_surjective
  rw [Set.image_univ, hsurj.range_eq] at hOn
  exact
    isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr hOn

/-- Saturation of a target set under the six cross-ratio transformations. -/
def lambdaCrossRatioSaturation
    (K : Set LambdaPuncturedPlane) :
    Set LambdaPuncturedPlane :=
  ⋃ g : SL(2, ZMod 2), (g • ·) '' K

/-- A compact target set has compact six-fold cross-ratio saturation. -/
theorem isCompact_lambdaCrossRatioSaturation
    {K : Set LambdaPuncturedPlane} (hK : IsCompact K) :
    IsCompact (lambdaCrossRatioSaturation K) := by
  apply isCompact_iUnion
  intro g
  exact hK.image (lambdaCrossRatio_smul_continuous g)

/-- Above a sufficiently high horocycle, canonical lambda avoids the
cross-ratio saturation of any fixed compact target set. -/
theorem exists_height_canonicalLambda_not_mem_saturation
    {K : Set LambdaPuncturedPlane} (hK : IsCompact K) :
    ∃ Y : ℝ, ∀ w : ℍ, Y ≤ w.im →
      canonicalLambdaPunctured w ∉
        lambdaCrossRatioSaturation K := by
  have hsat :
      IsCompact (lambdaCrossRatioSaturation K) :=
    isCompact_lambdaCrossRatioSaturation hK
  have hambient :
      IsCompact
        (Subtype.val ''
          lambdaCrossRatioSaturation K) :=
    hsat.image continuous_subtype_val
  have hzero :
      (0 : ℂ) ∈
        (Subtype.val ''
          lambdaCrossRatioSaturation K)ᶜ := by
    intro hmem
    obtain ⟨x, -, hx⟩ := hmem
    exact x.property.1 hx
  have hnhds :
      (Subtype.val ''
          lambdaCrossRatioSaturation K)ᶜ ∈
        𝓝 (0 : ℂ) :=
    hambient.isClosed.isOpen_compl.mem_nhds hzero
  have hevent :
      ∀ᶠ w in UpperHalfPlane.atImInfty,
        canonicalLambda w ∈
          (Subtype.val ''
            lambdaCrossRatioSaturation K)ᶜ :=
    canonicalLambda_tendsto_atImInfty.eventually hnhds
  have hevent' :
      {w : ℍ | canonicalLambda w ∈
        (Subtype.val ''
          lambdaCrossRatioSaturation K)ᶜ} ∈
        UpperHalfPlane.atImInfty :=
    hevent
  rw [UpperHalfPlane.atImInfty_mem] at hevent'
  obtain ⟨Y, hY⟩ := hevent'
  refine ⟨Y, fun w hw hmem ↦ ?_⟩
  exact (hY w hw)
    ⟨canonicalLambdaPunctured w, hmem, rfl⟩

/-- A compact set containing one representative for every modular quotient
class whose lambda value lies in a prescribed compact target set. -/
def lambdaFundamentalCompact (Y : ℝ) : Set ℍ :=
  ⋃ r : SL(2, ZMod 2),
    ((liftModTwo r)⁻¹ • ·) ''
      ModularGroup.truncatedFundamentalDomain Y

/-- The six-copy truncated fundamental set is compact. -/
theorem isCompact_lambdaFundamentalCompact (Y : ℝ) :
    IsCompact (lambdaFundamentalCompact Y) := by
  apply isCompact_iUnion
  intro r
  have hcontinuous :
      Continuous ((liftModTwo r)⁻¹ • · : ℍ → ℍ) := by
    simpa only [sl_moeb] using
      (continuous_const_smul
        (Matrix.SpecialLinearGroup.mapGL ℝ
          (liftModTwo r)⁻¹))
  exact
    (ModularGroup.isCompact_truncatedFundamentalDomain Y).image
      hcontinuous

/-- The map induced by canonical lambda on the effective modular quotient is
proper.  The proof is the compact-fundamental-domain argument:

* saturate the target compact set by the six cross-ratio transformations;
* use `Λ(τ) → 0` to bound the height of any standard-domain representative;
* use the six fixed lifts modulo two to place all relevant quotient classes
  in a compact finite union of truncated fundamental domains. -/
theorem canonicalLambdaOnModularQuotient_isProperMap :
    IsProperMap canonicalLambdaOnModularQuotient := by
  rw [isProperMap_iff_isCompact_preimage]
  refine
    ⟨canonicalLambdaOnModularQuotient_continuous,
      fun K hK ↦ ?_⟩
  obtain ⟨Y, hY⟩ :=
    exists_height_canonicalLambda_not_mem_saturation hK
  have hC :
      IsCompact (lambdaFundamentalCompact Y) :=
    isCompact_lambdaFundamentalCompact Y
  have hsubset :
      canonicalLambdaOnModularQuotient ⁻¹' K ⊆
        lambdaModularQuotientMk ''
          lambdaFundamentalCompact Y := by
    intro x hx
    obtain ⟨z, rfl⟩ := Quotient.mk_surjective x
    have hzK : canonicalLambdaPunctured z ∈ K := by
      simpa only [Set.mem_preimage,
        canonicalLambdaOnModularQuotient_mk] using hx
    obtain ⟨r, w, hwfd, hquot, hlambda⟩ :=
      exists_fundamentalDomain_quotient_representative z
    have hwSat :
        canonicalLambdaPunctured w ∈
          lambdaCrossRatioSaturation K := by
      apply Set.mem_iUnion_of_mem r
      exact
        ⟨canonicalLambdaPunctured z, hzK,
          hlambda.symm⟩
    have hwheight : w.im ≤ Y := by
      by_contra hwy
      exact (hY w (le_of_not_ge hwy)) hwSat
    have hwcompact :
        (liftModTwo r)⁻¹ • w ∈
          lambdaFundamentalCompact Y := by
      apply Set.mem_iUnion_of_mem r
      exact
        ⟨w, ⟨hwfd, hwheight⟩, rfl⟩
    exact
      ⟨(liftModTwo r)⁻¹ • w, hwcompact,
        hquot.symm⟩
  have hcompactImage :
      IsCompact
        (lambdaModularQuotientMk ''
          lambdaFundamentalCompact Y) :=
    hC.image
      lambdaModularQuotientMk_isCoveringMap.continuous
  exact hcompactImage.of_isClosed_subset
    (hK.isClosed.preimage
      canonicalLambdaOnModularQuotient_continuous)
    hsubset

/-- Every fiber of the induced quotient map is finite. -/
theorem canonicalLambdaOnModularQuotient_finite_fiber
    (x : LambdaPuncturedPlane) :
    (canonicalLambdaOnModularQuotient ⁻¹' {x}).Finite := by
  have hcompact :=
    IsProperMap.isCompact_preimage
      canonicalLambdaOnModularQuotient_isProperMap
      (K := {x}) isCompact_singleton
  apply hcompact.finite
  apply IsDiscrete.of_openPartialHomeomorph
    canonicalLambdaOnModularQuotient
    Set.Subset.rfl
  intro e he
  obtain ⟨φ, heφ, hφ⟩ :=
    canonicalLambdaOnModularQuotient_isLocalHomeomorph e
  exact ⟨φ, heφ, hφ.symm⟩

/-- The induced map on the effective modular quotient is a finite covering
map. -/
theorem canonicalLambdaOnModularQuotient_isCoveringMap :
    IsCoveringMap canonicalLambdaOnModularQuotient := by
  rw [isCoveringMap_iff_isCoveringMapOn_univ]
  apply IsClosedMap.isCoveringMapOn_of_openPartialHomeomorph
    (IsProperMap.isClosedMap
      canonicalLambdaOnModularQuotient_isProperMap)
  · intro x hx
    exact
      canonicalLambdaOnModularQuotient_finite_fiber x
  · intro e he
    obtain ⟨φ, heφ, hφ⟩ :=
      canonicalLambdaOnModularQuotient_isLocalHomeomorph e
    exact ⟨φ, heφ, hφ.symm⟩

/-- The induced quotient map is onto.  Its image is nonempty and open by
local invertibility, and closed by properness; the punctured target is
connected. -/
theorem canonicalLambdaOnModularQuotient_surjective :
    Function.Surjective
      canonicalLambdaOnModularQuotient := by
  have hopen :
      IsOpen (Set.range
        canonicalLambdaOnModularQuotient) :=
    IsOpenMap.isOpen_range
      (IsLocalHomeomorph.isOpenMap
        canonicalLambdaOnModularQuotient_isLocalHomeomorph)
  have hclosed :
      IsClosed (Set.range
        canonicalLambdaOnModularQuotient) := by
    simpa only [Set.image_univ] using
      (IsProperMap.isClosedMap
        canonicalLambdaOnModularQuotient_isProperMap)
          Set.univ isClosed_univ
  have hnonempty :
      (Set.range
        canonicalLambdaOnModularQuotient).Nonempty :=
    Set.range_nonempty _
  have hrange :
      Set.range canonicalLambdaOnModularQuotient =
        Set.univ :=
    IsClopen.eq_univ ⟨hclosed, hopen⟩ hnonempty
  intro x
  have hx :
      x ∈ Set.range canonicalLambdaOnModularQuotient := by
    rw [hrange]
    exact Set.mem_univ x
  exact hx

/-- Canonical lambda on the upper half-plane is a covering map.

The factorization through the effective level-two quotient has two covering
factors, and the induced outer covering has finite fibers.  The finite-fiber
composition theorem therefore supplies a single evenly covered neighborhood
common to all outer sheets. -/
theorem canonicalLambdaPunctured_isCoveringMap_global :
    CanonicalLambdaIsCovering := by
  change IsCoveringMap canonicalLambdaPunctured
  have hcomp :
      canonicalLambdaOnModularQuotient ∘
          lambdaModularQuotientMk =
        canonicalLambdaPunctured := by
    funext z
    exact canonicalLambdaOnModularQuotient_mk z
  rw [← hcomp]
  exact
    HGAS.Covering.IsCoveringMap.comp_of_finite_fibers
      canonicalLambdaOnModularQuotient_isCoveringMap
      lambdaModularQuotientMk_isCoveringMap
      canonicalLambdaOnModularQuotient_finite_fiber

/-- Unconditional global path lifting for canonical lambda. -/
theorem canonicalLambdaPunctured_existsUnique_continuous_lift_global
    (ell : C(ℝ, LambdaPuncturedPlane))
    (t₀ : ℝ) (z₀ : ℍ)
    (hinitial :
      canonicalLambdaPunctured z₀ = ell t₀) :
    ∃! T : C(ℝ, ℍ),
      T t₀ = z₀ ∧
        canonicalLambdaPunctured ∘ T = ell :=
  canonicalLambdaPunctured_existsUnique_continuous_lift
    canonicalLambdaPunctured_isCoveringMap_global
    ell t₀ z₀ hinitial

/-- Unconditional differentiable lift package used by modular trajectory
reconstruction. -/
theorem canonicalLambdaPunctured_exists_lift_with_derivatives_global
    (ell : C(ℝ, LambdaPuncturedPlane))
    (hell : ∀ t, ∃ v : ℂ,
      HasDerivAt (fun s : ℝ ↦ (ell s : ℂ)) v t)
    (t₀ : ℝ) (z₀ : ℍ)
    (hinitial :
      canonicalLambdaPunctured z₀ = ell t₀) :
    ∃ T : ℝ → ℍ,
      Continuous T ∧
      T t₀ = z₀ ∧
      (∀ t,
        canonicalLambdaPunctured (T t) = ell t) ∧
      ∀ t, ∃ v : ℂ,
        HasDerivAt (fun s : ℝ ↦ (T s : ℂ)) v t :=
  canonicalLambdaPunctured_exists_lift_with_derivatives
    canonicalLambdaPunctured_isCoveringMap_global
    ell hell t₀ z₀ hinitial

end

end HGAS.Modular
