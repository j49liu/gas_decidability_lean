import HGAS.Modular.JacobiThetaReciprocalLocalHomeomorph
import HGAS.Topology.ComplexProjectiveGram
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.Metrizable.Basic

/-!
# Projective Gram compactification of the reciprocal theta chart

The affine ratios `θⱼ/θ₁` diverge when `θ₁` approaches zero, while the
underlying projective theta vector remains perfectly regular.  To make
that compactness mechanism topologically explicit, we encode a
nonzero four-vector by its normalized Hermitian Gram matrix

```
             vᵢ conj(vⱼ) / ∑ₖ |vₖ|².
```

This matrix is invariant under every nonzero common scalar, so the
level-two theta automorphy factor disappears.  The resulting map
extends continuously over the *whole* fixed torus family.  On the
reciprocal chart it agrees with the Gram matrix of
`(1, θ₂/θ₁, θ₃/θ₁, θ₄/θ₁)`.

The extension is the compactness device needed to prove properness of
the reciprocal torus parametrization: a compact set in the affine
target has compact Gram image bounded away from the projective
hyperplane `θ₁=0`, so its preimage is closed inside a compact torus
slab.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I
open Complex Real Set Topology
open scoped BigOperators ComplexConjugate

noncomputable section

local instance projectiveGramLevelTwoPeriodPositive :
    Fact (0 < (2 : ℝ)) :=
  ⟨by norm_num⟩

/-- Hermitian Gram matrices for four complex coordinates. -/
abbrev JacobiThetaProjectiveGram :=
  Fin 4 → Fin 4 → ℂ

/-- Projective Gram data together with the varying modulus. -/
abbrev JacobiThetaProjectiveGramTotal :=
  ℍ × JacobiThetaProjectiveGram

/-! ## The extended Gram map before quotienting -/

/-- Theta vector in fixed real elliptic coordinates. -/
def fixedLevelTwoThetaVector
    (p : ℍ × (ℝ × ℝ)) : Fin 4 → ℂ :=
  jacobiThetaVector
    (fixedLevelTwoThetaParameter p)
    (p.1 : ℂ)

theorem fixedLevelTwoThetaVector_ne_zero
    (p : ℍ × (ℝ × ℝ)) :
    fixedLevelTwoThetaVector p ≠ 0 :=
  jacobiThetaVector_ne_zero
    (fixedLevelTwoThetaParameter p) p.1

theorem continuous_fixedLevelTwoThetaVector_component
    (j : Fin 4) :
    Continuous
      (fun p : ℍ × (ℝ × ℝ) =>
        fixedLevelTwoThetaVector p j) := by
  have hpair :
      Continuous
        (fun p : ℍ × (ℝ × ℝ) =>
          (fixedLevelTwoThetaParameter p, p.1)) :=
    continuous_fixedLevelTwoThetaParameter.prodMk
      continuous_fst
  simpa only [fixedLevelTwoThetaVector,
    Function.comp_apply] using
    (continuous_jacobiThetaVectorComponent_upperHalfPlane j).comp
      hpair

/-- The scalar-invariant projective theta data in real coordinates. -/
def fixedLevelTwoProjectiveGramRealMap
    (p : ℍ × (ℝ × ℝ)) :
    JacobiThetaProjectiveGramTotal :=
  (p.1,
    HGAS.Topology.complexProjectiveGram
      (fixedLevelTwoThetaVector p))

theorem continuous_fixedLevelTwoProjectiveGramRealMap :
    Continuous fixedLevelTwoProjectiveGramRealMap := by
  exact
    continuous_fst.prodMk
      (HGAS.Topology.continuous_complexProjectiveGram
        fixedLevelTwoThetaVector
        continuous_fixedLevelTwoThetaVector_component
        fixedLevelTwoThetaVector_ne_zero)

/-- The extended Gram map is exactly invariant under fixed doubled
lattice translation. -/
theorem fixedLevelTwoProjectiveGramRealMap_translate
    (p : ℍ × (ℝ × ℝ)) (m n : ℤ) :
    fixedLevelTwoProjectiveGramRealMap
        (HGAS.Topology.fixedLevelTwoTranslate m n p) =
      fixedLevelTwoProjectiveGramRealMap p := by
  have hparameter :=
    fixedLevelTwoThetaParameter_translate p m n
  have htheta :=
    jacobiThetaVector_add_levelTwo_lattice
      (fixedLevelTwoThetaParameter p)
      (p.1 : ℂ) m n
  have hmultiplier :
      levelTwoThetaMultiplier n
          (fixedLevelTwoThetaParameter p) (p.1 : ℂ) ≠ 0 :=
    levelTwoThetaMultiplier_ne_zero n
      (fixedLevelTwoThetaParameter p) (p.1 : ℂ)
  apply Prod.ext
  · rfl
  · change
      HGAS.Topology.complexProjectiveGram
          (jacobiThetaVector
            (fixedLevelTwoThetaParameter
              (HGAS.Topology.fixedLevelTwoTranslate m n p))
            (p.1 : ℂ)) =
        HGAS.Topology.complexProjectiveGram
          (jacobiThetaVector
            (fixedLevelTwoThetaParameter p)
            (p.1 : ℂ))
    rw [hparameter, htheta]
    exact
      HGAS.Topology.complexProjectiveGram_smul
        (levelTwoThetaMultiplier n
          (fixedLevelTwoThetaParameter p) (p.1 : ℂ))
        (jacobiThetaVector
          (fixedLevelTwoThetaParameter p) (p.1 : ℂ))
        hmultiplier

/-- The real Gram map is constant on fixed-torus quotient fibers. -/
theorem fixedLevelTwoProjectiveGramRealMap_factorsThrough :
    Function.FactorsThrough
      fixedLevelTwoProjectiveGramRealMap
      fixedLevelTwoTorusQuotient := by
  intro p q h
  obtain ⟨m, n, hp⟩ :=
    exists_fixedLevelTwoTranslate_of_quotient_eq p q h
  subst p
  exact fixedLevelTwoProjectiveGramRealMap_translate q m n

def fixedLevelTwoTorusQuotientContinuous :
    C(ℍ × (ℝ × ℝ), FixedLevelTwoTorusFamily) :=
  ⟨fixedLevelTwoTorusQuotient,
    continuous_fixedLevelTwoTorusQuotient⟩

def fixedLevelTwoProjectiveGramRealContinuous :
    C(ℍ × (ℝ × ℝ),
      JacobiThetaProjectiveGramTotal) :=
  ⟨fixedLevelTwoProjectiveGramRealMap,
    continuous_fixedLevelTwoProjectiveGramRealMap⟩

theorem fixedLevelTwoTorusQuotientContinuous_isQuotientMap :
    Topology.IsQuotientMap
      (fixedLevelTwoTorusQuotientContinuous :
        ℍ × (ℝ × ℝ) →
          FixedLevelTwoTorusFamily) := by
  simpa only [fixedLevelTwoTorusQuotientContinuous] using
    fixedLevelTwoTorusQuotient_isOpenQuotientMap.isQuotientMap

theorem
    fixedLevelTwoProjectiveGramContinuous_factorsThrough :
    Function.FactorsThrough
      (fixedLevelTwoProjectiveGramRealContinuous :
        ℍ × (ℝ × ℝ) →
          JacobiThetaProjectiveGramTotal)
      (fixedLevelTwoTorusQuotientContinuous :
        ℍ × (ℝ × ℝ) →
          FixedLevelTwoTorusFamily) := by
  simpa only [fixedLevelTwoProjectiveGramRealContinuous,
    fixedLevelTwoTorusQuotientContinuous] using
    fixedLevelTwoProjectiveGramRealMap_factorsThrough

/-- Continuous projective theta extension over the whole fixed torus
family. -/
noncomputable def fixedLevelTwoProjectiveGramTorusMap :
    C(FixedLevelTwoTorusFamily,
      JacobiThetaProjectiveGramTotal) :=
  fixedLevelTwoTorusQuotientContinuous_isQuotientMap.lift
    fixedLevelTwoProjectiveGramRealContinuous
    fixedLevelTwoProjectiveGramContinuous_factorsThrough

theorem fixedLevelTwoProjectiveGramTorusMap_comp_quotient :
    fixedLevelTwoProjectiveGramTorusMap.comp
        fixedLevelTwoTorusQuotientContinuous =
      fixedLevelTwoProjectiveGramRealContinuous := by
  exact
    Topology.IsQuotientMap.lift_comp
      fixedLevelTwoTorusQuotientContinuous_isQuotientMap
      fixedLevelTwoProjectiveGramRealContinuous
      fixedLevelTwoProjectiveGramContinuous_factorsThrough

@[simp]
theorem fixedLevelTwoProjectiveGramTorusMap_quotient_apply
    (p : ℍ × (ℝ × ℝ)) :
    fixedLevelTwoProjectiveGramTorusMap
        (fixedLevelTwoTorusQuotient p) =
      fixedLevelTwoProjectiveGramRealMap p := by
  exact
    congrArg
      (fun f :
        C(ℍ × (ℝ × ℝ),
          JacobiThetaProjectiveGramTotal) => f p)
      fixedLevelTwoProjectiveGramTorusMap_comp_quotient

/-! ## The reciprocal chart inside Gram space -/

/-- Gram embedding of the affine reciprocal residual target, using
the representative whose zeroth coordinate is one. -/
def jacobiThetaReciprocalGramEmbedding
    (p : JacobiThetaReciprocalTotal) :
    JacobiThetaProjectiveGramTotal :=
  (p.modulus,
    HGAS.Topology.complexProjectiveGram
      (jacobiThetaReciprocalRepresentative p.coordinates))

theorem continuous_jacobiThetaReciprocalRepresentative_component
    (j : Fin 4) :
    Continuous
      (fun p : JacobiThetaReciprocalTotal =>
        jacobiThetaReciprocalRepresentative
          p.coordinates j) := by
  fin_cases j
  · exact continuous_const
  · exact
      continuous_jacobiThetaReciprocalCoordinate_fromTotal 0
  · exact
      continuous_jacobiThetaReciprocalCoordinate_fromTotal 1
  · exact
      continuous_jacobiThetaReciprocalCoordinate_fromTotal 2

theorem continuous_jacobiThetaReciprocalGramEmbedding :
    Continuous jacobiThetaReciprocalGramEmbedding := by
  exact
    (continuous_fst.comp
        continuous_jacobiThetaReciprocalTotal_toBase).prodMk
      (HGAS.Topology.continuous_complexProjectiveGram
        (fun p : JacobiThetaReciprocalTotal =>
          jacobiThetaReciprocalRepresentative p.coordinates)
        continuous_jacobiThetaReciprocalRepresentative_component
        (fun p =>
          jacobiThetaReciprocalRepresentative_ne_zero
            p.coordinates))

theorem jacobiThetaReciprocalGramEmbedding_injective :
    Function.Injective
      jacobiThetaReciprocalGramEmbedding := by
  intro p q h
  have hmodulus : p.modulus = q.modulus :=
    congrArg Prod.fst h
  have hgram :
      HGAS.Topology.complexProjectiveGram
          (jacobiThetaReciprocalRepresentative
            p.coordinates) =
        HGAS.Topology.complexProjectiveGram
          (jacobiThetaReciprocalRepresentative
            q.coordinates) :=
    congrArg Prod.snd h
  have hrepresentative :
      jacobiThetaReciprocalRepresentative p.coordinates =
        jacobiThetaReciprocalRepresentative q.coordinates :=
    HGAS.Topology.complexProjectiveGram_affine_injective
      0 rfl rfl hgram
  apply JacobiThetaReciprocalTotal.ext hmodulus
  funext k
  simpa only
    [jacobiThetaReciprocalRepresentative_succ] using
    congrFun hrepresentative k.succ

/-- Every point of the affine reciprocal chart stays away from the
projective hyperplane whose zeroth diagonal Gram entry is zero. -/
theorem jacobiThetaReciprocalGramEmbedding_zero_zero_ne_zero
    (p : JacobiThetaReciprocalTotal) :
    (jacobiThetaReciprocalGramEmbedding p).2 0 0 ≠ 0 := by
  exact
    HGAS.Topology.complexProjectiveGram_apply_self_ne_zero
      (jacobiThetaReciprocalRepresentative p.coordinates)
      0 one_ne_zero

/-! ## Compatibility with the theta quotient -/

/-- On the reciprocal locus, the theta vector is the first theta
coordinate times its affine representative. -/
theorem fixedLevelTwoThetaVector_eq_smul_reciprocalRepresentative
    (p : FixedLevelTwoReciprocalRealDomain) :
    fixedLevelTwoThetaVector p.1 =
      jacobiTheta1
          (fixedLevelTwoThetaParameter p.1)
          (p.1.1 : ℂ) •
        jacobiThetaReciprocalRepresentative
          (jacobiThetaReciprocalCoordinates
            p.1.1
            (fixedLevelTwoThetaParameter p.1)) := by
  have h1 :
      jacobiTheta1
          (fixedLevelTwoThetaParameter p.1)
          (p.1.1 : ℂ) ≠ 0 :=
    (mem_preimage_fixedLevelTwoReciprocalTorusSet_iff
      p.1).mp p.2
  funext j
  fin_cases j
  · simp [fixedLevelTwoThetaVector,
      jacobiThetaVector,
      jacobiThetaReciprocalRepresentative]
  · simp only [fixedLevelTwoThetaVector,
      jacobiThetaReciprocalRepresentative,
      jacobiThetaReciprocalCoordinates_zero,
      Pi.smul_apply, smul_eq_mul]
    change
      jacobiTheta2
          (fixedLevelTwoThetaParameter p.1)
          (p.1.1 : ℂ) =
        jacobiTheta1
            (fixedLevelTwoThetaParameter p.1)
            (p.1.1 : ℂ) *
          (jacobiTheta2
              (fixedLevelTwoThetaParameter p.1)
              (p.1.1 : ℂ) /
            jacobiTheta1
              (fixedLevelTwoThetaParameter p.1)
              (p.1.1 : ℂ))
    field_simp
  · simp only [fixedLevelTwoThetaVector,
      jacobiThetaReciprocalRepresentative,
      jacobiThetaReciprocalCoordinates_one,
      Pi.smul_apply, smul_eq_mul]
    change
      jacobiTheta3
          (fixedLevelTwoThetaParameter p.1)
          (p.1.1 : ℂ) =
        jacobiTheta1
            (fixedLevelTwoThetaParameter p.1)
            (p.1.1 : ℂ) *
          (jacobiTheta3
              (fixedLevelTwoThetaParameter p.1)
              (p.1.1 : ℂ) /
            jacobiTheta1
              (fixedLevelTwoThetaParameter p.1)
              (p.1.1 : ℂ))
    field_simp
  · simp only [fixedLevelTwoThetaVector,
      jacobiThetaReciprocalRepresentative,
      jacobiThetaReciprocalCoordinates_two,
      Pi.smul_apply, smul_eq_mul]
    change
      jacobiTheta4
          (fixedLevelTwoThetaParameter p.1)
          (p.1.1 : ℂ) =
        jacobiTheta1
            (fixedLevelTwoThetaParameter p.1)
            (p.1.1 : ℂ) *
          (jacobiTheta4
              (fixedLevelTwoThetaParameter p.1)
              (p.1.1 : ℂ) /
            jacobiTheta1
              (fixedLevelTwoThetaParameter p.1)
              (p.1.1 : ℂ))
    field_simp

/-- The extended real-coordinate Gram map agrees with the affine Gram
embedding of the reciprocal theta map. -/
theorem fixedLevelTwoProjectiveGramRealMap_eq_reciprocalEmbedding
    (p : FixedLevelTwoReciprocalRealDomain) :
    fixedLevelTwoProjectiveGramRealMap p.1 =
      jacobiThetaReciprocalGramEmbedding
        (fixedLevelTwoReciprocalRealMap p) := by
  apply Prod.ext
  · rfl
  · change
      HGAS.Topology.complexProjectiveGram
          (fixedLevelTwoThetaVector p.1) =
        HGAS.Topology.complexProjectiveGram
          (jacobiThetaReciprocalRepresentative
            (jacobiThetaReciprocalCoordinates
              p.1.1
              (fixedLevelTwoThetaParameter p.1)))
    rw [fixedLevelTwoThetaVector_eq_smul_reciprocalRepresentative]
    exact
      HGAS.Topology.complexProjectiveGram_smul
        (jacobiTheta1
          (fixedLevelTwoThetaParameter p.1)
          (p.1.1 : ℂ))
        (jacobiThetaReciprocalRepresentative
          (jacobiThetaReciprocalCoordinates
            p.1.1
            (fixedLevelTwoThetaParameter p.1)))
        ((mem_preimage_fixedLevelTwoReciprocalTorusSet_iff
          p.1).mp p.2)

/-- Compatibility of the full torus Gram extension with the descended
reciprocal theta map. -/
theorem fixedLevelTwoProjectiveGramTorusMap_eq_reciprocalEmbedding
    (p : FixedLevelTwoReciprocalTorusDomain) :
    fixedLevelTwoProjectiveGramTorusMap p.1 =
      jacobiThetaReciprocalGramEmbedding
        (fixedLevelTwoReciprocalTorusMap p) := by
  obtain ⟨q, hq⟩ :=
    fixedLevelTwoReciprocalRestrictedQuotient_isOpenQuotientMap.surjective
      p
  subst p
  change
    fixedLevelTwoProjectiveGramTorusMap
        (fixedLevelTwoTorusQuotient q.1) =
      jacobiThetaReciprocalGramEmbedding
        (fixedLevelTwoReciprocalTorusMap
          (fixedLevelTwoReciprocalRestrictedQuotient q))
  rw [fixedLevelTwoProjectiveGramTorusMap_quotient_apply,
    fixedLevelTwoReciprocalTorusMap_quotient_apply]
  exact fixedLevelTwoProjectiveGramRealMap_eq_reciprocalEmbedding q

/-! ## Detecting the reciprocal divisor by one Gram entry -/

theorem mem_fixedLevelTwoReciprocalRealSet_iff_gram_zero_zero_ne_zero
    (p : ℍ × (ℝ × ℝ)) :
    p ∈ fixedLevelTwoReciprocalRealSet ↔
      (fixedLevelTwoProjectiveGramRealMap p).2 0 0 ≠ 0 := by
  constructor
  · intro hp
    exact
      HGAS.Topology.complexProjectiveGram_apply_self_ne_zero
        (fixedLevelTwoThetaVector p) 0 hp
  · rintro hgram h1
    apply hgram
    unfold fixedLevelTwoProjectiveGramRealMap
    unfold HGAS.Topology.complexProjectiveGram
    change
      jacobiTheta1
            (fixedLevelTwoThetaParameter p)
            (p.1 : ℂ) *
          conj
            (jacobiTheta1
              (fixedLevelTwoThetaParameter p)
              (p.1 : ℂ)) /
        (HGAS.Topology.complexProjectiveGramNormSq
          (fixedLevelTwoThetaVector p) : ℂ) =
        0
    rw [h1, zero_mul, zero_div]

theorem mem_fixedLevelTwoReciprocalTorusSet_iff_gram_zero_zero_ne_zero
    (p : FixedLevelTwoTorusFamily) :
    p ∈ fixedLevelTwoReciprocalTorusSet ↔
      (fixedLevelTwoProjectiveGramTorusMap p).2 0 0 ≠ 0 := by
  obtain ⟨q, hq⟩ :=
    fixedLevelTwoTorusQuotient_isOpenQuotientMap.surjective p
  subst p
  rw [mem_preimage_fixedLevelTwoReciprocalTorusSet_iff,
    fixedLevelTwoProjectiveGramTorusMap_quotient_apply]
  exact
    mem_fixedLevelTwoReciprocalRealSet_iff_gram_zero_zero_ne_zero q

/-! ## Properness of the reciprocal torus map -/

/-- The residual target embeds in its ordinary finite-dimensional
ambient coordinate space. -/
theorem jacobiThetaReciprocalTotal_toBase_isEmbedding :
    Topology.IsEmbedding
      JacobiThetaReciprocalTotal.toBase := by
  have hinjective :
      Function.Injective
        JacobiThetaReciprocalTotal.toBase := by
    intro p q h
    apply JacobiThetaReciprocalTotal.ext
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  exact hinjective.isEmbedding_induced

noncomputable instance
    jacobiThetaReciprocalTotalPseudoMetrizableSpace :
    TopologicalSpace.PseudoMetrizableSpace
      JacobiThetaReciprocalTotal :=
  jacobiThetaReciprocalTotal_toBase_isEmbedding.isInducing
    |>.pseudoMetrizableSpace

instance jacobiThetaReciprocalTotalT2Space :
    T2Space JacobiThetaReciprocalTotal :=
  jacobiThetaReciprocalTotal_toBase_isEmbedding.t2Space

theorem fixedLevelTwoProjectiveGramTorusMap_modulus
    (p : FixedLevelTwoTorusFamily) :
    (fixedLevelTwoProjectiveGramTorusMap p).1 =
      p.1 := by
  obtain ⟨q, hq⟩ :=
    fixedLevelTwoTorusQuotient_isOpenQuotientMap.surjective p
  subst p
  rw [fixedLevelTwoProjectiveGramTorusMap_quotient_apply]
  rfl

/-- Compact subsets of the affine residual target have compact
preimage in the reciprocal torus domain.  The projective Gram extension
is the compactification that prevents escape through `θ₁=0`. -/
theorem
    isCompact_preimage_fixedLevelTwoReciprocalTorusMap
    {K : Set JacobiThetaReciprocalTotal}
    (hK : IsCompact K) :
    IsCompact
      (fixedLevelTwoReciprocalTorusMap ⁻¹' K) := by
  let L : Set JacobiThetaProjectiveGramTotal :=
    jacobiThetaReciprocalGramEmbedding '' K
  have hL : IsCompact L :=
    hK.image
      continuous_jacobiThetaReciprocalGramEmbedding
  let A : Set FixedLevelTwoTorusFamily :=
    fixedLevelTwoProjectiveGramTorusMap ⁻¹' L
  have hAclosed : IsClosed A :=
    hL.isClosed.preimage
      fixedLevelTwoProjectiveGramTorusMap.continuous
  let C : Set ℍ :=
    Prod.fst '' L
  have hC : IsCompact C :=
    hL.image continuous_fst
  have hAsubset :
      A ⊆ C ×ˢ
        (Set.univ : Set FixedLevelTwoTorus) := by
    intro p hp
    refine ⟨?_, Set.mem_univ p.2⟩
    exact
      ⟨fixedLevelTwoProjectiveGramTorusMap p,
        hp,
        fixedLevelTwoProjectiveGramTorusMap_modulus p⟩
  have hA : IsCompact A :=
    (hC.prod (isCompact_univ :
      IsCompact (Set.univ :
        Set FixedLevelTwoTorus))).of_isClosed_subset
      hAclosed hAsubset
  have hAinReciprocal :
      A ⊆ fixedLevelTwoReciprocalTorusSet := by
    intro p hp
    apply
      (mem_fixedLevelTwoReciprocalTorusSet_iff_gram_zero_zero_ne_zero
        p).2
    obtain ⟨y, hyK, hy⟩ := hp
    rw [← hy]
    exact
      jacobiThetaReciprocalGramEmbedding_zero_zero_ne_zero y
  have himage :
      ((↑) :
          FixedLevelTwoReciprocalTorusDomain →
            FixedLevelTwoTorusFamily) ''
          (fixedLevelTwoReciprocalTorusMap ⁻¹' K) =
        A := by
    ext p
    constructor
    · rintro ⟨q, hqK, rfl⟩
      exact
        ⟨fixedLevelTwoReciprocalTorusMap q,
          hqK,
          (fixedLevelTwoProjectiveGramTorusMap_eq_reciprocalEmbedding
            q).symm⟩
    · intro hpA
      let q : FixedLevelTwoReciprocalTorusDomain :=
        ⟨p, hAinReciprocal hpA⟩
      obtain ⟨y, hyK, hy⟩ := hpA
      have hfy :
          fixedLevelTwoReciprocalTorusMap q = y := by
        apply
          jacobiThetaReciprocalGramEmbedding_injective
        calc
          jacobiThetaReciprocalGramEmbedding
                (fixedLevelTwoReciprocalTorusMap q) =
              fixedLevelTwoProjectiveGramTorusMap p :=
            (fixedLevelTwoProjectiveGramTorusMap_eq_reciprocalEmbedding
              q).symm
          _ =
              jacobiThetaReciprocalGramEmbedding y :=
            hy.symm
      have hqK :
          fixedLevelTwoReciprocalTorusMap q ∈ K := by
        rw [hfy]
        exact hyK
      exact
        ⟨q, hqK, rfl⟩
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff,
    himage]
  exact hA

/-- The descended reciprocal theta parametrization is proper. -/
theorem fixedLevelTwoReciprocalTorusMap_isProperMap :
    IsProperMap fixedLevelTwoReciprocalTorusMap := by
  rw [isProperMap_iff_isCompact_preimage]
  exact
    ⟨fixedLevelTwoReciprocalTorusMap.continuous,
      fun _ hK =>
        isCompact_preimage_fixedLevelTwoReciprocalTorusMap hK⟩

end

end HGAS.Modular
