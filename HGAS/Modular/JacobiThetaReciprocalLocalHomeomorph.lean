import HGAS.Modular.JacobiThetaReciprocalRegularCoordinate
import HGAS.Modular.JacobiThetaReciprocalTorusQuotient
import HGAS.Topology.LocalHomeomorphConstructions
import HGAS.Topology.PointwiseLocalHomeomorphFactor
import Mathlib.Topology.Covering.AddCircle

/-!
# Local homeomorphism of the reciprocal theta parametrization

This file joins the analytic and algebraic halves of the local chart
argument.

At a reciprocal point, choose one normalized theta coordinate with
nonzero vertical derivative.  Joint `C¹` regularity and the inverse
function theorem make

```
                   (τ,z) ↦ (τ,rₖ(τ,z))
```

locally invertible.  The Wronskian formula simultaneously says that
the other two reciprocal coordinates are nonzero.  The residual
quadrics therefore fix their signs locally, making projection from the
full residual family to `(τ,rₖ)` locally injective.  The pointwise
factor criterion then proves that the complete reciprocal theta map is
a local homeomorphism.

Finally we pass through the fixed doubled-period torus quotient.  Its
quotient map is a local homeomorphism because `ℝ → AddCircle 2` is a
covering map.  Cancellation of this quotient chart proves that the
descended torus parametrization is locally homeomorphic as well.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I
open Complex Real Set Topology

noncomputable section

/-! ## Open ambient embeddings -/

/-- The reciprocal analytic domain embedded in the ambient complex
parameter space, with coordinate order `(τ,z)`. -/
def jacobiThetaReciprocalDomainAmbient
    (p : JacobiThetaReciprocalDomain) : ℂ × ℂ :=
  ((p.modulus : ℂ), p.parameter)

/-- The structural forgetful map to `ℍ × ℂ` is an open embedding. -/
theorem jacobiThetaReciprocalDomain_toBase_isOpenEmbedding :
    Topology.IsOpenEmbedding
      JacobiThetaReciprocalDomain.toBase := by
  have hinjective :
      Function.Injective
        JacobiThetaReciprocalDomain.toBase := by
    intro p q h
    apply JacobiThetaReciprocalDomain.ext
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  have hembedding :
      Topology.IsEmbedding
        JacobiThetaReciprocalDomain.toBase :=
    hinjective.isEmbedding_induced
  let good : Set (ℍ × ℂ) :=
    {p |
      jacobiTheta1 p.2 (p.1 : ℂ) ≠ 0}
  have hgoodOpen : IsOpen good := by
    have hpair :
        Continuous
          (fun p : ℍ × ℂ => (p.2, p.1)) :=
      continuous_snd.prodMk continuous_fst
    have htheta :
        Continuous
          (fun p : ℍ × ℂ =>
            jacobiTheta1 p.2 (p.1 : ℂ)) := by
      simpa only [Function.comp_apply] using
        continuous_jacobiTheta1_upperHalfPlane.comp hpair
    exact
      isClosed_singleton.isOpen_compl.preimage htheta
  have hrange :
      Set.range
          JacobiThetaReciprocalDomain.toBase =
        good := by
    ext p
    constructor
    · rintro ⟨q, rfl⟩
      exact q.thetaOne_ne_zero
    · intro hp
      exact
        ⟨⟨p.1, p.2, hp⟩, rfl⟩
  exact
    ⟨hembedding, hrange ▸ hgoodOpen⟩

/-- The reciprocal analytic domain is an open subspace of `ℂ²`. -/
theorem jacobiThetaReciprocalDomainAmbient_isOpenEmbedding :
    Topology.IsOpenEmbedding
      jacobiThetaReciprocalDomainAmbient := by
  have hproduct :
      Topology.IsOpenEmbedding
        (Prod.map
          ((↑) : ℍ → ℂ)
          (id : ℂ → ℂ)) :=
    UpperHalfPlane.isOpenEmbedding_coe.prodMap
      Topology.IsOpenEmbedding.id
  have hcomp :=
    hproduct.comp
      jacobiThetaReciprocalDomain_toBase_isOpenEmbedding
  simpa only [jacobiThetaReciprocalDomainAmbient,
    JacobiThetaReciprocalDomain.toBase,
    Prod.map_apply, id_eq, Function.comp_apply] using hcomp

/-- Embed the selected-coordinate target `ℍ × ℂ` into ambient `ℂ²`. -/
def upperHalfPlaneComplexAmbient
    (p : ℍ × ℂ) : ℂ × ℂ :=
  ((p.1 : ℂ), p.2)

theorem upperHalfPlaneComplexAmbient_isOpenEmbedding :
    Topology.IsOpenEmbedding upperHalfPlaneComplexAmbient := by
  simpa only [upperHalfPlaneComplexAmbient,
    Prod.map_apply, id_eq] using
    UpperHalfPlane.isOpenEmbedding_coe.prodMap
      Topology.IsOpenEmbedding.id

/-! ## The analytic reciprocal map -/

/-- The selected reciprocal projection of the analytic theta map. -/
def jacobiThetaReciprocalSelectedMap
    (k : Fin 3)
    (p : JacobiThetaReciprocalDomain) :
    ℍ × ℂ :=
  jacobiThetaReciprocalProjection k
    (jacobiThetaReciprocalTotalMap p)

theorem continuous_jacobiThetaReciprocalSelectedMap
    (k : Fin 3) :
    Continuous
      (jacobiThetaReciprocalSelectedMap k) :=
  (continuous_jacobiThetaReciprocalProjection k).comp
    continuous_jacobiThetaReciprocalTotalMap

theorem
    upperHalfPlaneComplexAmbient_comp_selectedMap
    (k : Fin 3) :
    upperHalfPlaneComplexAmbient ∘
        jacobiThetaReciprocalSelectedMap k =
      (fun q : ℂ × ℂ =>
          (q.1,
            jacobiThetaReciprocalCoordinateAmbient k q)) ∘
        jacobiThetaReciprocalDomainAmbient := by
  rfl

/-- At one analytic reciprocal point, a suitable selected-coordinate
map is locally homeomorphic and its projection from the residual family
is locally injective. -/
theorem
    exists_jacobiThetaReciprocalSelectedMap_localHomeomorph
    (p : JacobiThetaReciprocalDomain) :
    ∃ (k : Fin 3)
        (e : OpenPartialHomeomorph
          JacobiThetaReciprocalDomain (ℍ × ℂ)),
      JacobiThetaReciprocalComplementNonzero k
          (jacobiThetaReciprocalTotalMap p) ∧
        p ∈ e.source ∧
          (e : JacobiThetaReciprocalDomain → ℍ × ℂ) =
            jacobiThetaReciprocalSelectedMap k := by
  obtain ⟨k, eAmbient, hcomplement,
      hpAmbient, heAmbient⟩ :=
    exists_jacobiThetaReciprocalRegularCoordinateAmbient_localHomeomorph
      p.modulus p.parameter p.thetaOne_ne_zero
  obtain ⟨eDomain, hpDomain, heDomain⟩ :=
    jacobiThetaReciprocalDomainAmbient_isOpenEmbedding.isLocalHomeomorph
      p
  let eComposite :
      OpenPartialHomeomorph
        JacobiThetaReciprocalDomain (ℂ × ℂ) :=
    eDomain.trans eAmbient
  have hpComposite : p ∈ eComposite.source := by
    refine ⟨hpDomain, ?_⟩
    change eDomain p ∈ eAmbient.source
    rw [← congrFun heDomain p]
    exact hpAmbient
  have heComposite :
      (eComposite :
          JacobiThetaReciprocalDomain → ℂ × ℂ) =
        upperHalfPlaneComplexAmbient ∘
          jacobiThetaReciprocalSelectedMap k := by
    funext q
    change eAmbient (eDomain q) =
      upperHalfPlaneComplexAmbient
        (jacobiThetaReciprocalSelectedMap k q)
    rw [congrFun heAmbient (eDomain q),
      ← congrFun heDomain q]
    rfl
  have hcompositeAt :
      IsLocalHomeomorphOn
        (upperHalfPlaneComplexAmbient ∘
          jacobiThetaReciprocalSelectedMap k)
        ({p} : Set JacobiThetaReciprocalDomain) := by
    intro q hq
    have hqp : q = p := by
      simpa only [Set.mem_singleton_iff] using hq
    subst q
    exact
      ⟨eComposite, hpComposite, heComposite.symm⟩
  have htarget :
      IsLocalHomeomorph
        upperHalfPlaneComplexAmbient :=
    upperHalfPlaneComplexAmbient_isOpenEmbedding.isLocalHomeomorph
  have hselectedAt :
      IsLocalHomeomorphOn
        (jacobiThetaReciprocalSelectedMap k)
        ({p} : Set JacobiThetaReciprocalDomain) :=
    hcompositeAt.of_comp_left
      htarget.isLocalHomeomorphOn
      (fun _ _ =>
        (continuous_jacobiThetaReciprocalSelectedMap k).continuousAt)
  obtain ⟨e, hpe, he⟩ :=
    hselectedAt p (Set.mem_singleton p)
  exact
    ⟨k, e, hcomplement, hpe, he.symm⟩

/-- The complete analytic reciprocal theta parametrization is a local
homeomorphism. -/
theorem
    jacobiThetaReciprocalTotalMap_isLocalHomeomorph :
    IsLocalHomeomorph
      jacobiThetaReciprocalTotalMap := by
  intro p
  obtain ⟨k, eSelected, hcomplement,
      hpSelected, heSelected⟩ :=
    exists_jacobiThetaReciprocalSelectedMap_localHomeomorph p
  obtain ⟨U, hUopen, hmapU, hUinj⟩ :=
    exists_open_jacobiThetaReciprocalProjection_injOn
      (jacobiThetaReciprocalTotalMap p) k hcomplement
  obtain ⟨e, hpe, he⟩ :=
    HGAS.Topology.exists_localHomeomorph_of_comp_of_injOn
      (f := jacobiThetaReciprocalTotalMap)
      (g := jacobiThetaReciprocalProjection k)
      p
      continuous_jacobiThetaReciprocalTotalMap
      (continuous_jacobiThetaReciprocalProjection k)
      ⟨eSelected, hpSelected, by
        simpa only [jacobiThetaReciprocalSelectedMap,
          Function.comp_apply] using heSelected⟩
      ⟨U, hUopen, hmapU, hUinj⟩
  exact ⟨e, hpe, he.symm⟩

/-! ## Passage to the fixed level-two torus -/

/-- Quotient the two fixed real elliptic coordinates modulo two. -/
def fixedLevelTwoPlaneQuotient
    (p : ℝ × ℝ) : FixedLevelTwoTorus :=
  ((p.1 : LevelTwoAddCircle),
    (p.2 : LevelTwoAddCircle))

/-- The fixed plane-to-torus quotient is locally homeomorphic. -/
theorem fixedLevelTwoPlaneQuotient_isLocalHomeomorph :
    IsLocalHomeomorph fixedLevelTwoPlaneQuotient := by
  have hcircle :
      IsLocalHomeomorph
        (fun x : ℝ =>
          (x : LevelTwoAddCircle)) :=
    AddCircle.isLocalHomeomorph_coe (2 : ℝ)
  simpa only [fixedLevelTwoPlaneQuotient,
    Prod.map_apply] using
    HGAS.Topology.IsLocalHomeomorph.prodMap
      hcircle hcircle

/-- The full fixed family quotient is locally homeomorphic. -/
theorem fixedLevelTwoTorusQuotient_isLocalHomeomorph :
    IsLocalHomeomorph fixedLevelTwoTorusQuotient := by
  have hidentity :
      IsLocalHomeomorph (id : ℍ → ℍ) :=
    Homeomorph.isLocalHomeomorph
      (Homeomorph.refl ℍ)
  have hproduct :=
    HGAS.Topology.IsLocalHomeomorph.prodMap
      hidentity
      fixedLevelTwoPlaneQuotient_isLocalHomeomorph
  simpa only [fixedLevelTwoTorusQuotient,
    fixedLevelTwoPlaneQuotient,
    Prod.map_apply, id_eq] using hproduct

/-- Restricting the fixed quotient over the reciprocal torus locus
preserves local homeomorphism. -/
theorem
    fixedLevelTwoReciprocalRestrictedQuotient_isLocalHomeomorph :
    IsLocalHomeomorph
      fixedLevelTwoReciprocalRestrictedQuotient := by
  simpa only
    [fixedLevelTwoReciprocalRestrictedQuotient] using
    HGAS.Topology.IsLocalHomeomorph.restrictPreimage
      fixedLevelTwoTorusQuotient_isLocalHomeomorph
      isOpen_fixedLevelTwoReciprocalTorusSet

/-- The real-coordinate reciprocal domain is an open subspace of the
full fixed real family. -/
theorem fixedLevelTwoReciprocalRealDomain_val_isOpenEmbedding :
    Topology.IsOpenEmbedding
      ((↑) :
        FixedLevelTwoReciprocalRealDomain →
          ℍ × (ℝ × ℝ)) := by
  have hopen :
      IsOpen
        (fixedLevelTwoTorusQuotient ⁻¹'
          fixedLevelTwoReciprocalTorusSet) :=
    isOpen_fixedLevelTwoReciprocalTorusSet.preimage
      continuous_fixedLevelTwoTorusQuotient
  exact hopen.isOpenEmbedding_subtypeVal

/-- The coordinate change `(τ,a,b) ↦ (τ,a+bτ)`, restricted to the
reciprocal loci, is a local homeomorphism. -/
theorem
    fixedLevelTwoReciprocalAnalyticDomainMap_isLocalHomeomorph :
    IsLocalHomeomorph
      fixedLevelTwoReciprocalAnalyticDomainMap := by
  have hsource :
      IsLocalHomeomorph
        ((↑) :
          FixedLevelTwoReciprocalRealDomain →
            ℍ × (ℝ × ℝ)) :=
    fixedLevelTwoReciprocalRealDomain_val_isOpenEmbedding.isLocalHomeomorph
  have hreconstruction :
      IsLocalHomeomorph
        HGAS.Topology.movingEllipticComplexReconstruction := by
    simpa only
      [HGAS.Topology.movingEllipticLatticeHomeomorph] using
      Homeomorph.isLocalHomeomorph
        HGAS.Topology.movingEllipticLatticeHomeomorph.symm
  have hright :
      IsLocalHomeomorph
        (HGAS.Topology.movingEllipticComplexReconstruction ∘
          ((↑) :
            FixedLevelTwoReciprocalRealDomain →
              ℍ × (ℝ × ℝ))) :=
    hreconstruction.comp hsource
  have htarget :
      IsLocalHomeomorph
        JacobiThetaReciprocalDomain.toBase :=
    jacobiThetaReciprocalDomain_toBase_isOpenEmbedding.isLocalHomeomorph
  have hcomposite :
      IsLocalHomeomorph
        (JacobiThetaReciprocalDomain.toBase ∘
          fixedLevelTwoReciprocalAnalyticDomainMap) := by
    simpa only [Function.comp_apply,
      fixedLevelTwoReciprocalAnalyticDomainMap,
      fixedLevelTwoThetaParameter,
      HGAS.Topology.movingEllipticComplexReconstruction] using
      hright
  exact
    hcomposite.of_comp htarget
      continuous_fixedLevelTwoReciprocalAnalyticDomainMap

/-- The real-coordinate pullback of the reciprocal theta map is a
local homeomorphism. -/
theorem fixedLevelTwoReciprocalRealMap_isLocalHomeomorph :
    IsLocalHomeomorph
      fixedLevelTwoReciprocalRealMap := by
  have hcomp :=
    jacobiThetaReciprocalTotalMap_isLocalHomeomorph.comp
      fixedLevelTwoReciprocalAnalyticDomainMap_isLocalHomeomorph
  simpa only [fixedLevelTwoReciprocalRealMap,
    Function.comp_apply] using hcomp

/-- The descended reciprocal theta map on the fixed torus divisor
complement is a local homeomorphism. -/
theorem fixedLevelTwoReciprocalTorusMap_isLocalHomeomorph :
    IsLocalHomeomorph
      fixedLevelTwoReciprocalTorusMap := by
  let q :
      FixedLevelTwoReciprocalRealDomain →
        FixedLevelTwoReciprocalTorusDomain :=
    fixedLevelTwoReciprocalRestrictedQuotient
  let f :
      FixedLevelTwoReciprocalTorusDomain →
        JacobiThetaReciprocalTotal :=
    fixedLevelTwoReciprocalTorusMap
  have hq : IsLocalHomeomorph q := by
    simpa only [q] using
      fixedLevelTwoReciprocalRestrictedQuotient_isLocalHomeomorph
  have hqSurjective : Function.Surjective q := by
    simpa only [q] using
      fixedLevelTwoReciprocalRestrictedQuotient_isOpenQuotientMap.surjective
  have hcomp : IsLocalHomeomorph (f ∘ q) := by
    have heq :
        f ∘ q =
          fixedLevelTwoReciprocalRealMap := by
      funext p
      exact
        fixedLevelTwoReciprocalTorusMap_quotient_apply p
    rw [heq]
    exact
      fixedLevelTwoReciprocalRealMap_isLocalHomeomorph
  have hOn :
      IsLocalHomeomorphOn f
        (q '' (Set.univ :
          Set FixedLevelTwoReciprocalRealDomain)) :=
    hcomp.isLocalHomeomorphOn.of_comp_right
      hq.isLocalHomeomorphOn
  have hrange :
      q '' (Set.univ :
          Set FixedLevelTwoReciprocalRealDomain) =
        Set.univ := by
    simpa only [Set.image_univ] using
      hqSurjective.range_eq
  rw [hrange] at hOn
  exact
    isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr hOn

end

end HGAS.Modular
