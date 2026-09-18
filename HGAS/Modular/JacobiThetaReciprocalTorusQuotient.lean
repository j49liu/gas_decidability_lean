import HGAS.Modular.JacobiThetaReciprocalCovering
import HGAS.Topology.MovingEllipticLatticeCoordinates
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.LocalAtTarget

/-!
# Fixed-torus descent of the reciprocal theta map

Write the elliptic parameter as `z = a + bτ`.  Translation by the
doubled period lattice then becomes

```
                    (a,b) ↦ (a+2m,b+2n).
```

This file replaces the moving lattice by the fixed compact torus

```
             (ℝ / 2ℤ) × (ℝ / 2ℤ)
               = AddCircle 2 × AddCircle 2.
```

The normalized theta vector is exactly invariant under both doubled
translations.  Its divisor condition `θ₁ ≠ 0` is invariant as well.
Consequently the continuous reciprocal theta map descends to the open
divisor complement in `ℍ × (AddCircle 2 × AddCircle 2)`.

This is a genuine quotient construction; no local-homeomorphism or
covering claim is made here.  It supplies the fixed compact source
needed for that later argument and removes the varying-lattice issue
completely.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I
open Complex Real Topology

noncomputable section

/-! ## The compact fixed torus -/

/-- One doubled-period real circle. -/
abbrev LevelTwoAddCircle := AddCircle (2 : ℝ)

/-- The fixed real two-torus carrying the two elliptic coordinates. -/
abbrev FixedLevelTwoTorus :=
  LevelTwoAddCircle × LevelTwoAddCircle

/-- The total fixed-torus family over the upper half-plane. -/
abbrev FixedLevelTwoTorusFamily :=
  ℍ × FixedLevelTwoTorus

local instance levelTwoPeriodPositive :
    Fact (0 < (2 : ℝ)) :=
  ⟨by norm_num⟩

theorem fixedLevelTwoTorus_compact :
    CompactSpace FixedLevelTwoTorus :=
  inferInstance

/-- Quotient both real elliptic coordinates modulo two. -/
def fixedLevelTwoTorusQuotient
    (p : ℍ × (ℝ × ℝ)) :
    FixedLevelTwoTorusFamily :=
  (p.1, (p.2.1, p.2.2))

theorem continuous_fixedLevelTwoTorusQuotient :
    Continuous fixedLevelTwoTorusQuotient := by
  unfold fixedLevelTwoTorusQuotient
  fun_prop

/-- The fixed quotient map is open and quotient. -/
theorem fixedLevelTwoTorusQuotient_isOpenQuotientMap :
    IsOpenQuotientMap fixedLevelTwoTorusQuotient := by
  have hc :
      IsOpenQuotientMap
        (fun x : ℝ => (x : LevelTwoAddCircle)) :=
    QuotientAddGroup.isOpenQuotientMap_mk
  have hp :
      IsOpenQuotientMap
        (fun p : ℝ × ℝ =>
          ((p.1 : LevelTwoAddCircle),
            (p.2 : LevelTwoAddCircle))) := by
    simpa only [Prod.map_apply] using hc.prodMap hc
  have ht :=
    (IsOpenQuotientMap.id :
      IsOpenQuotientMap (id : ℍ → ℍ)).prodMap hp
  simpa only [fixedLevelTwoTorusQuotient,
    id_eq, Prod.map_apply] using ht

/-! ## Exact doubled-period invariance -/

/-- Normalizing by the first theta coordinate removes the common
level-two automorphy multiplier. -/
theorem jacobiThetaReciprocalCoordinates_add_levelTwo_lattice
    (τ : ℍ) (z : ℂ) (m n : ℤ) :
    jacobiThetaReciprocalCoordinates τ
        (z + 2 * (m : ℂ) +
          2 * (n : ℂ) * (τ : ℂ)) =
      jacobiThetaReciprocalCoordinates τ z := by
  have htheta :=
    jacobiThetaVector_add_levelTwo_lattice
      z (τ : ℂ) m n
  have hmult :
      levelTwoThetaMultiplier n z (τ : ℂ) ≠ 0 :=
    levelTwoThetaMultiplier_ne_zero n z (τ : ℂ)
  funext k
  unfold jacobiThetaReciprocalCoordinates
  rw [congrFun htheta k.succ,
    congrFun htheta 0]
  simp only [Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left
    (jacobiThetaVector z (τ : ℂ) k.succ)
    (jacobiThetaVector z (τ : ℂ) 0)
    hmult

/-- The reciprocal divisor is invariant under the doubled lattice. -/
theorem jacobiTheta1_add_levelTwo_lattice_ne_zero_iff
    (τ : ℍ) (z : ℂ) (m n : ℤ) :
    jacobiTheta1
        (z + 2 * (m : ℂ) +
          2 * (n : ℂ) * (τ : ℂ))
        (τ : ℂ) ≠ 0 ↔
      jacobiTheta1 z (τ : ℂ) ≠ 0 := by
  have htheta :=
    congrFun
      (jacobiThetaVector_add_levelTwo_lattice
        z (τ : ℂ) m n) 0
  change
    jacobiTheta1
        (z + 2 * (m : ℂ) +
          2 * (n : ℂ) * (τ : ℂ))
        (τ : ℂ) =
      levelTwoThetaMultiplier n z (τ : ℂ) *
        jacobiTheta1 z (τ : ℂ) at htheta
  rw [htheta, mul_ne_zero_iff]
  constructor
  · exact And.right
  · exact fun h =>
      ⟨levelTwoThetaMultiplier_ne_zero
        n z (τ : ℂ), h⟩

/-- Reconstruct `z=a+bτ` from fixed real coordinates. -/
def fixedLevelTwoThetaParameter
    (p : ℍ × (ℝ × ℝ)) : ℂ :=
  (p.2.1 : ℂ) + (p.2.2 : ℂ) * (p.1 : ℂ)

theorem continuous_fixedLevelTwoThetaParameter :
    Continuous fixedLevelTwoThetaParameter := by
  unfold fixedLevelTwoThetaParameter
  fun_prop

/-- Translating `(a,b)` by `(2m,2n)` translates the reconstructed
complex parameter by the corresponding doubled elliptic period. -/
theorem fixedLevelTwoThetaParameter_translate
    (p : ℍ × (ℝ × ℝ)) (m n : ℤ) :
    fixedLevelTwoThetaParameter
        (HGAS.Topology.fixedLevelTwoTranslate m n p) =
      fixedLevelTwoThetaParameter p +
        2 * (m : ℂ) +
          2 * (n : ℂ) * (p.1 : ℂ) := by
  rcases p with ⟨τ, a, b⟩
  simp [fixedLevelTwoThetaParameter,
    HGAS.Topology.fixedLevelTwoTranslate]
  ring

/-- Exact invariance of normalized theta coordinates in fixed real
coordinates. -/
theorem jacobiThetaReciprocalCoordinates_fixed_translate
    (p : ℍ × (ℝ × ℝ)) (m n : ℤ) :
    jacobiThetaReciprocalCoordinates p.1
        (fixedLevelTwoThetaParameter
          (HGAS.Topology.fixedLevelTwoTranslate m n p)) =
      jacobiThetaReciprocalCoordinates p.1
        (fixedLevelTwoThetaParameter p) := by
  rw [fixedLevelTwoThetaParameter_translate]
  exact
    jacobiThetaReciprocalCoordinates_add_levelTwo_lattice
      p.1 (fixedLevelTwoThetaParameter p) m n

/-- Exact invariance of the reciprocal divisor condition in fixed real
coordinates. -/
theorem jacobiTheta1_fixed_translate_ne_zero_iff
    (p : ℍ × (ℝ × ℝ)) (m n : ℤ) :
    jacobiTheta1
        (fixedLevelTwoThetaParameter
          (HGAS.Topology.fixedLevelTwoTranslate m n p))
        (p.1 : ℂ) ≠ 0 ↔
      jacobiTheta1
        (fixedLevelTwoThetaParameter p)
        (p.1 : ℂ) ≠ 0 := by
  rw [fixedLevelTwoThetaParameter_translate]
  exact
    jacobiTheta1_add_levelTwo_lattice_ne_zero_iff
      p.1 (fixedLevelTwoThetaParameter p) m n

/-! ## Fibers and the invariant divisor complement -/

/-- Equal fixed-torus classes differ by one fixed doubled-period
translation. -/
theorem exists_fixedLevelTwoTranslate_of_quotient_eq
    (p q : ℍ × (ℝ × ℝ))
    (h :
      fixedLevelTwoTorusQuotient p =
        fixedLevelTwoTorusQuotient q) :
    ∃ m n : ℤ,
      p = HGAS.Topology.fixedLevelTwoTranslate m n q := by
  have ht : p.1 = q.1 :=
    congrArg
      (fun x : FixedLevelTwoTorusFamily => x.1) h
  have ha :
      (p.2.1 : LevelTwoAddCircle) =
        (q.2.1 : LevelTwoAddCircle) :=
    congrArg
      (fun x : FixedLevelTwoTorusFamily => x.2.1) h
  have hb :
      (p.2.2 : LevelTwoAddCircle) =
        (q.2.2 : LevelTwoAddCircle) :=
    congrArg
      (fun x : FixedLevelTwoTorusFamily => x.2.2) h
  have ha' :
      p.2.1 - q.2.1 ∈
        AddSubgroup.zmultiples (2 : ℝ) :=
    QuotientAddGroup.eq_iff_sub_mem.mp ha
  have hb' :
      p.2.2 - q.2.2 ∈
        AddSubgroup.zmultiples (2 : ℝ) :=
    QuotientAddGroup.eq_iff_sub_mem.mp hb
  obtain ⟨m, hm⟩ :=
    AddSubgroup.mem_zmultiples_iff.mp ha'
  obtain ⟨n, hn⟩ :=
    AddSubgroup.mem_zmultiples_iff.mp hb'
  refine ⟨m, n, ?_⟩
  apply Prod.ext
  · exact ht
  · apply Prod.ext
    · dsimp [HGAS.Topology.fixedLevelTwoTranslate]
      rw [zsmul_eq_mul] at hm
      linarith
    · dsimp [HGAS.Topology.fixedLevelTwoTranslate]
      rw [zsmul_eq_mul] at hn
      linarith

/-- The reciprocal divisor complement in fixed real coordinates. -/
def fixedLevelTwoReciprocalRealSet :
    Set (ℍ × (ℝ × ℝ)) :=
  {p |
    jacobiTheta1
      (fixedLevelTwoThetaParameter p)
      (p.1 : ℂ) ≠ 0}

theorem isOpen_fixedLevelTwoReciprocalRealSet :
    IsOpen fixedLevelTwoReciprocalRealSet := by
  have hpair :
      Continuous
        (fun p : ℍ × (ℝ × ℝ) =>
          (fixedLevelTwoThetaParameter p, p.1)) :=
    continuous_fixedLevelTwoThetaParameter.prodMk
      continuous_fst
  have htheta :
      Continuous
        (fun p : ℍ × (ℝ × ℝ) =>
          jacobiTheta1
            (fixedLevelTwoThetaParameter p)
            (p.1 : ℂ)) := by
    simpa only [Function.comp_apply] using
      continuous_jacobiTheta1_upperHalfPlane.comp hpair
  exact
    isClosed_singleton.isOpen_compl.preimage htheta

/-- The reciprocal divisor condition is constant on every fixed-torus
fiber. -/
theorem fixedLevelTwoReciprocalRealSet_mem_iff_of_quotient_eq
    {p q : ℍ × (ℝ × ℝ)}
    (h :
      fixedLevelTwoTorusQuotient p =
        fixedLevelTwoTorusQuotient q) :
    p ∈ fixedLevelTwoReciprocalRealSet ↔
      q ∈ fixedLevelTwoReciprocalRealSet := by
  obtain ⟨m, n, rfl⟩ :=
    exists_fixedLevelTwoTranslate_of_quotient_eq p q h
  exact jacobiTheta1_fixed_translate_ne_zero_iff q m n

/-- Normalized theta coordinates are constant on every fixed-torus
fiber. -/
theorem jacobiThetaReciprocalCoordinates_eq_of_fixedQuotient_eq
    {p q : ℍ × (ℝ × ℝ)}
    (h :
      fixedLevelTwoTorusQuotient p =
        fixedLevelTwoTorusQuotient q) :
    jacobiThetaReciprocalCoordinates p.1
        (fixedLevelTwoThetaParameter p) =
      jacobiThetaReciprocalCoordinates q.1
        (fixedLevelTwoThetaParameter q) := by
  obtain ⟨m, n, hp⟩ :=
    exists_fixedLevelTwoTranslate_of_quotient_eq p q h
  subst p
  exact
    jacobiThetaReciprocalCoordinates_fixed_translate
      q m n

/-- The open reciprocal locus in the fixed torus family. -/
def fixedLevelTwoReciprocalTorusSet :
    Set FixedLevelTwoTorusFamily :=
  fixedLevelTwoTorusQuotient ''
    fixedLevelTwoReciprocalRealSet

theorem isOpen_fixedLevelTwoReciprocalTorusSet :
    IsOpen fixedLevelTwoReciprocalTorusSet :=
  fixedLevelTwoTorusQuotient_isOpenQuotientMap.isOpenMap
    fixedLevelTwoReciprocalRealSet
    isOpen_fixedLevelTwoReciprocalRealSet

/-- Pulling the torus reciprocal locus back to real coordinates gives
exactly the original reciprocal divisor complement. -/
theorem mem_preimage_fixedLevelTwoReciprocalTorusSet_iff
    (p : ℍ × (ℝ × ℝ)) :
    fixedLevelTwoTorusQuotient p ∈
        fixedLevelTwoReciprocalTorusSet ↔
      p ∈ fixedLevelTwoReciprocalRealSet := by
  constructor
  · rintro ⟨q, hq, hqp⟩
    exact
      (fixedLevelTwoReciprocalRealSet_mem_iff_of_quotient_eq
        hqp).mp hq
  · intro hp
    exact ⟨p, hp, rfl⟩

/-! ## Continuous descent to the torus divisor complement -/

/-- The real-coordinate pullback of the torus divisor complement. -/
abbrev FixedLevelTwoReciprocalRealDomain :=
  {p : ℍ × (ℝ × ℝ) //
    fixedLevelTwoTorusQuotient p ∈
      fixedLevelTwoReciprocalTorusSet}

/-- The divisor complement inside the fixed torus family. -/
abbrev FixedLevelTwoReciprocalTorusDomain :=
  fixedLevelTwoReciprocalTorusSet

/-- The quotient map restricted over the reciprocal torus locus. -/
def fixedLevelTwoReciprocalRestrictedQuotient :
    FixedLevelTwoReciprocalRealDomain →
      FixedLevelTwoReciprocalTorusDomain :=
  fixedLevelTwoReciprocalTorusSet.restrictPreimage
    fixedLevelTwoTorusQuotient

theorem
    fixedLevelTwoReciprocalRestrictedQuotient_isOpenQuotientMap :
    IsOpenQuotientMap
      fixedLevelTwoReciprocalRestrictedQuotient :=
  fixedLevelTwoTorusQuotient_isOpenQuotientMap.restrictPreimage
    fixedLevelTwoReciprocalTorusSet

/-- Interpret a real-coordinate reciprocal point as a point of the
analytic reciprocal theta domain. -/
def fixedLevelTwoReciprocalAnalyticDomainMap
    (p : FixedLevelTwoReciprocalRealDomain) :
    JacobiThetaReciprocalDomain :=
  ⟨p.1.1,
    fixedLevelTwoThetaParameter p.1,
    (mem_preimage_fixedLevelTwoReciprocalTorusSet_iff
      p.1).mp p.2⟩

theorem continuous_fixedLevelTwoReciprocalAnalyticDomainMap :
    Continuous fixedLevelTwoReciprocalAnalyticDomainMap := by
  rw [continuous_induced_rng]
  exact
    (continuous_fst.comp continuous_subtype_val).prodMk
      (continuous_fixedLevelTwoThetaParameter.comp
        continuous_subtype_val)

/-- The reciprocal theta map pulled back to fixed real coordinates. -/
def fixedLevelTwoReciprocalRealMap
    (p : FixedLevelTwoReciprocalRealDomain) :
    JacobiThetaReciprocalTotal :=
  jacobiThetaReciprocalTotalMap
    (fixedLevelTwoReciprocalAnalyticDomainMap p)

theorem continuous_fixedLevelTwoReciprocalRealMap :
    Continuous fixedLevelTwoReciprocalRealMap :=
  continuous_jacobiThetaReciprocalTotalMap.comp
    continuous_fixedLevelTwoReciprocalAnalyticDomainMap

/-- The pulled-back reciprocal theta map is constant on the restricted
torus quotient fibers. -/
theorem fixedLevelTwoReciprocalRealMap_factorsThrough :
    Function.FactorsThrough
      fixedLevelTwoReciprocalRealMap
      fixedLevelTwoReciprocalRestrictedQuotient := by
  intro p q h
  have hq :
      fixedLevelTwoTorusQuotient p.1 =
        fixedLevelTwoTorusQuotient q.1 :=
    congrArg Subtype.val h
  apply JacobiThetaReciprocalTotal.ext
  · exact
      congrArg
        (fun x : FixedLevelTwoTorusFamily => x.1) hq
  · exact
      jacobiThetaReciprocalCoordinates_eq_of_fixedQuotient_eq
        hq

/-- Continuous-map packaging of the restricted quotient. -/
def fixedLevelTwoReciprocalRestrictedQuotientContinuous :
    C(FixedLevelTwoReciprocalRealDomain,
      FixedLevelTwoReciprocalTorusDomain) :=
  ⟨fixedLevelTwoReciprocalRestrictedQuotient,
    fixedLevelTwoReciprocalRestrictedQuotient_isOpenQuotientMap.continuous⟩

/-- Continuous-map packaging of the real pullback. -/
def fixedLevelTwoReciprocalRealContinuousMap :
    C(FixedLevelTwoReciprocalRealDomain,
      JacobiThetaReciprocalTotal) :=
  ⟨fixedLevelTwoReciprocalRealMap,
    continuous_fixedLevelTwoReciprocalRealMap⟩

theorem
    fixedLevelTwoReciprocalRestrictedQuotientContinuous_isQuotientMap :
    Topology.IsQuotientMap
      (fixedLevelTwoReciprocalRestrictedQuotientContinuous :
        FixedLevelTwoReciprocalRealDomain →
          FixedLevelTwoReciprocalTorusDomain) := by
  simpa only
    [fixedLevelTwoReciprocalRestrictedQuotientContinuous] using
    fixedLevelTwoReciprocalRestrictedQuotient_isOpenQuotientMap.isQuotientMap

theorem fixedLevelTwoReciprocalContinuousMap_factorsThrough :
    Function.FactorsThrough
      (fixedLevelTwoReciprocalRealContinuousMap :
        FixedLevelTwoReciprocalRealDomain →
          JacobiThetaReciprocalTotal)
      (fixedLevelTwoReciprocalRestrictedQuotientContinuous :
        FixedLevelTwoReciprocalRealDomain →
          FixedLevelTwoReciprocalTorusDomain) := by
  simpa only [fixedLevelTwoReciprocalRealContinuousMap,
    fixedLevelTwoReciprocalRestrictedQuotientContinuous] using
    fixedLevelTwoReciprocalRealMap_factorsThrough

/-- The descended reciprocal theta map on the fixed torus divisor
complement. -/
noncomputable def fixedLevelTwoReciprocalTorusMap :
    C(FixedLevelTwoReciprocalTorusDomain,
      JacobiThetaReciprocalTotal) :=
  fixedLevelTwoReciprocalRestrictedQuotientContinuous_isQuotientMap.lift
    fixedLevelTwoReciprocalRealContinuousMap
    fixedLevelTwoReciprocalContinuousMap_factorsThrough

/-- Pulling the descended map back along the quotient recovers exactly
the original real-coordinate reciprocal theta map. -/
theorem fixedLevelTwoReciprocalTorusMap_comp_quotient :
    fixedLevelTwoReciprocalTorusMap.comp
        fixedLevelTwoReciprocalRestrictedQuotientContinuous =
      fixedLevelTwoReciprocalRealContinuousMap := by
  exact
    Topology.IsQuotientMap.lift_comp
      fixedLevelTwoReciprocalRestrictedQuotientContinuous_isQuotientMap
      fixedLevelTwoReciprocalRealContinuousMap
      fixedLevelTwoReciprocalContinuousMap_factorsThrough

@[simp]
theorem fixedLevelTwoReciprocalTorusMap_quotient_apply
    (p : FixedLevelTwoReciprocalRealDomain) :
    fixedLevelTwoReciprocalTorusMap
        (fixedLevelTwoReciprocalRestrictedQuotient p) =
      jacobiThetaReciprocalTotalMap
        (fixedLevelTwoReciprocalAnalyticDomainMap p) := by
  exact
    congrArg
      (fun f :
        C(FixedLevelTwoReciprocalRealDomain,
          JacobiThetaReciprocalTotal) => f p)
      fixedLevelTwoReciprocalTorusMap_comp_quotient

/-- The descended fixed-torus map is globally surjective.  This is the
torus-quotient form of affine theta saturation. -/
theorem fixedLevelTwoReciprocalTorusMap_surjective :
    Function.Surjective fixedLevelTwoReciprocalTorusMap := by
  intro y
  obtain ⟨d, hd⟩ :=
    jacobiThetaReciprocalTotalMap_surjective y
  let r : ℍ × (ℝ × ℝ) :=
    HGAS.Topology.movingEllipticLatticeHomeomorph
      (d.modulus, d.parameter)
  have hr :
      HGAS.Topology.movingEllipticComplexReconstruction r =
        (d.modulus, d.parameter) := by
    exact
      HGAS.Topology.movingEllipticComplexReconstruction_leftInverse
        (d.modulus, d.parameter)
  have hr_modulus : r.1 = d.modulus :=
    congrArg Prod.fst hr
  have hr_parameter :
      fixedLevelTwoThetaParameter r = d.parameter := by
    exact congrArg Prod.snd hr
  have hr_good :
      r ∈ fixedLevelTwoReciprocalRealSet := by
    change
      jacobiTheta1
        (fixedLevelTwoThetaParameter r)
        (r.1 : ℂ) ≠ 0
    rw [hr_parameter, hr_modulus]
    exact d.thetaOne_ne_zero
  let p : FixedLevelTwoReciprocalRealDomain :=
    ⟨r,
      (mem_preimage_fixedLevelTwoReciprocalTorusSet_iff r).2
        hr_good⟩
  have hp_domain :
      fixedLevelTwoReciprocalAnalyticDomainMap p = d := by
    apply JacobiThetaReciprocalDomain.ext
    · exact hr_modulus
    · exact hr_parameter
  refine
    ⟨fixedLevelTwoReciprocalRestrictedQuotient p, ?_⟩
  rw [fixedLevelTwoReciprocalTorusMap_quotient_apply,
    hp_domain, hd]

end

end HGAS.Modular
