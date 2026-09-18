import HGAS.MeasureTheory.FiniteIndexFundamentalDomain
import HGAS.Modular.FrameBaseHaarVolume
import HGAS.Modular.GammaTwoFiniteHaarReduction
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic

/-!
# A finite-Haar fundamental domain for integral modular frames

We lift the usual modular fundamental domain from the upper half-plane
to `SL(2, ℝ)`.  The central element `-1` acts trivially on the base, so
one additional measurable sign convention is imposed on the frame.
The boundary of the usual closed modular domain has hyperbolic area
zero; hence the resulting set is a measure-theoretic fundamental domain.

Finally, the general finite-index construction passes from
`SL(2, ℤ)` to `Γ(2)`.
-/

namespace HGAS.Modular

open Function Matrix _root_.MeasureTheory
  _root_.MeasureTheory.Measure Set
open scoped ENNReal MatrixGroups Modular NNReal Pointwise

noncomputable section

abbrev IntegralModularGroup := SL(2, ℤ)

private instance integralModularGroupCountable :
    Countable IntegralModularGroup :=
  Function.Injective.countable
    (β := Fin 2 → Fin 2 → ℤ)
    (by
      intro γ δ h
      exact Subtype.ext h)

/-- Integral special-linear matrices embedded in real
special-linear matrices. -/
def integralToRealFrame :
    IntegralModularGroup →* RealModularFrame :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)

/-- The full integral modular group acts on real frames by left
multiplication. -/
instance integralModularGroupMulActionRealFrame :
    MulAction IntegralModularGroup RealModularFrame :=
  MulAction.compHom RealModularFrame integralToRealFrame

@[simp]
theorem integralModularGroup_smul_realFrame
    (γ : IntegralModularGroup) (g : RealModularFrame) :
    γ • g = integralToRealFrame γ * g :=
  rfl

instance integralModularGroupContinuousConstSMulRealFrame :
    ContinuousConstSMul IntegralModularGroup RealModularFrame where
  continuous_const_smul γ := by
    simpa only [integralModularGroup_smul_realFrame] using
      continuous_const_mul (integralToRealFrame γ)

/-- Left Haar measure is invariant under integral deck
transformations. -/
instance integralModularGroupSMulInvariantHaar
    (m : Measure RealModularFrame) [IsMulLeftInvariant m] :
    SMulInvariantMeasure IntegralModularGroup RealModularFrame m where
  measure_preimage_smul γ A hA := by
    simpa only [integralModularGroup_smul_realFrame] using
      measure_preimage_mul m (integralToRealFrame γ) A

/-- The real embedding preserves the Möbius action. -/
theorem integralToRealFrame_smul
    (γ : IntegralModularGroup) (z : UpperHalfPlane) :
    integralToRealFrame γ • z = γ • z := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply,
    UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [integralToRealFrame,
    Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, Int.coe_castRingHom]

/-- Taking the base point intertwines the integral action on frames
with its Möbius action on the upper half-plane. -/
theorem realModularFrameBasePoint_integral_smul
    (γ : IntegralModularGroup) (g : RealModularFrame) :
    realModularFrameBasePoint (γ • g) =
      γ • realModularFrameBasePoint g := by
  change
    (integralToRealFrame γ * g) • UpperHalfPlane.I =
      γ • (g • UpperHalfPlane.I)
  rw [mul_smul, integralToRealFrame_smul]

/-! ## The null boundary of the standard base domain -/

/-- The boundary discarded when passing from the closed standard
modular domain to its open interior. -/
def modularDomainBoundary : Set UpperHalfPlane :=
  ModularGroup.fd \ ModularGroup.fdo

private theorem complex_volume_re_level_zero (c : ℝ) :
    (volume : Measure ℂ) {z | z.re = c} = 0 := by
  let S : Set (ℝ × ℝ) := {c} ×ˢ Set.univ
  have hS : MeasurableSet S :=
    MeasurableSet.prod (measurableSet_singleton c)
      MeasurableSet.univ
  have hpre :
      Complex.measurableEquivRealProd ⁻¹' S =
        {z : ℂ | z.re = c} := by
    ext z
    simp [S, Complex.measurableEquivRealProd_apply]
  rw [← hpre,
    Complex.volume_preserving_equiv_real_prod.measure_preimage
      hS.nullMeasurableSet]
  rw [Measure.volume_eq_prod, Measure.prod_prod]
  simp

private theorem complex_volume_modular_boundary_image_zero :
    (volume : Measure ℂ)
        (UpperHalfPlane.coe '' modularDomainBoundary) = 0 := by
  let Vneg : Set ℂ := {z | z.re = -(1 / 2 : ℝ)}
  let Vpos : Set ℂ := {z | z.re = (1 / 2 : ℝ)}
  have hsubset :
      UpperHalfPlane.coe '' modularDomainBoundary ⊆
        Metric.sphere 0 1 ∪ (Vneg ∪ Vpos) := by
    rintro z ⟨τ, ⟨hfd, hfdo⟩, rfl⟩
    by_cases hnorm : 1 < (τ : ℂ).normSq
    · have hre_not : ¬|τ.re| < 1 / 2 := by
        intro hre
        exact hfdo ⟨hnorm, hre⟩
      have hre : |τ.re| = 1 / 2 :=
        le_antisymm hfd.2 (not_lt.mp hre_not)
      rw [abs_eq (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hre
      rcases hre with hre | hre
      · exact Or.inr (Or.inr hre)
      · exact Or.inr (Or.inl hre)
    · have hnormSq : (τ : ℂ).normSq = 1 :=
        le_antisymm (not_lt.mp hnorm) hfd.1
      left
      rw [Metric.mem_sphere, dist_zero_right]
      rw [Complex.normSq_eq_norm_sq] at hnormSq
      nlinarith [norm_nonneg (τ : ℂ)]
  apply measure_mono_null hsubset
  apply measure_union_null
  · exact addHaar_sphere (volume : Measure ℂ) 0 1
  · apply measure_union_null
    · exact complex_volume_re_level_zero (-(1 / 2 : ℝ))
    · exact complex_volume_re_level_zero (1 / 2 : ℝ)

/-- The boundary of the standard modular domain has zero hyperbolic
area. -/
theorem upperHalfPlane_volume_modularDomainBoundary :
    (volume : Measure UpperHalfPlane) modularDomainBoundary = 0 := by
  rw [UpperHalfPlane.volume_def]
  apply
    withDensity_absolutelyContinuous
      ((volume : Measure ℂ).comap UpperHalfPlane.coe) _
  rw [UpperHalfPlane.measurableEmbedding_coe.comap_apply]
  exact complex_volume_modular_boundary_image_zero

/-- Haar-almost every frame avoids every integral translate of the
boundary of the standard modular domain. -/
theorem ae_forall_basePoint_integral_smul_not_mem_boundary :
    ∀ᵐ g ∂(Measure.haar : Measure RealModularFrame),
      ∀ γ : IntegralModularGroup,
        realModularFrameBasePoint (γ • g) ∉
          modularDomainBoundary := by
  apply ae_all_iff.mpr
  intro γ
  rw [ae_iff]
  have hbase :
      (Measure.haar : Measure RealModularFrame)
          (realModularFrameBasePoint ⁻¹'
            modularDomainBoundary) = 0 := by
    change
      (Measure.haar : Measure RealModularFrame)
          (realModularFrameBasePoint ⁻¹'
            (ModularGroup.fd \ ModularGroup.fdo)) = 0
    rw [← frameBaseProjectionMeasure_apply
      (Measure.haar : Measure RealModularFrame)
      ((ModularGroup.isClosed_fd.measurableSet).diff
        ModularGroup.isOpen_fdo.measurableSet)]
    obtain ⟨c, hc⟩ :=
      frameBaseProjectionMeasure_eq_smul_volume
        (Measure.haar : Measure RealModularFrame)
    rw [hc]
    have hboundary :
        (volume : Measure UpperHalfPlane)
            (ModularGroup.fd \ ModularGroup.fdo) = 0 := by
      simpa only [modularDomainBoundary] using
        upperHalfPlane_volume_modularDomainBoundary
    rw [Measure.coe_nnreal_smul_apply, hboundary, mul_zero]
  have htranslate :
      (Measure.haar : Measure RealModularFrame)
          ((fun g ↦ γ • g) ⁻¹'
            (realModularFrameBasePoint ⁻¹'
              modularDomainBoundary)) = 0 := by
    change
      (Measure.haar : Measure RealModularFrame)
          ((fun g ↦ γ • g) ⁻¹'
            (realModularFrameBasePoint ⁻¹'
              (ModularGroup.fd \ ModularGroup.fdo))) = 0
    rw [SMulInvariantMeasure.measure_preimage_smul γ
      (((ModularGroup.isClosed_fd.measurableSet).diff
          ModularGroup.isOpen_fdo.measurableSet).preimage
        realModularFrameBasePoint_continuous.measurable)]
    exact hbase
  simpa only [Set.mem_setOf_eq, not_not,
    Set.mem_preimage] using htranslate

/-! ## Resolving the central sign -/

/-- A measurable lexicographic half of the frame group.  Exactly one
of `g` and `-g` belongs to this set. -/
def positiveFrameHalf : Set RealModularFrame :=
  {g | 0 < g 0 0 ∨ (g 0 0 = 0 ∧ 0 < g 0 1)}

theorem measurableSet_positiveFrameHalf :
    MeasurableSet positiveFrameHalf := by
  have hentry (i j : Fin 2) :
      Continuous (fun g : RealModularFrame ↦ g i j) := by
    exact
      (continuous_apply j).comp
        (Matrix.SpecialLinearGroup.continuous_apply
          (fun g : RealModularFrame ↦ g) continuous_id i)
  apply MeasurableSet.union
  · exact measurableSet_lt measurable_const (hentry 0 0).measurable
  · exact
      (isClosed_eq (hentry 0 0) continuous_const).measurableSet.inter
        (measurableSet_lt measurable_const (hentry 0 1).measurable)

private theorem frame_firstRow_ne_zero
    (g : RealModularFrame) :
    g 0 0 ≠ 0 ∨ g 0 1 ≠ 0 := by
  by_contra h
  push Not at h
  have hdet := g.2
  rw [Matrix.det_fin_two, h.1, h.2] at hdet
  norm_num at hdet

theorem mem_positiveFrameHalf_or_neg
    (g : RealModularFrame) :
    g ∈ positiveFrameHalf ∨ -g ∈ positiveFrameHalf := by
  rcases lt_trichotomy (g 0 0) 0 with hneg | hzero | hpos
  · right
    exact Or.inl (by simpa using neg_pos.mpr hneg)
  · rcases frame_firstRow_ne_zero g with h | h
    · exact (h hzero).elim
    · rcases lt_or_gt_of_ne h with hneg | hpos
      · right
        exact Or.inr ⟨by simp [hzero],
          by simpa using neg_pos.mpr hneg⟩
      · left
        exact Or.inr ⟨hzero, hpos⟩
  · left
    exact Or.inl hpos

theorem not_mem_positiveFrameHalf_neg_of_mem
    {g : RealModularFrame} (hg : g ∈ positiveFrameHalf) :
    -g ∉ positiveFrameHalf := by
  rcases hg with hpos | ⟨hzero, hpos⟩
  · rintro (hneg | ⟨hzero', -⟩)
    · simp only [Matrix.SpecialLinearGroup.coe_neg,
        Matrix.neg_apply, neg_pos] at hneg
      exact (not_lt_of_ge hpos.le) hneg
    · simp only [Matrix.SpecialLinearGroup.coe_neg,
        Matrix.neg_apply, neg_eq_zero] at hzero'
      exact hpos.ne' hzero'
  · rintro (hneg | ⟨-, hneg⟩)
    · simp only [Matrix.SpecialLinearGroup.coe_neg,
        Matrix.neg_apply, neg_pos] at hneg
      exact hneg.ne hzero
    · simp only [Matrix.SpecialLinearGroup.coe_neg,
        Matrix.neg_apply, neg_pos] at hneg
      exact (not_lt_of_ge hpos.le) hneg

/-! ## The frame fundamental domain -/

/-- Lift the open modular domain to frames and impose the central sign
convention. -/
def integralFrameFundamentalDomain : Set RealModularFrame :=
  realModularFrameBasePoint ⁻¹' ModularGroup.fdo ∩
    positiveFrameHalf

theorem measurableSet_integralFrameFundamentalDomain :
    MeasurableSet integralFrameFundamentalDomain :=
  (ModularGroup.isOpen_fdo.measurableSet.preimage
      realModularFrameBasePoint_continuous.measurable).inter
    measurableSet_positiveFrameHalf

theorem integralFrameFundamentalDomain_subset_base_fd :
    integralFrameFundamentalDomain ⊆
      realModularFrameBasePoint ⁻¹' ModularGroup.fd := by
  intro g hg
  exact ModularGroup.fdo_subset_fd hg.1

theorem integralFrameFundamentalDomain_measure_ne_top :
    (Measure.haar : Measure RealModularFrame)
        integralFrameFundamentalDomain ≠ ∞ := by
  apply ne_of_lt
  exact
    (measure_mono
      integralFrameFundamentalDomain_subset_base_fd).trans_lt
      (lt_top_iff_ne_top.mpr
        haar_basePoint_preimage_modular_fd_ne_top)

/-- Negating an integral deck transformation negates the resulting
real frame. -/
theorem neg_integral_smul_realFrame
    (γ : IntegralModularGroup) (g : RealModularFrame) :
    (-γ) • g = -(γ • g) := by
  apply Subtype.ext
  simp only [integralModularGroup_smul_realFrame,
    Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_neg]
  simp [integralToRealFrame,
    Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, Int.coe_castRingHom]

/-- Almost every real frame can be moved into the lifted open modular
domain with the chosen central sign. -/
theorem integralFrameFundamentalDomain_ae_covers :
    ∀ᵐ g ∂(Measure.haar : Measure RealModularFrame),
      ∃ γ : IntegralModularGroup,
        γ • g ∈ integralFrameFundamentalDomain := by
  filter_upwards
    [ae_forall_basePoint_integral_smul_not_mem_boundary]
      with g hg
  obtain ⟨γ, hγfd⟩ :=
    ModularGroup.exists_smul_mem_fd
      (realModularFrameBasePoint g)
  have hbasefd :
      realModularFrameBasePoint (γ • g) ∈
        ModularGroup.fd := by
    rw [realModularFrameBasePoint_integral_smul]
    exact hγfd
  have hbasefdo :
      realModularFrameBasePoint (γ • g) ∈
        ModularGroup.fdo := by
    by_contra hnot
    exact hg γ ⟨hbasefd, hnot⟩
  rcases mem_positiveFrameHalf_or_neg (γ • g) with hpos | hneg
  · exact ⟨γ, hbasefdo, hpos⟩
  · refine ⟨-γ, ?_, ?_⟩
    · change
        realModularFrameBasePoint ((-γ) • g) ∈
          ModularGroup.fdo
      rw [realModularFrameBasePoint_integral_smul,
        ModularGroup.SL_neg_smul,
        ← realModularFrameBasePoint_integral_smul]
      exact hbasefdo
    · rw [neg_integral_smul_realFrame]
      exact hneg

/-- A nontrivial integral translate of the lifted domain is disjoint
from the domain itself.  The open modular-domain uniqueness theorem
reduces the only possible overlap to the central element `-1`, and the
frame-sign convention removes that overlap. -/
theorem integralFrameFundamentalDomain_disjoint_smul
    (γ : IntegralModularGroup) (hγ : γ ≠ 1) :
    Disjoint
      (γ • integralFrameFundamentalDomain)
      integralFrameFundamentalDomain := by
  rw [Set.disjoint_left]
  intro x hxtranslate hx
  have hu :
      γ⁻¹ • x ∈ integralFrameFundamentalDomain := by
    rwa [Set.mem_smul_set_iff_inv_smul_mem] at hxtranslate
  have htranslatedBase :
      γ • realModularFrameBasePoint (γ⁻¹ • x) ∈
        ModularGroup.fdo := by
    rw [← realModularFrameBasePoint_integral_smul]
    simpa only [smul_inv_smul] using hx.1
  rcases
      ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fdo
        hu.1 htranslatedBase with hone | hneg
  · exact hγ hone
  · have hxneg :
        x = -(γ⁻¹ • x) := by
      calc
        x = γ • (γ⁻¹ • x) := by simp
        _ = (-1 : IntegralModularGroup) •
            (γ⁻¹ • x) := by rw [hneg]
        _ = -(γ⁻¹ • x) := by
          simpa only [one_smul] using
            neg_integral_smul_realFrame
              (1 : IntegralModularGroup) (γ⁻¹ • x)
    have hnegmem :
        -(γ⁻¹ • x) ∈ positiveFrameHalf := by
      rw [← hxneg]
      exact hx.2
    exact
      not_mem_positiveFrameHalf_neg_of_mem hu.2 hnegmem

/-- The lifted open modular domain with its sign convention is a
measure-theoretic fundamental domain for the full integral modular
group acting on real frames. -/
theorem integralFrameFundamentalDomain_isFundamentalDomain :
    IsFundamentalDomain IntegralModularGroup
      integralFrameFundamentalDomain
      (Measure.haar : Measure RealModularFrame) := by
  apply IsFundamentalDomain.mk''
  · exact
      measurableSet_integralFrameFundamentalDomain.nullMeasurableSet
  · exact integralFrameFundamentalDomain_ae_covers
  · intro γ hγ
    exact
      (integralFrameFundamentalDomain_disjoint_smul γ hγ).aedisjoint
  · intro γ
    exact
      (measurePreserving_smul γ
        (Measure.haar : Measure RealModularFrame))
        |>.quasiMeasurePreserving

/-! ## Passage to `Γ(2)` -/

/-- The finite-index construction applied to the explicit integral
frame domain gives a finite-Haar fundamental domain for `Γ(2)`. -/
theorem gammaTwoHasFiniteHaarFundamentalDomain :
    GammaTwoHasFiniteHaarFundamentalDomain := by
  let D : Set RealModularFrame :=
    HGAS.MeasureTheory.finiteIndexSubgroupDomain
      GammaTwo integralFrameFundamentalDomain
  refine ⟨D, ?_, ?_⟩
  · exact
      HGAS.MeasureTheory.IsFundamentalDomain.finiteIndexSubgroup
        integralFrameFundamentalDomain_isFundamentalDomain
        GammaTwo
  · exact
      HGAS.MeasureTheory.finiteIndexSubgroupDomain_measure_ne_top
        GammaTwo integralFrameFundamentalDomain_measure_ne_top

/-- In particular, the level-two frame quotient carries a normalized
right-invariant Haar probability. -/
theorem gammaTwoHasFiniteFrameVolume :
    GammaTwoHasFiniteFrameVolume :=
  gammaTwoHasFiniteHaarFundamentalDomain.hasFiniteFrameVolume

end

end HGAS.Modular
