import HGAS.Modular.ExplicitGammaTwoHaarCusp
import HGAS.Modular.HaarExclusion
import Mathlib.Tactic

/-!
# The explicit normalized frame-Haar cusp marginal

This file normalizes the quotient measure obtained from the explicit
`Γ(2)` fundamental domain and proves that the measurable cusp height
constructed in `ExplicitGammaTwoHaarCusp` has a positive standard cusp
marginal.

The final theorem has exactly the hypothesis shape required by
`haarMarginal_reciprocalSlowdown_lintegral_eq_top`.
-/

namespace HGAS.Modular

open Function Matrix _root_.MeasureTheory
  _root_.MeasureTheory.Measure Set
open scoped ENNReal NNReal Pointwise

noncomputable section

private theorem realModularFrameHaar_ne_zero :
    (Measure.haar : Measure RealModularFrame) ≠ 0 := by
  rw [← measure_univ_pos]
  exact
    pos_iff_ne_zero.mpr
      (isOpen_univ.measure_ne_zero
        (Measure.haar : Measure RealModularFrame)
        univ_nonempty)

/-- The unnormalized quotient measure associated with the explicit
finite-index fundamental domain. -/
def gammaTwoExplicitRawHaarMeasure :
    Measure GammaTwoFrameQuotient :=
  gammaTwoFrameFundamentalDomainMeasure
    (Measure.haar : Measure RealModularFrame)
    gammaTwoExplicitFrameFundamentalDomain

@[simp]
theorem gammaTwoExplicitRawHaarMeasure_univ :
    gammaTwoExplicitRawHaarMeasure Set.univ =
      (Measure.haar : Measure RealModularFrame)
        gammaTwoExplicitFrameFundamentalDomain := by
  exact
    gammaTwoFrameFundamentalDomainMeasure_univ
      (Measure.haar : Measure RealModularFrame)
      gammaTwoExplicitFrameFundamentalDomain

theorem gammaTwoExplicitRawHaarMeasure_ne_zero :
    gammaTwoExplicitRawHaarMeasure ≠ 0 := by
  intro hzero
  have hdomainzero :
      (Measure.haar : Measure RealModularFrame)
          gammaTwoExplicitFrameFundamentalDomain = 0 := by
    rw [← gammaTwoExplicitRawHaarMeasure_univ, hzero]
    rfl
  exact
    (gammaTwoExplicitFrameFundamentalDomain_isFundamentalDomain
      |>.measure_ne_zero realModularFrameHaar_ne_zero)
      hdomainzero

/-- The raw explicit quotient measure packaged as a finite measure. -/
def gammaTwoExplicitFiniteHaarMeasure :
    FiniteMeasure GammaTwoFrameQuotient :=
  ⟨gammaTwoExplicitRawHaarMeasure,
    IsFiniteMeasure.mk (by
      rw [gammaTwoExplicitRawHaarMeasure_univ]
      exact
        lt_top_iff_ne_top.mpr
          gammaTwoExplicitFrameFundamentalDomain_measure_ne_top)⟩

theorem gammaTwoExplicitFiniteHaarMeasure_ne_zero :
    gammaTwoExplicitFiniteHaarMeasure ≠ 0 := by
  intro hzero
  apply gammaTwoExplicitRawHaarMeasure_ne_zero
  exact Subtype.ext_iff.mp hzero

/-- The explicitly normalized frame-Haar probability. -/
def gammaTwoExplicitFrameHaarProbability :
    ProbabilityMeasure GammaTwoFrameQuotient :=
  gammaTwoExplicitFiniteHaarMeasure.normalize

theorem gammaTwoExplicitFrameHaarProbability_toMeasure :
    (gammaTwoExplicitFrameHaarProbability :
        Measure GammaTwoFrameQuotient) =
      gammaTwoExplicitFiniteHaarMeasure.mass⁻¹ •
        gammaTwoExplicitRawHaarMeasure := by
  exact
    gammaTwoExplicitFiniteHaarMeasure
      |>.toMeasure_normalize_eq_of_nonzero
        gammaTwoExplicitFiniteHaarMeasure_ne_zero

/-- The explicitly normalized probability is invariant under all
descended right translations. -/
theorem gammaTwoExplicitFrameHaarProbability_rightInvariant :
    IsRightInvariantFrameProbability
      gammaTwoExplicitFrameHaarProbability := by
  letI : IsMulRightInvariant
      (Measure.haar : Measure RealModularFrame) :=
    gammaTwoHaar_rightInvariant_of_finiteFundamentalDomain
      (Measure.haar : Measure RealModularFrame)
      gammaTwoExplicitFrameFundamentalDomain_isFundamentalDomain
      gammaTwoExplicitFrameFundamentalDomain_measure_ne_top
  intro a
  apply ProbabilityMeasure.toMeasure_injective
  change
    Measure.map (gammaTwoFrameRightMul a)
        (gammaTwoExplicitFrameHaarProbability :
          Measure GammaTwoFrameQuotient) =
      (gammaTwoExplicitFrameHaarProbability :
        Measure GammaTwoFrameQuotient)
  rw [gammaTwoExplicitFrameHaarProbability_toMeasure,
    Measure.map_smul]
  congr 1
  exact
    gammaTwoFrameFundamentalDomainMeasure_rightInvariant
      (Measure.haar : Measure RealModularFrame)
      gammaTwoExplicitFrameFundamentalDomain_isFundamentalDomain
      a

/-- The frame height after undoing the fixed deck translation used by
the quotient cusp chart. -/
def translatedFrameCuspHeight
    (g : RealModularFrame) : ℝ :=
  realModularFrameHeight
    (gammaTwoIdentityDeckFactor⁻¹ • g)

theorem measurable_translatedFrameCuspHeight :
    Measurable translatedFrameCuspHeight := by
  unfold translatedFrameCuspHeight
  exact
    measurable_realModularFrameHeight.comp
      (measurable_const_smul
        gammaTwoIdentityDeckFactor⁻¹)

private theorem map_deck_smul_restrict_frameCuspRectangle
    (Y : ℝ) :
    Measure.map
        (fun g : RealModularFrame ↦
          gammaTwoIdentityDeckFactor • g)
        ((Measure.haar : Measure RealModularFrame).restrict
          (frameCuspRectangle Y)) =
      (Measure.haar : Measure RealModularFrame).restrict
        (gammaTwoTranslatedFrameCusp Y) := by
  let f : RealModularFrame → RealModularFrame :=
    fun g ↦ gammaTwoIdentityDeckFactor • g
  have hf :
      Measurable f :=
    measurable_const_smul gammaTwoIdentityDeckFactor
  have hfembed :
      MeasurableEmbedding f :=
    measurableEmbedding_const_smul
      gammaTwoIdentityDeckFactor
  have hmap :
      Measure.map f
          (Measure.haar : Measure RealModularFrame) =
        (Measure.haar : Measure RealModularFrame) := by
    change
      Measure.map
          (fun g : RealModularFrame ↦
            gammaTwoToRealFrame
              gammaTwoIdentityDeckFactor * g)
          (Measure.haar : Measure RealModularFrame) =
        (Measure.haar : Measure RealModularFrame)
    exact
      map_mul_left_eq_self
        (Measure.haar : Measure RealModularFrame)
        (gammaTwoToRealFrame
          gammaTwoIdentityDeckFactor)
  have hpreimage :
      f ⁻¹' gammaTwoTranslatedFrameCusp Y =
        frameCuspRectangle Y := by
    ext g
    simp only [f, gammaTwoTranslatedFrameCusp,
      mem_preimage, Set.mem_smul_set_iff_inv_smul_mem,
      inv_smul_smul]
  calc
    Measure.map f
        ((Measure.haar : Measure RealModularFrame).restrict
          (frameCuspRectangle Y)) =
        Measure.map f
          ((Measure.haar : Measure RealModularFrame).restrict
            (f ⁻¹' gammaTwoTranslatedFrameCusp Y)) := by
          rw [hpreimage]
    _ =
        (Measure.map f
          (Measure.haar : Measure RealModularFrame)).restrict
            (gammaTwoTranslatedFrameCusp Y) := by
          rw [hfembed.restrict_map]
    _ =
        (Measure.haar : Measure RealModularFrame).restrict
          (gammaTwoTranslatedFrameCusp Y) := by
          rw [hmap]

/-- Undoing the deck translation recovers exactly the positive-sign
frame-cusp marginal. -/
theorem exists_translatedFrameCusp_heightMarginal
    (Y : ℝ) (hY : 0 < Y) :
    ∃ c : ℝ≥0, c ≠ 0 ∧
      Measure.map translatedFrameCuspHeight
          ((Measure.haar : Measure RealModularFrame).restrict
            (gammaTwoTranslatedFrameCusp Y)) =
        c • HGAS.Dynamics.cuspHeightMeasure Y := by
  obtain ⟨c, hc, hcusp⟩ :=
    exists_positive_frameCuspRectangle_heightMarginal
      Y hY
  refine ⟨c, hc, ?_⟩
  calc
    Measure.map translatedFrameCuspHeight
        ((Measure.haar : Measure RealModularFrame).restrict
          (gammaTwoTranslatedFrameCusp Y)) =
        Measure.map translatedFrameCuspHeight
          (Measure.map
            (fun g : RealModularFrame ↦
              gammaTwoIdentityDeckFactor • g)
            ((Measure.haar : Measure RealModularFrame).restrict
              (frameCuspRectangle Y))) := by
          rw [map_deck_smul_restrict_frameCuspRectangle]
    _ =
        Measure.map
          (translatedFrameCuspHeight ∘
            fun g : RealModularFrame ↦
              gammaTwoIdentityDeckFactor • g)
          ((Measure.haar : Measure RealModularFrame).restrict
            (frameCuspRectangle Y)) := by
          rw [Measure.map_map
            measurable_translatedFrameCuspHeight
            (measurable_const_smul
              gammaTwoIdentityDeckFactor)]
    _ =
        Measure.map realModularFrameHeight
          ((Measure.haar : Measure RealModularFrame).restrict
            (frameCuspRectangle Y)) := by
          apply Measure.map_congr
          exact Filter.Eventually.of_forall fun g ↦ by
            simp [translatedFrameCuspHeight]
    _ = c • HGAS.Dynamics.cuspHeightMeasure Y :=
          hcusp

/-- On the translated cusp, quotient height agrees with the recovered
frame height after quotient projection. -/
theorem gammaTwoExplicitCuspHeight_comp_quotientMk_ae
    {Y : ℝ} (hY : 1 < Y) :
    (fun g : RealModularFrame ↦
        gammaTwoExplicitCuspHeight Y
          (gammaTwoFrameQuotientMk g)) =ᵐ[
      (Measure.haar : Measure RealModularFrame).restrict
        (gammaTwoTranslatedFrameCusp Y)]
      translatedFrameCuspHeight := by
  filter_upwards
    [ae_restrict_mem
      (measurableSet_gammaTwoTranslatedFrameCusp Y)]
      with g hg
  let ĝ : gammaTwoTranslatedFrameCusp Y := ⟨g, hg⟩
  change
    gammaTwoExplicitCuspHeight Y
        (gammaTwoCuspChartMap Y ĝ) =
      gammaTwoCuspChartHeight Y ĝ
  exact gammaTwoExplicitCuspHeight_chart hY ĝ

/-- Before normalization, the quotient height marginal already
dominates a positive standard cusp measure. -/
theorem exists_gammaTwoExplicitRawHaar_cuspMarginal
    (Y : ℝ) (hY : 1 < Y) :
    ∃ c : ℝ≥0, c ≠ 0 ∧
      c • HGAS.Dynamics.cuspHeightMeasure Y ≤
        Measure.map (gammaTwoExplicitCuspHeight Y)
          gammaTwoExplicitRawHaarMeasure := by
  obtain ⟨c, hc, hcusp⟩ :=
    exists_translatedFrameCusp_heightMarginal
      Y (zero_lt_one.trans hY)
  refine ⟨c, hc, ?_⟩
  have hrestrict :
      (Measure.haar : Measure RealModularFrame).restrict
          (gammaTwoTranslatedFrameCusp Y) ≤
        (Measure.haar : Measure RealModularFrame).restrict
          gammaTwoExplicitFrameFundamentalDomain :=
    Measure.restrict_mono_set _
      (gammaTwoTranslatedFrameCusp_subset_explicitDomain hY)
  have hprojection :
      Measure.map gammaTwoFrameQuotientMk
          ((Measure.haar : Measure RealModularFrame).restrict
            (gammaTwoTranslatedFrameCusp Y)) ≤
        gammaTwoExplicitRawHaarMeasure := by
    exact
      Measure.map_mono hrestrict
        (gammaTwoFrameQuotientMk_isCoveringMap
          |>.continuous.measurable)
  have hheight :=
    Measure.map_mono hprojection
      (measurable_gammaTwoExplicitCuspHeight hY)
  calc
    c • HGAS.Dynamics.cuspHeightMeasure Y =
        Measure.map translatedFrameCuspHeight
          ((Measure.haar : Measure RealModularFrame).restrict
            (gammaTwoTranslatedFrameCusp Y)) :=
      hcusp.symm
    _ =
        Measure.map (gammaTwoExplicitCuspHeight Y)
          (Measure.map gammaTwoFrameQuotientMk
            ((Measure.haar : Measure RealModularFrame).restrict
              (gammaTwoTranslatedFrameCusp Y))) := by
          rw [Measure.map_map
            (measurable_gammaTwoExplicitCuspHeight hY)
            (gammaTwoFrameQuotientMk_isCoveringMap
              |>.continuous.measurable)]
          exact
            Measure.map_congr
              (gammaTwoExplicitCuspHeight_comp_quotientMk_ae hY).symm
    _ ≤
        Measure.map (gammaTwoExplicitCuspHeight Y)
          gammaTwoExplicitRawHaarMeasure :=
      hheight

/-- The normalized explicit Haar probability has a positive standard
cusp-height marginal.  This is the concrete replacement for the
abstract `hcusp` hypothesis in `HaarExclusion`. -/
theorem exists_gammaTwoExplicitFrameHaarProbability_cuspMarginal
    (Y : ℝ) (hY : 1 < Y) :
    ∃ c : ℝ≥0, c ≠ 0 ∧
      c • HGAS.Dynamics.cuspHeightMeasure Y ≤
        Measure.map (gammaTwoExplicitCuspHeight Y)
          (gammaTwoExplicitFrameHaarProbability :
            Measure GammaTwoFrameQuotient) := by
  obtain ⟨c, hc, hcusp⟩ :=
    exists_gammaTwoExplicitRawHaar_cuspMarginal Y hY
  let a : ℝ≥0 :=
    gammaTwoExplicitFiniteHaarMeasure.mass⁻¹
  have hmass :
      gammaTwoExplicitFiniteHaarMeasure.mass ≠ 0 :=
    gammaTwoExplicitFiniteHaarMeasure
      |>.mass_nonzero_iff.mpr
        gammaTwoExplicitFiniteHaarMeasure_ne_zero
  have ha : a ≠ 0 := inv_ne_zero hmass
  refine ⟨a * c, mul_ne_zero ha hc, ?_⟩
  have hscaled :
      a • (c • HGAS.Dynamics.cuspHeightMeasure Y) ≤
        a • Measure.map (gammaTwoExplicitCuspHeight Y)
          gammaTwoExplicitRawHaarMeasure :=
    Measure.le_iff.2 fun s hs ↦ by
      simp only [Measure.coe_nnreal_smul_apply]
      exact
        mul_le_mul_right
          (Measure.le_iff.1 hcusp s hs)
          (a : ℝ≥0∞)
  rw [gammaTwoExplicitFrameHaarProbability_toMeasure,
    Measure.map_smul]
  simpa only [a, smul_smul] using hscaled

/-- A direct specialization of Haar exclusion to the explicit
`Γ(2)` frame-Haar probability and its measurable quotient height. -/
theorem explicitGammaTwoHaar_reciprocalSlowdown_lintegral_eq_top
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X)
    (proj : X → GammaTwoFrameQuotient)
    (hproj : Measurable proj)
    (reciprocalSlowdown : X → ℝ≥0∞)
    (Y : ℝ) (hY : 1 < Y)
    (Ychart : ℝ)
    (M : ℕ) (hM : 2 ≤ M)
    (hmarginal :
      Measure.map proj μ =
        (gammaTwoExplicitFrameHaarProbability :
          Measure GammaTwoFrameQuotient))
    (κ : ℝ≥0) (hκ : κ ≠ 0)
    (hchart :
      ∀ᵐ x ∂μ,
        (κ : ℝ≥0∞) ^ M *
            HGAS.Dynamics.cuspTailHeightPower
              Ychart M
              (gammaTwoExplicitCuspHeight Y (proj x)) ≤
          reciprocalSlowdown x) :
    ∫⁻ x, reciprocalSlowdown x ∂μ = ∞ := by
  obtain ⟨c, hc, hcusp⟩ :=
    exists_gammaTwoExplicitFrameHaarProbability_cuspMarginal
      Y hY
  exact
    haarMarginal_reciprocalSlowdown_lintegral_eq_top
      μ
      (gammaTwoExplicitFrameHaarProbability :
        Measure GammaTwoFrameQuotient)
      proj hproj
      (gammaTwoExplicitCuspHeight Y)
      (measurable_gammaTwoExplicitCuspHeight hY)
      reciprocalSlowdown
      Y Ychart M hM c hc hcusp hmarginal
      κ hκ hchart

end

end HGAS.Modular
