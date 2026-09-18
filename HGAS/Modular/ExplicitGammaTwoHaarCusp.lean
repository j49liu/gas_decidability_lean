import HGAS.Modular.FrameCuspMarginal
import HGAS.Modular.GammaTwoFiniteVolumeConsequences
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Tactic

/-!
# An explicit cusp-height model for the level-two frame quotient

This file inserts the rectangular frame cusp into the explicit
finite-index fundamental domain for `Γ(2)`, builds a measurable height
function on the quotient, and proves a positive `dy / y²` marginal
lower bound for the normalized fundamental-domain probability.

The height function is intentionally local.  The quotient projection is
injective on one high-cusp chart.  We invert it measurably there, read
off the usual height, and extend the result measurably by zero outside
the chart.  This is all the Haar-exclusion argument needs, and avoids
introducing a global reduction-theory selector.
-/

namespace HGAS.Modular

open Function Matrix _root_.MeasureTheory
  _root_.MeasureTheory.Measure Set
open scoped ENNReal MatrixGroups NNReal Pointwise

noncomputable section

private instance integralModularGroupCountableForCusp :
    Countable IntegralModularGroup :=
  Function.Injective.countable
    (β := Fin 2 → Fin 2 → ℤ)
    (by
      intro γ δ h
      exact Subtype.ext h)

private instance gammaTwoCountableForCusp :
    Countable GammaTwo :=
  Function.Injective.countable
    (β := IntegralModularGroup)
    (fun _ _ h ↦ Subtype.ext h :
      Function.Injective
        (fun γ : GammaTwo ↦ γ.1))

private instance realMatrixPolishForCusp :
    PolishSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
  inferInstanceAs
    (PolishSpace (Fin 2 → Fin 2 → ℝ))

private instance realModularFramePolishForCusp :
    PolishSpace RealModularFrame :=
  Matrix.SpecialLinearGroup.isClosedEmbedding_val.polishSpace

/-- The explicit finite-index domain already used in the finite-volume
proof. -/
def gammaTwoExplicitFrameFundamentalDomain :
    Set RealModularFrame :=
  HGAS.MeasureTheory.finiteIndexSubgroupDomain
    GammaTwo integralFrameFundamentalDomain

theorem gammaTwoExplicitFrameFundamentalDomain_isFundamentalDomain :
    IsFundamentalDomain GammaTwo
      gammaTwoExplicitFrameFundamentalDomain
      (Measure.haar : Measure RealModularFrame) :=
  HGAS.MeasureTheory.IsFundamentalDomain.finiteIndexSubgroup
    integralFrameFundamentalDomain_isFundamentalDomain GammaTwo

theorem gammaTwoExplicitFrameFundamentalDomain_measure_ne_top :
    (Measure.haar : Measure RealModularFrame)
        gammaTwoExplicitFrameFundamentalDomain ≠ ∞ :=
  HGAS.MeasureTheory.finiteIndexSubgroupDomain_measure_ne_top
    GammaTwo integralFrameFundamentalDomain_measure_ne_top

/-- Mathlib's default left transversal for `Γ(2)` in the integral
modular group. -/
def gammaTwoDefaultLeftTransversal :
    GammaTwo.LeftTransversal :=
  default

/-- The representative selected by the default transversal when the
group element being decomposed is the identity. -/
def gammaTwoIdentityTransversalRepresentative :
    ↥(gammaTwoDefaultLeftTransversal :
      Set IntegralModularGroup) :=
  (gammaTwoDefaultLeftTransversal.2.equiv
    (1 : IntegralModularGroup)).1

/-- The `Γ(2)` factor in the same identity decomposition. -/
def gammaTwoIdentityDeckFactor : GammaTwo :=
  (gammaTwoDefaultLeftTransversal.2.equiv
    (1 : IntegralModularGroup)).2

theorem gammaTwoIdentityRepresentative_mul_deckFactor :
    (gammaTwoIdentityTransversalRepresentative :
        IntegralModularGroup) *
      (gammaTwoIdentityDeckFactor :
        IntegralModularGroup) = 1 :=
  gammaTwoDefaultLeftTransversal.2
    |>.equiv_fst_mul_equiv_snd
      (1 : IntegralModularGroup)

theorem gammaTwoIdentityRepresentative_inv_eq_deckFactor :
    (gammaTwoIdentityTransversalRepresentative :
        IntegralModularGroup)⁻¹ =
      (gammaTwoIdentityDeckFactor :
        IntegralModularGroup) := by
  calc
    (gammaTwoIdentityTransversalRepresentative :
        IntegralModularGroup)⁻¹ =
        (gammaTwoIdentityTransversalRepresentative :
          IntegralModularGroup)⁻¹ * 1 := by simp
    _ =
        (gammaTwoIdentityTransversalRepresentative :
          IntegralModularGroup)⁻¹ *
          ((gammaTwoIdentityTransversalRepresentative :
              IntegralModularGroup) *
            (gammaTwoIdentityDeckFactor :
              IntegralModularGroup)) := by
          rw [gammaTwoIdentityRepresentative_mul_deckFactor]
    _ = (gammaTwoIdentityDeckFactor :
        IntegralModularGroup) := by simp

@[simp]
theorem gammaTwoFrameQuotientMk_smul
    (γ : GammaTwo) (g : RealModularFrame) :
    gammaTwoFrameQuotientMk (γ • g) =
      gammaTwoFrameQuotientMk g := by
  apply Quotient.sound
  exact ⟨γ, rfl⟩

private theorem gammaTwo_smul_eq_integral_smul
    (γ : GammaTwo) (g : RealModularFrame) :
    γ • g = (γ.1 : IntegralModularGroup) • g :=
  rfl

/-- The quotient projection is pointwise injective on the open
integral frame fundamental domain. -/
theorem gammaTwoFrameQuotientMk_injOn_integralFrameFundamentalDomain :
    Set.InjOn gammaTwoFrameQuotientMk
      integralFrameFundamentalDomain := by
  intro g hg h hh hquot
  have horbit := Quotient.exact hquot
  change g ∈ MulAction.orbit GammaTwo h at horbit
  obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp horbit
  by_cases hγone : γ = 1
  · subst γ
    simpa only [one_smul] using hγ.symm
  · have hγval : (γ.1 : IntegralModularGroup) ≠ 1 := by
      intro hval
      apply hγone
      exact Subtype.ext hval
    have htranslated :
        g ∈ (γ.1 : IntegralModularGroup) •
          integralFrameFundamentalDomain := by
      rw [← hγ]
      rw [gammaTwo_smul_eq_integral_smul]
      exact Set.smul_mem_smul_set hh
    exact False.elim <|
      (Set.disjoint_left.mp
        (integralFrameFundamentalDomain_disjoint_smul
          (γ.1 : IntegralModularGroup) hγval))
        htranslated hg

/-- The translated high-cusp chart which is visibly contained in the
default finite-index domain. -/
def gammaTwoTranslatedFrameCusp (Y : ℝ) :
    Set RealModularFrame :=
  gammaTwoIdentityDeckFactor • frameCuspRectangle Y

theorem measurableSet_gammaTwoTranslatedFrameCusp
    (Y : ℝ) :
    MeasurableSet (gammaTwoTranslatedFrameCusp Y) :=
  (measurableSet_frameCuspRectangle Y).const_smul
    gammaTwoIdentityDeckFactor

theorem gammaTwoTranslatedFrameCusp_subset_explicitDomain
    {Y : ℝ} (hY : 1 < Y) :
    gammaTwoTranslatedFrameCusp Y ⊆
      gammaTwoExplicitFrameFundamentalDomain := by
  intro g hg
  apply Set.mem_iUnion.2
  refine
    ⟨gammaTwoIdentityTransversalRepresentative, ?_⟩
  rw [gammaTwoIdentityRepresentative_inv_eq_deckFactor]
  change
    g ∈ gammaTwoIdentityDeckFactor •
      integralFrameFundamentalDomain
  exact
    Set.smul_set_mono
      (frameCuspRectangle_subset_integralFrameFundamentalDomain
        hY) hg

/-- Deck-translating the integral domain preserves pointwise
injectivity of the quotient projection. -/
theorem gammaTwoFrameQuotientMk_injOn_deckTranslateIntegralDomain
    (δ : GammaTwo) :
    Set.InjOn gammaTwoFrameQuotientMk
      (δ • integralFrameFundamentalDomain) := by
  intro g hg h hh hquot
  have hg0 :
      δ⁻¹ • g ∈ integralFrameFundamentalDomain := by
    exact
      (Set.mem_smul_set_iff_inv_smul_mem.mp hg)
  have hh0 :
      δ⁻¹ • h ∈ integralFrameFundamentalDomain := by
    exact
      (Set.mem_smul_set_iff_inv_smul_mem.mp hh)
  have hquot0 :
      gammaTwoFrameQuotientMk (δ⁻¹ • g) =
        gammaTwoFrameQuotientMk (δ⁻¹ • h) := by
    simpa only [gammaTwoFrameQuotientMk_smul] using hquot
  have heq0 :
      δ⁻¹ • g = δ⁻¹ • h :=
    gammaTwoFrameQuotientMk_injOn_integralFrameFundamentalDomain
      hg0 hh0 hquot0
  exact (smul_left_cancel_iff δ⁻¹).mp heq0

theorem gammaTwoFrameQuotientMk_injOn_translatedFrameCusp
    {Y : ℝ} (hY : 1 < Y) :
    Set.InjOn gammaTwoFrameQuotientMk
      (gammaTwoTranslatedFrameCusp Y) :=
  (gammaTwoFrameQuotientMk_injOn_deckTranslateIntegralDomain
      gammaTwoIdentityDeckFactor).mono
    (Set.smul_set_mono
      (frameCuspRectangle_subset_integralFrameFundamentalDomain
        hY))

/-- Quotient projection restricted to the translated cusp chart. -/
def gammaTwoCuspChartMap (Y : ℝ) :
    gammaTwoTranslatedFrameCusp Y →
      GammaTwoFrameQuotient :=
  fun g ↦ gammaTwoFrameQuotientMk g.1

theorem gammaTwoCuspChartMap_measurableEmbedding
    {Y : ℝ} (hY : 1 < Y) :
    MeasurableEmbedding (gammaTwoCuspChartMap Y) := by
  apply ContinuousOn.measurableEmbedding
    (measurableSet_gammaTwoTranslatedFrameCusp Y)
  · exact
      gammaTwoFrameQuotientMk_isCoveringMap.continuous.continuousOn
  · exact
      gammaTwoFrameQuotientMk_injOn_translatedFrameCusp hY

/-- Recover the ordinary frame height after undoing the fixed deck
translation. -/
def gammaTwoCuspChartHeight (Y : ℝ)
    (g : gammaTwoTranslatedFrameCusp Y) : ℝ :=
  realModularFrameHeight
    (gammaTwoIdentityDeckFactor⁻¹ • g.1)

theorem measurable_gammaTwoCuspChartHeight
    (Y : ℝ) :
    Measurable (gammaTwoCuspChartHeight Y) := by
  unfold gammaTwoCuspChartHeight
  exact
    measurable_realModularFrameHeight.comp
      (measurable_const_smul
        gammaTwoIdentityDeckFactor⁻¹)
        |>.comp measurable_subtype_coe

/-- A globally measurable quotient height obtained by extending the
ordinary height from the injective cusp chart and assigning zero
elsewhere. -/
def gammaTwoExplicitCuspHeight
    (Y : ℝ) : GammaTwoFrameQuotient → ℝ :=
  Function.extend (gammaTwoCuspChartMap Y)
    (gammaTwoCuspChartHeight Y) 0

theorem measurable_gammaTwoExplicitCuspHeight
    {Y : ℝ} (hY : 1 < Y) :
    Measurable (gammaTwoExplicitCuspHeight Y) := by
  exact
    (gammaTwoCuspChartMap_measurableEmbedding hY)
      |>.measurable_extend
        (measurable_gammaTwoCuspChartHeight Y)
        measurable_const

@[simp]
theorem gammaTwoExplicitCuspHeight_chart
    {Y : ℝ} (hY : 1 < Y)
    (g : gammaTwoTranslatedFrameCusp Y) :
    gammaTwoExplicitCuspHeight Y
        (gammaTwoCuspChartMap Y g) =
      gammaTwoCuspChartHeight Y g :=
  (gammaTwoCuspChartMap_measurableEmbedding hY).injective
    |>.extend_apply _ _ g

end

end HGAS.Modular
