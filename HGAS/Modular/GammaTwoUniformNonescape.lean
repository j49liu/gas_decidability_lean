import HGAS.Modular.GammaTwoCuspExcursionFamilyBound
import HGAS.Modular.GammaTwoPeriodicMassExclusion
import Mathlib.Tactic

/-!
# Uniform nonescape for nonperiodic level-two horocycles

This file proves the level-two instance of the classical cusp-nonescape
estimate.  The compact core is the explicit Mahler core from
`GammaTwoMahlerCompactCore`.  If a time-`t` frame lies outside that core,
some primitive lattice row is shorter than the cutoff `δ`; the
quantitative excursion theorem then bounds the total bad time by

```text
  B_g + 12 δ T.
```

After division by `T`, the initial term tends to zero.  Choosing `δ`
from the requested error tolerance gives one compact core, uniform over
all nonperiodic starting points.  The time at which the estimate begins
may depend on the starting point, exactly as in Hubbard--Miller
Proposition 12.
-/

namespace HGAS.Modular

open Filter Function _root_.MeasureTheory Set Topology
open scoped ENNReal MatrixGroups

noncomputable section

local instance gammaTwoFrameQuotientMetricSpaceForNonescape :
    MetricSpace GammaTwoFrameQuotient :=
  TopologicalSpace.metrizableSpaceMetric GammaTwoFrameQuotient

/-- The union of all primitive-row `δ`-short times for the frame `g`. -/
def gammaTwoPrimitiveBadTimeSet
    (δ : ℝ) (g : RealModularFrame) : Set ℝ :=
  ⋃ v : PrimitiveIntegralRow,
    primitiveRowShortTimes δ g v

/-- Leaving the Mahler compact core forces a short primitive row. -/
theorem horocycle_preimage_compl_mahlerCore_subset_badTimeSet
    {δ : ℝ} (hδ : 0 < δ)
    (g : RealModularFrame) :
    (fun t : ℝ ↦
      gammaTwoHorocycleFlow t
        (gammaTwoFrameQuotientMk g)) ⁻¹'
          (gammaTwoMahlerCompactCore δ)ᶜ ⊆
      gammaTwoPrimitiveBadTimeSet δ g := by
  intro t ht
  by_contra htbad
  have hlower :
      HasPrimitiveRowLowerBound δ
        (g * upperUnipotent t) := by
    intro v
    have hvnot :
        t ∉ primitiveRowShortTimes δ g v := by
      intro htv
      apply htbad
      exact mem_iUnion.mpr ⟨v, htv⟩
    simp only [primitiveRowShortTimes, mem_setOf_eq,
      not_lt] at hvnot
    exact hvnot
  apply ht
  change
    gammaTwoFrameQuotientMk
        (g * upperUnipotent t) ∈
      gammaTwoMahlerCompactCore δ
  exact
    gammaTwoFrameQuotientMk_mem_mahlerCompactCore
      hδ (g * upperUnipotent t) hlower

/-- The disjoint-excursion estimate, reindexed over all primitive rows. -/
theorem exists_finite_initialCost_volume_badTimeSet_le
    {δ : ℝ} (hδ : 0 < δ)
    (hδle : δ ≤ 1 / 6)
    (g : RealModularFrame)
    (hnonperiodic :
      ¬ IsPeriodicHorocyclePoint 1
        (gammaTwoFrameQuotientMk g)) :
    ∃ B : ℝ≥0∞, B < ∞ ∧
      ∀ T : ℝ,
        volume
            (gammaTwoPrimitiveBadTimeSet δ g ∩
              Ioc 0 T) ≤
          B + ENNReal.ofReal (12 * δ) *
            ENNReal.ofReal T := by
  obtain ⟨B, hBfinite, hB⟩ :=
    exists_finite_initialCost_volume_iUnion_shortTimes_le
      hδ hδle g
  refine ⟨B, hBfinite, ?_⟩
  intro T
  have h := hB T
  rw [gammaTwoPrimitiveBadTimeSet,
    ← iUnion_positivePrimitiveRowShortTimes
      g hnonperiodic δ]
  simpa only [iUnion_inter] using h

/-- Evaluation of an occupation probability on a measurable set as
normalized Lebesgue time in its orbit preimage. -/
theorem orbitOccupationProbability_apply
    (q : GammaTwoFrameQuotient)
    {T : ℝ} (hT : 0 < T)
    (A : Set GammaTwoFrameQuotient)
    (hA : MeasurableSet A) :
    (HGAS.Dynamics.orbitOccupationProbability
        gammaTwoHorocycleFlow q T hT :
          Measure GammaTwoFrameQuotient) A =
      (ENNReal.ofReal T)⁻¹ *
        volume
          ((fun t : ℝ ↦ gammaTwoHorocycleFlow t q) ⁻¹' A ∩
            Ioc 0 T) := by
  have hmeas :
      Measurable
        (fun t : ℝ ↦ gammaTwoHorocycleFlow t q) :=
    (gammaTwoHorocycleFlow.continuous
      continuous_id continuous_const).measurable
  rw [HGAS.Dynamics.orbitOccupationProbability,
    ProbabilityMeasure.toMeasure_map,
    Measure.map_apply hmeas hA]
  simp only [HGAS.Dynamics.positiveIntervalProbability,
    ProbabilityMeasure.coe_mk, Measure.smul_apply,
    smul_eq_mul]
  have hpre :
      MeasurableSet
        ((fun t : ℝ ↦ gammaTwoHorocycleFlow t q) ⁻¹' A) :=
    hA.preimage hmeas
  rw [Measure.restrict_apply hpre]

/-- Finite-time occupation outside the compact core is bounded by the
normalized primitive-row bad-time estimate. -/
theorem orbitOccupationProbability_compl_mahlerCore_le
    {δ : ℝ} (hδ : 0 < δ)
    (g : RealModularFrame)
    {T : ℝ} (hT : 0 < T)
    {B : ℝ≥0∞}
    (hbad :
      volume
          (gammaTwoPrimitiveBadTimeSet δ g ∩
            Ioc 0 T) ≤
        B + ENNReal.ofReal (12 * δ) *
          ENNReal.ofReal T) :
    (HGAS.Dynamics.orbitOccupationProbability
        gammaTwoHorocycleFlow
        (gammaTwoFrameQuotientMk g) T hT :
          Measure GammaTwoFrameQuotient)
        (gammaTwoMahlerCompactCore δ)ᶜ ≤
      (ENNReal.ofReal T)⁻¹ *
        (B + ENNReal.ofReal (12 * δ) *
          ENNReal.ofReal T) := by
  rw [orbitOccupationProbability_apply
    (gammaTwoFrameQuotientMk g) hT
    (gammaTwoMahlerCompactCore δ)ᶜ
    (isCompact_gammaTwoMahlerCompactCore δ).isClosed.measurableSet.compl]
  gcongr
  exact
    (measure_mono
      (inter_subset_inter_left (Ioc 0 T)
        (horocycle_preimage_compl_mahlerCore_subset_badTimeSet
          hδ g))).trans hbad

/-- Real-valued form of the preceding estimate. -/
theorem orbitOccupationProbability_compl_mahlerCore_le_ofReal
    {δ : ℝ} (hδ : 0 < δ)
    (g : RealModularFrame)
    {T : ℝ} (hT : 0 < T)
    {B : ℝ≥0∞} (hBfinite : B < ∞)
    (hbad :
      volume
          (gammaTwoPrimitiveBadTimeSet δ g ∩
            Ioc 0 T) ≤
        B + ENNReal.ofReal (12 * δ) *
          ENNReal.ofReal T) :
    (HGAS.Dynamics.orbitOccupationProbability
        gammaTwoHorocycleFlow
        (gammaTwoFrameQuotientMk g) T hT :
          Measure GammaTwoFrameQuotient)
        (gammaTwoMahlerCompactCore δ)ᶜ ≤
      ENNReal.ofReal (B.toReal / T + 12 * δ) := by
  have hbase :=
    orbitOccupationProbability_compl_mahlerCore_le
      hδ g hT hbad
  calc
    (HGAS.Dynamics.orbitOccupationProbability
        gammaTwoHorocycleFlow
        (gammaTwoFrameQuotientMk g) T hT :
          Measure GammaTwoFrameQuotient)
        (gammaTwoMahlerCompactCore δ)ᶜ ≤
        (ENNReal.ofReal T)⁻¹ *
          (B + ENNReal.ofReal (12 * δ) *
            ENNReal.ofReal T) :=
      hbase
    _ = ENNReal.ofReal (B.toReal / T + 12 * δ) := by
      rw [← ENNReal.ofReal_toReal hBfinite.ne]
      rw [← ENNReal.ofReal_mul (by positivity :
        0 ≤ 12 * δ)]
      rw [← ENNReal.ofReal_add
        ENNReal.toReal_nonneg
        (mul_nonneg (by positivity) hT.le)]
      rw [← ENNReal.ofReal_inv_of_pos hT]
      rw [← ENNReal.ofReal_mul
        (inv_nonneg.mpr hT.le)]
      congr 1
      field_simp
      rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]

/-- **Uniform nonescape theorem for nonperiodic `Γ(2)` horocycles.**

For every positive error tolerance, one explicit compact Mahler core
works for every nonperiodic starting point. -/
theorem gammaTwoUniformNonperiodicRealOccupationNonescape :
    GammaTwoUniformNonperiodicRealOccupationNonescape := by
  intro ε hε
  by_cases hεtop : ε = ∞
  · refine ⟨∅, isCompact_empty, ?_⟩
    intro q hq T hTpos hTtop
    filter_upwards []
    intro j
    rw [hεtop]
    exact le_top
  · let e : ℝ := ε.toReal
    have he : 0 < e :=
      ENNReal.toReal_pos hε.ne' hεtop
    let δ : ℝ := min (1 / 12 : ℝ) (e / 48)
    have hδ : 0 < δ := by
      exact lt_min (by norm_num) (div_pos he (by norm_num))
    have hδle : δ ≤ (1 / 6 : ℝ) := by
      exact (min_le_left _ _).trans (by norm_num)
    refine
      ⟨gammaTwoMahlerCompactCore δ,
        isCompact_gammaTwoMahlerCompactCore δ, ?_⟩
    intro q hq T hTpos hTtop
    induction q using Quotient.inductionOn with
    | _ g =>
        obtain ⟨B, hBfinite, hB⟩ :=
          exists_finite_initialCost_volume_badTimeSet_le
            hδ hδle g hq
        let L : ℝ := 4 * B.toReal / e
        have hevent :
            ∀ᶠ j in atTop, L ≤ T j :=
          hTtop.eventually (eventually_ge_atTop L)
        filter_upwards [hevent] with j hj
        have hestimate :=
          orbitOccupationProbability_compl_mahlerCore_le_ofReal
            hδ g (hTpos j) hBfinite (hB (T j))
        apply hestimate.trans
        rw [← ENNReal.ofReal_toReal hεtop]
        apply ENNReal.ofReal_le_ofReal
        have hfour :
            4 * B.toReal ≤ T j * e := by
          apply (div_le_iff₀ he).mp
          simpa only [L] using hj
        have hBover :
            B.toReal / T j ≤ e / 4 := by
          apply (div_le_iff₀ (hTpos j)).mpr
          nlinarith
        have hδe : 12 * δ ≤ e / 4 := by
          have hmin := min_le_right
            (1 / 12 : ℝ) (e / 48)
          dsimp only [δ]
          nlinarith
        linarith

/-- Consequently, every nonperiodic occupation limit has the uniformly
tight family of positive-geodesic renormalizations required by the
periodic-mass exclusion argument. -/
theorem
    gammaTwoNonperiodicOccupationLimitRenormalizationTightness_unconditional :
    GammaTwoNonperiodicOccupationLimitRenormalizationTightness :=
  gammaTwoNonperiodicOccupationLimitRenormalizationTightness_of_uniformNonescape
    gammaTwoUniformNonperiodicRealOccupationNonescape

/-- The corrected Hubbard--Miller periodic-mass exclusion conclusion,
now with no remaining nonescape hypothesis. -/
theorem
    gammaTwoNonperiodicOccupationLimitsAvoidPeriodic_unconditional :
    GammaTwoNonperiodicOccupationLimitsAvoidPeriodic :=
  gammaTwoNonperiodicOccupationLimitsAvoidPeriodic_of_nonescape
    gammaTwoNonperiodicOccupationLimitRenormalizationTightness_unconditional

end

end HGAS.Modular
