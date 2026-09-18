import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic

/-!
# Cusp tails and divergence after taking a marginal

This file isolates the measure-theoretic part of the ``Haar exclusion''
argument.  No modular quotient is mentioned here.  The one-dimensional
model of a finite-volume cusp has height coordinate `y` and density
`y⁻² dy`.  Its moments of every integral order at least two diverge.

The second half of the file records the two operations used in the
application:

* a positive amount of cusp measure below a height marginal forces the
  same divergent height moment for the marginal;
* if a measure on a joining has that marginal, then any observable which
  dominates the pulled-back height moment also has infinite lower
  integral.

The latter statement is precisely the Tonelli/pushforward step in a form
which applies to arbitrary joinings.  The quotient-specific assertion that
Haar measure has the displayed cusp-coordinate density is deliberately a
hypothesis of the eventual modular theorem, not an implicit axiom.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal

namespace HGAS.Dynamics

/-- The nonnegative integral power of a real height.  The `max` makes this
globally measurable while agreeing with `y^M` throughout every positive
cusp. -/
def cuspHeightPower (M : ℕ) (y : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((max y 0) ^ M)

/-- The height moment restricted to a specified cusp tail.  Outside the
tail it vanishes, which is essential when a cusp-coordinate estimate is
only valid above a threshold. -/
def cuspTailHeightPower (Y : ℝ) (M : ℕ) (y : ℝ) : ℝ≥0∞ :=
  (Ici Y).indicator (cuspHeightPower M) y

/-- The one-dimensional height marginal of the standard cusp density
`dy / y²`, restricted to heights at least `Y`.  It is not normalized:
normalization is irrelevant for divergence. -/
def cuspHeightMeasure (Y : ℝ) : Measure ℝ :=
  (volume.restrict (Ici Y)).withDensity
    (fun y ↦ ENNReal.ofReal ((y ^ 2)⁻¹))

instance instSFiniteCuspHeightMeasure (Y : ℝ) :
    SFinite (cuspHeightMeasure Y) := by
  unfold cuspHeightMeasure
  infer_instance

/-- A standard cusp box: `A` packages all bounded transverse variables
(for example `x`, the compact rotation angle, and finitely many labels),
while the second coordinate is height. -/
def cuspBoxMeasure
    {A : Type*} [MeasurableSpace A]
    (σ : Measure A) (Y : ℝ) : Measure (A × ℝ) :=
  σ.prod (cuspHeightMeasure Y)

/-- The height marginal of a standard cusp box is exactly its transverse
mass times `dy/y²`. -/
theorem map_snd_cuspBoxMeasure
    {A : Type*} [MeasurableSpace A]
    (σ : Measure A) (Y : ℝ) :
    Measure.map Prod.snd (cuspBoxMeasure σ Y) =
      (σ univ) • cuspHeightMeasure Y := by
  exact Measure.map_snd_prod

/-- With normalized transverse variables, the standard cusp box has
exactly the canonical cusp-height marginal. -/
theorem map_snd_cuspBoxMeasure_of_probability
    {A : Type*} [MeasurableSpace A]
    (σ : Measure A) [IsProbabilityMeasure σ]
    (Y : ℝ) :
    Measure.map Prod.snd (cuspBoxMeasure σ Y) =
      cuspHeightMeasure Y := by
  rw [map_snd_cuspBoxMeasure, measure_univ, one_smul]

/-- A positive constant multiple of a normalized cusp box produces the
same constant multiple of the cusp-height marginal.  This is the exact
product-coordinate calculation behind the abstract `hcusp` hypothesis. -/
theorem map_snd_smul_cuspBoxMeasure_of_probability
    {A : Type*} [MeasurableSpace A]
    (σ : Measure A) [IsProbabilityMeasure σ]
    (Y : ℝ) (c : ℝ≥0) :
    Measure.map Prod.snd (c • cuspBoxMeasure σ Y) =
      c • cuspHeightMeasure Y := by
  rw [Measure.map_smul,
    map_snd_cuspBoxMeasure_of_probability]

theorem measurable_cuspHeightPower (M : ℕ) :
    Measurable (cuspHeightPower M) := by
  unfold cuspHeightPower
  fun_prop

theorem measurable_cuspTailHeightPower (Y : ℝ) (M : ℕ) :
    Measurable (cuspTailHeightPower Y M) := by
  exact (measurable_cuspHeightPower M).indicator measurableSet_Ici

theorem measurable_cuspHeightDensity :
    Measurable (fun y : ℝ ↦ ENNReal.ofReal ((y ^ 2)⁻¹)) := by
  fun_prop

/-- Every moment of integral order at least two diverges against the
standard cusp height measure. -/
theorem lintegral_cuspHeightPower_cuspHeightMeasure_eq_top
    (Y : ℝ) (M : ℕ) (hM : 2 ≤ M) :
    ∫⁻ y, cuspHeightPower M y ∂cuspHeightMeasure Y = ∞ := by
  rw [cuspHeightMeasure,
    lintegral_withDensity_eq_lintegral_mul
      (volume.restrict (Ici Y))
      measurable_cuspHeightDensity
      (measurable_cuspHeightPower M)]
  let A : ℝ := max Y 1
  have hA_one : 1 ≤ A := le_max_right _ _
  have hA_Y : Y ≤ A := le_max_left _ _
  have hminorant :
      (Ici A).indicator (fun _ : ℝ ↦ (1 : ℝ≥0∞)) ≤
        fun y ↦
          ENNReal.ofReal ((y ^ 2)⁻¹) *
            cuspHeightPower M y := by
    intro y
    by_cases hy : y ∈ Ici A
    · rw [Set.indicator_of_mem hy]
      have hy_one : 1 ≤ y := hA_one.trans hy
      have hy_pos : 0 < y := zero_lt_one.trans_le hy_one
      have hpow : y ^ 2 ≤ y ^ M :=
        pow_le_pow_right₀ hy_one (by omega)
      have hinv_mul :
          1 ≤ (y ^ 2)⁻¹ * y ^ M := by
        rw [one_le_inv_mul₀ (sq_pos_of_pos hy_pos)]
        exact hpow
      change
        1 ≤ ENNReal.ofReal ((y ^ 2)⁻¹) *
          ENNReal.ofReal ((max y 0) ^ M)
      rw [max_eq_left hy_pos.le,
        ← ENNReal.ofReal_mul (by positivity),
        ENNReal.one_le_ofReal]
      exact hinv_mul
    · rw [Set.indicator_of_notMem hy]
      exact bot_le
  have htail :
      (∫⁻ y, (Ici A).indicator
          (fun _ : ℝ ↦ (1 : ℝ≥0∞)) y
          ∂(volume.restrict (Ici Y))) = ∞ := by
    rw [lintegral_indicator measurableSet_Ici]
    simp only [lintegral_const, Measure.restrict_apply_univ,
      one_mul]
    rw [Measure.restrict_apply measurableSet_Ici,
      inter_eq_self_of_subset_left (Ici_subset_Ici.mpr hA_Y)]
    exact Real.volume_Ici
  apply top_unique
  calc
    ∞ = ∫⁻ y, (Ici A).indicator
          (fun _ : ℝ ↦ (1 : ℝ≥0∞)) y
          ∂(volume.restrict (Ici Y)) := htail.symm
    _ ≤ ∫⁻ y,
          ENNReal.ofReal ((y ^ 2)⁻¹) *
            cuspHeightPower M y
          ∂(volume.restrict (Ici Y)) :=
      lintegral_mono hminorant

/-- Truncating a height moment below any finite threshold does not affect
its cusp divergence.  This is the version which directly matches an
eventual theta asymptotic. -/
theorem lintegral_cuspTailHeightPower_cuspHeightMeasure_eq_top
    (Y₀ Y : ℝ) (M : ℕ) (hM : 2 ≤ M) :
    ∫⁻ y, cuspTailHeightPower Y M y
      ∂cuspHeightMeasure Y₀ = ∞ := by
  rw [cuspHeightMeasure,
    lintegral_withDensity_eq_lintegral_mul
      (volume.restrict (Ici Y₀))
      measurable_cuspHeightDensity
      (measurable_cuspTailHeightPower Y M)]
  let A : ℝ := max (max Y₀ Y) 1
  have hA_one : 1 ≤ A := le_max_right _ _
  have hA_Y₀ : Y₀ ≤ A :=
    (le_max_left Y₀ Y).trans (le_max_left _ _)
  have hA_Y : Y ≤ A :=
    (le_max_right Y₀ Y).trans (le_max_left _ _)
  have hminorant :
      (Ici A).indicator (fun _ : ℝ ↦ (1 : ℝ≥0∞)) ≤
        fun y ↦
          ENNReal.ofReal ((y ^ 2)⁻¹) *
            cuspTailHeightPower Y M y := by
    intro y
    by_cases hy : y ∈ Ici A
    · rw [Set.indicator_of_mem hy]
      have hy_one : 1 ≤ y := hA_one.trans hy
      have hy_pos : 0 < y := zero_lt_one.trans_le hy_one
      have hy_Y : y ∈ Ici Y := hA_Y.trans hy
      have hpow : y ^ 2 ≤ y ^ M :=
        pow_le_pow_right₀ hy_one (by omega)
      have hinv_mul :
          1 ≤ (y ^ 2)⁻¹ * y ^ M := by
        rw [one_le_inv_mul₀ (sq_pos_of_pos hy_pos)]
        exact hpow
      change
        1 ≤ ENNReal.ofReal ((y ^ 2)⁻¹) *
          (Ici Y).indicator
            (fun z ↦ ENNReal.ofReal ((max z 0) ^ M)) y
      rw [Set.indicator_of_mem hy_Y]
      rw [max_eq_left hy_pos.le,
        ← ENNReal.ofReal_mul (by positivity),
        ENNReal.one_le_ofReal]
      exact hinv_mul
    · rw [Set.indicator_of_notMem hy]
      exact bot_le
  have htail :
      (∫⁻ y, (Ici A).indicator
          (fun _ : ℝ ↦ (1 : ℝ≥0∞)) y
          ∂(volume.restrict (Ici Y₀))) = ∞ := by
    rw [lintegral_indicator measurableSet_Ici]
    simp only [lintegral_const, Measure.restrict_apply_univ,
      one_mul]
    rw [Measure.restrict_apply measurableSet_Ici,
      inter_eq_self_of_subset_left
        (Ici_subset_Ici.mpr hA_Y₀)]
    exact Real.volume_Ici
  apply top_unique
  calc
    ∞ = ∫⁻ y, (Ici A).indicator
          (fun _ : ℝ ↦ (1 : ℝ≥0∞)) y
          ∂(volume.restrict (Ici Y₀)) := htail.symm
    _ ≤ ∫⁻ y,
          ENNReal.ofReal ((y ^ 2)⁻¹) *
            cuspTailHeightPower Y M y
          ∂(volume.restrict (Ici Y₀)) :=
      lintegral_mono hminorant

/-- A positive scalar multiple of the standard cusp height measure still
has divergent moments. -/
theorem lintegral_cuspHeightPower_smul_cuspHeightMeasure_eq_top
    (Y : ℝ) (M : ℕ) (hM : 2 ≤ M)
    (c : ℝ≥0) (hc : c ≠ 0) :
    ∫⁻ y, cuspHeightPower M y
      ∂(c • cuspHeightMeasure Y) = ∞ := by
  rw [lintegral_smul_measure,
    lintegral_cuspHeightPower_cuspHeightMeasure_eq_top Y M hM]
  rw [ENNReal.smul_top, if_neg hc]

/-- A height marginal which dominates a positive standard cusp tail has
an infinite height moment.  This is the exact interface needed from an
Iwasawa-coordinate formula for Haar measure. -/
theorem lintegral_cuspHeightPower_eq_top_of_cusp_marginal
    {Q : Type*} [MeasurableSpace Q]
    (ν : Measure Q) (height : Q → ℝ)
    (hheight : Measurable height)
    (Y : ℝ) (M : ℕ) (hM : 2 ≤ M)
    (c : ℝ≥0) (hc : c ≠ 0)
    (hcusp :
      c • cuspHeightMeasure Y ≤ Measure.map height ν) :
    ∫⁻ q, cuspHeightPower M (height q) ∂ν = ∞ := by
  have hdiv :
      ∫⁻ y, cuspHeightPower M y
        ∂(c • cuspHeightMeasure Y) = ∞ :=
    lintegral_cuspHeightPower_smul_cuspHeightMeasure_eq_top
      Y M hM c hc
  have hmono :
      (∫⁻ y, cuspHeightPower M y
          ∂(c • cuspHeightMeasure Y)) ≤
        ∫⁻ y, cuspHeightPower M y
          ∂Measure.map height ν :=
    lintegral_mono' hcusp le_rfl
  rw [lintegral_map (measurable_cuspHeightPower M) hheight] at hmono
  exact top_unique (hdiv ▸ hmono)

/-- Multiplying a cusp moment by any positive finite constant does not
restore integrability.  Keeping the scale explicit is useful because the
theta-coordinate lower bound has the form `|C| ≥ κ y` with an arbitrary
`κ > 0`. -/
theorem lintegral_scaledCuspHeightPower_eq_top_of_cusp_marginal
    {Q : Type*} [MeasurableSpace Q]
    (ν : Measure Q) (height : Q → ℝ)
    (hheight : Measurable height)
    (Y : ℝ) (M : ℕ) (hM : 2 ≤ M)
    (c : ℝ≥0) (hc : c ≠ 0)
    (hcusp :
      c • cuspHeightMeasure Y ≤ Measure.map height ν)
    (κ : ℝ≥0) (hκ : κ ≠ 0) :
    ∫⁻ q,
        (κ : ℝ≥0∞) ^ M *
          cuspHeightPower M (height q) ∂ν = ∞ := by
  have hpower :
      Measurable (fun q ↦ cuspHeightPower M (height q)) :=
    (measurable_cuspHeightPower M).comp hheight
  rw [lintegral_const_mul _ hpower,
    lintegral_cuspHeightPower_eq_top_of_cusp_marginal
      ν height hheight Y M hM c hc hcusp]
  exact ENNReal.mul_top (pow_ne_zero M (ENNReal.coe_ne_zero.mpr hκ))

/-- Cusp-marginal divergence for a scaled moment which vanishes below the
threshold where the chart estimate is known. -/
theorem lintegral_scaledCuspTailHeightPower_eq_top_of_cusp_marginal
    {Q : Type*} [MeasurableSpace Q]
    (ν : Measure Q) (height : Q → ℝ)
    (hheight : Measurable height)
    (Y₀ Y : ℝ) (M : ℕ) (hM : 2 ≤ M)
    (c : ℝ≥0) (hc : c ≠ 0)
    (hcusp :
      c • cuspHeightMeasure Y₀ ≤ Measure.map height ν)
    (κ : ℝ≥0) (hκ : κ ≠ 0) :
    ∫⁻ q,
        (κ : ℝ≥0∞) ^ M *
          cuspTailHeightPower Y M (height q) ∂ν = ∞ := by
  have htail :
      ∫⁻ y, cuspTailHeightPower Y M y
        ∂(c • cuspHeightMeasure Y₀) = ∞ := by
    rw [lintegral_smul_measure,
      lintegral_cuspTailHeightPower_cuspHeightMeasure_eq_top
        Y₀ Y M hM,
      ENNReal.smul_top, if_neg hc]
  have hmono :
      (∫⁻ y, cuspTailHeightPower Y M y
          ∂(c • cuspHeightMeasure Y₀)) ≤
        ∫⁻ y, cuspTailHeightPower Y M y
          ∂Measure.map height ν :=
    lintegral_mono' hcusp le_rfl
  rw [lintegral_map
    (measurable_cuspTailHeightPower Y M) hheight] at hmono
  have hbase :
      ∫⁻ q, cuspTailHeightPower Y M (height q) ∂ν = ∞ :=
    top_unique (htail ▸ hmono)
  have hpower :
      Measurable
        (fun q ↦ cuspTailHeightPower Y M (height q)) :=
    (measurable_cuspTailHeightPower Y M).comp hheight
  rw [lintegral_const_mul _ hpower, hbase]
  exact ENNReal.mul_top
    (pow_ne_zero M (ENNReal.coe_ne_zero.mpr hκ))

/-- Divergence passes from a marginal to every joining.  More precisely,
if `π` has marginal `ν`, and `F` dominates the pullback of a divergent
nonnegative observable `G`, then `F` has infinite lower integral.

This is the measure-theoretic content usually summarized as “Tonelli shows
the same divergence for every joining”.  No product or disintegration
hypothesis is needed: the equality of the marginal is exactly what the
argument uses. -/
theorem lintegral_eq_top_of_marginal_and_ae_le
    {X Q : Type*} [MeasurableSpace X] [MeasurableSpace Q]
    (μ : Measure X) (ν : Measure Q)
    (π : X → Q) (hπ : Measurable π)
    (G : Q → ℝ≥0∞) (hG : Measurable G)
    (F : X → ℝ≥0∞)
    (hmarginal : Measure.map π μ = ν)
    (hbound : ∀ᵐ x ∂μ, G (π x) ≤ F x)
    (hdiv : ∫⁻ q, G q ∂ν = ∞) :
    ∫⁻ x, F x ∂μ = ∞ := by
  apply top_unique
  calc
    ∞ = ∫⁻ q, G q ∂ν := hdiv.symm
    _ = ∫⁻ x, G (π x) ∂μ := by
      rw [← hmarginal, lintegral_map hG hπ]
    _ ≤ ∫⁻ x, F x ∂μ := lintegral_mono_ae hbound

/-- An infinite lower integral cannot be represented by a finite
nonnegative normalizing constant.  This is the final contradiction with
the reciprocal-density time-change constructor. -/
theorem no_nnreal_normalizingConstant_of_lintegral_eq_top
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (F : X → ℝ≥0∞)
    (hdiv : ∫⁻ x, F x ∂μ = ∞) :
    ¬ ∃ Z : ℝ≥0, ∫⁻ x, F x ∂μ = (Z : ℝ≥0∞) := by
  rintro ⟨Z, hZ⟩
  rw [hdiv] at hZ
  exact ENNReal.top_ne_coe hZ

/-- The complete abstract cusp-exclusion theorem: a cusp density lower
bound for the marginal and a pointwise chart-coordinate lower bound imply
that the reciprocal slowdown is nonintegrable on every joining. -/
theorem reciprocalSlowdown_lintegral_eq_top_of_cusp_marginal
    {X Q : Type*} [MeasurableSpace X] [MeasurableSpace Q]
    (μ : Measure X) (ν : Measure Q)
    (π : X → Q) (hπ : Measurable π)
    (height : Q → ℝ) (hheight : Measurable height)
    (reciprocalSlowdown : X → ℝ≥0∞)
    (Y : ℝ) (M : ℕ) (hM : 2 ≤ M)
    (c : ℝ≥0) (hc : c ≠ 0)
    (hcusp :
      c • cuspHeightMeasure Y ≤ Measure.map height ν)
    (hmarginal : Measure.map π μ = ν)
    (hchart :
      ∀ᵐ x ∂μ,
        cuspHeightPower M (height (π x)) ≤
          reciprocalSlowdown x) :
    ∫⁻ x, reciprocalSlowdown x ∂μ = ∞ := by
  apply lintegral_eq_top_of_marginal_and_ae_le
    μ ν π hπ
    (fun q ↦ cuspHeightPower M (height q))
    ((measurable_cuspHeightPower M).comp hheight)
    reciprocalSlowdown hmarginal hchart
  exact lintegral_cuspHeightPower_eq_top_of_cusp_marginal
    ν height hheight Y M hM c hc hcusp

/-- Scaled version of `reciprocalSlowdown_lintegral_eq_top_of_cusp_marginal`.
It is the form used by the weight-two theta coordinate, whose cusp lower
bound contains a positive scale depending on the modular first integral. -/
theorem reciprocalSlowdown_lintegral_eq_top_of_scaled_cusp_marginal
    {X Q : Type*} [MeasurableSpace X] [MeasurableSpace Q]
    (μ : Measure X) (ν : Measure Q)
    (π : X → Q) (hπ : Measurable π)
    (height : Q → ℝ) (hheight : Measurable height)
    (reciprocalSlowdown : X → ℝ≥0∞)
    (Y : ℝ) (M : ℕ) (hM : 2 ≤ M)
    (c : ℝ≥0) (hc : c ≠ 0)
    (hcusp :
      c • cuspHeightMeasure Y ≤ Measure.map height ν)
    (hmarginal : Measure.map π μ = ν)
    (κ : ℝ≥0) (hκ : κ ≠ 0)
    (hchart :
      ∀ᵐ x ∂μ,
        (κ : ℝ≥0∞) ^ M *
            cuspHeightPower M (height (π x)) ≤
          reciprocalSlowdown x) :
    ∫⁻ x, reciprocalSlowdown x ∂μ = ∞ := by
  apply lintegral_eq_top_of_marginal_and_ae_le
    μ ν π hπ
    (fun q ↦
      (κ : ℝ≥0∞) ^ M *
        cuspHeightPower M (height q))
    (measurable_const.mul
      ((measurable_cuspHeightPower M).comp hheight))
    reciprocalSlowdown hmarginal hchart
  exact
    lintegral_scaledCuspHeightPower_eq_top_of_cusp_marginal
      ν height hheight Y M hM c hc hcusp κ hκ

/-- Fully local cusp version: the pointwise chart estimate is required
only above `Y`, because the comparison observable is zero below `Y`. -/
theorem reciprocalSlowdown_lintegral_eq_top_of_scaled_cusp_tail
    {X Q : Type*} [MeasurableSpace X] [MeasurableSpace Q]
    (μ : Measure X) (ν : Measure Q)
    (π : X → Q) (hπ : Measurable π)
    (height : Q → ℝ) (hheight : Measurable height)
    (reciprocalSlowdown : X → ℝ≥0∞)
    (Y₀ Y : ℝ) (M : ℕ) (hM : 2 ≤ M)
    (c : ℝ≥0) (hc : c ≠ 0)
    (hcusp :
      c • cuspHeightMeasure Y₀ ≤ Measure.map height ν)
    (hmarginal : Measure.map π μ = ν)
    (κ : ℝ≥0) (hκ : κ ≠ 0)
    (hchart :
      ∀ᵐ x ∂μ,
        (κ : ℝ≥0∞) ^ M *
            cuspTailHeightPower Y M (height (π x)) ≤
          reciprocalSlowdown x) :
    ∫⁻ x, reciprocalSlowdown x ∂μ = ∞ := by
  apply lintegral_eq_top_of_marginal_and_ae_le
    μ ν π hπ
    (fun q ↦
      (κ : ℝ≥0∞) ^ M *
        cuspTailHeightPower Y M (height q))
    (measurable_const.mul
      ((measurable_cuspTailHeightPower Y M).comp hheight))
    reciprocalSlowdown hmarginal hchart
  exact
    lintegral_scaledCuspTailHeightPower_eq_top_of_cusp_marginal
      ν height hheight Y₀ Y M hM c hc hcusp κ hκ

end HGAS.Dynamics
