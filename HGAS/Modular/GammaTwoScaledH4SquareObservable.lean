import HGAS.Modular.GammaTwoH4SquareObservable
import Mathlib.Tactic

/-!
# Speed-normalized `H₄²` observables on the level-two frame quotient

The intrinsic quotient observable

```text
  q ↦ ‖H₄²_frame(q)‖^K
```

records the square of `height · ‖H₄‖`.  A unary trajectory moving on the
real-frame horocycle with signed speed `σ` has fourth-theta amplitude

```text
  ‖C‖ = |σ| · height · ‖H₄‖.
```

Consequently the observable which agrees exactly with `‖C‖^(2K)` is the
unscaled quotient observable multiplied by `|σ|^(2K)`.  This file packages
that harmless but essential normalization with a nonnegative scale
`a : ℝ≥0`.

The cusp lower bound is proved directly from the canonical cusp coordinate
at scale `a`; no constant is discarded.  Thus every nonzero scale has the
same divergent Haar integral when `K ≥ 1`.
-/

namespace HGAS.Modular

open Complex
open UpperHalfPlane hiding I
open scoped ENNReal NNReal

noncomputable section

/-- The speed-normalized power observable.  In applications
`a = |σ|`, where `σ` is the signed horocycle speed. -/
def gammaTwoScaledH4SquareNormPower
    (a : ℝ≥0) (K : ℕ) :
    C(GammaTwoFrameQuotient, ℝ) :=
  ⟨fun q ↦
      (a : ℝ) ^ (2 * K) *
        gammaTwoH4SquareNormPower K q,
    (continuous_const.pow (2 * K)).mul
      (gammaTwoH4SquareNormPower K).continuous⟩

@[simp]
theorem gammaTwoScaledH4SquareNormPower_apply
    (a : ℝ≥0) (K : ℕ)
    (q : GammaTwoFrameQuotient) :
    gammaTwoScaledH4SquareNormPower a K q =
      (a : ℝ) ^ (2 * K) *
        gammaTwoH4SquareNormPower K q :=
  rfl

theorem gammaTwoScaledH4SquareNormPower_nonneg
    (a : ℝ≥0) (K : ℕ)
    (q : GammaTwoFrameQuotient) :
    0 ≤ gammaTwoScaledH4SquareNormPower a K q :=
  mul_nonneg
    (pow_nonneg a.coe_nonneg (2 * K))
    (gammaTwoH4SquareNormPower_nonneg K q)

/-- On a representative frame, the scaled observable is the even power
of `a · height · ‖H₄‖`. -/
theorem gammaTwoScaledH4SquareNormPower_mk
    (a : ℝ≥0) (K : ℕ)
    (g : RealModularFrame) :
    gammaTwoScaledH4SquareNormPower a K
        (gammaTwoFrameQuotientMk g) =
      ((a : ℝ) * realModularFrameHeight g *
          ‖H₄ (realModularFrameBasePoint g)‖) ^
        (2 * K) := by
  rw [gammaTwoScaledH4SquareNormPower_apply,
    gammaTwoH4SquareNormPower_mk]
  rw [mul_pow]
  ring

/-- In the explicit cusp chart, the scaled quotient observable is exactly
the power of the canonical cusp coordinate at the same scale. -/
theorem gammaTwoScaledH4SquareNormPower_cuspChart
    (a : ℝ≥0) (K : ℕ) {Y : ℝ}
    (g : gammaTwoTranslatedFrameCusp Y) :
    gammaTwoScaledH4SquareNormPower a K
        (gammaTwoCuspChartMap Y g) =
      ‖canonicalHaarCuspCoordinate (a : ℝ)
          (realModularFrameBasePoint
            (gammaTwoIdentityDeckFactor⁻¹ • g.1))‖ ^
        (2 * K) := by
  rw [gammaTwoScaledH4SquareNormPower_apply,
    gammaTwoH4SquareNormPower_cuspChart]
  let τ : ℍ :=
    realModularFrameBasePoint
      (gammaTwoIdentityDeckFactor⁻¹ • g.1)
  rw [norm_canonicalHaarCuspCoordinate_one]
  rw [canonicalHaarCuspCoordinate,
    norm_mul, norm_real, Real.norm_eq_abs]
  have hprod : 0 ≤ (a : ℝ) * τ.im :=
    mul_nonneg a.coe_nonneg τ.im_pos.le
  rw [abs_of_nonneg hprod]
  change
    (a : ℝ) ^ (2 * K) *
        (τ.im * ‖H₄ τ‖) ^ (2 * K) =
      ((a : ℝ) * τ.im * ‖H₄ τ‖) ^ (2 * K)
  rw [mul_pow]
  ring

/-- The positive cusp coefficient `a/2`. -/
def gammaTwoScaledThetaCuspHalf
    (a : ℝ≥0) : ℝ≥0 :=
  a / 2

theorem gammaTwoScaledThetaCuspHalf_ne_zero
    {a : ℝ≥0} (ha : a ≠ 0) :
    gammaTwoScaledThetaCuspHalf a ≠ 0 := by
  exact div_ne_zero ha (by norm_num)

/-- Uniform cusp lower bound for the speed-normalized observable.

The threshold is enlarged to be positive so that outside the explicit
cusp chart the extended height is zero and the tail expression vanishes.
-/
theorem
    exists_gammaTwoScaledH4SquareNormPower_cuspLowerBound
    {Y : ℝ} (hY : 1 < Y)
    (a : ℝ≥0) (ha : a ≠ 0) (K : ℕ) :
    ∃ Ytail : ℝ, 0 < Ytail ∧
      ∀ q : GammaTwoFrameQuotient,
        (gammaTwoScaledThetaCuspHalf a : ℝ≥0∞) ^
              (2 * K) *
            HGAS.Dynamics.cuspTailHeightPower
              Ytail (2 * K)
              (gammaTwoExplicitCuspHeight Y q) ≤
          ENNReal.ofReal
            (gammaTwoScaledH4SquareNormPower a K q) := by
  have ha_nn : 0 < a :=
    bot_lt_iff_ne_bot.mpr ha
  have ha_pos : 0 < (a : ℝ) := by
    exact_mod_cast ha_nn
  obtain ⟨Y₀, hY₀⟩ :=
    exists_cuspHeight_scaledPower_le_canonicalCoordinatePower
      ha_pos (2 * K)
  let Ytail : ℝ := max Y₀ 1
  have hYtail_pos : 0 < Ytail :=
    zero_lt_one.trans_le (le_max_right Y₀ 1)
  have hcanonical :
      ∀ τ : ℍ,
        ENNReal.ofReal ((a : ℝ) / 2) ^ (2 * K) *
            HGAS.Dynamics.cuspTailHeightPower
              Ytail (2 * K) τ.im ≤
          ENNReal.ofReal
            ‖canonicalHaarCuspCoordinate (a : ℝ) τ‖ ^
              (2 * K) := by
    intro τ
    by_cases hτ : Ytail ≤ τ.im
    · have hτ₀ : Y₀ ≤ τ.im :=
        (le_max_left Y₀ 1).trans hτ
      have hold := hY₀ τ
      simpa only [
        HGAS.Dynamics.cuspTailHeightPower,
        Set.indicator_of_mem
          (show τ.im ∈ Set.Ici Ytail from hτ),
        Set.indicator_of_mem
          (show τ.im ∈ Set.Ici Y₀ from hτ₀)] using hold
    · simp only [
        HGAS.Dynamics.cuspTailHeightPower,
        Set.indicator_of_notMem
          (show τ.im ∉ Set.Ici Ytail from hτ),
        mul_zero]
      exact bot_le
  refine ⟨Ytail, hYtail_pos, ?_⟩
  intro q
  by_cases hq :
      ∃ g : gammaTwoTranslatedFrameCusp Y,
        gammaTwoCuspChartMap Y g = q
  · obtain ⟨g, rfl⟩ := hq
    let τ : ℍ :=
      realModularFrameBasePoint
        (gammaTwoIdentityDeckFactor⁻¹ • g.1)
    have hlower := hcanonical τ
    rw [gammaTwoExplicitCuspHeight_chart hY,
      gammaTwoScaledH4SquareNormPower_cuspChart]
    change
      (gammaTwoScaledThetaCuspHalf a : ℝ≥0∞) ^
              (2 * K) *
            HGAS.Dynamics.cuspTailHeightPower
              Ytail (2 * K) τ.im ≤
        ENNReal.ofReal
          (‖canonicalHaarCuspCoordinate (a : ℝ) τ‖ ^
            (2 * K))
    rw [ENNReal.ofReal_pow (norm_nonneg _) (2 * K)]
    have hscale :
        (gammaTwoScaledThetaCuspHalf a : ℝ≥0∞) =
          ENNReal.ofReal ((a : ℝ) / 2) := by
      rw [ENNReal.coe_nnreal_eq]
      rfl
    rw [hscale]
    exact hlower
  · have hheight :
        gammaTwoExplicitCuspHeight Y q = 0 := by
      unfold gammaTwoExplicitCuspHeight
      simpa using
        (Function.extend_apply'
          (f := gammaTwoCuspChartMap Y)
          (gammaTwoCuspChartHeight Y)
          (0 : GammaTwoFrameQuotient → ℝ) q hq)
    rw [hheight]
    simp only [HGAS.Dynamics.cuspTailHeightPower,
      Set.indicator_of_notMem
        (show (0 : ℝ) ∉ Set.Ici Ytail by
          simpa only [Set.mem_Ici, not_le] using hYtail_pos),
      mul_zero]
    exact bot_le

end

end HGAS.Modular
