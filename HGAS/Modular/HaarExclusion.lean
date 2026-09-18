import HGAS.Compactification.CentralSphere
import HGAS.Dynamics.CuspMeasureDivergence
import HGAS.Modular.ThetaAsymptotics
import Mathlib.Tactic

/-!
# The formal core of modular Haar exclusion

The projective slowdown used in the reduction must not turn an affine
invariant measure with modular Haar marginal into an interior invariant
probability.  The reason is a cusp divergence:

```
  |C_s(τ)| = s Im(τ) |θ₄(τ)|⁴  ≳  s Im(τ),
  |w_mod|⁻ᴹ                         ≳ |C_s(τ)|ᴹ,
  dμ_Haar                           ≍ dx dy dφ / y².
```

This file formalizes every part of that argument which is independent of
constructing the finite modular quotient:

* the canonical theta coordinate has the required uniform linear cusp
  growth, derived from the already proved limit `H₄(τ) → 1`;
* a coordinate in a central affine chart is bounded by the reciprocal of
  its chart weight;
* the general measure-theoretic theorem from
  `Dynamics.CuspMeasureDivergence` is specialized to a joining with a
  modular marginal.

The only quotient-specific input left as a visible theorem hypothesis is
the Iwasawa-coordinate measure inequality

```
  c • (1_{[Y,∞)}(y) y⁻² dy) ≤ height₊ μ_Haar.
```

Thus this module does not pretend that a modular quotient or its Haar
coordinate formula has already been constructed in Lean.
-/

noncomputable section

open Complex Filter MeasureTheory Set Topology UpperHalfPlane
open scoped ENNReal NNReal Real Topology

namespace HGAS.Modular

/-- The canonical weight-two coordinate used in the cusp argument.  On a
multiplier-trivial Iwasawa chart the modular solution has exactly this
coordinate, up to a unit-modulus multiplier which does not affect its
norm. -/
def canonicalHaarCuspCoordinate (s : ℝ) (τ : ℍ) : ℂ :=
  ((s * τ.im : ℝ) : ℂ) * H₄ τ

/-- The fourth theta power is uniformly bounded below by `1/2` above some
height.  Uniformity in the real part is built into Mathlib's
`atImInfty` filter and is exposed by `Analysis.eventually_atImInfty`. -/
theorem exists_cuspHeight_oneHalf_le_norm_H₄ :
    ∃ Y : ℝ, ∀ τ : ℍ, Y ≤ τ.im →
      (1 / 2 : ℝ) ≤ ‖H₄ τ‖ := by
  have hnorm :
      Tendsto (fun τ : ℍ ↦ ‖H₄ τ‖)
        atImInfty (𝓝 ‖(1 : ℂ)‖) :=
    H₄_tendsto_atImInfty.norm
  have hevent :
      ∀ᶠ τ : ℍ in atImInfty,
        (1 / 2 : ℝ) < ‖H₄ τ‖ :=
    hnorm.eventually
      (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < ‖(1 : ℂ)‖))
  obtain ⟨Y, hY⟩ :=
    HGAS.Analysis.eventually_atImInfty.mp hevent
  exact ⟨Y, fun τ hτ ↦ (hY τ hτ).le⟩

/-- The canonical weight-two coordinate grows at least linearly in cusp
height.  This is equation (10.9) of the written proof, with the harmless
choice of a possibly larger height threshold left implicit in `Y`. -/
theorem exists_cuspHeight_canonicalHaarCuspCoordinate_lower
    {s : ℝ} (hs : 0 < s) :
    ∃ Y : ℝ, ∀ τ : ℍ, Y ≤ τ.im →
      (s / 2) * τ.im ≤
        ‖canonicalHaarCuspCoordinate s τ‖ := by
  obtain ⟨Y, hY⟩ :=
    exists_cuspHeight_oneHalf_le_norm_H₄
  refine ⟨Y, fun τ hτ ↦ ?_⟩
  rw [canonicalHaarCuspCoordinate, norm_mul]
  have hnormReal :
      ‖((s * τ.im : ℝ) : ℂ)‖ = s * τ.im := by
    rw [ofReal_mul, norm_mul, norm_real, norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hs, abs_of_pos τ.im_pos]
  rw [hnormReal]
  calc
    (s / 2) * τ.im =
        (s * τ.im) * (1 / 2) := by ring
    _ ≤ (s * τ.im) * ‖H₄ τ‖ :=
      mul_le_mul_of_nonneg_left
        (hY τ hτ) (mul_nonneg hs.le τ.im_pos.le)

/-- Power form of the theta cusp estimate, truncated below the height at
which it is valid.  This is ready to compare with a reciprocal central
chart weight in the measure theorem. -/
theorem exists_cuspHeight_scaledPower_le_canonicalCoordinatePower
    {s : ℝ} (hs : 0 < s) (M : ℕ) :
    ∃ Y : ℝ, ∀ τ : ℍ,
      ENNReal.ofReal (s / 2) ^ M *
          Dynamics.cuspTailHeightPower Y M τ.im ≤
        ENNReal.ofReal ‖canonicalHaarCuspCoordinate s τ‖ ^ M := by
  obtain ⟨Y, hY⟩ :=
    exists_cuspHeight_canonicalHaarCuspCoordinate_lower hs
  refine ⟨Y, fun τ ↦ ?_⟩
  by_cases hτ : Y ≤ τ.im
  · have hcoord :
        ENNReal.ofReal ((s / 2) * τ.im) ≤
          ENNReal.ofReal
            ‖canonicalHaarCuspCoordinate s τ‖ :=
      ENNReal.ofReal_le_ofReal (hY τ hτ)
    have hpow :=
      pow_le_pow_left₀ bot_le hcoord M
    have hsdiv : 0 ≤ s / 2 := div_nonneg hs.le (by norm_num)
    have hprod : 0 ≤ (s / 2) * τ.im :=
      mul_nonneg hsdiv τ.im_pos.le
    simp only [Dynamics.cuspTailHeightPower,
      Set.indicator_of_mem
        (show τ.im ∈ Ici Y from hτ)]
    rw [
      Dynamics.cuspHeightPower,
      max_eq_left τ.im_pos.le,
      ← ENNReal.ofReal_pow hsdiv M,
      ← ENNReal.ofReal_mul (pow_nonneg hsdiv M),
      ← mul_pow,
      ENNReal.ofReal_pow hprod M]
    exact hpow
  · simp only [Dynamics.cuspTailHeightPower,
      Set.indicator_of_notMem
        (show τ.im ∉ Ici Y from hτ),
      mul_zero]
    exact bot_le

end HGAS.Modular

namespace HGAS

/-- A coordinate of a point on a central sphere has absolute value at most
one.  This elementary fact is the only place where the sphere equation is
used in the chart estimate below. -/
theorem abs_centralSphere_coordinate_le_one
    {n : ℕ} (q : CentralSphere n) (i : Fin n) :
    |q.1.1 i| ≤ 1 := by
  have hcoord :
      q.1.1 i ^ 2 ≤ normSq q.1.1 := by
    simp only [normSq, dot]
    simpa only [pow_two] using
      Finset.single_le_sum
        (fun j _ ↦ sq_nonneg (q.1.1 j))
        (Finset.mem_univ i)
  have hnorm : normSq q.1.1 ≤ 1 := by
    nlinarith [q.2, sq_nonneg q.1.2]
  have hsquare : q.1.1 i ^ 2 ≤ 1 := hcoord.trans hnorm
  nlinarith [sq_abs (q.1.1 i), abs_nonneg (q.1.1 i)]

/-- In a finite central chart, the norm of every affine coordinate
`x_i / w` is bounded above by `|w|⁻¹`. -/
theorem abs_centralChartCoordinate_le_inv_abs_weight
    {n : ℕ} (q : FiniteCentralChart n) (i : Fin n) :
    |centralChartCoordinate q i| ≤ |q.1.1.2|⁻¹ := by
  rw [centralChartCoordinate, abs_div, div_eq_mul_inv]
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right
      (abs_centralSphere_coordinate_le_one q.1 i)
      (inv_nonneg.mpr (abs_nonneg q.1.1.2))

/-- Raising the central-chart estimate to an integral power gives the
pointwise lower bound used for the reciprocal slowdown. -/
theorem centralChartCoordinate_power_le_invWeightPower
    {n M : ℕ} (q : FiniteCentralChart n) (i : Fin n) :
    ENNReal.ofReal |centralChartCoordinate q i| ^ M ≤
      ENNReal.ofReal |q.1.1.2|⁻¹ ^ M := by
  exact pow_le_pow_left₀ bot_le
    (ENNReal.ofReal_le_ofReal
      (abs_centralChartCoordinate_le_inv_abs_weight q i))
    M

end HGAS

namespace HGAS.Modular

/-- A sharply factored version of Haar exclusion.

`Q` is the modular quotient, `height` its cusp height, and `ν` the Haar
measure.  The hypothesis `hcusp` is exactly the unformalized
quotient/Iwasawa density statement.  `μ` may be any joining whatsoever
having modular marginal `ν`; no product structure is assumed.  The
pointwise hypothesis `hchart` packages the already elementary facts that
the modular theta coordinate grows like `κ y`, that the central chart
weight controls that coordinate, and that all other central weights are at
most one.

Under these explicit assumptions, the reciprocal projective slowdown has
infinite lower integral and hence cannot be normalized to an interior
time-changed probability. -/
theorem haarMarginal_reciprocalSlowdown_lintegral_eq_top
    {X Q : Type*} [MeasurableSpace X] [MeasurableSpace Q]
    (μ : Measure X) (ν : Measure Q)
    (proj : X → Q) (hproj : Measurable proj)
    (height : Q → ℝ) (hheight : Measurable height)
    (reciprocalSlowdown : X → ℝ≥0∞)
    (Y₀ Y : ℝ) (M : ℕ) (hM : 2 ≤ M)
    (c : ℝ≥0) (hc : c ≠ 0)
    (hcusp :
      c • Dynamics.cuspHeightMeasure Y₀ ≤
        Measure.map height ν)
    (hmarginal : Measure.map proj μ = ν)
    (κ : ℝ≥0) (hκ : κ ≠ 0)
    (hchart :
      ∀ᵐ x ∂μ,
        (κ : ℝ≥0∞) ^ M *
            Dynamics.cuspTailHeightPower Y M
              (height (proj x)) ≤
          reciprocalSlowdown x) :
    ∫⁻ x, reciprocalSlowdown x ∂μ = ∞ :=
  Dynamics.reciprocalSlowdown_lintegral_eq_top_of_scaled_cusp_tail
    μ ν proj hproj height hheight reciprocalSlowdown
    Y₀ Y M hM c hc hcusp hmarginal κ hκ hchart

end HGAS.Modular
