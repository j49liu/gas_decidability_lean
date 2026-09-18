import HGAS.Dynamics.ContinuousInfiniteIntegralCompactMinorants
import HGAS.Dynamics.GenericUnboundedClockContradiction
import HGAS.Modular.GammaTwoHaarProbabilityUnique
import Mathlib.Tactic

/-!
# Compact cusp tests for the level-two Haar probability

The explicit cusp marginal proves divergence first for a measurable
height expression.  Genericity, however, is formulated using
compactly supported continuous test functions.  This file closes that
small but essential gap.

Suppose a continuous nonnegative observable `R` on
`Γ(2) \ SL(2, ℝ)` dominates, almost everywhere, a positive multiple of

```text
       1_{[Ychart,∞)}(height) · height^M,       M ≥ 2.
```

The explicit Haar cusp marginal says that the lower integral of `R` is
infinite.  The Radon--Urysohn lemma from
`ContinuousInfiniteIntegralCompactMinorants` then supplies
nonnegative `C_c` minorants of `R` with arbitrarily large Haar mean.

Two versions are provided:

* one for the explicit normalized fundamental-domain probability;
* one for the canonical Haar probability used by the horocycle
  equidistribution theorems.

The latter is unconditional because
`GammaTwoHaarProbabilityUnique` identifies the two probabilities.
-/

namespace HGAS.Modular

open Filter Function _root_.MeasureTheory Set Topology
open scoped ENNReal NNReal CompactlySupported

noncomputable section

/-- The explicit `Γ(2)` Haar cusp marginal produces arbitrarily large
compactly supported continuous minorants of any continuous observable
which dominates the scaled cusp power. -/
theorem
    exists_explicitGammaTwoHaar_compactMinorant_integral_gt
    (R : C(GammaTwoFrameQuotient, ℝ))
    (hR : ∀ q, 0 ≤ R q)
    (Y : ℝ) (hY : 1 < Y)
    (Ychart : ℝ)
    (M : ℕ) (hM : 2 ≤ M)
    (κ : ℝ≥0) (hκ : κ ≠ 0)
    (hchart :
      ∀ᵐ q ∂(gammaTwoExplicitFrameHaarProbability :
          Measure GammaTwoFrameQuotient),
        (κ : ℝ≥0∞) ^ M *
            HGAS.Dynamics.cuspTailHeightPower
              Ychart M
              (gammaTwoExplicitCuspHeight Y q) ≤
          ENNReal.ofReal (R q))
    (B : ℝ) :
    ∃ f : C_c(GammaTwoFrameQuotient, ℝ),
      (∀ q, 0 ≤ f q) ∧
      (∀ q, f q ≤ R q) ∧
      B <
        ∫ q, f q
          ∂(gammaTwoExplicitFrameHaarProbability :
            Measure GammaTwoFrameQuotient) := by
  have hmarginal :
      Measure.map id
          (gammaTwoExplicitFrameHaarProbability :
            Measure GammaTwoFrameQuotient) =
        (gammaTwoExplicitFrameHaarProbability :
          Measure GammaTwoFrameQuotient) := by
    exact Measure.map_id
  have htop :
      ∫⁻ q, ENNReal.ofReal (R q)
          ∂(gammaTwoExplicitFrameHaarProbability :
            Measure GammaTwoFrameQuotient) = ∞ :=
    explicitGammaTwoHaar_reciprocalSlowdown_lintegral_eq_top
      (gammaTwoExplicitFrameHaarProbability :
        Measure GammaTwoFrameQuotient)
      id measurable_id
      (fun q ↦ ENNReal.ofReal (R q))
      Y hY Ychart M hM hmarginal κ hκ
      (by simpa only [id_eq] using hchart)
  exact
    HGAS.Dynamics.exists_compactlySupportedContinuous_minorant_integral_gt
      (gammaTwoExplicitFrameHaarProbability :
        Measure GammaTwoFrameQuotient)
      R hR htop B

/-- The same compact-minorant theorem for the canonical Haar
probability used by the pointwise horocycle theorem. -/
theorem
    exists_gammaTwoHaar_compactMinorant_integral_gt
    (R : C(GammaTwoFrameQuotient, ℝ))
    (hR : ∀ q, 0 ≤ R q)
    (Y : ℝ) (hY : 1 < Y)
    (Ychart : ℝ)
    (M : ℕ) (hM : 2 ≤ M)
    (κ : ℝ≥0) (hκ : κ ≠ 0)
    (hchart :
      ∀ᵐ q ∂(gammaTwoFrameHaarProbability :
          Measure GammaTwoFrameQuotient),
        (κ : ℝ≥0∞) ^ M *
            HGAS.Dynamics.cuspTailHeightPower
              Ychart M
              (gammaTwoExplicitCuspHeight Y q) ≤
          ENNReal.ofReal (R q))
    (B : ℝ) :
    ∃ f : C_c(GammaTwoFrameQuotient, ℝ),
      (∀ q, 0 ≤ f q) ∧
      (∀ q, f q ≤ R q) ∧
      B <
        ∫ q, f q
          ∂(gammaTwoFrameHaarProbability :
            Measure GammaTwoFrameQuotient) := by
  have hmarginal :
      Measure.map id
          (gammaTwoFrameHaarProbability :
            Measure GammaTwoFrameQuotient) =
        (gammaTwoFrameHaarProbability :
          Measure GammaTwoFrameQuotient) := by
    exact Measure.map_id
  have htop :
      ∫⁻ q, ENNReal.ofReal (R q)
          ∂(gammaTwoFrameHaarProbability :
            Measure GammaTwoFrameQuotient) = ∞ :=
    gammaTwoHaar_reciprocalSlowdown_lintegral_eq_top
      (gammaTwoFrameHaarProbability :
        Measure GammaTwoFrameQuotient)
      id measurable_id
      (fun q ↦ ENNReal.ofReal (R q))
      Y hY Ychart M hM hmarginal κ hκ
      (by simpa only [id_eq] using hchart)
  exact
    HGAS.Dynamics.exists_compactlySupportedContinuous_minorant_integral_gt
      (gammaTwoFrameHaarProbability :
        Measure GammaTwoFrameQuotient)
      R hR htop B

/-- Orbit-ready form of the canonical Haar compact-test theorem.

If `R` is bounded above by reciprocal clock speed along the selected
orbit, every large compact minorant inherits the same orbitwise bound.
This has exactly the hypothesis shape consumed by
`not_generic_of_positiveMeanClock_and_largeCompactTests`. -/
theorem gammaTwoHaar_largeCompactTests_of_cuspLowerBound
    (ϕ : Flow ℝ GammaTwoFrameQuotient)
    (R : C(GammaTwoFrameQuotient, ℝ))
    (hR : ∀ q, 0 ≤ R q)
    (Y : ℝ) (hY : 1 < Y)
    (Ychart : ℝ)
    (M : ℕ) (hM : 2 ≤ M)
    (κ : ℝ≥0) (hκ : κ ≠ 0)
    (hchart :
      ∀ᵐ q ∂(gammaTwoFrameHaarProbability :
          Measure GammaTwoFrameQuotient),
        (κ : ℝ≥0∞) ^ M *
            HGAS.Dynamics.cuspTailHeightPower
              Ychart M
              (gammaTwoExplicitCuspHeight Y q) ≤
          ENNReal.ofReal (R q))
    {q : GammaTwoFrameQuotient}
    {w : ℝ → ℝ}
    (hclock : HGAS.PositiveIntegralClock w)
    (horbit :
      ∀ τ : ℝ,
        R (ϕ τ q) ≤
          HGAS.Dynamics.inverseClockReciprocal hclock τ) :
    ∀ B : ℝ,
      ∃ f : C_c(GammaTwoFrameQuotient, ℝ),
        (∀ p, 0 ≤ f p) ∧
        B <
          ∫ p, f p
            ∂(gammaTwoFrameHaarProbability :
              Measure GammaTwoFrameQuotient) ∧
        ∀ τ : ℝ,
          f (ϕ τ q) ≤
            HGAS.Dynamics.inverseClockReciprocal hclock τ := by
  intro B
  obtain ⟨f, hfnonneg, hfR, hfmean⟩ :=
    exists_gammaTwoHaar_compactMinorant_integral_gt
      R hR Y hY Ychart M hM κ hκ hchart B
  refine ⟨f, hfnonneg, hfmean, ?_⟩
  intro τ
  exact (hfR (ϕ τ q)).trans (horbit τ)

/-- Direct nonperiodic-cusp exclusion endpoint.

A Haar-generic modular orbit cannot simultaneously carry a
positive-mean compactification clock and a continuous reciprocal-speed
observable with the standard `M ≥ 2` cusp lower bound. -/
theorem not_gammaTwoHaarGeneric_of_positiveMeanClock_and_cuspLowerBound
    (ϕ : Flow ℝ GammaTwoFrameQuotient)
    {q : GammaTwoFrameQuotient}
    (hq :
      IsForwardGenericFor ϕ
        gammaTwoFrameHaarProbability q)
    {w : ℝ → ℝ}
    (hclock : HGAS.PositiveIntegralClock w)
    {c : ℝ} (hc : 0 < c)
    (hmean :
      Tendsto
        (fun n : ℕ ↦
          (HGAS.positiveIntegerHorizon n)⁻¹ *
            HGAS.integralClock w
              (HGAS.positiveIntegerHorizon n))
        atTop (𝓝 c))
    (R : C(GammaTwoFrameQuotient, ℝ))
    (hR : ∀ p, 0 ≤ R p)
    (Y : ℝ) (hY : 1 < Y)
    (Ychart : ℝ)
    (M : ℕ) (hM : 2 ≤ M)
    (κ : ℝ≥0) (hκ : κ ≠ 0)
    (hchart :
      ∀ᵐ p ∂(gammaTwoFrameHaarProbability :
          Measure GammaTwoFrameQuotient),
        (κ : ℝ≥0∞) ^ M *
            HGAS.Dynamics.cuspTailHeightPower
              Ychart M
              (gammaTwoExplicitCuspHeight Y p) ≤
          ENNReal.ofReal (R p))
    (horbit :
      ∀ τ : ℝ,
        R (ϕ τ q) ≤
          HGAS.Dynamics.inverseClockReciprocal hclock τ) :
    False :=
  HGAS.Dynamics.not_generic_of_positiveMeanClock_and_largeCompactTests
    ϕ gammaTwoFrameHaarProbability
    hq hclock hc hmean
    (gammaTwoHaar_largeCompactTests_of_cuspLowerBound
      ϕ R hR Y hY Ychart M hM κ hκ hchart
      hclock horbit)

end

end HGAS.Modular
