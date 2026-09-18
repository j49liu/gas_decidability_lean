import HGAS.Modular.ExplicitGammaTwoHaarCompactTests
import HGAS.Modular.GammaTwoScaledH4SquareObservable
import Mathlib.Tactic

/-!
# Compact Haar tests from a speed-normalized `H₄²` observable

For a nonzero scale `a` and `K ≥ 1`, the continuous observable

```text
  q ↦ a^(2K) ‖H₄²_frame(q)‖^K
```

has cusp order `2K ≥ 2`.  Hence it admits nonnegative compactly supported
minorants with arbitrarily large Haar mean.  If the observable is bounded
by reciprocal clock speed along an orbit, those same tests exclude Haar
genericity whenever the compact-time clock has positive mean.

Keeping `a` explicit is important: for an exact real-frame horocycle,
`a` is the absolute signed speed and the observable then agrees exactly
with the `2K`-th power of the unary `C` coordinate.
-/

namespace HGAS.Modular

open Filter Function _root_.MeasureTheory Set Topology
open scoped CompactlySupported ENNReal NNReal

noncomputable section

/-- Orbit-ready large compact tests for every nonzero speed scale. -/
theorem
    gammaTwoHaar_largeCompactTests_of_scaledH4Square_orbitBound
    (ϕ : Flow ℝ GammaTwoFrameQuotient)
    (a : ℝ≥0) (ha : a ≠ 0)
    (K : ℕ) (hK : 1 ≤ K)
    {q : GammaTwoFrameQuotient}
    {w : ℝ → ℝ}
    (hclock : HGAS.PositiveIntegralClock w)
    (horbit :
      ∀ τ : ℝ,
        gammaTwoScaledH4SquareNormPower a K (ϕ τ q) ≤
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
  obtain ⟨Ytail, _hYtail, hcusp⟩ :=
    exists_gammaTwoScaledH4SquareNormPower_cuspLowerBound
      (Y := 2) (by norm_num) a ha K
  exact
    gammaTwoHaar_largeCompactTests_of_cuspLowerBound
      ϕ (gammaTwoScaledH4SquareNormPower a K)
      (gammaTwoScaledH4SquareNormPower_nonneg a K)
      2 (by norm_num) Ytail (2 * K) (by omega)
      (gammaTwoScaledThetaCuspHalf a)
      (gammaTwoScaledThetaCuspHalf_ne_zero ha)
      (Filter.Eventually.of_forall hcusp)
      hclock horbit

/-- Haar genericity is incompatible with reciprocal-clock domination by
the speed-normalized observable. -/
theorem
    not_gammaTwoHaarGeneric_of_positiveMeanClock_and_scaledH4Square_orbitBound
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
    (a : ℝ≥0) (ha : a ≠ 0)
    (K : ℕ) (hK : 1 ≤ K)
    (horbit :
      ∀ τ : ℝ,
        gammaTwoScaledH4SquareNormPower a K (ϕ τ q) ≤
          HGAS.Dynamics.inverseClockReciprocal hclock τ) :
    False :=
  HGAS.Dynamics.not_generic_of_positiveMeanClock_and_largeCompactTests
    ϕ gammaTwoFrameHaarProbability hq hclock hc hmean
    (gammaTwoHaar_largeCompactTests_of_scaledH4Square_orbitBound
      ϕ a ha K hK hclock horbit)

end

end HGAS.Modular
