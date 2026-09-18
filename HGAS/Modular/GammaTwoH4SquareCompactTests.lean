import HGAS.Modular.ExplicitGammaTwoHaarCompactTests
import HGAS.Modular.GammaTwoH4SquareObservable
import Mathlib.Tactic

/-!
# Large compact Haar tests from the intrinsic `H₄²` observable

This module specializes the general cusp-minorant theorem to the concrete
continuous observable constructed in `GammaTwoH4SquareObservable`.
There is no remaining topological or Haar-coordinate hypothesis.

For every `K ≥ 1`, the observable

```
       q ↦ ‖H₄²_frame(q)‖^K
```

has cusp order `2K ≥ 2`; hence it admits nonnegative compactly supported
minorants with arbitrarily large Haar mean.  If that observable is
bounded by the reciprocal clock speed along an orbit, the orbit cannot
be Haar generic when the clock has positive mean.
-/

namespace HGAS.Modular

open Filter Function _root_.MeasureTheory Set Topology
open scoped CompactlySupported ENNReal NNReal

noncomputable section

/-- Concrete orbit-ready large compact tests. -/
theorem gammaTwoHaar_largeCompactTests_of_H4Square_orbitBound
    (ϕ : Flow ℝ GammaTwoFrameQuotient)
    (K : ℕ) (hK : 1 ≤ K)
    {q : GammaTwoFrameQuotient}
    {w : ℝ → ℝ}
    (hclock : HGAS.PositiveIntegralClock w)
    (horbit :
      ∀ τ : ℝ,
        gammaTwoH4SquareNormPower K (ϕ τ q) ≤
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
    exists_gammaTwoH4SquareNormPower_cuspLowerBound
      (Y := 2) (by norm_num) K
  exact
    gammaTwoHaar_largeCompactTests_of_cuspLowerBound
      ϕ (gammaTwoH4SquareNormPower K)
      (gammaTwoH4SquareNormPower_nonneg K)
      2 (by norm_num) Ytail (2 * K) (by omega)
      gammaTwoThetaCuspHalf gammaTwoThetaCuspHalf_ne_zero
      (Filter.Eventually.of_forall hcusp)
      hclock horbit

/-- Fully concrete Haar-genericity contradiction, conditional only on
the orbitwise comparison with reciprocal clock speed. -/
theorem not_gammaTwoHaarGeneric_of_positiveMeanClock_and_H4Square_orbitBound
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
    (K : ℕ) (hK : 1 ≤ K)
    (horbit :
      ∀ τ : ℝ,
        gammaTwoH4SquareNormPower K (ϕ τ q) ≤
          HGAS.Dynamics.inverseClockReciprocal hclock τ) :
    False :=
  HGAS.Dynamics.not_generic_of_positiveMeanClock_and_largeCompactTests
    ϕ gammaTwoFrameHaarProbability hq hclock hc hmean
    (gammaTwoHaar_largeCompactTests_of_H4Square_orbitBound
      ϕ K hK hclock horbit)

end

end HGAS.Modular
