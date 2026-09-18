import HGAS.Modular.GammaTwoScaledH4SquareCompactTests
import Mathlib.Tactic

/-!
# Positive multiples of the speed-normalized cusp observable

A further positive scalar occurs when a detector column is normalized by
a constant change of physical time.  This file shows that it is harmless
without taking any artificial `2K`-th roots.

Starting from an arbitrary large compact minorant `g ≤ R`, the function
`b g` is a compact minorant of `b R`; its Haar mean is multiplied by the
same positive constant.  Thus positive multiples of the scaled `H₄²`
observable retain the large-compact-test contradiction.
-/

namespace HGAS.Modular

open Filter Function _root_.MeasureTheory Set Topology
open scoped CompactlySupported ENNReal NNReal

noncomputable section

/-- Large compact Haar tests for a positive multiple of the
speed-normalized `H₄²` observable. -/
theorem
    gammaTwoHaar_largeCompactTests_of_positiveMultiple_scaledH4Square_orbitBound
    (ϕ : Flow ℝ GammaTwoFrameQuotient)
    (a : ℝ≥0) (ha : a ≠ 0)
    (K : ℕ) (hK : 1 ≤ K)
    (b : ℝ) (hb : 0 < b)
    {q : GammaTwoFrameQuotient}
    {w : ℝ → ℝ}
    (hclock : HGAS.PositiveIntegralClock w)
    (horbit :
      ∀ τ : ℝ,
        b * gammaTwoScaledH4SquareNormPower a K (ϕ τ q) ≤
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
  intro B
  obtain ⟨g, hgnonneg, hgR, hgmean⟩ :=
    exists_gammaTwoHaar_compactMinorant_integral_gt
      (gammaTwoScaledH4SquareNormPower a K)
      (gammaTwoScaledH4SquareNormPower_nonneg a K)
      2 (by norm_num) Ytail (2 * K) (by omega)
      (gammaTwoScaledThetaCuspHalf a)
      (gammaTwoScaledThetaCuspHalf_ne_zero ha)
      (Filter.Eventually.of_forall hcusp)
      (B / b)
  let f : C_c(GammaTwoFrameQuotient, ℝ) := b • g
  refine ⟨f, ?_, ?_, ?_⟩
  · intro p
    change 0 ≤ b * g p
    exact mul_nonneg hb.le (hgnonneg p)
  · have hmul :
        b * (B / b) <
          b *
            ∫ p, g p
              ∂(gammaTwoFrameHaarProbability :
                Measure GammaTwoFrameQuotient) :=
      mul_lt_mul_of_pos_left hgmean hb
    have hb0 : b ≠ 0 := hb.ne'
    change
      B <
        ∫ p, b * g p
          ∂(gammaTwoFrameHaarProbability :
            Measure GammaTwoFrameQuotient)
    rw [MeasureTheory.integral_const_mul]
    convert hmul using 1
    field_simp
  · intro τ
    change b * g (ϕ τ q) ≤
      HGAS.Dynamics.inverseClockReciprocal hclock τ
    exact
      (mul_le_mul_of_nonneg_left
        (hgR (ϕ τ q)) hb.le).trans
        (horbit τ)

/-- Haar genericity is incompatible with reciprocal-clock domination by
any positive multiple of the speed-normalized observable. -/
theorem
    not_gammaTwoHaarGeneric_of_positiveMeanClock_and_positiveMultiple_scaledH4Square_orbitBound
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
    (b : ℝ) (hb : 0 < b)
    (horbit :
      ∀ τ : ℝ,
        b * gammaTwoScaledH4SquareNormPower a K (ϕ τ q) ≤
          HGAS.Dynamics.inverseClockReciprocal hclock τ) :
    False :=
  HGAS.Dynamics.not_generic_of_positiveMeanClock_and_largeCompactTests
    ϕ gammaTwoFrameHaarProbability hq hclock hc hmean
    (gammaTwoHaar_largeCompactTests_of_positiveMultiple_scaledH4Square_orbitBound
      ϕ a ha K hK b hb hclock horbit)

end

end HGAS.Modular
