import HGAS.Analysis.NormalizedCorrectedCanonicalEffectivePrimitiveBudget
import HGAS.Arithmetic.CanonicalRawOrbitEffectiveBudget
import HGAS.Lyapunov.ExactGridPositivityComputability
import Mathlib.Tactic

/-!
# A computable rational gain for the canonical no-instance component

This file removes the last rational-density choice from the primitive
finite-graph argument.  Put

```text
 T = totalPrimitiveBudget(I,p),
 R = rawNormSqNatBudget(eqs,vars),
 D = 8 (T+1) (R+1),
 κ = 1/D.
```

Both `T` and `R` are natural numbers obtained by finite arithmetic.  The
previous quantitative modules prove

```text
 unscaled primitive square sum ≤ T,
 canonical central square weight ≥ 1/(R+1).
```

The elementary inequality

```text
       8 κ² T ≤ 1/(R+1)
```

therefore supplies the exact compiler-facing small-gain condition.  The
code is defined with `RationalCode.unitFraction`, whose construction is
primitive recursive.
-/

noncomputable section

open scoped BigOperators

namespace HGAS.NormalizedCorrectedCanonicalEffectivePrimitiveGain

open HGAS
open HGAS.Analysis
open HGAS.Analysis.CanonicalEffectivePrimitiveBudget
open HGAS.Analysis.NormalizedCorrectedCanonicalDriftFourierFamily
open HGAS.Analysis.NormalizedCorrectedCanonicalEffectivePrimitiveBudget
open HGAS.CanonicalRawOrbitEffectiveBudget
open HGAS.Clocks

variable {eqs vars : ℕ}

/-- Positive integer denominator used by the effective accumulator
gain. -/
def effectiveAccumulatorDenominator
    (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ) : ℕ :=
  8 * (totalPrimitiveBudget I p + 1) *
    (rawNormSqNatBudget eqs vars + 1)

/-- Literal rational compiler code for the effective gain. -/
def effectiveAccumulatorScaleCode
    (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ) : RationalCode :=
  RationalCode.unitFraction
    (effectiveAccumulatorDenominator I p)

theorem effectiveAccumulatorDenominator_pos
    (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ) :
    0 < effectiveAccumulatorDenominator I p := by
  unfold effectiveAccumulatorDenominator
  positivity

@[simp]
theorem decode_effectiveAccumulatorScaleCode
    (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ) :
    (RationalCode.decode
        (effectiveAccumulatorScaleCode I p) : ℝ) =
      1 / (effectiveAccumulatorDenominator I p : ℝ) := by
  unfold effectiveAccumulatorScaleCode
  rw [RationalCode.decode_unitFraction
    (effectiveAccumulatorDenominator_pos I p)]
  simp only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast]

theorem decode_effectiveAccumulatorScaleCode_pos
    (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ) :
    0 <
      (RationalCode.decode
        (effectiveAccumulatorScaleCode I p) : ℝ) := by
  rw [decode_effectiveAccumulatorScaleCode]
  exact one_div_pos.mpr (by
    exact_mod_cast effectiveAccumulatorDenominator_pos I p)

/-- The natural raw-orbit budget gives a rational lower bound for the
canonical squared central weight. -/
theorem effectiveCentralLower_le_canonicalCentralWeightSqLowerBound
    (eqs vars : ℕ) :
    1 / (1 + (rawNormSqNatBudget eqs vars : ℝ)) ≤
      NormalizedCorrectedCanonicalFixedDetectorCentralChart.canonicalCentralWeightSqLowerBound
        eqs vars := by
  unfold
    NormalizedCorrectedCanonicalFixedDetectorCentralChart.canonicalCentralWeightSqLowerBound
    positiveCentralWeightSqLowerBound
  rw [one_div]
  apply
    (inv_le_inv₀
      (by positivity :
        0 < 1 + (rawNormSqNatBudget eqs vars : ℝ))
      (by
        linarith [
          CanonicalFixedDetectorRawOrbitBound.canonicalRawNormSqBound_nonneg
            (eqs := eqs) (vars := vars)] :
        0 <
          1 +
            CanonicalFixedDetectorRawOrbitBound.canonicalRawNormSqBound
              eqs vars)).2
  linarith [
    canonicalRawNormSqBound_le_rawNormSqNatBudget eqs vars]

/-- Elementary numerical inequality behind the chosen denominator. -/
theorem unitFraction_effectiveGain_le
    (T R : ℕ) :
    8 *
          |(1 /
            (8 * ((T : ℝ) + 1) * ((R : ℝ) + 1)))| ^ 2 *
          (T : ℝ) ≤
      1 / (1 + (R : ℝ)) := by
  have hT : 0 ≤ (T : ℝ) := Nat.cast_nonneg T
  have hR : 0 ≤ (R : ℝ) := Nat.cast_nonneg R
  have hd :
      0 < 8 * ((T : ℝ) + 1) * ((R : ℝ) + 1) := by
    positivity
  rw [abs_of_pos (one_div_pos.mpr hd)]
  field_simp
  nlinarith [sq_nonneg (T : ℝ), sq_nonneg (R : ℝ),
    mul_nonneg hT hR]

/-- The explicit unit-fraction code satisfies the complete scaled
primitive smallness inequality required by the finite-graph theorem. -/
theorem effectiveAccumulatorScale_small
    (I : DQLSystem eqs vars)
    (hnot : ¬ I.Solvable)
    (p : Fin (vars + eqs) → ℕ)
    (hp : ∀ i, (p i).Prime)
    (hinjective : Function.Injective p)
    (sign : Fin (vars + eqs) → ℤ)
    (hsign : ∀ i, sign i = 1 ∨ sign i = -1) :
    8 *
        (∑ q : Fin (driftCount vars),
          (primitiveCoordinateBound
            (Index I hnot)
            (scaledRealCoefficient
              (RationalCode.decode
                (effectiveAccumulatorScaleCode I p) : ℝ)
              (coefficient I hnot))
            (exponent I hnot)
            (RadicalTimeChangedTorusFourierComponent.frequency
              (1 / (2 * Real.pi)) p sign) q) ^ 2) ≤
      NormalizedCorrectedCanonicalFixedDetectorCentralChart.canonicalCentralWeightSqLowerBound
        eqs vars := by
  let T := totalPrimitiveBudget I p
  let R := rawNormSqNatBudget eqs vars
  let κ :=
    (RationalCode.decode
      (effectiveAccumulatorScaleCode I p) : ℝ)
  have hbudget :
      NormalizedCorrectedCanonicalPrimitiveGain.unscaledPrimitiveBudget
          I hnot p sign ≤ (T : ℝ) := by
    simpa [T] using
      unscaledPrimitiveBudget_le_totalPrimitiveBudget
        I hnot p hp hinjective sign hsign
  have hκ :
      κ =
        1 /
          (8 * ((T : ℝ) + 1) * ((R : ℝ) + 1)) := by
    unfold κ T R
    rw [decode_effectiveAccumulatorScaleCode]
    unfold effectiveAccumulatorDenominator
    push_cast
    ring
  rw [
    NormalizedCorrectedCanonicalPrimitiveGain.scaledPrimitiveBudget_eq]
  calc
    8 * (|κ| ^ 2 *
          NormalizedCorrectedCanonicalPrimitiveGain.unscaledPrimitiveBudget
            I hnot p sign) =
        (8 * |κ| ^ 2) *
          NormalizedCorrectedCanonicalPrimitiveGain.unscaledPrimitiveBudget
            I hnot p sign := by ring
    _ ≤ (8 * |κ| ^ 2) * (T : ℝ) :=
      mul_le_mul_of_nonneg_left hbudget (by positivity)
    _ = 8 * |κ| ^ 2 * (T : ℝ) := by ring
    _ ≤ 1 / (1 + (R : ℝ)) := by
      rw [hκ]
      exact unitFraction_effectiveGain_le T R
    _ ≤
      NormalizedCorrectedCanonicalFixedDetectorCentralChart.canonicalCentralWeightSqLowerBound
        eqs vars := by
      exact
        effectiveCentralLower_le_canonicalCentralWeightSqLowerBound
          eqs vars

/-- Final effective replacement for the earlier qualitative existence
theorem: the returned code is named, positive, and satisfies the needed
smallness estimate. -/
theorem effectiveAccumulatorScale_spec
    (I : DQLSystem eqs vars)
    (hnot : ¬ I.Solvable)
    (p : Fin (vars + eqs) → ℕ)
    (hp : ∀ i, (p i).Prime)
    (hinjective : Function.Injective p)
    (sign : Fin (vars + eqs) → ℤ)
    (hsign : ∀ i, sign i = 1 ∨ sign i = -1) :
    0 <
        (RationalCode.decode
          (effectiveAccumulatorScaleCode I p) : ℝ) ∧
      8 *
          (∑ q : Fin (driftCount vars),
            (primitiveCoordinateBound
              (Index I hnot)
              (scaledRealCoefficient
                (RationalCode.decode
                  (effectiveAccumulatorScaleCode I p) : ℝ)
                (coefficient I hnot))
              (exponent I hnot)
              (RadicalTimeChangedTorusFourierComponent.frequency
                (1 / (2 * Real.pi)) p sign) q) ^ 2) ≤
        NormalizedCorrectedCanonicalFixedDetectorCentralChart.canonicalCentralWeightSqLowerBound
          eqs vars :=
  ⟨decode_effectiveAccumulatorScaleCode_pos I p,
    effectiveAccumulatorScale_small
      I hnot p hp hinjective sign hsign⟩

end HGAS.NormalizedCorrectedCanonicalEffectivePrimitiveGain
