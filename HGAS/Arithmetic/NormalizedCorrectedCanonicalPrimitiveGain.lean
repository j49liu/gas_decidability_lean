import HGAS.Analysis.RationalAccumulatorGain
import HGAS.Analysis.RadicalTimeChangedTorusComponentFiniteGraph
import HGAS.Analysis.ScaledRealTorusFourierFamily
import HGAS.Arithmetic.NormalizedCorrectedCanonicalFixedDetectorCentralChart
import HGAS.Arithmetic.NormalizedCorrectedCanonicalDriftFourierCrosswalk
import Mathlib.Tactic

/-!
# A positive rational gain fitting the canonical primitive graph

The complete no-instance Fourier family is fixed once the DQL input is
fixed.  Its finitely many inverse-frequency `ℓ¹` bounds therefore have a
finite nonnegative squared sum `S`.  Scaling the accumulator forcing by a
rational gain `κ` scales this sum by `|κ|²`.

Combining the exact scaling law with rational density yields a positive
rational code for which

```text
                   8 Σ_q primitiveBound_κ(q)²
                     ≤ canonicalCentralLower.
```

This closes the analytic *existence* of a suitable nonzero accumulator
gain.  Effectivity requires an explicit computable upper bound for the
unscaled sum; that is a separate quantitative refinement.
-/

noncomputable section

open scoped BigOperators

namespace HGAS.NormalizedCorrectedCanonicalPrimitiveGain

open HGAS
open HGAS.Analysis
open HGAS.Analysis.NormalizedCorrectedCanonicalDriftFourierFamily
open HGAS.Clocks

variable {eqs vars : ℕ}

/-- The unscaled finite squared sum of inverse-frequency coordinate
bounds for the complete normalized no-instance drift. -/
def unscaledPrimitiveBudget
    (I : DQLSystem eqs vars)
    (hnot : ¬ I.Solvable)
    (p : Fin (vars + eqs) → ℕ)
    (sign : Fin (vars + eqs) → ℤ) : ℝ :=
  ∑ q : Fin (driftCount vars),
    (primitiveCoordinateBound
      (Index I hnot)
      (coefficient I hnot)
      (exponent I hnot)
      (RadicalTimeChangedTorusFourierComponent.frequency
        (1 / (2 * Real.pi)) p sign) q) ^ 2

theorem unscaledPrimitiveBudget_nonneg
    (I : DQLSystem eqs vars)
    (hnot : ¬ I.Solvable)
    (p : Fin (vars + eqs) → ℕ)
    (sign : Fin (vars + eqs) → ℤ) :
    0 ≤ unscaledPrimitiveBudget I hnot p sign := by
  unfold unscaledPrimitiveBudget
  exact Finset.sum_nonneg fun q _ ↦ sq_nonneg _

/-- Exact formula for the squared primitive budget after applying a real
gain. -/
theorem scaledPrimitiveBudget_eq
    (c : ℝ)
    (I : DQLSystem eqs vars)
    (hnot : ¬ I.Solvable)
    (p : Fin (vars + eqs) → ℕ)
    (sign : Fin (vars + eqs) → ℤ) :
    (∑ q : Fin (driftCount vars),
      (primitiveCoordinateBound
        (Index I hnot)
        (scaledRealCoefficient c (coefficient I hnot))
        (exponent I hnot)
        (RadicalTimeChangedTorusFourierComponent.frequency
          (1 / (2 * Real.pi)) p sign) q) ^ 2) =
      |c| ^ 2 * unscaledPrimitiveBudget I hnot p sign := by
  exact
    sum_sq_primitiveCoordinateBound_scaledRealCoefficient
      c (coefficient I hnot) (exponent I hnot)
      (RadicalTimeChangedTorusFourierComponent.frequency
        (1 / (2 * Real.pi)) p sign)

/-- A positive rational code always exists whose scaled primitive fits
inside the explicit positive canonical central chart. -/
theorem exists_positiveAccumulatorScale
    (I : DQLSystem eqs vars)
    (hnot : ¬ I.Solvable)
    (p : Fin (vars + eqs) → ℕ)
    (sign : Fin (vars + eqs) → ℤ) :
    ∃ κ : RationalCode,
      0 < (RationalCode.decode κ : ℝ) ∧
      8 *
          (∑ q : Fin (driftCount vars),
            (primitiveCoordinateBound
              (Index I hnot)
              (scaledRealCoefficient
                (RationalCode.decode κ : ℝ)
                (coefficient I hnot))
              (exponent I hnot)
              (RadicalTimeChangedTorusFourierComponent.frequency
                (1 / (2 * Real.pi)) p sign) q) ^ 2) ≤
        NormalizedCorrectedCanonicalFixedDetectorCentralChart.canonicalCentralWeightSqLowerBound
          eqs vars := by
  have hcentral :
      0 <
        NormalizedCorrectedCanonicalFixedDetectorCentralChart.canonicalCentralWeightSqLowerBound
          eqs vars :=
    NormalizedCorrectedCanonicalFixedDetectorCentralChart.canonicalCentralWeightSqLowerBound_pos
  obtain ⟨κ, hκpos, hκ⟩ :=
    exists_positive_rationalCode_mul_sq_le
      hcentral
      (unscaledPrimitiveBudget_nonneg I hnot p sign)
  refine ⟨κ, hκpos, ?_⟩
  rw [scaledPrimitiveBudget_eq]
  simpa only [mul_assoc] using hκ

end HGAS.NormalizedCorrectedCanonicalPrimitiveGain
