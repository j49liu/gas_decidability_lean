import HGAS.Analysis.CanonicalEffectivePrimitiveBudget
import HGAS.Arithmetic.NormalizedCorrectedCanonicalPrimitiveGain
import Mathlib.Tactic

/-!
# Effective primitive budget for the complete canonical drift

`CanonicalEffectivePrimitiveBudget` bounds the seven complex selector
families and the complex arithmetic detector before support collection.
This file transports those estimates through the literal compiler layout:

* the validity coordinate is identically zero;
* each complex selector contributes two real coordinates;
* the detector contributes its real and imaginary coordinates.

The result is one completely explicit natural number bounding every
inverse-frequency coordinate norm, and hence the squared norm of the
complete primitive vector.  It is the quantitative input needed for a
computable accumulator gain.
-/

noncomputable section

open scoped BigOperators
open Function

namespace HGAS.Analysis.NormalizedCorrectedCanonicalEffectivePrimitiveBudget

open HGAS
open HGAS.Clocks
open HGAS.Analysis
open HGAS.Analysis.CanonicalSelectorMomentAggregatedFamilies
open HGAS.Analysis.CanonicalSelectorMomentSupportedCrosswalk
open HGAS.Analysis.CanonicalDetectorNoInstanceAggregatedFamily
open HGAS.Analysis.CanonicalEffectivePrimitiveBudget
open HGAS.Analysis.NormalizedCorrectedCanonicalDriftFourierFamily

variable {eqs vars : ℕ}

@[simp]
theorem label_outer_inl
    (a : Fin 1) :
    label
        (finSumFinEquiv
          (Sum.inl a :
            Fin 1 ⊕
              Fin
                (CorrectedFixedDetectorMomentCode.scalarMomentCount
                  vars + 2))) =
      Sum.inl a := by
  simp [label]

@[simp]
theorem label_outer_inr_inner_inl
    (k :
      Fin (CorrectedFixedDetectorMomentCode.scalarMomentCount vars)) :
    label
        (finSumFinEquiv
          (Sum.inr
            (finSumFinEquiv
              (Sum.inl k :
                Fin
                    (CorrectedFixedDetectorMomentCode.scalarMomentCount
                      vars) ⊕
                  Fin 2)) :
            Fin 1 ⊕
              Fin
                (CorrectedFixedDetectorMomentCode.scalarMomentCount
                  vars + 2))) =
      Sum.inr (Sum.inl k) := by
  simp [label]

@[simp]
theorem label_outer_inr_inner_inr
    (b : Fin 2) :
    label
        (finSumFinEquiv
          (Sum.inr
            (finSumFinEquiv
              (Sum.inr b :
                Fin
                    (CorrectedFixedDetectorMomentCode.scalarMomentCount
                      vars) ⊕
                  Fin 2)) :
            Fin 1 ⊕
              Fin
                (CorrectedFixedDetectorMomentCode.scalarMomentCount
                  vars + 2))) =
      Sum.inr (Sum.inr b) := by
  simp [label]

/-- Every literal real drift coordinate has inverse-frequency `ℓ¹` norm
bounded by the same explicit natural number. -/
theorem primitiveCoordinateBound_le_coordinatePrimitiveBudget
    (I : DQLSystem eqs vars)
    (hnot : ¬ I.Solvable)
    (p : Fin (vars + eqs) → ℕ)
    (hp : ∀ i, (p i).Prime)
    (hinjective : Function.Injective p)
    (sign : Fin (vars + eqs) → ℤ)
    (hsign : ∀ i, sign i = 1 ∨ sign i = -1)
    (q : Fin (driftCount vars)) :
    primitiveCoordinateBound
        (Index I hnot)
        (coefficient I hnot)
        (exponent I hnot)
        (RadicalTimeChangedTorusFourierComponent.frequency
          (1 / (2 * Real.pi)) p sign) q ≤
      (coordinatePrimitiveBudget I p : ℕ) := by
  obtain ⟨a | r, hq⟩ := finSumFinEquiv.surjective q
  · fin_cases a
    have hlabel : label q = Sum.inl 0 := by
      rw [← hq]
      exact label_outer_inl 0
    unfold primitiveCoordinateBound Index coefficient exponent
    rw [hlabel]
    simp only [indexAtLabel, coefficientAtLabel, exponentAtLabel,
      cohomologicalPrimitiveCoefficient, RadicalClock.frequencyPairing,
      Pi.zero_apply, Int.cast_zero, zero_mul, Finset.sum_const_zero,
      if_true, norm_zero]
    change
      (∑' _i : Unit, (0 : ℝ)) ≤
        (coordinatePrimitiveBudget I p : ℕ)
    rw [tsum_zero]
    exact Nat.cast_nonneg _
  · obtain ⟨k | b, hr⟩ := finSumFinEquiv.surjective r
    · let kb := finProdFinEquiv.symm k
      have hlabel : label q = Sum.inr (Sum.inl k) := by
        rw [← hq, ← hr]
        exact label_outer_inr_inner_inl k
      have hprimitive :=
        HGAS.Analysis.RawCenteredFamily.primitiveBound_le_rawWeightedTsum
          (momentFamily I kb.1) p hp hinjective sign hsign
      have hraw :=
        momentFamilyRawWeightedTsum_le I p kb.1
      have hselector :
          (∑' i : (momentFamily I kb.1).SupportedIndex,
            ‖cohomologicalPrimitiveCoefficient
                (momentFamily I kb.1).supportedCoefficient
                (momentFamily I kb.1).supportedExponent
                (fun j ↦
                  (1 / (2 * Real.pi)) *
                    RadicalIndependence.signedPrimeSqrtFrequency
                      p sign j)
                i‖) ≤
            (selectorRawBudget I p : ℕ) :=
        hprimitive.trans hraw
      unfold primitiveCoordinateBound Index coefficient exponent
      rw [hlabel]
      change
        (∑' i : (momentFamily I kb.1).SupportedIndex,
          ‖cohomologicalPrimitiveCoefficient
              (realifiedCoefficient kb.2
                (momentFamily I kb.1).supportedCoefficient)
              (momentFamily I kb.1).supportedExponent
              (RadicalTimeChangedTorusFourierComponent.frequency
                (1 / (2 * Real.pi)) p sign)
              i‖) ≤
          (coordinatePrimitiveBudget I p : ℕ)
      rw [primitiveTsum_realifiedCoefficient]
      change
        (∑' i : (momentFamily I kb.1).SupportedIndex,
          ‖cohomologicalPrimitiveCoefficient
              (momentFamily I kb.1).supportedCoefficient
              (momentFamily I kb.1).supportedExponent
              (fun j ↦
                (1 / (2 * Real.pi)) *
                  RadicalIndependence.signedPrimeSqrtFrequency
                    p sign j)
              i‖) ≤
          (coordinatePrimitiveBudget I p : ℕ)
      exact hselector.trans (by
        unfold coordinatePrimitiveBudget
        push_cast
        exact le_add_of_nonneg_right (Nat.cast_nonneg _))
    · have hlabel : label q = Sum.inr (Sum.inr b) := by
        rw [← hq, ← hr]
        exact label_outer_inr_inner_inr b
      have hprimitive :=
        HGAS.Analysis.RawCenteredFamily.primitiveBound_le_rawWeightedTsum
          (detector I hnot) p hp hinjective sign hsign
      have hdetector :
          (∑' i : (detector I hnot).SupportedIndex,
            ‖cohomologicalPrimitiveCoefficient
                (detector I hnot).supportedCoefficient
                (detector I hnot).supportedExponent
                (fun j ↦
                  (1 / (2 * Real.pi)) *
                    RadicalIndependence.signedPrimeSqrtFrequency
                      p sign j)
                i‖) ≤
            (detectorRawBudget I p : ℕ) :=
        hprimitive.trans (detectorWeightedTsum_le I p)
      unfold primitiveCoordinateBound Index coefficient exponent
      rw [hlabel]
      change
        (∑' i : (detector I hnot).SupportedIndex,
          ‖cohomologicalPrimitiveCoefficient
              (realifiedCoefficient b
                (detector I hnot).supportedCoefficient)
              (detector I hnot).supportedExponent
              (RadicalTimeChangedTorusFourierComponent.frequency
                (1 / (2 * Real.pi)) p sign)
              i‖) ≤
          (coordinatePrimitiveBudget I p : ℕ)
      rw [primitiveTsum_realifiedCoefficient]
      change
        (∑' i : (detector I hnot).SupportedIndex,
          ‖cohomologicalPrimitiveCoefficient
              (detector I hnot).supportedCoefficient
              (detector I hnot).supportedExponent
              (fun j ↦
                (1 / (2 * Real.pi)) *
                  RadicalIndependence.signedPrimeSqrtFrequency
                    p sign j)
              i‖) ≤
          (coordinatePrimitiveBudget I p : ℕ)
      exact hdetector.trans (by
        unfold coordinatePrimitiveBudget
        push_cast
        exact le_add_of_nonneg_left (Nat.cast_nonneg _))

/-- The complete squared primitive budget is bounded by the explicit
natural number `totalPrimitiveBudget`. -/
theorem unscaledPrimitiveBudget_le_totalPrimitiveBudget
    (I : DQLSystem eqs vars)
    (hnot : ¬ I.Solvable)
    (p : Fin (vars + eqs) → ℕ)
    (hp : ∀ i, (p i).Prime)
    (hinjective : Function.Injective p)
    (sign : Fin (vars + eqs) → ℤ)
    (hsign : ∀ i, sign i = 1 ∨ sign i = -1) :
    NormalizedCorrectedCanonicalPrimitiveGain.unscaledPrimitiveBudget
        I hnot p sign ≤
      (totalPrimitiveBudget I p : ℕ) := by
  let C := coordinatePrimitiveBudget I p
  have hpoint :
      ∀ q : Fin (driftCount vars),
        (primitiveCoordinateBound
          (Index I hnot)
          (coefficient I hnot)
          (exponent I hnot)
          (RadicalTimeChangedTorusFourierComponent.frequency
            (1 / (2 * Real.pi)) p sign) q) ^ 2 ≤
          (C : ℝ) ^ 2 := by
    intro q
    exact
      pow_le_pow_left₀
        (primitiveCoordinateBound_nonneg
          (Index I hnot)
          (coefficient I hnot)
          (exponent I hnot)
          (RadicalTimeChangedTorusFourierComponent.frequency
            (1 / (2 * Real.pi)) p sign) q)
        (by
          simpa [C] using
            primitiveCoordinateBound_le_coordinatePrimitiveBudget
              I hnot p hp hinjective sign hsign q)
        2
  calc
    NormalizedCorrectedCanonicalPrimitiveGain.unscaledPrimitiveBudget
        I hnot p sign ≤
        ∑ _q : Fin (driftCount vars), (C : ℝ) ^ 2 := by
      unfold
        NormalizedCorrectedCanonicalPrimitiveGain.unscaledPrimitiveBudget
      exact Finset.sum_le_sum fun q _ ↦ hpoint q
    _ = ((driftCount vars : ℕ) : ℝ) * (C : ℝ) ^ 2 := by
      simp
    _ = (totalPrimitiveBudget I p : ℕ) := by
      have hcount :
          driftCount vars = 14 * vars + 3 := by
        unfold driftCount
          NormalizedCorrectedFixedDetectorDriftCode.driftCount
          CorrectedFixedDetectorDriftCode.driftCount
          FixedDetectorDriftCode.driftCount
          FixedDetectorMomentCode.scalarMomentCount
          FixedDetectorMomentCode.momentCount
          FixedDetectorMomentCode.localMomentCount
        omega
      unfold totalPrimitiveBudget
      rw [hcount]
      dsimp [C]
      push_cast
      ring

end HGAS.Analysis.NormalizedCorrectedCanonicalEffectivePrimitiveBudget
