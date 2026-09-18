import HGAS.Arithmetic.CorrectedFixedDetectorMomentSemantics
import HGAS.Arithmetic.FixedDetectorDriftCode
import Mathlib.Tactic

/-!
# Corrected complete drift observable

This is the corrected replacement for `FixedDetectorDriftCode`.  The
validity energy and final arithmetic detector are reused literally.  The
middle block uses `CorrectedFixedDetectorMomentCode`, whose last two
moments subtract the exact conditional zero-mode coefficient.

The block layout remains

```text
  validity | 14·vars real selector coordinates | detector.re | detector.im.
```

Thus the correction changes no dimensions and introduces no additional
state variable or moment.
-/

namespace HGAS.CorrectedFixedDetectorDriftCode

open HGAS
open _root_.MvPolynomial
open HGAS.Modular

variable {eqs vars : ℕ}

abbrev dimension (eqs vars : ℕ) : ℕ :=
  FixedDetectorDriftCode.dimension eqs vars

abbrev driftCount (vars : ℕ) : ℕ :=
  FixedDetectorDriftCode.driftCount vars

abbrev validityIndex (vars : ℕ) : Fin (driftCount vars) :=
  FixedDetectorDriftCode.validityIndex vars

abbrev momentIndex
    (k : Fin (CorrectedFixedDetectorMomentCode.scalarMomentCount vars)) :
    Fin (driftCount vars) :=
  FixedDetectorDriftCode.momentIndex k

abbrev detectorIndex (b : Fin 2) :
    Fin (driftCount vars) :=
  FixedDetectorDriftCode.detectorIndex b

/-- The corrected finite drift compiler. -/
def driftCode
    (I : DQLSystem eqs vars) :
    Fin (driftCount vars) → PolynomialCode (dimension eqs vars) :=
  fun q ↦
    match finSumFinEquiv.symm q with
    | Sum.inl _ =>
        FixedDetectorValidityEnergyCode.totalValidityEnergyCode I
    | Sum.inr r =>
        match finSumFinEquiv.symm r with
        | Sum.inl k =>
            CorrectedFixedDetectorMomentCode.scalarMomentCode I k
        | Sum.inr b =>
            ![
              (FixedDetectorPolynomialCode.detectorCode
                (eqs := eqs) (vars := vars)).1,
              (FixedDetectorPolynomialCode.detectorCode
                (eqs := eqs) (vars := vars)).2
            ] b

/-- The validity semantics is unchanged. -/
noncomputable abbrev validityEnergyValue
    (I : DQLSystem eqs vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) : ℝ :=
  FixedDetectorDriftCode.validityEnergyValue I z

/-- The arithmetic detector semantics is unchanged. -/
noncomputable abbrev detectorValue
    (z : FixedDetectorPolynomialCode.State eqs vars) : ℂ :=
  FixedDetectorDriftCode.detectorValue z

/-- Semantic vector corresponding to the corrected sparse drift code. -/
noncomputable def driftValue
    (I : DQLSystem eqs vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    Fin (driftCount vars) → ℝ :=
  fun q ↦
    match finSumFinEquiv.symm q with
    | Sum.inl _ => validityEnergyValue I z
    | Sum.inr r =>
        match finSumFinEquiv.symm r with
        | Sum.inl k =>
            CorrectedFixedDetectorMomentCode.scalarMomentValue I z k
        | Sum.inr b =>
            ![(detectorValue z).re, (detectorValue z).im] b

theorem validityEnergyValue_nonneg
    (I : DQLSystem eqs vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    0 ≤ validityEnergyValue I z :=
  FixedDetectorDriftCode.validityEnergyValue_nonneg I z

/-- Vanishing of the unchanged first coordinate is equivalent to all
pointwise algebraic graph constraints. -/
theorem validityEnergyValue_eq_zero_iff
    (I : DQLSystem eqs vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    validityEnergyValue I z = 0 ↔
      (∀ a (r : LinkedJacobiResidualIndex),
          linkedJacobiResidual r
            (z.base.base.source.linked a) = 0) ∧
        (∀ k,
          eval₂Hom (algebraMap ℚ ℝ)
            (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.point
              z.base.base)
            (PolynomialCode.decode
              (DetectorJacobiGaugeData.residualCode
                FixedDetectorValidityEnergyCode.thetaGaugeScale I k)) =
              0) ∧
        ∀ k,
          eval₂Hom (algebraMap ℚ ℝ)
            (DetectorPoissonReciprocalCode.point z.base)
            (PolynomialCode.decode
              (DetectorPoissonReciprocalCode.residualCode I k)) = 0 :=
  FixedDetectorDriftCode.validityEnergyValue_eq_zero_iff I z

/-- Every emitted corrected polynomial evaluates to the named semantic
coordinate. -/
@[simp]
theorem eval_driftCode
    (I : DQLSystem eqs vars)
    (q : Fin (driftCount vars))
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    eval₂Hom (algebraMap ℚ ℝ)
        (FixedDetectorPolynomialCode.point z)
        (PolynomialCode.decode (driftCode I q)) =
      driftValue I z q := by
  obtain ⟨i | r, rfl⟩ := finSumFinEquiv.surjective q
  · fin_cases i
    simpa [driftCode, driftValue] using
      FixedDetectorDriftCode.eval_totalValidityEnergyCode_eq_validityEnergyValue
        I z
  · obtain ⟨k | b, rfl⟩ := finSumFinEquiv.surjective r
    · simp [driftCode, driftValue]
    · fin_cases b
      · simpa [driftCode, driftValue,
          Clocks.ControllerPhaseProductCharacterCode.evalPair] using
          congrArg Complex.re
            (FixedDetectorDriftCode.evalPair_detectorCode_eq_detectorValue z)
      · simpa [driftCode, driftValue,
          Clocks.ControllerPhaseProductCharacterCode.evalPair] using
          congrArg Complex.im
            (FixedDetectorDriftCode.evalPair_detectorCode_eq_detectorValue z)

@[simp]
theorem eval_driftCode_validityIndex
    (I : DQLSystem eqs vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    eval₂Hom (algebraMap ℚ ℝ)
        (FixedDetectorPolynomialCode.point z)
        (PolynomialCode.decode
          (driftCode I (validityIndex vars))) =
      validityEnergyValue I z :=
  eval_driftCode I (validityIndex vars) z

@[simp]
theorem eval_driftCode_momentIndex
    (I : DQLSystem eqs vars)
    (k : Fin (CorrectedFixedDetectorMomentCode.scalarMomentCount vars))
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    eval₂Hom (algebraMap ℚ ℝ)
        (FixedDetectorPolynomialCode.point z)
        (PolynomialCode.decode
          (driftCode I (momentIndex k))) =
      CorrectedFixedDetectorMomentCode.scalarMomentValue I z k := by
  simp [driftValue, momentIndex,
    FixedDetectorDriftCode.momentIndex]

@[simp]
theorem eval_driftCode_detectorIndex
    (I : DQLSystem eqs vars)
    (b : Fin 2)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    eval₂Hom (algebraMap ℚ ℝ)
        (FixedDetectorPolynomialCode.point z)
        (PolynomialCode.decode
          (driftCode I (detectorIndex b))) =
      ![(detectorValue z).re, (detectorValue z).im] b := by
  simp [driftValue, detectorIndex,
    FixedDetectorDriftCode.detectorIndex]

end HGAS.CorrectedFixedDetectorDriftCode
