import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorValidityCode
import HGAS.Arithmetic.CorrectedFixedDetectorMomentSemantics
import Mathlib.Tactic

/-!
# Corrected fixed-detector drift with radius-normalized validity

This is a drop-in replacement for `CorrectedFixedDetectorDriftCode`.
It preserves the state dimension, drift dimension, seven corrected
selector moments, and two arithmetic detector coordinates.  Its sole
change is that drift coordinate zero is the normalized validity energy
from `NormalizedCorrectedFixedDetectorValidityCode`.
-/

namespace HGAS.NormalizedCorrectedFixedDetectorDriftCode

open HGAS
open HGAS.Modular
open _root_.MvPolynomial

noncomputable section

variable {eqs vars : ℕ}

abbrev dimension (eqs vars : ℕ) : ℕ :=
  CorrectedFixedDetectorDriftCode.dimension eqs vars

abbrev driftCount (vars : ℕ) : ℕ :=
  CorrectedFixedDetectorDriftCode.driftCount vars

abbrev validityIndex (vars : ℕ) : Fin (driftCount vars) :=
  CorrectedFixedDetectorDriftCode.validityIndex vars

abbrev momentIndex
    (k : Fin (CorrectedFixedDetectorMomentCode.scalarMomentCount vars)) :
    Fin (driftCount vars) :=
  CorrectedFixedDetectorDriftCode.momentIndex k

abbrev detectorIndex (b : Fin 2) :
    Fin (driftCount vars) :=
  CorrectedFixedDetectorDriftCode.detectorIndex b

/-- Normalized corrected drift in the unchanged block order. -/
def driftCode
    (I : DQLSystem eqs vars) :
    Fin (driftCount vars) → PolynomialCode (dimension eqs vars) :=
  fun q ↦
    match finSumFinEquiv.symm q with
    | Sum.inl _ =>
        HGAS.NormalizedCorrectedFixedDetectorValidityCode.totalNormalizedValidityEnergyCode
          I
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

noncomputable abbrev validityEnergyValue
    (I : DQLSystem eqs vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) : ℝ :=
  HGAS.NormalizedCorrectedFixedDetectorValidityCode.totalNormalizedValidityEnergyValue
    I z

noncomputable abbrev detectorValue
    (z : FixedDetectorPolynomialCode.State eqs vars) : ℂ :=
  CorrectedFixedDetectorDriftCode.detectorValue z

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
  HGAS.NormalizedCorrectedFixedDetectorValidityCode.totalNormalizedValidityEnergyValue_nonneg
    I z

/-- Exact graph-and-normalization semantics of the first coordinate. -/
theorem validityEnergyValue_eq_zero_iff
    (I : DQLSystem eqs vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    validityEnergyValue I z = 0 ↔
      ((∀ a (r : LinkedJacobiResidualIndex),
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
              (DetectorPoissonReciprocalCode.residualCode I k)) = 0) ∧
      (∀ i,
        Clocks.Controller.controllerRadiusSq
          (z.base.base.source.controllers i).controller = 1) ∧
      (∀ i,
        Clocks.Controller.phaseRadiusSq
          (z.base.base.source.controllers i).phase = 1) ∧
      Clocks.Controller.phaseRadiusSq z.rhs = 1 :=
  HGAS.NormalizedCorrectedFixedDetectorValidityCode.totalNormalizedValidityEnergyValue_eq_zero_iff
    I z

/-- Every emitted sparse polynomial has the displayed semantic value. -/
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
    exact
      HGAS.NormalizedCorrectedFixedDetectorValidityCode.eval_totalNormalizedValidityEnergyCode
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
    CorrectedFixedDetectorDriftCode.momentIndex]

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
    CorrectedFixedDetectorDriftCode.detectorIndex]

end

end HGAS.NormalizedCorrectedFixedDetectorDriftCode
