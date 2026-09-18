import HGAS.Arithmetic.FixedDetectorMomentCode
import Mathlib.Tactic

/-!
# The complete finite drift observable of the fixed detector

The affine source is coupled to one vector accumulator.  Its drift has
three logically separate blocks:

1. one nonnegative validity energy, whose zero set is exactly the full
   linked-Jacobi, gauge, and reciprocal graph;
2. the real and imaginary parts of all seven selector moments for every
   arithmetic variable; and
3. the real and imaginary parts of the final arithmetic detector.

Keeping these entries in separate coordinates is essential.  A zero
vector average then cannot hide a failed validity equation or cancel one
selector moment against another.

This file contains the finite syntax and exact pointwise semantics.  The
degree and computability ledgers are deliberately separate reusable
modules.
-/

namespace HGAS

open _root_.MvPolynomial
open Modular
open Clocks.ControllerPhaseProductCharacterCode

namespace FixedDetectorDriftCode

variable {eqs vars : ℕ}

abbrev dimension (eqs vars : ℕ) : ℕ :=
  FixedDetectorPolynomialCode.dimension eqs vars

/-- One validity entry, all realified moments, and two detector entries. -/
abbrev driftCount (vars : ℕ) : ℕ :=
  1 + (FixedDetectorMomentCode.scalarMomentCount vars + 2)

/-- Index of the aggregate nonnegative validity energy. -/
def validityIndex (vars : ℕ) : Fin (driftCount vars) :=
  finSumFinEquiv (Sum.inl (0 : Fin 1))

/-- Index of one realified selector-moment coordinate. -/
def momentIndex
    (k : Fin (FixedDetectorMomentCode.scalarMomentCount vars)) :
    Fin (driftCount vars) :=
  finSumFinEquiv
    (Sum.inr (finSumFinEquiv (Sum.inl k)))

/-- Index `0` is the real and index `1` the imaginary detector
coordinate. -/
def detectorIndex (b : Fin 2) :
    Fin (driftCount vars) :=
  finSumFinEquiv
    (Sum.inr (finSumFinEquiv (Sum.inr b)))

@[simp]
theorem finSumFinEquiv_symm_validityIndex :
    finSumFinEquiv.symm (validityIndex vars) =
      Sum.inl (0 : Fin 1) := by
  simp [validityIndex]

@[simp]
theorem finSumFinEquiv_symm_momentIndex
    (k : Fin (FixedDetectorMomentCode.scalarMomentCount vars)) :
    finSumFinEquiv.symm (momentIndex k) =
      Sum.inr (finSumFinEquiv (Sum.inl k)) := by
  simp [momentIndex]

@[simp]
theorem finSumFinEquiv_symm_detectorIndex
    (b : Fin 2) :
    finSumFinEquiv.symm (detectorIndex (vars := vars) b) =
      Sum.inr (finSumFinEquiv (Sum.inr b)) := by
  simp [detectorIndex]

/-- The complete drift compiler in its canonical block order. -/
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
            FixedDetectorMomentCode.scalarMomentCode I k
        | Sum.inr b =>
            ![
              (FixedDetectorPolynomialCode.detectorCode
                (eqs := eqs) (vars := vars)).1,
              (FixedDetectorPolynomialCode.detectorCode
                (eqs := eqs) (vars := vars)).2
            ] b

/-! ## Human-facing semantics -/

/-- Explicit sum of squares represented by the validity coordinate. -/
noncomputable def validityEnergyValue
    (I : DQLSystem eqs vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) : ℝ :=
  (∑ k : Fin
      (ControllerProductLinkedJacobiFamilyResidualEnergyCode.energyDimension
        vars),
      Complex.normSq
        (linkedJacobiResidual
          (LinkedJacobiPolynomialCode.residualIndex
            (finProdFinEquiv.symm k).2)
          (z.base.base.source.linked
            (finProdFinEquiv.symm k).1))) +
    (∑ k : Fin
      (ComplexGaugeFamilyPolynomialCode.gaugeDimension vars),
      (eval₂Hom (algebraMap ℚ ℝ)
        (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.point
          z.base.base)
        (PolynomialCode.decode
          (DetectorJacobiGaugeData.residualCode
            FixedDetectorValidityEnergyCode.thetaGaugeScale I k))) ^ 2) +
    ∑ k : Fin
      (ComplexReciprocalFamilyPolynomialCode.reciprocalDimension
        (DetectorPoissonReciprocalCode.reciprocalCount vars)),
      (eval₂Hom (algebraMap ℚ ℝ)
        (DetectorPoissonReciprocalCode.point z.base)
        (PolynomialCode.decode
          (DetectorPoissonReciprocalCode.residualCode I k))) ^ 2

/-- The complex arithmetic detector evaluated on a structured state. -/
noncomputable def detectorValue
    (z : FixedDetectorPolynomialCode.State eqs vars) : ℂ :=
  (⟨z.rhs.c, z.rhs.d⟩ : ℂ) *
    ∏ j : Fin vars,
      ((z.base.base.gauge j *
          (z.base.base.source.linked j).jacobi.T1) *
        (((3 / 4 : ℝ) : ℂ) *
          z.base.reciprocal
            (DetectorPoissonReciprocalCode.positiveIndex j) *
          z.base.reciprocal
            (DetectorPoissonReciprocalCode.negativeIndex j)))

/-- The semantic vector matching `driftCode`. -/
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
            FixedDetectorMomentCode.scalarMomentValue I z k
        | Sum.inr b =>
            ![(detectorValue z).re, (detectorValue z).im] b

@[simp]
theorem eval_totalValidityEnergyCode_eq_validityEnergyValue
    (I : DQLSystem eqs vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    eval₂Hom (algebraMap ℚ ℝ)
        (FixedDetectorPolynomialCode.point z)
        (PolynomialCode.decode
          (FixedDetectorValidityEnergyCode.totalValidityEnergyCode I)) =
      validityEnergyValue I z := by
  rw [FixedDetectorValidityEnergyCode.eval_totalValidityEnergyCode,
    FixedDetectorValidityEnergyCode.eval_linkedResidualEnergyCode,
    FixedDetectorValidityEnergyCode.eval_gaugeResidualEnergyCode,
    FixedDetectorValidityEnergyCode.eval_reciprocalResidualEnergyCode]
  rfl

theorem validityEnergyValue_nonneg
    (I : DQLSystem eqs vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    0 ≤ validityEnergyValue I z := by
  rw [← eval_totalValidityEnergyCode_eq_validityEnergyValue]
  exact
    FixedDetectorValidityEnergyCode.eval_totalValidityEnergyCode_nonneg I z

/-- Vanishing of the first drift coordinate means literal pointwise
validity of every graph constraint. -/
theorem validityEnergyValue_eq_zero_iff
    (I : DQLSystem eqs vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    validityEnergyValue I z = 0 ↔
      (∀ a (r : LinkedJacobiResidualIndex),
          linkedJacobiResidual r (z.base.base.source.linked a) = 0) ∧
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
              (DetectorPoissonReciprocalCode.residualCode I k)) = 0 := by
  rw [← eval_totalValidityEnergyCode_eq_validityEnergyValue]
  exact
    FixedDetectorValidityEnergyCode.eval_totalValidityEnergyCode_eq_zero_iff
      I z

@[simp]
theorem evalPair_detectorCode_eq_detectorValue
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    evalPair
        (FixedDetectorPolynomialCode.detectorCode
          (eqs := eqs) (vars := vars))
        (FixedDetectorPolynomialCode.point z) =
      detectorValue z := by
  exact FixedDetectorPolynomialCode.evalPair_detectorCode z

/-- Every emitted sparse polynomial evaluates to its correspondingly
named semantic drift coordinate. -/
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
    exact eval_totalValidityEnergyCode_eq_validityEnergyValue I z
  · obtain ⟨k | b, rfl⟩ := finSumFinEquiv.surjective r
    · simp [driftCode, driftValue]
    · fin_cases b
      · simpa [driftCode, driftValue, evalPair] using
          congrArg Complex.re
            (evalPair_detectorCode_eq_detectorValue z)
      · simpa [driftCode, driftValue, evalPair] using
          congrArg Complex.im
            (evalPair_detectorCode_eq_detectorValue z)

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
    (k : Fin (FixedDetectorMomentCode.scalarMomentCount vars))
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    eval₂Hom (algebraMap ℚ ℝ)
        (FixedDetectorPolynomialCode.point z)
        (PolynomialCode.decode
          (driftCode I (momentIndex k))) =
      FixedDetectorMomentCode.scalarMomentValue I z k :=
  by
    simp [driftValue, momentIndex]

@[simp]
theorem eval_driftCode_detectorIndex
    (I : DQLSystem eqs vars)
    (b : Fin 2)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    eval₂Hom (algebraMap ℚ ℝ)
        (FixedDetectorPolynomialCode.point z)
        (PolynomialCode.decode
          (driftCode I (detectorIndex b))) =
      ![(detectorValue z).re, (detectorValue z).im] b :=
  by
    simp [driftValue, detectorIndex]

end FixedDetectorDriftCode

end HGAS
