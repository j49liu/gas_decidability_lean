import HGAS.Arithmetic.CorrectedFixedDetectorDriftCode
import HGAS.Algebra.PolynomialFiniteProductCode
import Mathlib.Tactic

/-!
# Radius-normalized validity for the corrected fixed detector

The original fixed detector treats every source coordinate as affine.
The controller and phase equations preserve their radii, but the old
validity energy did not say which invariant radius was intended.  In
particular, the appended right-hand-side oscillator admitted the invariant
choice `R = 0`, which annihilated the arithmetic detector.

This module adds exactly the missing normalizations:

* every controller pair has squared radius one;
* every driven phase pair has squared radius one; and
* the final right-hand-side oscillator has squared radius one.

Each equality is imposed by the square of its polynomial residual, and all
squares are added to the existing linked-Jacobi/gauge/reciprocal validity
energy.  Gauge and reciprocal radii are not separately normalized: once
the phase characters have unit modulus, their already compiled graph
equations force the required gauge modulus and reciprocal nonvanishing.

The resulting code has the same state dimension and the same single
validity coordinate.  The added terms have degree four.
-/

namespace HGAS.NormalizedCorrectedFixedDetectorValidityCode

open HGAS
open HGAS.Clocks
open HGAS.Modular
open _root_.MvPolynomial

noncomputable section

variable {eqs vars : ℕ}

abbrev clockCount (eqs vars : ℕ) : ℕ :=
  FixedDetectorPolynomialCode.clockCount eqs vars

abbrev dimension (eqs vars : ℕ) : ℕ :=
  FixedDetectorPolynomialCode.dimension eqs vars

/-! ## Local radius residuals -/

/-- Local controller residual `r²+s²-1` in one four-coordinate clock
block. -/
def localControllerRadiusResidualCode :
    PolynomialCode ControllerPolynomialCode.dimension :=
  PolynomialCode.sub
    (PolynomialCode.add
      (PolynomialCode.pow ControllerPolynomialCode.rCode 2)
      (PolynomialCode.pow ControllerPolynomialCode.sCode 2))
    PolynomialCode.one

/-- Local phase residual `c²+d²-1` in one four-coordinate clock block. -/
def localPhaseRadiusResidualCode :
    PolynomialCode ControllerPolynomialCode.dimension :=
  PolynomialCode.sub
    (PolynomialCode.add
      (PolynomialCode.pow ControllerPolynomialCode.cCode 2)
      (PolynomialCode.pow ControllerPolynomialCode.dCode 2))
    PolynomialCode.one

@[simp]
theorem eval_localControllerRadiusResidualCode
    (z : ControllerPhaseState ℝ) :
    eval₂Hom (algebraMap ℚ ℝ)
        (ControllerPolynomialCode.point z)
        (PolynomialCode.decode localControllerRadiusResidualCode) =
      Controller.controllerRadiusSq z.controller - 1 := by
  simp [localControllerRadiusResidualCode,
    ControllerPolynomialCode.rCode, ControllerPolynomialCode.sCode,
    ControllerPolynomialCode.point, ControllerPolynomialCode.rIndex,
    ControllerPolynomialCode.sIndex,
    Controller.controllerRadiusSq]

@[simp]
theorem eval_localPhaseRadiusResidualCode
    (z : ControllerPhaseState ℝ) :
    eval₂Hom (algebraMap ℚ ℝ)
        (ControllerPolynomialCode.point z)
        (PolynomialCode.decode localPhaseRadiusResidualCode) =
      Controller.phaseRadiusSq z.phase - 1 := by
  simp [localPhaseRadiusResidualCode,
    ControllerPolynomialCode.cCode, ControllerPolynomialCode.dCode,
    ControllerPolynomialCode.point, ControllerPolynomialCode.cIndex,
    ControllerPolynomialCode.dIndex,
    Controller.phaseRadiusSq]

/-! ## Lifting the clock residuals to the complete detector -/

/-- Lift a polynomial in all controller-product coordinates through the
linked, gauge, reciprocal, and RHS layers. -/
def liftControllerProductScalar
    (p : PolynomialCode
      (ControllerProductLinkedJacobiFamilyPolynomialCode.controllerDimension
        (clockCount eqs vars))) :
    PolynomialCode (dimension eqs vars) :=
  FixedDetectorValidityEnergyCode.liftLinkedScalar
    (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.liftController
      (b := vars) p)

/-- Radius residual of controller block `i`, in complete detector
coordinates. -/
def controllerRadiusResidualCode
    (i : Fin (clockCount eqs vars)) :
    PolynomialCode (dimension eqs vars) :=
  liftControllerProductScalar
    (PolynomialFiniteProductCode.lift i
      localControllerRadiusResidualCode)

/-- Radius residual of driven phase block `i`, in complete detector
coordinates. -/
def phaseRadiusResidualCode
    (i : Fin (clockCount eqs vars)) :
    PolynomialCode (dimension eqs vars) :=
  liftControllerProductScalar
    (PolynomialFiniteProductCode.lift i
      localPhaseRadiusResidualCode)

/-- Radius residual `R.re²+R.im²-1` of the final RHS oscillator. -/
def rhsRadiusResidualCode :
    PolynomialCode (dimension eqs vars) :=
  PolynomialCode.sub
    (PolynomialCode.add
      (PolynomialCode.pow
        Clocks.RHSOscillatorPolynomialCode.xCode 2)
      (PolynomialCode.pow
        Clocks.RHSOscillatorPolynomialCode.yCode 2))
    PolynomialCode.one

@[simp]
theorem eval_liftControllerProductScalar
    (p : PolynomialCode
      (ControllerProductLinkedJacobiFamilyPolynomialCode.controllerDimension
        (clockCount eqs vars)))
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    eval₂Hom (algebraMap ℚ ℝ)
        (FixedDetectorPolynomialCode.point z)
        (PolynomialCode.decode (liftControllerProductScalar p)) =
      eval₂Hom (algebraMap ℚ ℝ)
        (ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint
          z.base.base.source)
        (PolynomialCode.decode p) := by
  rw [liftControllerProductScalar,
    FixedDetectorValidityEnergyCode.eval_liftLinkedScalar,
    ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.eval₂Hom_liftController]

@[simp]
theorem eval_controllerRadiusResidualCode
    (i : Fin (clockCount eqs vars))
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    eval₂Hom (algebraMap ℚ ℝ)
        (FixedDetectorPolynomialCode.point z)
        (PolynomialCode.decode (controllerRadiusResidualCode i)) =
      Controller.controllerRadiusSq
          (z.base.base.source.controllers i).controller -
        1 := by
  rw [controllerRadiusResidualCode, eval_liftControllerProductScalar]
  change
    eval₂Hom (algebraMap ℚ ℝ)
        (ControllerPhaseProductPolynomialCode.point
          z.base.base.source.controllers)
        (PolynomialCode.decode
          (PolynomialFiniteProductCode.lift i
            localControllerRadiusResidualCode)) =
      _
  rw [PolynomialFiniteProductCode.eval₂Hom_lift]
  simp [ControllerPhaseProductPolynomialCode.point]

@[simp]
theorem eval_phaseRadiusResidualCode
    (i : Fin (clockCount eqs vars))
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    eval₂Hom (algebraMap ℚ ℝ)
        (FixedDetectorPolynomialCode.point z)
        (PolynomialCode.decode (phaseRadiusResidualCode i)) =
      Controller.phaseRadiusSq
          (z.base.base.source.controllers i).phase -
        1 := by
  rw [phaseRadiusResidualCode, eval_liftControllerProductScalar]
  change
    eval₂Hom (algebraMap ℚ ℝ)
        (ControllerPhaseProductPolynomialCode.point
          z.base.base.source.controllers)
        (PolynomialCode.decode
          (PolynomialFiniteProductCode.lift i
            localPhaseRadiusResidualCode)) =
      _
  rw [PolynomialFiniteProductCode.eval₂Hom_lift]
  simp [ControllerPhaseProductPolynomialCode.point]

@[simp]
theorem eval_rhsRadiusResidualCode
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    eval₂Hom (algebraMap ℚ ℝ)
        (FixedDetectorPolynomialCode.point z)
        (PolynomialCode.decode
          (rhsRadiusResidualCode (eqs := eqs) (vars := vars))) =
      Controller.phaseRadiusSq z.rhs - 1 := by
  simp only [FixedDetectorPolynomialCode.point, rhsRadiusResidualCode,
    PolynomialCode.decode_sub_code, PolynomialCode.decode_add_code,
    PolynomialCode.decode_pow_code, map_sub, map_add, map_pow]
  rw [Clocks.RHSOscillatorPolynomialCode.eval₂Hom_xCode,
    Clocks.RHSOscillatorPolynomialCode.eval₂Hom_yCode]
  simp [Controller.phaseRadiusSq]

/-! ## The normalization energy -/

def controllerRadiusSquareCode
    (i : Fin (clockCount eqs vars)) :
    PolynomialCode (dimension eqs vars) :=
  PolynomialCode.pow (controllerRadiusResidualCode i) 2

def phaseRadiusSquareCode
    (i : Fin (clockCount eqs vars)) :
    PolynomialCode (dimension eqs vars) :=
  PolynomialCode.pow (phaseRadiusResidualCode i) 2

def rhsRadiusSquareCode :
    PolynomialCode (dimension eqs vars) :=
  PolynomialCode.pow
    (rhsRadiusResidualCode (eqs := eqs) (vars := vars)) 2

/-- Sum of all clock and RHS radius squares. -/
def normalizationEnergyCode :
    PolynomialCode (dimension eqs vars) :=
  PolynomialCode.sumCodes
    [PolynomialCode.sumCodes
        (List.ofFn
          (controllerRadiusSquareCode (eqs := eqs) (vars := vars))),
      PolynomialCode.sumCodes
        (List.ofFn
          (phaseRadiusSquareCode (eqs := eqs) (vars := vars))),
      rhsRadiusSquareCode (eqs := eqs) (vars := vars)]

/-- Human-facing value of the normalization energy. -/
def normalizationEnergyValue
    (z : FixedDetectorPolynomialCode.State eqs vars) : ℝ :=
  (∑ i : Fin (clockCount eqs vars),
      (Controller.controllerRadiusSq
          (z.base.base.source.controllers i).controller - 1) ^ 2) +
    (∑ i : Fin (clockCount eqs vars),
      (Controller.phaseRadiusSq
          (z.base.base.source.controllers i).phase - 1) ^ 2) +
    (Controller.phaseRadiusSq z.rhs - 1) ^ 2

@[simp]
theorem eval_controllerRadiusSquareCode
    (i : Fin (clockCount eqs vars))
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    eval₂Hom (algebraMap ℚ ℝ)
        (FixedDetectorPolynomialCode.point z)
        (PolynomialCode.decode (controllerRadiusSquareCode i)) =
      (Controller.controllerRadiusSq
          (z.base.base.source.controllers i).controller - 1) ^ 2 := by
  rw [controllerRadiusSquareCode,
    PolynomialCode.decode_pow_code, map_pow,
    eval_controllerRadiusResidualCode]

@[simp]
theorem eval_phaseRadiusSquareCode
    (i : Fin (clockCount eqs vars))
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    eval₂Hom (algebraMap ℚ ℝ)
        (FixedDetectorPolynomialCode.point z)
        (PolynomialCode.decode (phaseRadiusSquareCode i)) =
      (Controller.phaseRadiusSq
          (z.base.base.source.controllers i).phase - 1) ^ 2 := by
  rw [phaseRadiusSquareCode,
    PolynomialCode.decode_pow_code, map_pow,
    eval_phaseRadiusResidualCode]

@[simp]
theorem eval_rhsRadiusSquareCode
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    eval₂Hom (algebraMap ℚ ℝ)
        (FixedDetectorPolynomialCode.point z)
        (PolynomialCode.decode
          (rhsRadiusSquareCode (eqs := eqs) (vars := vars))) =
      (Controller.phaseRadiusSq z.rhs - 1) ^ 2 := by
  rw [rhsRadiusSquareCode,
    PolynomialCode.decode_pow_code, map_pow,
    eval_rhsRadiusResidualCode]

@[simp]
theorem eval_normalizationEnergyCode
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    eval₂Hom (algebraMap ℚ ℝ)
        (FixedDetectorPolynomialCode.point z)
        (PolynomialCode.decode
          (normalizationEnergyCode (eqs := eqs) (vars := vars))) =
      normalizationEnergyValue z := by
  have hcontroller :
      eval₂Hom (algebraMap ℚ ℝ)
          (FixedDetectorPolynomialCode.point z)
          (PolynomialCode.decode
            (PolynomialCode.sumCodes
              (List.ofFn
                (controllerRadiusSquareCode
                  (eqs := eqs) (vars := vars))))) =
        ∑ i : Fin (clockCount eqs vars),
          (Controller.controllerRadiusSq
              (z.base.base.source.controllers i).controller - 1) ^ 2 := by
    rw [PolynomialCode.decode_sumCodes, List.map_ofFn,
      List.sum_ofFn, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact eval_controllerRadiusSquareCode i z
  have hphase :
      eval₂Hom (algebraMap ℚ ℝ)
          (FixedDetectorPolynomialCode.point z)
          (PolynomialCode.decode
            (PolynomialCode.sumCodes
              (List.ofFn
                (phaseRadiusSquareCode
                  (eqs := eqs) (vars := vars))))) =
        ∑ i : Fin (clockCount eqs vars),
          (Controller.phaseRadiusSq
              (z.base.base.source.controllers i).phase - 1) ^ 2 := by
    rw [PolynomialCode.decode_sumCodes, List.map_ofFn,
      List.sum_ofFn, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact eval_phaseRadiusSquareCode i z
  rw [normalizationEnergyCode, PolynomialCode.decode_sumCodes]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    map_add, add_zero]
  rw [hcontroller, hphase, eval_rhsRadiusSquareCode]
  unfold normalizationEnergyValue
  ring

theorem normalizationEnergyValue_nonneg
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    0 ≤ normalizationEnergyValue z := by
  exact add_nonneg
    (add_nonneg
      (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
      (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _))
    (sq_nonneg _)

/-- Exact zero set of the added normalization energy. -/
theorem normalizationEnergyValue_eq_zero_iff
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    normalizationEnergyValue z = 0 ↔
      (∀ i,
        Controller.controllerRadiusSq
          (z.base.base.source.controllers i).controller = 1) ∧
      (∀ i,
        Controller.phaseRadiusSq
          (z.base.base.source.controllers i).phase = 1) ∧
      Controller.phaseRadiusSq z.rhs = 1 := by
  let A : ℝ :=
    ∑ i : Fin (clockCount eqs vars),
      (Controller.controllerRadiusSq
          (z.base.base.source.controllers i).controller - 1) ^ 2
  let B : ℝ :=
    ∑ i : Fin (clockCount eqs vars),
      (Controller.phaseRadiusSq
          (z.base.base.source.controllers i).phase - 1) ^ 2
  let C : ℝ := (Controller.phaseRadiusSq z.rhs - 1) ^ 2
  have hA : 0 ≤ A :=
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hB : 0 ≤ B :=
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hC : 0 ≤ C := sq_nonneg _
  change A + B + C = 0 ↔ _
  rw [add_eq_zero_iff_of_nonneg (add_nonneg hA hB) hC,
    add_eq_zero_iff_of_nonneg hA hB]
  constructor
  · rintro ⟨⟨hAzero, hBzero⟩, hCzero⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i
      have hi :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun j _ ↦ sq_nonneg
            (Controller.controllerRadiusSq
              (z.base.base.source.controllers j).controller - 1))).1
          hAzero i (Finset.mem_univ i)
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hi)
    · intro i
      have hi :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun j _ ↦ sq_nonneg
            (Controller.phaseRadiusSq
              (z.base.base.source.controllers j).phase - 1))).1
          hBzero i (Finset.mem_univ i)
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hi)
    · exact sub_eq_zero.mp (sq_eq_zero_iff.mp hCzero)
  · rintro ⟨hcontroller, hphase, hrhs⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact Finset.sum_eq_zero fun i _ ↦ by simp [hcontroller i]
    · exact Finset.sum_eq_zero fun i _ ↦ by simp [hphase i]
    · exact sq_eq_zero_iff.mpr (sub_eq_zero.mpr hrhs)

/-! ## Augmenting the old graph validity -/

/-- One aggregate nonnegative polynomial containing both the old graph
validity and all radius normalizations. -/
def totalNormalizedValidityEnergyCode
    (I : DQLSystem eqs vars) :
    PolynomialCode (dimension eqs vars) :=
  PolynomialCode.add
    (FixedDetectorValidityEnergyCode.totalValidityEnergyCode I)
    normalizationEnergyCode

def totalNormalizedValidityEnergyValue
    (I : DQLSystem eqs vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) : ℝ :=
  CorrectedFixedDetectorDriftCode.validityEnergyValue I z +
    normalizationEnergyValue z

@[simp]
theorem eval_totalNormalizedValidityEnergyCode
    (I : DQLSystem eqs vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    eval₂Hom (algebraMap ℚ ℝ)
        (FixedDetectorPolynomialCode.point z)
        (PolynomialCode.decode
          (totalNormalizedValidityEnergyCode I)) =
      totalNormalizedValidityEnergyValue I z := by
  rw [totalNormalizedValidityEnergyCode,
    PolynomialCode.decode_add_code, map_add,
    FixedDetectorDriftCode.eval_totalValidityEnergyCode_eq_validityEnergyValue,
    eval_normalizationEnergyCode]
  rfl

theorem totalNormalizedValidityEnergyValue_nonneg
    (I : DQLSystem eqs vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    0 ≤ totalNormalizedValidityEnergyValue I z :=
  add_nonneg
    (CorrectedFixedDetectorDriftCode.validityEnergyValue_nonneg I z)
    (normalizationEnergyValue_nonneg z)

/-- Vanishing now means all old graph constraints and every unit-radius
normalization, with no hidden zero-radius branch. -/
theorem totalNormalizedValidityEnergyValue_eq_zero_iff
    (I : DQLSystem eqs vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    totalNormalizedValidityEnergyValue I z = 0 ↔
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
        Controller.controllerRadiusSq
          (z.base.base.source.controllers i).controller = 1) ∧
      (∀ i,
        Controller.phaseRadiusSq
          (z.base.base.source.controllers i).phase = 1) ∧
      Controller.phaseRadiusSq z.rhs = 1 := by
  rw [totalNormalizedValidityEnergyValue]
  have hold :=
    CorrectedFixedDetectorDriftCode.validityEnergyValue_nonneg I z
  have hnew := normalizationEnergyValue_nonneg z
  rw [add_eq_zero_iff_of_nonneg hold hnew,
    CorrectedFixedDetectorDriftCode.validityEnergyValue_eq_zero_iff,
    normalizationEnergyValue_eq_zero_iff]

/-! ## Degree and effectivity ledgers -/

theorem localControllerRadiusResidualCode_termsDegreeLE :
    PolynomialCode.TermsDegreeLE 2
      localControllerRadiusResidualCode := by
  apply PolynomialCode.termsDegreeLE_sub
  · apply PolynomialCode.termsDegreeLE_add
    · simpa [ControllerPolynomialCode.rCode] using
        (PolynomialCode.termsDegreeLE_pow
          (PolynomialCode.termsDegreeLE_varCode
            ControllerPolynomialCode.rIndex) 2)
    · simpa [ControllerPolynomialCode.sCode] using
        (PolynomialCode.termsDegreeLE_pow
          (PolynomialCode.termsDegreeLE_varCode
            ControllerPolynomialCode.sIndex) 2)
  · exact PolynomialCode.termsDegreeLE_one.promote (by omega)

theorem localPhaseRadiusResidualCode_termsDegreeLE :
    PolynomialCode.TermsDegreeLE 2
      localPhaseRadiusResidualCode := by
  apply PolynomialCode.termsDegreeLE_sub
  · apply PolynomialCode.termsDegreeLE_add
    · simpa [ControllerPolynomialCode.cCode] using
        (PolynomialCode.termsDegreeLE_pow
          (PolynomialCode.termsDegreeLE_varCode
            ControllerPolynomialCode.cIndex) 2)
    · simpa [ControllerPolynomialCode.dCode] using
        (PolynomialCode.termsDegreeLE_pow
          (PolynomialCode.termsDegreeLE_varCode
            ControllerPolynomialCode.dIndex) 2)
  · exact PolynomialCode.termsDegreeLE_one.promote (by omega)

theorem liftControllerProductScalar_termsDegreeLE
    {D : ℕ}
    {p : PolynomialCode
      (ControllerProductLinkedJacobiFamilyPolynomialCode.controllerDimension
        (clockCount eqs vars))}
    (hp : PolynomialCode.TermsDegreeLE D p) :
    PolynomialCode.TermsDegreeLE D
      (liftControllerProductScalar p) :=
  FixedDetectorValidityEnergyCode.liftLinkedScalar_termsDegreeLE
    (PolynomialCode.termsDegreeLE_injectVariables
      ControllerProductLinkedJacobiFamilyPolynomialCode.controllersEmbedding
      hp)

theorem controllerRadiusResidualCode_termsDegreeLE
    (i : Fin (clockCount eqs vars)) :
    PolynomialCode.TermsDegreeLE 2
      (controllerRadiusResidualCode i) :=
  liftControllerProductScalar_termsDegreeLE
    (PolynomialFiniteProductCode.termsDegreeLE_lift
      localControllerRadiusResidualCode_termsDegreeLE)

theorem phaseRadiusResidualCode_termsDegreeLE
    (i : Fin (clockCount eqs vars)) :
    PolynomialCode.TermsDegreeLE 2
      (phaseRadiusResidualCode i) :=
  liftControllerProductScalar_termsDegreeLE
    (PolynomialFiniteProductCode.termsDegreeLE_lift
      localPhaseRadiusResidualCode_termsDegreeLE)

theorem rhsRadiusResidualCode_termsDegreeLE :
    PolynomialCode.TermsDegreeLE 2
      (rhsRadiusResidualCode (eqs := eqs) (vars := vars)) := by
  apply PolynomialCode.termsDegreeLE_sub
  · apply PolynomialCode.termsDegreeLE_add
    · simpa [Clocks.RHSOscillatorPolynomialCode.xCode] using
        (PolynomialCode.termsDegreeLE_pow
          (PolynomialCode.termsDegreeLE_varCode
            (Clocks.RHSOscillatorPolynomialCode.xIndex
              (FixedDetectorPolynomialCode.baseDimension eqs vars))) 2)
    · simpa [Clocks.RHSOscillatorPolynomialCode.yCode] using
        (PolynomialCode.termsDegreeLE_pow
          (PolynomialCode.termsDegreeLE_varCode
            (Clocks.RHSOscillatorPolynomialCode.yIndex
              (FixedDetectorPolynomialCode.baseDimension eqs vars))) 2)
  · exact PolynomialCode.termsDegreeLE_one.promote (by omega)

theorem normalizationEnergyCode_termsDegreeLE :
    PolynomialCode.TermsDegreeLE 4
      (normalizationEnergyCode (eqs := eqs) (vars := vars)) := by
  apply PolynomialCode.termsDegreeLE_sumCodes
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · apply PolynomialCode.termsDegreeLE_sumCodes
    intro p hp
    rw [List.mem_ofFn] at hp
    obtain ⟨i, rfl⟩ := hp
    simpa [controllerRadiusSquareCode, two_mul] using
      PolynomialCode.termsDegreeLE_pow
        (controllerRadiusResidualCode_termsDegreeLE i) 2
  · apply PolynomialCode.termsDegreeLE_sumCodes
    intro p hp
    rw [List.mem_ofFn] at hp
    obtain ⟨i, rfl⟩ := hp
    simpa [phaseRadiusSquareCode, two_mul] using
      PolynomialCode.termsDegreeLE_pow
        (phaseRadiusResidualCode_termsDegreeLE i) 2
  · simpa [rhsRadiusSquareCode, two_mul] using
      PolynomialCode.termsDegreeLE_pow
        (rhsRadiusResidualCode_termsDegreeLE
          (eqs := eqs) (vars := vars)) 2

theorem totalNormalizedValidityEnergyCode_termsDegreeLE
    (I : DQLSystem eqs vars) :
    PolynomialCode.TermsDegreeLE
      (max (FixedDetectorValidityEnergyCode.validityDegree I) 4)
      (totalNormalizedValidityEnergyCode I) := by
  apply PolynomialCode.termsDegreeLE_add
  · exact
      (FixedDetectorValidityEnergyCode.totalValidityEnergyCode_termsDegreeLE
        I).promote (Nat.le_max_left _ _)
  · exact normalizationEnergyCode_termsDegreeLE.promote
      (Nat.le_max_right _ _)

theorem totalNormalizedValidityEnergyCode_primrec :
    Primrec
      (totalNormalizedValidityEnergyCode :
        DQLSystem eqs vars →
          PolynomialCode (dimension eqs vars)) := by
  exact
    (PolynomialCode.add_primrec.comp
      FixedDetectorValidityEnergyCode.totalValidityEnergyCode_primrec
      (Primrec.const normalizationEnergyCode)).of_eq
      (fun _ ↦ rfl)

theorem totalNormalizedValidityEnergyCode_computable :
    Computable
      (totalNormalizedValidityEnergyCode :
        DQLSystem eqs vars →
          PolynomialCode (dimension eqs vars)) :=
  totalNormalizedValidityEnergyCode_primrec.to_comp

end

end HGAS.NormalizedCorrectedFixedDetectorValidityCode
