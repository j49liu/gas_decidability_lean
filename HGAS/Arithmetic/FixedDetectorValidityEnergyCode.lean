import HGAS.Arithmetic.FixedDetectorPolynomialDegrees
import HGAS.Arithmetic.FixedDetectorPolynomialComputability
import HGAS.Modular.ControllerProductLinkedJacobiFamilyResidualEnergyCode
import Mathlib.Tactic

/-!
# A single nonnegative validity coordinate for the fixed detector

The complete detector field contains three families of algebraic graph
constraints:

* the ten complex unary--Jacobi residuals in every linked block;
* the fourth-root gauge residuals; and
* the two Poisson reciprocal residuals for every arithmetic variable.

This module lifts all of their finite sparse codes through the successive
compiler layers and combines their squares into one polynomial.  Its value
is nonnegative at every ambient state, and it vanishes exactly when all
three residual families vanish.  The construction is independent of any
analytic theta-function interpretation and is reusable as one coordinate
of the compact accumulator drift.
-/

namespace HGAS

open _root_.MvPolynomial
open Clocks.ControllerPhaseProductCharacterCode
open Modular

namespace FixedDetectorValidityEnergyCode

variable {eqs vars : ℕ}

abbrev clockCount (eqs vars : ℕ) : ℕ :=
  FixedDetectorPolynomialCode.clockCount eqs vars

abbrev linkedDimension (eqs vars : ℕ) : ℕ :=
  ControllerProductLinkedJacobiFamilyPolynomialCode.dimension
    (clockCount eqs vars) vars

abbrev gaugeDimension (eqs vars : ℕ) : ℕ :=
  DetectorJacobiGaugeData.dimension eqs vars

abbrev poissonDimension (eqs vars : ℕ) : ℕ :=
  DetectorPoissonReciprocalCode.dimension eqs vars

abbrev dimension (eqs vars : ℕ) : ℕ :=
  FixedDetectorPolynomialCode.dimension eqs vars

/-- The canonical theta gauge relation is
`G_j^4 = λ χ_j`, with `λ = 1/256`.  Equivalently, the intended gauge
has modulus `r₀ = λ^(1/4) = 1/4` on the phase torus. -/
def thetaGaugeScale : Fin vars → RationalCode :=
  fun _ ↦ RationalCode.encode (1 / 256)

/-- Lift a scalar code from the controller--linked family through the
gauge, reciprocal, and RHS-oscillator extensions. -/
def liftLinkedScalar
    (p : PolynomialCode (linkedDimension eqs vars)) :
    PolynomialCode (dimension eqs vars) :=
  Clocks.RHSOscillatorPolynomialCode.liftBase
    (ComplexReciprocalFamilyPolynomialCode.liftBase
      (ComplexGaugeFamilyPolynomialCode.liftBase p))

/-- Lift a scalar gauge-layer code through the reciprocal and RHS layers. -/
def liftGaugeScalar
    (p : PolynomialCode (gaugeDimension eqs vars)) :
    PolynomialCode (dimension eqs vars) :=
  Clocks.RHSOscillatorPolynomialCode.liftBase
    (ComplexReciprocalFamilyPolynomialCode.liftBase p)

/-- Lift a scalar reciprocal-layer code through the final RHS layer. -/
def liftPoissonScalar
    (p : PolynomialCode (poissonDimension eqs vars)) :
    PolynomialCode (dimension eqs vars) :=
  Clocks.RHSOscillatorPolynomialCode.liftBase p

@[simp]
theorem eval_liftPoissonScalar
    (p : PolynomialCode (poissonDimension eqs vars))
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    eval₂Hom (algebraMap ℚ ℝ)
        (FixedDetectorPolynomialCode.point z)
        (PolynomialCode.decode (liftPoissonScalar p)) =
      eval₂Hom (algebraMap ℚ ℝ)
        (DetectorPoissonReciprocalCode.point z.base)
        (PolynomialCode.decode p) := by
  exact
    Clocks.RHSOscillatorPolynomialCode.eval₂Hom_liftBase
      p (DetectorPoissonReciprocalCode.point z.base) z.rhs

@[simp]
theorem eval_liftGaugeScalar
    (p : PolynomialCode (gaugeDimension eqs vars))
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    eval₂Hom (algebraMap ℚ ℝ)
        (FixedDetectorPolynomialCode.point z)
        (PolynomialCode.decode (liftGaugeScalar p)) =
      eval₂Hom (algebraMap ℚ ℝ)
        (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.point
          z.base.base)
        (PolynomialCode.decode p) := by
  simp only [FixedDetectorPolynomialCode.point]
  rw [liftGaugeScalar,
    Clocks.RHSOscillatorPolynomialCode.eval₂Hom_liftBase]
  exact
    ComplexReciprocalFamilyPolynomialCode.eval₂Hom_liftBase_point
      p (DetectorPoissonReciprocalCode.rawState z.base)

@[simp]
theorem eval_liftLinkedScalar
    (p : PolynomialCode (linkedDimension eqs vars))
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    eval₂Hom (algebraMap ℚ ℝ)
        (FixedDetectorPolynomialCode.point z)
        (PolynomialCode.decode (liftLinkedScalar p)) =
      eval₂Hom (algebraMap ℚ ℝ)
        (ControllerProductLinkedJacobiFamilyPolynomialCode.point
          z.base.base.source)
        (PolynomialCode.decode p) := by
  change
    eval₂Hom (algebraMap ℚ ℝ)
        (FixedDetectorPolynomialCode.point z)
        (PolynomialCode.decode
          (liftGaugeScalar
            (ComplexGaugeFamilyPolynomialCode.liftBase p))) =
      _
  rw [eval_liftGaugeScalar]
  exact
    ComplexGaugeFamilyPolynomialCode.eval₂Hom_liftBase_point
      p
      (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.rawState
        z.base.base)

/-! ## Sparse energy codes -/

/-- The already aggregated linked unary--Jacobi residual energy, lifted to
the final detector layout. -/
def linkedResidualEnergyCode :
    PolynomialCode (dimension eqs vars) :=
  liftLinkedScalar
    (ControllerProductLinkedJacobiFamilyResidualEnergyCode.totalResidualEnergyCode
      (clockCount eqs vars) vars)

/-- One squared real gauge residual. -/
def gaugeResidualSquareCode
    (I : DQLSystem eqs vars)
    (k : Fin (ComplexGaugeFamilyPolynomialCode.gaugeDimension vars)) :
    PolynomialCode (dimension eqs vars) :=
  let p :=
    liftGaugeScalar
      (DetectorJacobiGaugeData.residualCode thetaGaugeScale I k)
  PolynomialCode.mul p p

/-- Sum of the squares of all real gauge residual coordinates. -/
def gaugeResidualEnergyCode
    (I : DQLSystem eqs vars) :
    PolynomialCode (dimension eqs vars) :=
  PolynomialCode.sumCodes
    (List.ofFn (gaugeResidualSquareCode I))

/-- One squared real reciprocal residual. -/
def reciprocalResidualSquareCode
    (I : DQLSystem eqs vars)
    (k : Fin
      (ComplexReciprocalFamilyPolynomialCode.reciprocalDimension
        (DetectorPoissonReciprocalCode.reciprocalCount vars))) :
    PolynomialCode (dimension eqs vars) :=
  let p :=
    liftPoissonScalar
      (DetectorPoissonReciprocalCode.residualCode I k)
  PolynomialCode.mul p p

/-- Sum of the squares of all real reciprocal residual coordinates. -/
def reciprocalResidualEnergyCode
    (I : DQLSystem eqs vars) :
    PolynomialCode (dimension eqs vars) :=
  PolynomialCode.sumCodes
    (List.ofFn (reciprocalResidualSquareCode I))

/-- One aggregate nonnegative validity polynomial for the complete fixed
detector. -/
def totalValidityEnergyCode
    (I : DQLSystem eqs vars) :
    PolynomialCode (dimension eqs vars) :=
  PolynomialCode.sumCodes
    [linkedResidualEnergyCode,
      gaugeResidualEnergyCode I,
      reciprocalResidualEnergyCode I]

/-! ## Exact evaluation and zero-set semantics -/

@[simp]
theorem eval_linkedResidualEnergyCode
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    eval₂Hom (algebraMap ℚ ℝ)
        (FixedDetectorPolynomialCode.point z)
        (PolynomialCode.decode
          (linkedResidualEnergyCode (eqs := eqs) (vars := vars))) =
      ∑ k : Fin
          (ControllerProductLinkedJacobiFamilyResidualEnergyCode.energyDimension
            vars),
        Complex.normSq
          (linkedJacobiResidual
            (LinkedJacobiPolynomialCode.residualIndex
              (finProdFinEquiv.symm k).2)
            (z.base.base.source.linked
              (finProdFinEquiv.symm k).1)) := by
  rw [linkedResidualEnergyCode, eval_liftLinkedScalar]
  exact
    ControllerProductLinkedJacobiFamilyResidualEnergyCode.eval_totalResidualEnergyCode
      z.base.base.source

@[simp]
theorem eval_gaugeResidualSquareCode
    (I : DQLSystem eqs vars)
    (z : FixedDetectorPolynomialCode.State eqs vars)
    (k : Fin (ComplexGaugeFamilyPolynomialCode.gaugeDimension vars)) :
    eval₂Hom (algebraMap ℚ ℝ)
        (FixedDetectorPolynomialCode.point z)
        (PolynomialCode.decode (gaugeResidualSquareCode I k)) =
      (eval₂Hom (algebraMap ℚ ℝ)
        (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.point
          z.base.base)
        (PolynomialCode.decode
          (DetectorJacobiGaugeData.residualCode thetaGaugeScale I k))) ^ 2 := by
  rw [gaugeResidualSquareCode,
    PolynomialCode.decode_mul_code, map_mul,
    eval_liftGaugeScalar]
  simp only [pow_two]

@[simp]
theorem eval_gaugeResidualEnergyCode
    (I : DQLSystem eqs vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    eval₂Hom (algebraMap ℚ ℝ)
        (FixedDetectorPolynomialCode.point z)
        (PolynomialCode.decode (gaugeResidualEnergyCode I)) =
      ∑ k : Fin
          (ComplexGaugeFamilyPolynomialCode.gaugeDimension vars),
        (eval₂Hom (algebraMap ℚ ℝ)
          (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.point
            z.base.base)
          (PolynomialCode.decode
            (DetectorJacobiGaugeData.residualCode
              thetaGaugeScale I k))) ^ 2 := by
  rw [gaugeResidualEnergyCode, PolynomialCode.decode_sumCodes,
    List.map_ofFn, List.sum_ofFn, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact eval_gaugeResidualSquareCode I z k

@[simp]
theorem eval_reciprocalResidualSquareCode
    (I : DQLSystem eqs vars)
    (z : FixedDetectorPolynomialCode.State eqs vars)
    (k : Fin
      (ComplexReciprocalFamilyPolynomialCode.reciprocalDimension
        (DetectorPoissonReciprocalCode.reciprocalCount vars))) :
    eval₂Hom (algebraMap ℚ ℝ)
        (FixedDetectorPolynomialCode.point z)
        (PolynomialCode.decode (reciprocalResidualSquareCode I k)) =
      (eval₂Hom (algebraMap ℚ ℝ)
        (DetectorPoissonReciprocalCode.point z.base)
        (PolynomialCode.decode
          (DetectorPoissonReciprocalCode.residualCode I k))) ^ 2 := by
  rw [reciprocalResidualSquareCode,
    PolynomialCode.decode_mul_code, map_mul,
    eval_liftPoissonScalar]
  simp only [pow_two]

@[simp]
theorem eval_reciprocalResidualEnergyCode
    (I : DQLSystem eqs vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    eval₂Hom (algebraMap ℚ ℝ)
        (FixedDetectorPolynomialCode.point z)
        (PolynomialCode.decode (reciprocalResidualEnergyCode I)) =
      ∑ k : Fin
          (ComplexReciprocalFamilyPolynomialCode.reciprocalDimension
            (DetectorPoissonReciprocalCode.reciprocalCount vars)),
        (eval₂Hom (algebraMap ℚ ℝ)
          (DetectorPoissonReciprocalCode.point z.base)
          (PolynomialCode.decode
            (DetectorPoissonReciprocalCode.residualCode I k))) ^ 2 := by
  rw [reciprocalResidualEnergyCode, PolynomialCode.decode_sumCodes,
    List.map_ofFn, List.sum_ofFn, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact eval_reciprocalResidualSquareCode I z k

theorem eval_linkedResidualEnergyCode_nonneg
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    0 ≤
      eval₂Hom (algebraMap ℚ ℝ)
        (FixedDetectorPolynomialCode.point z)
        (PolynomialCode.decode
          (linkedResidualEnergyCode (eqs := eqs) (vars := vars))) := by
  rw [eval_linkedResidualEnergyCode]
  exact Finset.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _

theorem eval_gaugeResidualEnergyCode_nonneg
    (I : DQLSystem eqs vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    0 ≤
      eval₂Hom (algebraMap ℚ ℝ)
        (FixedDetectorPolynomialCode.point z)
        (PolynomialCode.decode (gaugeResidualEnergyCode I)) := by
  rw [eval_gaugeResidualEnergyCode]
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

theorem eval_reciprocalResidualEnergyCode_nonneg
    (I : DQLSystem eqs vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    0 ≤
      eval₂Hom (algebraMap ℚ ℝ)
        (FixedDetectorPolynomialCode.point z)
        (PolynomialCode.decode (reciprocalResidualEnergyCode I)) := by
  rw [eval_reciprocalResidualEnergyCode]
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

theorem eval_gaugeResidualEnergyCode_eq_zero_iff
    (I : DQLSystem eqs vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    eval₂Hom (algebraMap ℚ ℝ)
        (FixedDetectorPolynomialCode.point z)
        (PolynomialCode.decode (gaugeResidualEnergyCode I)) = 0 ↔
      ∀ k,
        eval₂Hom (algebraMap ℚ ℝ)
          (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.point
            z.base.base)
          (PolynomialCode.decode
            (DetectorJacobiGaugeData.residualCode
              thetaGaugeScale I k)) = 0 := by
  rw [eval_gaugeResidualEnergyCode]
  constructor
  · intro h k
    have hk :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ ↦ sq_nonneg
          (eval₂Hom (algebraMap ℚ ℝ)
            (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.point
              z.base.base)
            (PolynomialCode.decode
              (DetectorJacobiGaugeData.residualCode
                thetaGaugeScale I j))))).1
        h k (Finset.mem_univ k)
    exact sq_eq_zero_iff.mp hk
  · intro h
    exact Finset.sum_eq_zero fun k _ ↦ by simp [h k]

theorem eval_reciprocalResidualEnergyCode_eq_zero_iff
    (I : DQLSystem eqs vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    eval₂Hom (algebraMap ℚ ℝ)
        (FixedDetectorPolynomialCode.point z)
        (PolynomialCode.decode (reciprocalResidualEnergyCode I)) = 0 ↔
      ∀ k,
        eval₂Hom (algebraMap ℚ ℝ)
          (DetectorPoissonReciprocalCode.point z.base)
          (PolynomialCode.decode
            (DetectorPoissonReciprocalCode.residualCode I k)) = 0 := by
  rw [eval_reciprocalResidualEnergyCode]
  constructor
  · intro h k
    have hk :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ ↦ sq_nonneg
          (eval₂Hom (algebraMap ℚ ℝ)
            (DetectorPoissonReciprocalCode.point z.base)
            (PolynomialCode.decode
              (DetectorPoissonReciprocalCode.residualCode I j))))).1
        h k (Finset.mem_univ k)
    exact sq_eq_zero_iff.mp hk
  · intro h
    exact Finset.sum_eq_zero fun k _ ↦ by simp [h k]

@[simp]
theorem eval_totalValidityEnergyCode
    (I : DQLSystem eqs vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    eval₂Hom (algebraMap ℚ ℝ)
        (FixedDetectorPolynomialCode.point z)
        (PolynomialCode.decode (totalValidityEnergyCode I)) =
      eval₂Hom (algebraMap ℚ ℝ)
          (FixedDetectorPolynomialCode.point z)
          (PolynomialCode.decode
            (linkedResidualEnergyCode (eqs := eqs) (vars := vars))) +
        eval₂Hom (algebraMap ℚ ℝ)
          (FixedDetectorPolynomialCode.point z)
          (PolynomialCode.decode (gaugeResidualEnergyCode I)) +
        eval₂Hom (algebraMap ℚ ℝ)
          (FixedDetectorPolynomialCode.point z)
          (PolynomialCode.decode (reciprocalResidualEnergyCode I)) := by
  rw [totalValidityEnergyCode, PolynomialCode.decode_sumCodes]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    map_add, add_zero]
  ring

theorem eval_totalValidityEnergyCode_nonneg
    (I : DQLSystem eqs vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    0 ≤
      eval₂Hom (algebraMap ℚ ℝ)
        (FixedDetectorPolynomialCode.point z)
        (PolynomialCode.decode (totalValidityEnergyCode I)) := by
  rw [eval_totalValidityEnergyCode]
  exact
    add_nonneg
      (add_nonneg
        (eval_linkedResidualEnergyCode_nonneg z)
        (eval_gaugeResidualEnergyCode_nonneg I z))
      (eval_reciprocalResidualEnergyCode_nonneg I z)

/-- The aggregate validity coordinate vanishes precisely when every linked
Jacobi residual and every scalar gauge/reciprocal residual vanishes. -/
theorem eval_totalValidityEnergyCode_eq_zero_iff
    (I : DQLSystem eqs vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    eval₂Hom (algebraMap ℚ ℝ)
        (FixedDetectorPolynomialCode.point z)
        (PolynomialCode.decode (totalValidityEnergyCode I)) = 0 ↔
      (∀ a (r : LinkedJacobiResidualIndex),
          linkedJacobiResidual r (z.base.base.source.linked a) = 0) ∧
        (∀ k,
          eval₂Hom (algebraMap ℚ ℝ)
            (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.point
              z.base.base)
            (PolynomialCode.decode
              (DetectorJacobiGaugeData.residualCode
                thetaGaugeScale I k)) = 0) ∧
        ∀ k,
          eval₂Hom (algebraMap ℚ ℝ)
            (DetectorPoissonReciprocalCode.point z.base)
            (PolynomialCode.decode
              (DetectorPoissonReciprocalCode.residualCode I k)) = 0 := by
  rw [eval_totalValidityEnergyCode]
  have hlinked :
      eval₂Hom (algebraMap ℚ ℝ)
          (FixedDetectorPolynomialCode.point z)
          (PolynomialCode.decode
            (linkedResidualEnergyCode (eqs := eqs) (vars := vars))) = 0 ↔
        ∀ a (r : LinkedJacobiResidualIndex),
          linkedJacobiResidual r
            (z.base.base.source.linked a) = 0 := by
    rw [linkedResidualEnergyCode, eval_liftLinkedScalar]
    exact
      ControllerProductLinkedJacobiFamilyResidualEnergyCode.eval_totalResidualEnergyCode_eq_zero_iff
        z.base.base.source
  have hfirst_nonneg :=
    eval_linkedResidualEnergyCode_nonneg
      (eqs := eqs) (vars := vars) z
  have hsecond_nonneg :=
    eval_gaugeResidualEnergyCode_nonneg I z
  have hthird_nonneg :=
    eval_reciprocalResidualEnergyCode_nonneg I z
  rw [add_eq_zero_iff_of_nonneg
      (add_nonneg hfirst_nonneg hsecond_nonneg)
      hthird_nonneg,
    add_eq_zero_iff_of_nonneg hfirst_nonneg hsecond_nonneg,
    hlinked,
    eval_gaugeResidualEnergyCode_eq_zero_iff,
    eval_reciprocalResidualEnergyCode_eq_zero_iff]
  tauto

/-! ## Degree ledger -/

def gaugeResidualEnergyDegree
    (I : DQLSystem eqs vars) : ℕ :=
  2 * max 4 (FixedDetectorPolynomialCode.gaugeExponentEnergySum I)

def reciprocalResidualEnergyDegree
    (I : DQLSystem eqs vars) : ℕ :=
  2 * (FixedDetectorPolynomialCode.reciprocalExponentEnergySum I + 1)

/-- One executable bound for the aggregate validity polynomial. -/
def validityDegree
    (I : DQLSystem eqs vars) : ℕ :=
  max 8
    (max (gaugeResidualEnergyDegree I)
      (reciprocalResidualEnergyDegree I))

theorem liftLinkedScalar_termsDegreeLE
    {D : ℕ}
    {p : PolynomialCode (linkedDimension eqs vars)}
    (hp : PolynomialCode.TermsDegreeLE D p) :
    PolynomialCode.TermsDegreeLE D (liftLinkedScalar p) :=
  Clocks.RHSOscillatorPolynomialCode.liftBase_termsDegreeLE
    (ComplexReciprocalFamilyPolynomialCode.liftBase_termsDegreeLE
      (ComplexGaugeFamilyPolynomialCode.liftBase_termsDegreeLE hp))

theorem liftGaugeScalar_termsDegreeLE
    {D : ℕ}
    {p : PolynomialCode (gaugeDimension eqs vars)}
    (hp : PolynomialCode.TermsDegreeLE D p) :
    PolynomialCode.TermsDegreeLE D (liftGaugeScalar p) :=
  Clocks.RHSOscillatorPolynomialCode.liftBase_termsDegreeLE
    (ComplexReciprocalFamilyPolynomialCode.liftBase_termsDegreeLE hp)

theorem liftPoissonScalar_termsDegreeLE
    {D : ℕ}
    {p : PolynomialCode (poissonDimension eqs vars)}
    (hp : PolynomialCode.TermsDegreeLE D p) :
    PolynomialCode.TermsDegreeLE D (liftPoissonScalar p) :=
  Clocks.RHSOscillatorPolynomialCode.liftBase_termsDegreeLE hp

theorem linkedResidualEnergyCode_termsDegreeLE :
    PolynomialCode.TermsDegreeLE 8
      (linkedResidualEnergyCode (eqs := eqs) (vars := vars)) :=
  liftLinkedScalar_termsDegreeLE
    (ControllerProductLinkedJacobiFamilyResidualEnergyCode.totalResidualEnergyCode_termsDegreeLE
      (q := clockCount eqs vars) (b := vars))

theorem gaugeResidualSquareCode_termsDegreeLE
    (I : DQLSystem eqs vars)
    (k : Fin (ComplexGaugeFamilyPolynomialCode.gaugeDimension vars)) :
    PolynomialCode.TermsDegreeLE
      (gaugeResidualEnergyDegree I)
      (gaugeResidualSquareCode I k) := by
  have hbase :=
    FixedDetectorPolynomialCode.gaugeResidualCode_termsDegreeLE
      thetaGaugeScale I k
  have hlift := liftGaugeScalar_termsDegreeLE hbase
  simpa [gaugeResidualSquareCode, gaugeResidualEnergyDegree,
    two_mul] using
    PolynomialCode.termsDegreeLE_mul hlift hlift

theorem gaugeResidualEnergyCode_termsDegreeLE
    (I : DQLSystem eqs vars) :
    PolynomialCode.TermsDegreeLE
      (gaugeResidualEnergyDegree I)
      (gaugeResidualEnergyCode I) := by
  apply PolynomialCode.termsDegreeLE_sumCodes
  intro p hp
  rw [List.mem_ofFn] at hp
  obtain ⟨k, rfl⟩ := hp
  exact gaugeResidualSquareCode_termsDegreeLE I k

theorem reciprocalResidualSquareCode_termsDegreeLE
    (I : DQLSystem eqs vars)
    (k : Fin
      (ComplexReciprocalFamilyPolynomialCode.reciprocalDimension
        (DetectorPoissonReciprocalCode.reciprocalCount vars))) :
    PolynomialCode.TermsDegreeLE
      (reciprocalResidualEnergyDegree I)
      (reciprocalResidualSquareCode I k) := by
  have hbase :=
    FixedDetectorPolynomialCode.reciprocalResidualCode_termsDegreeLE I k
  have hlift := liftPoissonScalar_termsDegreeLE hbase
  simpa [reciprocalResidualSquareCode,
    reciprocalResidualEnergyDegree, two_mul] using
    PolynomialCode.termsDegreeLE_mul hlift hlift

theorem reciprocalResidualEnergyCode_termsDegreeLE
    (I : DQLSystem eqs vars) :
    PolynomialCode.TermsDegreeLE
      (reciprocalResidualEnergyDegree I)
      (reciprocalResidualEnergyCode I) := by
  apply PolynomialCode.termsDegreeLE_sumCodes
  intro p hp
  rw [List.mem_ofFn] at hp
  obtain ⟨k, rfl⟩ := hp
  exact reciprocalResidualSquareCode_termsDegreeLE I k

theorem totalValidityEnergyCode_termsDegreeLE
    (I : DQLSystem eqs vars) :
    PolynomialCode.TermsDegreeLE
      (validityDegree I)
      (totalValidityEnergyCode I) := by
  apply PolynomialCode.termsDegreeLE_sumCodes
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact linkedResidualEnergyCode_termsDegreeLE.promote
      (Nat.le_max_left 8 _)
  · exact (gaugeResidualEnergyCode_termsDegreeLE I).promote
      ((Nat.le_max_left _ _).trans (Nat.le_max_right 8 _))
  · exact (reciprocalResidualEnergyCode_termsDegreeLE I).promote
      ((Nat.le_max_right _ _).trans (Nat.le_max_right 8 _))

/-! ## Effectivity -/

theorem liftLinkedScalar_primrec :
    Primrec
      (liftLinkedScalar :
        PolynomialCode (linkedDimension eqs vars) →
          PolynomialCode (dimension eqs vars)) :=
  Clocks.RHSOscillatorPolynomialCode.liftBase_primrec.comp
    (ComplexReciprocalFamilyPolynomialCode.liftBase_primrec.comp
      ComplexGaugeFamilyPolynomialCode.liftBase_primrec)

theorem liftGaugeScalar_primrec :
    Primrec
      (liftGaugeScalar :
        PolynomialCode (gaugeDimension eqs vars) →
          PolynomialCode (dimension eqs vars)) :=
  Clocks.RHSOscillatorPolynomialCode.liftBase_primrec.comp
    ComplexReciprocalFamilyPolynomialCode.liftBase_primrec

theorem liftPoissonScalar_primrec :
    Primrec
      (liftPoissonScalar :
        PolynomialCode (poissonDimension eqs vars) →
          PolynomialCode (dimension eqs vars)) :=
  Clocks.RHSOscillatorPolynomialCode.liftBase_primrec

private theorem gaugeResidualFamily_primrec :
    Primrec
      (fun I : DQLSystem eqs vars ↦
        DetectorJacobiGaugeData.residualCode thetaGaugeScale I) := by
  let input :
      DQLSystem eqs vars →
        DetectorJacobiGaugeData.ResidualCompilerInput eqs vars :=
    fun I ↦ (thetaGaugeScale, I)
  have hinput : Primrec input :=
    Primrec.pair (Primrec.const thetaGaugeScale) Primrec.id
  exact
    (DetectorJacobiGaugeData.residualCode_primrec.comp hinput).of_eq
      (fun _ ↦ rfl)

private theorem gaugeResidualSquareCode_at_primrec
    (k : Fin (ComplexGaugeFamilyPolynomialCode.gaugeDimension vars)) :
    Primrec
      (fun I : DQLSystem eqs vars ↦
        gaugeResidualSquareCode I k) := by
  have hres :
      Primrec
        (fun I : DQLSystem eqs vars ↦
          DetectorJacobiGaugeData.residualCode
            thetaGaugeScale I k) :=
    Primrec.fin_app.comp gaugeResidualFamily_primrec
      (Primrec.const k)
  have hlift := liftGaugeScalar_primrec.comp hres
  exact
    (PolynomialCode.mul_primrec.comp hlift hlift).of_eq
      (fun _ ↦ rfl)

theorem gaugeResidualSquareCode_primrec :
    Primrec
      (gaugeResidualSquareCode :
        DQLSystem eqs vars →
          Fin (ComplexGaugeFamilyPolynomialCode.gaugeDimension vars) →
            PolynomialCode (dimension eqs vars)) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro k
  exact gaugeResidualSquareCode_at_primrec k

theorem gaugeResidualEnergyCode_primrec :
    Primrec
      (gaugeResidualEnergyCode :
        DQLSystem eqs vars →
          PolynomialCode (dimension eqs vars)) := by
  apply PolynomialCode.sumCodes_primrec.comp
  apply Primrec.list_ofFn
  intro k
  exact gaugeResidualSquareCode_at_primrec k

private theorem reciprocalResidualSquareCode_at_primrec
    (k : Fin
      (ComplexReciprocalFamilyPolynomialCode.reciprocalDimension
        (DetectorPoissonReciprocalCode.reciprocalCount vars))) :
    Primrec
      (fun I : DQLSystem eqs vars ↦
        reciprocalResidualSquareCode I k) := by
  have hres :
      Primrec
        (fun I : DQLSystem eqs vars ↦
          DetectorPoissonReciprocalCode.residualCode I k) :=
    Primrec.fin_app.comp
      DetectorPoissonReciprocalCode.residualCode_primrec
      (Primrec.const k)
  have hlift := liftPoissonScalar_primrec.comp hres
  exact
    (PolynomialCode.mul_primrec.comp hlift hlift).of_eq
      (fun _ ↦ rfl)

theorem reciprocalResidualSquareCode_primrec :
    Primrec
      (reciprocalResidualSquareCode :
        DQLSystem eqs vars →
          Fin
              (ComplexReciprocalFamilyPolynomialCode.reciprocalDimension
                (DetectorPoissonReciprocalCode.reciprocalCount vars)) →
            PolynomialCode (dimension eqs vars)) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro k
  exact reciprocalResidualSquareCode_at_primrec k

theorem reciprocalResidualEnergyCode_primrec :
    Primrec
      (reciprocalResidualEnergyCode :
        DQLSystem eqs vars →
          PolynomialCode (dimension eqs vars)) := by
  apply PolynomialCode.sumCodes_primrec.comp
  apply Primrec.list_ofFn
  intro k
  exact reciprocalResidualSquareCode_at_primrec k

/-- The complete aggregate validity coordinate is primitive recursive in
the finite DQL table. -/
theorem totalValidityEnergyCode_primrec :
    Primrec
      (totalValidityEnergyCode :
        DQLSystem eqs vars →
          PolynomialCode (dimension eqs vars)) := by
  apply PolynomialCode.sumCodes_primrec.comp
  exact
    Primrec.list_cons.comp
      (Primrec.const linkedResidualEnergyCode)
      (Primrec.list_cons.comp gaugeResidualEnergyCode_primrec
        (Primrec.list_cons.comp reciprocalResidualEnergyCode_primrec
          (Primrec.const [])))

theorem totalValidityEnergyCode_computable :
    Computable
      (totalValidityEnergyCode :
        DQLSystem eqs vars →
          PolynomialCode (dimension eqs vars)) :=
  totalValidityEnergyCode_primrec.to_comp

end FixedDetectorValidityEnergyCode

end HGAS
