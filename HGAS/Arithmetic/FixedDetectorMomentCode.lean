import HGAS.Arithmetic.FixedDetectorValidityEnergyCode
import Mathlib.Tactic

/-!
# Finite selector-moment codes for the fixed detector

For every arithmetic variable the all-state selector uses seven complex
mean-zero observables:

1. `Y - 1`;
2. `Y Q⁻¹ - 1/128`;
3. `p₄ - 1`;
4. `p₂ ζ⁻² - 1/4`;
5. `F - 1`;
6. `F (QV)⁻¹ - 1/256`;
7. `F Q⁻¹V - 1/256`.

Here `Q = ζ⁴` is the private arithmetic clock, `V` is the linear DQL
character, and `F = G T₁` is the gauge-corrected Jacobi output.  This file
compiles those observables into the final fixed-detector coordinate layout.
The constants correspond to `r₀ = 1/4` and `λ = r₀⁴ = 1/256`.

The module is purely finite algebra.  It does not assume that any residual
vanishes or that the state is a canonical theta trajectory.
-/

namespace HGAS

open _root_.MvPolynomial
open Modular
open Clocks.ControllerPhaseProductCharacterCode

namespace FixedDetectorMomentCode

variable {eqs vars : ℕ}

abbrev clockCount (eqs vars : ℕ) : ℕ :=
  FixedDetectorPolynomialCode.clockCount eqs vars

abbrev dimension (eqs vars : ℕ) : ℕ :=
  FixedDetectorPolynomialCode.dimension eqs vars

/-- Seven complex selector moments per arithmetic variable. -/
abbrev localMomentCount : ℕ := 7

abbrev momentCount (vars : ℕ) : ℕ :=
  vars * localMomentCount

abbrev scalarMomentCount (vars : ℕ) : ℕ :=
  momentCount vars * 2

def momentBlockEmbedding (j : Fin vars) :
    Fin localMomentCount ↪ Fin (momentCount vars) :=
  PolynomialFiniteProductCode.blockEmbedding j

/-- A rational real constant regarded as a complex polynomial. -/
def rationalPair
    (c : ℚ) : ComplexPairCode (dimension eqs vars) :=
  (PolynomialCode.constant (RationalCode.encode c),
    PolynomialCode.zero)

def addPair
    (p r : ComplexPairCode (dimension eqs vars)) :
    ComplexPairCode (dimension eqs vars) :=
  (PolynomialCode.add p.1 r.1,
    PolynomialCode.add p.2 r.2)

def subPair
    (p r : ComplexPairCode (dimension eqs vars)) :
    ComplexPairCode (dimension eqs vars) :=
  (PolynomialCode.sub p.1 r.1,
    PolynomialCode.sub p.2 r.2)

@[simp]
theorem evalPair_rationalPair
    (c : ℚ) (x : Fin (dimension eqs vars) → ℝ) :
    evalPair (rationalPair c) x = ((c : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [evalPair, rationalPair]

@[simp]
theorem evalPair_addPair
    (p r : ComplexPairCode (dimension eqs vars))
    (x : Fin (dimension eqs vars) → ℝ) :
    evalPair (addPair p r) x =
      evalPair p x + evalPair r x := by
  apply Complex.ext <;> simp [evalPair, addPair]

@[simp]
theorem evalPair_subPair
    (p r : ComplexPairCode (dimension eqs vars))
    (x : Fin (dimension eqs vars) → ℝ) :
    evalPair (subPair p r) x =
      evalPair p x - evalPair r x := by
  apply Complex.ext <;> simp [evalPair, subPair]

/-! ## Lifting linked and controller observables -/

/-- Lift a local real scalar code into block `j` of the common linked
family. -/
def liftLocalLinkedScalar
    (j : Fin vars)
    (p : PolynomialCode
      (LinkedJacobiPolynomialCode.dimension +
        LinkedJacobiPolynomialCode.dimension)) :
    PolynomialCode
      (ControllerProductLinkedJacobiFamilyPolynomialCode.dimension
        (clockCount eqs vars) vars) :=
  PolynomialBlockCode.right
    (m :=
      ControllerProductLinkedJacobiFamilyPolynomialCode.controllerDimension
        (clockCount eqs vars))
    (PolynomialFiniteProductCode.lift j p)

def liftLocalLinkedPair
    (j : Fin vars)
    (p : ComplexPolynomialCode LinkedJacobiPolynomialCode.dimension) :
    ComplexPairCode
      (ControllerProductLinkedJacobiFamilyPolynomialCode.dimension
        (clockCount eqs vars) vars) :=
  (liftLocalLinkedScalar j p.1,
    liftLocalLinkedScalar j p.2)

/-- Lift a common-linked-family complex observable through the gauge,
reciprocal, and RHS extensions. -/
def liftLinkedPair
    (p : ComplexPairCode
      (ControllerProductLinkedJacobiFamilyPolynomialCode.dimension
        (clockCount eqs vars) vars)) :
    ComplexPairCode (dimension eqs vars) :=
  (FixedDetectorValidityEnergyCode.liftLinkedScalar p.1,
    FixedDetectorValidityEnergyCode.liftLinkedScalar p.2)

/-- Lift a local linked-block complex polynomial all the way to the final
detector layout. -/
def linkedCoordinatePair
    (j : Fin vars)
    (p : ComplexPolynomialCode LinkedJacobiPolynomialCode.dimension) :
    ComplexPairCode (dimension eqs vars) :=
  liftLinkedPair (liftLocalLinkedPair j p)

/-- Lift a controller character through every detector extension. -/
def controllerCharacterPair
    (exponents : Fin (clockCount eqs vars) → ℤ) :
    ComplexPairCode (dimension eqs vars) :=
  FixedDetectorPolynomialCode.liftBasePair
    (DetectorPoissonReciprocalCode.liftGaugeBasePair
      (DetectorPoissonReciprocalCode.liftControllerPair
        (characterCode exponents)))

/-- The final-layout code for the selected output `F_j = G_j T₁,j`. -/
def thetaOutputPair
    (j : Fin vars) :
    ComplexPairCode (dimension eqs vars) :=
  FixedDetectorPolynomialCode.liftBasePair
    (DetectorPoissonReciprocalCode.liftGaugeBasePair
      (DetectorJacobiGaugeData.thetaOutputCode (eqs := eqs) j))

@[simp]
theorem evalPair_liftLinkedPair
    (p : ComplexPairCode
      (ControllerProductLinkedJacobiFamilyPolynomialCode.dimension
        (clockCount eqs vars) vars))
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    evalPair (liftLinkedPair p)
        (FixedDetectorPolynomialCode.point z) =
      evalPair p
        (ControllerProductLinkedJacobiFamilyPolynomialCode.point
          z.base.base.source) := by
  apply Complex.ext <;>
    simp [evalPair, liftLinkedPair,
      FixedDetectorValidityEnergyCode.eval_liftLinkedScalar]

@[simp]
theorem evalPair_liftLocalLinkedPair
    (j : Fin vars)
    (p : ComplexPolynomialCode LinkedJacobiPolynomialCode.dimension)
    (z :
      ControllerProductLinkedJacobiFamilyState
        (clockCount eqs vars) vars) :
    evalPair (liftLocalLinkedPair j p)
        (ControllerProductLinkedJacobiFamilyPolynomialCode.point z) =
      ComplexPolynomialCode.eval p
        (LinkedJacobiPolynomialCode.point (z.linked j)) := by
  apply Complex.ext
  · simp only [evalPair, liftLocalLinkedPair]
    rw [ControllerProductLinkedJacobiFamilyPolynomialCode.point,
      liftLocalLinkedScalar, PolynomialBlockCode.eval₂Hom_right,
      PolynomialFiniteProductCode.eval₂Hom_lift]
    rw [show
      PolynomialFiniteProductCode.unflattenPoint
          (ControllerProductLinkedJacobiFamilyPolynomialCode.linkedFamilyPoint z)
          j =
        ComplexCoordinates.realifyPoint
          (LinkedJacobiPolynomialCode.point (z.linked j)) by
      simp [ControllerProductLinkedJacobiFamilyPolynomialCode.linkedFamilyPoint]]
    change
      ComplexPolynomialCode.evalReal p.1
          (LinkedJacobiPolynomialCode.point (z.linked j)) =
        (ComplexPolynomialCode.eval p
          (LinkedJacobiPolynomialCode.point (z.linked j))).re
    rfl
  · simp only [evalPair, liftLocalLinkedPair]
    rw [ControllerProductLinkedJacobiFamilyPolynomialCode.point,
      liftLocalLinkedScalar, PolynomialBlockCode.eval₂Hom_right,
      PolynomialFiniteProductCode.eval₂Hom_lift]
    rw [show
      PolynomialFiniteProductCode.unflattenPoint
          (ControllerProductLinkedJacobiFamilyPolynomialCode.linkedFamilyPoint z)
          j =
        ComplexCoordinates.realifyPoint
          (LinkedJacobiPolynomialCode.point (z.linked j)) by
      simp [ControllerProductLinkedJacobiFamilyPolynomialCode.linkedFamilyPoint]]
    change
      ComplexPolynomialCode.evalReal p.2
          (LinkedJacobiPolynomialCode.point (z.linked j)) =
        (ComplexPolynomialCode.eval p
          (LinkedJacobiPolynomialCode.point (z.linked j))).im
    rfl

@[simp]
theorem evalPair_linkedCoordinatePair
    (j : Fin vars)
    (p : ComplexPolynomialCode LinkedJacobiPolynomialCode.dimension)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    evalPair (linkedCoordinatePair j p)
        (FixedDetectorPolynomialCode.point z) =
      ComplexPolynomialCode.eval p
        (LinkedJacobiPolynomialCode.point
          (z.base.base.source.linked j)) := by
  rw [linkedCoordinatePair, evalPair_liftLinkedPair,
    evalPair_liftLocalLinkedPair]

@[simp]
theorem evalPair_controllerCharacterPair
    (exponents : Fin (clockCount eqs vars) → ℤ)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    evalPair (controllerCharacterPair exponents)
        (FixedDetectorPolynomialCode.point z) =
      characterValue exponents z.base.base.source.controllers := by
  rw [controllerCharacterPair,
    FixedDetectorPolynomialCode.evalPair_liftBasePair,
    DetectorPoissonReciprocalCode.evalPair_liftGaugeBasePair,
    DetectorPoissonReciprocalCode.evalPair_liftControllerPair]
  simp [ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint]

@[simp]
theorem evalPair_thetaOutputPair
    (j : Fin vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    evalPair (thetaOutputPair j)
        (FixedDetectorPolynomialCode.point z) =
      z.base.base.gauge j *
        (z.base.base.source.linked j).jacobi.T1 := by
  rw [thetaOutputPair,
    FixedDetectorPolynomialCode.evalPair_liftBasePair,
    DetectorPoissonReciprocalCode.evalPair_liftGaugeBasePair,
    DetectorJacobiGaugeData.thetaOutputCode]
  exact
    ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.evalPair_thetaOutputCode
      z.base.base j

/-! ## Character exponents used by the moments -/

def privateExponent
    (j : Fin vars) :
    Fin (clockCount eqs vars) → ℤ :=
  DetectorCharacterCode.flattenCharacter
    (DetectorCharacterCode.privateCharacter j)

def linearExponent
    (I : DQLSystem eqs vars) (j : Fin vars) :
    Fin (clockCount eqs vars) → ℤ :=
  DetectorCharacterCode.flattenCharacter
    (DetectorCharacterCode.linearCharacter I j)

def rootHalfExponent
    (j : Fin vars) :
    Fin (clockCount eqs vars) → ℤ :=
  fun i ↦
    match finSumFinEquiv.symm i with
    | Sum.inl k => if k = j then -2 else 0
    | Sum.inr _ => 0

def unaryFirstHarmonicExponent
    (j : Fin vars) :
    Fin (clockCount eqs vars) → ℤ :=
  fun i ↦ -privateExponent j i

def jacobiPlusExponent
    (I : DQLSystem eqs vars) (j : Fin vars) :
    Fin (clockCount eqs vars) → ℤ :=
  fun i ↦ -(privateExponent j i + linearExponent I j i)

def jacobiMinusExponent
    (I : DQLSystem eqs vars) (j : Fin vars) :
    Fin (clockCount eqs vars) → ℤ :=
  fun i ↦ -privateExponent j i + linearExponent I j i

/-! ## The seven complex moments -/

def YPair (j : Fin vars) :
    ComplexPairCode (dimension eqs vars) :=
  linkedCoordinatePair j LinkedJacobiPolynomialCode.YCode

def p2Pair (j : Fin vars) :
    ComplexPairCode (dimension eqs vars) :=
  linkedCoordinatePair j LinkedJacobiPolynomialCode.p2Code

def p4Pair (j : Fin vars) :
    ComplexPairCode (dimension eqs vars) :=
  linkedCoordinatePair j LinkedJacobiPolynomialCode.p4Code

def unaryMeanCode (j : Fin vars) :
    ComplexPairCode (dimension eqs vars) :=
  subPair (YPair j) (rationalPair 1)

def unaryFirstHarmonicCode (j : Fin vars) :
    ComplexPairCode (dimension eqs vars) :=
  subPair
    (mul (YPair j)
      (controllerCharacterPair (unaryFirstHarmonicExponent j)))
    (rationalPair (1 / 128))

def rootP4MeanCode (j : Fin vars) :
    ComplexPairCode (dimension eqs vars) :=
  subPair (p4Pair j) (rationalPair 1)

def rootP2MeanCode (j : Fin vars) :
    ComplexPairCode (dimension eqs vars) :=
  subPair
    (mul (p2Pair j)
      (controllerCharacterPair (rootHalfExponent j)))
    (rationalPair (1 / 4))

def jacobiMeanCode (j : Fin vars) :
    ComplexPairCode (dimension eqs vars) :=
  subPair (thetaOutputPair j) (rationalPair 1)

def jacobiPlusMeanCode
    (I : DQLSystem eqs vars) (j : Fin vars) :
    ComplexPairCode (dimension eqs vars) :=
  subPair
    (mul (thetaOutputPair j)
      (controllerCharacterPair (jacobiPlusExponent I j)))
    (rationalPair (1 / 256))

def jacobiMinusMeanCode
    (I : DQLSystem eqs vars) (j : Fin vars) :
    ComplexPairCode (dimension eqs vars) :=
  subPair
    (mul (thetaOutputPair j)
    (controllerCharacterPair (jacobiMinusExponent I j)))
    (rationalPair (1 / 256))

/-! ## Exact pointwise semantics -/

@[simp]
theorem evalPair_YPair
    (j : Fin vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    evalPair (YPair j) (FixedDetectorPolynomialCode.point z) =
      (z.base.base.source.linked j).unary.Y := by
  rw [YPair, evalPair_linkedCoordinatePair]
  simp [LinkedJacobiPolynomialCode.YCode,
    LinkedJacobiPolynomialCode.point,
    LinkedJacobiPolynomialCode.unaryEmbedding,
    UnaryPolynomialCode.modularPoint,
    UnaryPolynomialCode.YIndex]

@[simp]
theorem evalPair_p2Pair
    (j : Fin vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    evalPair (p2Pair j) (FixedDetectorPolynomialCode.point z) =
      (z.base.base.source.linked j).jacobi.p2 := by
  rw [p2Pair, evalPair_linkedCoordinatePair]
  simp [LinkedJacobiPolynomialCode.p2Code,
    LinkedJacobiPolynomialCode.point,
    LinkedJacobiPolynomialCode.jacobiEmbedding,
    JacobiPolynomialCode.point,
    JacobiPolynomialCode.p2Index]

@[simp]
theorem evalPair_p4Pair
    (j : Fin vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    evalPair (p4Pair j) (FixedDetectorPolynomialCode.point z) =
      (z.base.base.source.linked j).jacobi.p4 := by
  rw [p4Pair, evalPair_linkedCoordinatePair]
  simp [LinkedJacobiPolynomialCode.p4Code,
    LinkedJacobiPolynomialCode.point,
    LinkedJacobiPolynomialCode.jacobiEmbedding,
    JacobiPolynomialCode.point,
    JacobiPolynomialCode.p4Index]

@[simp]
theorem evalPair_unaryMeanCode
    (j : Fin vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    evalPair (unaryMeanCode j)
        (FixedDetectorPolynomialCode.point z) =
      (z.base.base.source.linked j).unary.Y - 1 := by
  simp [unaryMeanCode]

@[simp]
theorem evalPair_unaryFirstHarmonicCode
    (j : Fin vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    evalPair (unaryFirstHarmonicCode j)
        (FixedDetectorPolynomialCode.point z) =
      (z.base.base.source.linked j).unary.Y *
          characterValue (unaryFirstHarmonicExponent j)
            z.base.base.source.controllers -
        (1 / 128 : ℚ) := by
  simp [unaryFirstHarmonicCode]

@[simp]
theorem evalPair_rootP4MeanCode
    (j : Fin vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    evalPair (rootP4MeanCode j)
        (FixedDetectorPolynomialCode.point z) =
      (z.base.base.source.linked j).jacobi.p4 - 1 := by
  simp [rootP4MeanCode]

@[simp]
theorem evalPair_rootP2MeanCode
    (j : Fin vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    evalPair (rootP2MeanCode j)
        (FixedDetectorPolynomialCode.point z) =
      (z.base.base.source.linked j).jacobi.p2 *
          characterValue (rootHalfExponent j)
            z.base.base.source.controllers -
        (1 / 4 : ℚ) := by
  simp [rootP2MeanCode]

@[simp]
theorem evalPair_jacobiMeanCode
    (j : Fin vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    evalPair (jacobiMeanCode j)
        (FixedDetectorPolynomialCode.point z) =
      z.base.base.gauge j *
          (z.base.base.source.linked j).jacobi.T1 -
        1 := by
  simp [jacobiMeanCode]

@[simp]
theorem evalPair_jacobiPlusMeanCode
    (I : DQLSystem eqs vars) (j : Fin vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    evalPair (jacobiPlusMeanCode I j)
        (FixedDetectorPolynomialCode.point z) =
      (z.base.base.gauge j *
          (z.base.base.source.linked j).jacobi.T1) *
          characterValue (jacobiPlusExponent I j)
            z.base.base.source.controllers -
        (1 / 256 : ℚ) := by
  simp [jacobiPlusMeanCode]

@[simp]
theorem evalPair_jacobiMinusMeanCode
    (I : DQLSystem eqs vars) (j : Fin vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    evalPair (jacobiMinusMeanCode I j)
        (FixedDetectorPolynomialCode.point z) =
      (z.base.base.gauge j *
          (z.base.base.source.linked j).jacobi.T1) *
          characterValue (jacobiMinusExponent I j)
            z.base.base.source.controllers -
        (1 / 256 : ℚ) := by
  simp [jacobiMinusMeanCode]

/-- The fixed local ordering of the seven selector moments. -/
def localMomentCode
    (I : DQLSystem eqs vars) (j : Fin vars) :
    Fin localMomentCount →
      ComplexPairCode (dimension eqs vars) :=
  ![unaryMeanCode j,
    unaryFirstHarmonicCode j,
    rootP4MeanCode j,
    rootP2MeanCode j,
    jacobiMeanCode j,
    jacobiPlusMeanCode I j,
    jacobiMinusMeanCode I j]

/-- All complex moments, flattened first by variable and then by local
moment kind. -/
def momentCode
    (I : DQLSystem eqs vars) :
    Fin (momentCount vars) →
      ComplexPairCode (dimension eqs vars) :=
  fun k ↦
    let jm := finProdFinEquiv.symm k
    localMomentCode I jm.1 jm.2

/-- Real and imaginary moment coordinates, flattened in adjacent pairs. -/
def scalarMomentCode
    (I : DQLSystem eqs vars) :
    Fin (scalarMomentCount vars) →
      PolynomialCode (dimension eqs vars) :=
  fun k ↦
    let mc := finProdFinEquiv.symm k
    ![(momentCode I mc.1).1,
      (momentCode I mc.1).2] mc.2

/-! ## Structured semantic vectors

The following definitions deliberately repeat the seven displayed
mathematical formulas.  They are the human-facing interface of the
compiler: later arguments can speak about a vector of selector moments,
while the theorems below certify that the sparse codes are its literal
realification.
-/

/-- The seven semantic selector moments for variable `j`, in the same
order as `localMomentCode`. -/
noncomputable def localMomentValue
    (I : DQLSystem eqs vars) (j : Fin vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    Fin localMomentCount → ℂ :=
  ![
    (z.base.base.source.linked j).unary.Y - 1,
    (z.base.base.source.linked j).unary.Y *
        characterValue (unaryFirstHarmonicExponent j)
          z.base.base.source.controllers -
      (1 / 128 : ℚ),
    (z.base.base.source.linked j).jacobi.p4 - 1,
    (z.base.base.source.linked j).jacobi.p2 *
        characterValue (rootHalfExponent j)
          z.base.base.source.controllers -
      (1 / 4 : ℚ),
    z.base.base.gauge j *
        (z.base.base.source.linked j).jacobi.T1 -
      1,
    (z.base.base.gauge j *
        (z.base.base.source.linked j).jacobi.T1) *
        characterValue (jacobiPlusExponent I j)
          z.base.base.source.controllers -
      (1 / 256 : ℚ),
    (z.base.base.gauge j *
        (z.base.base.source.linked j).jacobi.T1) *
        characterValue (jacobiMinusExponent I j)
          z.base.base.source.controllers -
      (1 / 256 : ℚ)
  ]

/-- The flattened complex selector-moment vector. -/
noncomputable def momentValue
    (I : DQLSystem eqs vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    Fin (momentCount vars) → ℂ :=
  fun k ↦
    let jm := finProdFinEquiv.symm k
    localMomentValue I jm.1 z jm.2

/-- The realification of `momentValue`, with real and imaginary parts in
adjacent coordinates. -/
noncomputable def scalarMomentValue
    (I : DQLSystem eqs vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    Fin (scalarMomentCount vars) → ℝ :=
  fun k ↦
    let mc := finProdFinEquiv.symm k
    ![(momentValue I z mc.1).re,
      (momentValue I z mc.1).im] mc.2

@[simp]
theorem evalPair_localMomentCode
    (I : DQLSystem eqs vars) (j : Fin vars)
    (m : Fin localMomentCount)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    evalPair (localMomentCode I j m)
        (FixedDetectorPolynomialCode.point z) =
      localMomentValue I j z m := by
  fin_cases m <;>
    simp [localMomentCode, localMomentValue]

@[simp]
theorem evalPair_momentCode
    (I : DQLSystem eqs vars)
    (k : Fin (momentCount vars))
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    evalPair (momentCode I k)
        (FixedDetectorPolynomialCode.point z) =
      momentValue I z k := by
  simp [momentCode, momentValue]

@[simp]
theorem eval_scalarMomentCode
    (I : DQLSystem eqs vars)
    (k : Fin (scalarMomentCount vars))
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    eval₂Hom (algebraMap ℚ ℝ)
        (FixedDetectorPolynomialCode.point z)
        (PolynomialCode.decode (scalarMomentCode I k)) =
      scalarMomentValue I z k := by
  let mc := finProdFinEquiv.symm k
  have h :=
    evalPair_momentCode I mc.1 z
  change
    eval₂Hom (algebraMap ℚ ℝ)
        (FixedDetectorPolynomialCode.point z)
        (PolynomialCode.decode
          (![(momentCode I mc.1).1,
            (momentCode I mc.1).2] mc.2)) =
      ![(momentValue I z mc.1).re,
        (momentValue I z mc.1).im] mc.2
  have hmc : mc.2 = 0 ∨ mc.2 = 1 := by
    omega
  rcases hmc with hmc | hmc
  · rw [hmc]
    exact congrArg Complex.re h
  · rw [hmc]
    exact congrArg Complex.im h

end FixedDetectorMomentCode

end HGAS
