import HGAS.Arithmetic.DetectorJacobiGaugeData
import HGAS.Compiler.ComplexReciprocalFamilyPolynomialCode
import Mathlib.Tactic

/-!
# Polynomial Poisson factors for the DQL detector

For each arithmetic variable, put

```text
                         Wⱼ = Qⱼ⁻¹Sⱼ.
```

At the fixed value `η = 1/2`, the Poisson kernel is

```text
       Pη(Wⱼ) = (1-η²) / ((1-ηWⱼ)(1-ηWⱼ⁻¹)).
```

This module adjoins two complex reciprocal states for every `j`:

```text
       Gⱼ,+ = (1-ηWⱼ)⁻¹,       Gⱼ,- = (1-ηWⱼ⁻¹)⁻¹.
```

Both characters and both character derivatives are compiled from the
common controller product and lifted through the completed Jacobi/gauge
source.  The final Poisson factor is the literal fixed-degree polynomial

```text
                         (1-η²)Gⱼ,+Gⱼ,-.
```

All realization statements are ambient polynomial identities; reciprocal
equations are represented separately by the audited residual family.
-/

namespace HGAS

namespace DetectorPoissonReciprocalCode

open _root_.MvPolynomial
open Clocks
open Clocks.ControllerPhaseProductCharacterCode
open Modular

variable {eqs vars : ℕ}

abbrev clockCount (eqs vars : ℕ) : ℕ :=
  DetectorCharacterCode.clockCount eqs vars

abbrev baseDimension (eqs vars : ℕ) : ℕ :=
  DetectorJacobiGaugeData.dimension eqs vars

/-- Two denominator characters, `W` and `W⁻¹`, per arithmetic variable. -/
abbrev reciprocalCount (vars : ℕ) : ℕ :=
  vars * 2

abbrev dimension (eqs vars : ℕ) : ℕ :=
  ComplexReciprocalFamilyPolynomialCode.dimension
    (baseDimension eqs vars) (reciprocalCount vars)

/-- A completed Jacobi/gauge source together with every Poisson
reciprocal. -/
@[ext]
structure State (eqs vars : ℕ) where
  base :
    ControllerProductLinkedJacobiGaugeFamilyState
      (clockCount eqs vars) vars
  reciprocal : Fin (reciprocalCount vars) → ℂ

def rawState (z : State eqs vars) :
    ComplexReciprocalFamilyPolynomialCode.State
      (baseDimension eqs vars) (reciprocalCount vars) :=
  (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.point z.base,
    z.reciprocal)

def point (z : State eqs vars) :
    Fin (dimension eqs vars) → ℝ :=
  ComplexReciprocalFamilyPolynomialCode.point (rawState z)

def state (x : Fin (dimension eqs vars) → ℝ) :
    State eqs vars :=
  let z := ComplexReciprocalFamilyPolynomialCode.state x
  { base :=
      ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.state z.1
    reciprocal := z.2 }

@[simp]
theorem state_point (z : State eqs vars) :
    state (point z) = z := by
  apply State.ext
  · simp [state, point, rawState]
  · simp [state, point, rawState]

@[simp]
theorem point_state
    (x : Fin (dimension eqs vars) → ℝ) :
    point (state x) = x := by
  simp [state, point, rawState]

/-! ## The two signed denominator characters -/

def positiveIndex (j : Fin vars) :
    Fin (reciprocalCount vars) :=
  finProdFinEquiv (j, (0 : Fin 2))

def negativeIndex (j : Fin vars) :
    Fin (reciprocalCount vars) :=
  finProdFinEquiv (j, (1 : Fin 2))

def poissonExponent
    (I : DQLSystem eqs vars) (j : Fin vars) :
    Fin (clockCount eqs vars) → ℤ :=
  DetectorCharacterCode.flattenCharacter
    (DetectorCharacterCode.poissonArgumentCharacter I j)

def reciprocalExponent
    (I : DQLSystem eqs vars)
    (k : Fin (reciprocalCount vars)) :
    Fin (clockCount eqs vars) → ℤ :=
  let js := finProdFinEquiv.symm k
  ![poissonExponent I js.1,
    fun i ↦ -poissonExponent I js.1 i] js.2

@[simp]
theorem reciprocalExponent_positiveIndex
    (I : DQLSystem eqs vars) (j : Fin vars) :
    reciprocalExponent I (positiveIndex j) =
      poissonExponent I j := by
  simp [reciprocalExponent, positiveIndex]

@[simp]
theorem reciprocalExponent_negativeIndex
    (I : DQLSystem eqs vars) (j : Fin vars) :
    reciprocalExponent I (negativeIndex j) =
      fun i ↦ -poissonExponent I j i := by
  simp [reciprocalExponent, negativeIndex]

/-! ## Lifting controller character codes through the gauge source -/

def liftControllerPair
    (p : ComplexPairCode
      (ControllerProductLinkedJacobiFamilyPolynomialCode.controllerDimension
        (clockCount eqs vars))) :
    ComplexPairCode (baseDimension eqs vars) :=
  ComplexGaugeFamilyPolynomialCode.liftBasePair
    (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.liftControllerPair
      (b := vars) p)

def characterBaseCode
    (I : DQLSystem eqs vars)
    (k : Fin (reciprocalCount vars)) :
    ComplexPairCode (baseDimension eqs vars) :=
  liftControllerPair
    (characterCode (reciprocalExponent I k))

def derivativeBaseCode
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (k : Fin (reciprocalCount vars)) :
    ComplexPairCode (baseDimension eqs vars) :=
  liftControllerPair
    (derivativeCode parameters (reciprocalExponent I k))

@[simp]
theorem evalPair_liftControllerPair
    (p : ComplexPairCode
      (ControllerProductLinkedJacobiFamilyPolynomialCode.controllerDimension
        (clockCount eqs vars)))
    (z :
      ControllerProductLinkedJacobiGaugeFamilyState
        (clockCount eqs vars) vars) :
    evalPair (liftControllerPair p)
        (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.point z) =
      evalPair p
        (ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint
          z.source) := by
  rw [liftControllerPair]
  change
    evalPair
        (ComplexGaugeFamilyPolynomialCode.liftBasePair
          (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.liftControllerPair
            p))
        (ComplexGaugeFamilyPolynomialCode.point
          (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.rawState
            z)) =
      _
  rw [
    ComplexGaugeFamilyPolynomialCode.evalPair_liftBasePair]
  exact
    ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.evalPair_liftControllerPair
      p z.source

@[simp]
theorem evalPair_characterBaseCode
    (I : DQLSystem eqs vars)
    (z :
      ControllerProductLinkedJacobiGaugeFamilyState
        (clockCount eqs vars) vars)
    (k : Fin (reciprocalCount vars)) :
    evalPair (characterBaseCode I k)
        (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.point z) =
      characterValue (reciprocalExponent I k)
        z.source.controllers := by
  rw [characterBaseCode, evalPair_liftControllerPair]
  exact
    evalPair_characterCode
      (reciprocalExponent I k) z.source.controllers

@[simp]
theorem evalPair_derivativeBaseCode
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (z :
      ControllerProductLinkedJacobiGaugeFamilyState
        (clockCount eqs vars) vars)
    (k : Fin (reciprocalCount vars)) :
    evalPair (derivativeBaseCode parameters I k)
        (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.point z) =
      Complex.I *
        (frequencyValue parameters (reciprocalExponent I k)
          z.source.controllers : ℂ) *
        characterValue (reciprocalExponent I k)
          z.source.controllers := by
  rw [derivativeBaseCode, evalPair_liftControllerPair]
  exact
    evalPair_derivativeCode
      parameters (reciprocalExponent I k) z.source.controllers

/-! ## Complete reciprocal field and residual family -/

def etaCode :
    Fin (reciprocalCount vars) → RationalCode :=
  fun _ ↦ RationalCode.encode (1 / 2 : ℚ)

def fieldCode
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars) :
    PolynomialFieldCode (dimension eqs vars) :=
  ComplexReciprocalFamilyPolynomialCode.fieldCode
    (DetectorJacobiGaugeData.fieldCode parameters I)
    etaCode
    (derivativeBaseCode parameters I)

def residualCode
    (I : DQLSystem eqs vars) :
    Fin (ComplexReciprocalFamilyPolynomialCode.reciprocalDimension
      (reciprocalCount vars)) →
      PolynomialCode (dimension eqs vars) :=
  ComplexReciprocalFamilyPolynomialCode.residualCode
    etaCode (characterBaseCode I)

noncomputable def vectorField
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (z : State eqs vars) :
    State eqs vars where
  base :=
    ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.vectorField
      parameters
      (DetectorCharacterCode.omegaWeights (eqs := eqs))
      (DetectorCharacterCode.numberWeights I)
      (DetectorJacobiGaugeData.gaugeExponents I)
      z.base
  reciprocal := fun k ↦
    reciprocalVelocity
      ((1 / 2 : ℝ) : ℂ)
      (evalPair (derivativeBaseCode parameters I k)
        (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.point
          z.base))
      (z.reciprocal k)

@[simp]
theorem realize_fieldCode
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (z : State eqs vars) :
    PolynomialFieldCode.realize
        (fieldCode parameters I) (point z) =
      point (vectorField parameters I z) := by
  rw [fieldCode, point,
    ComplexReciprocalFamilyPolynomialCode.realize_fieldCode]
  congr 1
  apply Prod.ext
  · exact
      ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.realize_fieldCode
          parameters
          (DetectorCharacterCode.omegaWeights (eqs := eqs))
          (DetectorCharacterCode.numberWeights I)
          (DetectorJacobiGaugeData.gaugeExponents I)
          z.base
  · funext k
    simp only [ComplexReciprocalFamilyPolynomialCode.vectorField,
      rawState, vectorField]
    simp [etaCode,
      ComplexReciprocalFamilyPolynomialCode.evalObservable,
      ComplexReciprocalPolynomialCode.evalObservable, evalPair]

@[simp]
theorem realize_fieldCode_arbitrary
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (x : Fin (dimension eqs vars) → ℝ) :
    PolynomialFieldCode.realize (fieldCode parameters I) x =
      point (vectorField parameters I (state x)) := by
  simpa using realize_fieldCode parameters I (state x)

/-! ## The fixed polynomial Poisson output -/

def reciprocalPairCode
    (k : Fin (reciprocalCount vars)) :
    ComplexPairCode (dimension eqs vars) :=
  (PolynomialCode.varCode
      (ComplexReciprocalFamilyPolynomialCode.reciprocalReIndex k),
    PolynomialCode.varCode
      (ComplexReciprocalFamilyPolynomialCode.reciprocalImIndex k))

@[simp]
theorem evalPair_reciprocalPairCode
    (z : State eqs vars)
    (k : Fin (reciprocalCount vars)) :
    evalPair (reciprocalPairCode k) (point z) =
      z.reciprocal k := by
  apply Complex.ext <;>
    simp [evalPair, reciprocalPairCode, point, rawState]

def poissonScaleCode :
    ComplexPairCode (dimension eqs vars) :=
  (PolynomialCode.constant
      (RationalCode.encode (3 / 4 : ℚ)),
    PolynomialCode.zero)

def poissonFactorCode
    (j : Fin vars) :
    ComplexPairCode (dimension eqs vars) :=
  mul poissonScaleCode
    (mul
      (reciprocalPairCode (positiveIndex j))
      (reciprocalPairCode (negativeIndex j)))

@[simp]
theorem evalPair_poissonScaleCode
    (x : Fin (dimension eqs vars) → ℝ) :
    evalPair poissonScaleCode x = ((3 / 4 : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp [evalPair, poissonScaleCode]

@[simp]
theorem evalPair_poissonFactorCode
    (z : State eqs vars) (j : Fin vars) :
    evalPair (poissonFactorCode j) (point z) =
      ((3 / 4 : ℝ) : ℂ) *
        z.reciprocal (positiveIndex j) *
        z.reciprocal (negativeIndex j) := by
  simp [poissonFactorCode]
  ring

/-! ## Theta--Poisson detector product before the RHS oscillator -/

def liftGaugeBasePair
    (p : ComplexPairCode (baseDimension eqs vars)) :
    ComplexPairCode (dimension eqs vars) :=
  (ComplexReciprocalFamilyPolynomialCode.liftBase p.1,
    ComplexReciprocalFamilyPolynomialCode.liftBase p.2)

@[simp]
theorem evalPair_liftGaugeBasePair
    (p : ComplexPairCode (baseDimension eqs vars))
    (z : State eqs vars) :
    evalPair (liftGaugeBasePair p) (point z) =
      evalPair p
        (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.point
          z.base) := by
  apply Complex.ext <;>
    simp [evalPair, liftGaugeBasePair, point, rawState]

def thetaFactorCode
    (j : Fin vars) :
    ComplexPairCode (dimension eqs vars) :=
  liftGaugeBasePair
    (DetectorJacobiGaugeData.thetaOutputCode
      (eqs := eqs) j)

@[simp]
theorem evalPair_thetaFactorCode
    (z : State eqs vars) (j : Fin vars) :
    evalPair (thetaFactorCode (eqs := eqs) j) (point z) =
      z.base.gauge j *
        (z.base.source.linked j).jacobi.T1 := by
  rw [thetaFactorCode, evalPair_liftGaugeBasePair]
  exact
    ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.evalPair_thetaOutputCode
      z.base j

/-- The `j`th fixed-degree factor
`Theta(Qⱼ,Vⱼ) Pη(Qⱼ⁻¹Sⱼ)`. -/
def detectorFactorCode
    (j : Fin vars) :
    ComplexPairCode (dimension eqs vars) :=
  mul (thetaFactorCode (eqs := eqs) j)
    (poissonFactorCode (eqs := eqs) j)

@[simp]
theorem evalPair_detectorFactorCode
    (z : State eqs vars) (j : Fin vars) :
    evalPair (detectorFactorCode (eqs := eqs) j) (point z) =
      (z.base.gauge j *
          (z.base.source.linked j).jacobi.T1) *
        (((3 / 4 : ℝ) : ℂ) *
          z.reciprocal (positiveIndex j) *
          z.reciprocal (negativeIndex j)) := by
  simp [detectorFactorCode]

/-- Product of all theta--Poisson factors. -/
def detectorProductCode :
    ComplexPairCode (dimension eqs vars) :=
  product
    (List.ofFn fun j : Fin vars ↦
      detectorFactorCode (eqs := eqs) j)

@[simp]
theorem evalPair_detectorProductCode
    (z : State eqs vars) :
    evalPair (detectorProductCode (eqs := eqs) (vars := vars))
        (point z) =
      ∏ j : Fin vars,
        ((z.base.gauge j *
            (z.base.source.linked j).jacobi.T1) *
          (((3 / 4 : ℝ) : ℂ) *
            z.reciprocal (positiveIndex j) *
            z.reciprocal (negativeIndex j))) := by
  rw [detectorProductCode, evalPair_product,
    List.map_ofFn, List.prod_ofFn]
  apply Finset.prod_congr rfl
  intro j _
  exact evalPair_detectorFactorCode z j

end DetectorPoissonReciprocalCode

end HGAS
