import HGAS.Compiler.ComplexGaugeFamilyPolynomialCode
import HGAS.Modular.ControllerProductLinkedJacobiFamilyPolynomialCode
import Mathlib.Tactic

/-!
# Gauge-completed common-controller Jacobi families

The linked Jacobi compiler stores the shifted odd theta coordinate `T₁`.
The arithmetic detector, however, uses the unshifted zero-free theta
function.  The manuscript relates them by

```text
                         F = G T₁,
              G⁴ = λ exp(i(α + 2β)).
```

This module performs that completion literally.  One common product of
`q` controller--phase clocks drives `b` linked Jacobi blocks and `b`
complex gauges.  An integral exponent vector `gaugeExponents a` describes
the character `exp(i(αₐ+2βₐ))`; its compiled frequency drives

```text
                  Gₐ' = (i/4)(αₐ' + 2βₐ')Gₐ.
```

The final output code is exactly `Gₐ T₁,ₐ`.  All code-evaluation and field
realization theorems are ambient identities.  The specialization does not
assume controller circles, Jacobi residuals, gauge residuals, or
nonvanishing.
-/

namespace HGAS.Modular

open HGAS

/-- Structured state of the gauge-completed Jacobi family. -/
@[ext]
structure ControllerProductLinkedJacobiGaugeFamilyState
    (q b : ℕ) where
  source : ControllerProductLinkedJacobiFamilyState q b
  gauge : Fin b → ℂ

namespace ControllerProductLinkedJacobiGaugeFamilyPolynomialCode

open HGAS.Clocks
open HGAS.Clocks.ControllerPhaseProductCharacterCode

variable {q b : ℕ}

namespace Base

abbrev dimension (q b : ℕ) : ℕ :=
  ControllerProductLinkedJacobiFamilyPolynomialCode.dimension q b

end Base

abbrev dimension (q b : ℕ) : ℕ :=
  ComplexGaugeFamilyPolynomialCode.dimension (Base.dimension q b) b

def rawState
    (z : ControllerProductLinkedJacobiGaugeFamilyState q b) :
    ComplexGaugeFamilyPolynomialCode.State
      (Base.dimension q b) b :=
  (ControllerProductLinkedJacobiFamilyPolynomialCode.point z.source,
    z.gauge)

def point
    (z : ControllerProductLinkedJacobiGaugeFamilyState q b) :
    Fin (dimension q b) → ℝ :=
  ComplexGaugeFamilyPolynomialCode.point (rawState z)

def state
    (x : Fin (dimension q b) → ℝ) :
    ControllerProductLinkedJacobiGaugeFamilyState q b :=
  let z := ComplexGaugeFamilyPolynomialCode.state x
  { source :=
      ControllerProductLinkedJacobiFamilyPolynomialCode.state z.1
    gauge := z.2 }

@[simp]
theorem state_point
    (z : ControllerProductLinkedJacobiGaugeFamilyState q b) :
    state (point z) = z := by
  apply ControllerProductLinkedJacobiGaugeFamilyState.ext
  · simp [state, point, rawState]
  · simp [state, point, rawState]

@[simp]
theorem point_state
    (x : Fin (dimension q b) → ℝ) :
    point (state x) = x := by
  simp [point, state, rawState]

/-! ## Lifting controller characters into the common source -/

def liftController
    (p : PolynomialCode
      (ControllerProductLinkedJacobiFamilyPolynomialCode.controllerDimension
        q)) :
    PolynomialCode (Base.dimension q b) :=
  PolynomialCode.injectVariables
    ControllerProductLinkedJacobiFamilyPolynomialCode.controllersEmbedding
    p

def liftControllerPair
    (p : ComplexPairCode
      (ControllerProductLinkedJacobiFamilyPolynomialCode.controllerDimension
        q)) :
    ComplexPairCode (Base.dimension q b) :=
  (liftController p.1, liftController p.2)

@[simp]
theorem eval₂Hom_liftController
    (p : PolynomialCode
      (ControllerProductLinkedJacobiFamilyPolynomialCode.controllerDimension
        q))
    (z : ControllerProductLinkedJacobiFamilyState q b) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (ControllerProductLinkedJacobiFamilyPolynomialCode.point z)
        (PolynomialCode.decode (liftController p)) =
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint z)
        (PolynomialCode.decode p) := by
  rw [liftController,
    PolynomialCode.eval₂Hom_decode_injectVariables]
  congr 2
  funext i
  simp [ControllerProductLinkedJacobiFamilyPolynomialCode.point,
    ControllerProductLinkedJacobiFamilyPolynomialCode.controllersEmbedding]

@[simp]
theorem evalPair_liftControllerPair
    (p : ComplexPairCode
      (ControllerProductLinkedJacobiFamilyPolynomialCode.controllerDimension
        q))
    (z : ControllerProductLinkedJacobiFamilyState q b) :
    evalPair (liftControllerPair p)
        (ControllerProductLinkedJacobiFamilyPolynomialCode.point z) =
      evalPair p
        (ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint
          z) := by
  apply Complex.ext <;>
    simp [evalPair, liftControllerPair]

/-- Character `χₐ` viewed as an observable on the entire linked source. -/
def gaugeCharacterBaseCode
    (gaugeExponents : Fin b → Fin q → ℤ)
    (a : Fin b) :
    ComplexPairCode (Base.dimension q b) :=
  liftControllerPair (characterCode (gaugeExponents a))

/-- Its instantaneous frequency, viewed as a polynomial on the entire
linked source. -/
def gaugeFrequencyBaseCode
    (parameters : Fin q → RationalCode)
    (gaugeExponents : Fin b → Fin q → ℤ)
    (a : Fin b) :
    PolynomialCode (Base.dimension q b) :=
  liftController
    (frequencyCode parameters (gaugeExponents a))

@[simp]
theorem evalPair_gaugeCharacterBaseCode
    (gaugeExponents : Fin b → Fin q → ℤ)
    (z : ControllerProductLinkedJacobiFamilyState q b)
    (a : Fin b) :
    evalPair (gaugeCharacterBaseCode gaugeExponents a)
        (ControllerProductLinkedJacobiFamilyPolynomialCode.point z) =
      characterValue (gaugeExponents a) z.controllers := by
  rw [gaugeCharacterBaseCode, evalPair_liftControllerPair]
  exact evalPair_characterCode (gaugeExponents a) z.controllers

@[simp]
theorem eval₂Hom_gaugeFrequencyBaseCode
    (parameters : Fin q → RationalCode)
    (gaugeExponents : Fin b → Fin q → ℤ)
    (z : ControllerProductLinkedJacobiFamilyState q b)
    (a : Fin b) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (ControllerProductLinkedJacobiFamilyPolynomialCode.point z)
        (PolynomialCode.decode
          (gaugeFrequencyBaseCode parameters gaugeExponents a)) =
      frequencyValue parameters (gaugeExponents a) z.controllers := by
  rw [gaugeFrequencyBaseCode, eval₂Hom_liftController]
  exact
    eval₂Hom_frequencyCode parameters (gaugeExponents a)
      z.controllers

/-! ## The exact `T₁` coordinate and the output `G T₁` -/

def localT1ComplexIndex : Fin LinkedJacobiPolynomialCode.dimension :=
  LinkedJacobiPolynomialCode.jacobiEmbedding
    JacobiPolynomialCode.T1Index

def localT1ReIndex :
    Fin ControllerProductLinkedJacobiFamilyPolynomialCode.localLinkedRealDimension :=
  ComplexCoordinates.realIndex localT1ComplexIndex

def localT1ImIndex :
    Fin ControllerProductLinkedJacobiFamilyPolynomialCode.localLinkedRealDimension :=
  ComplexCoordinates.imagIndex localT1ComplexIndex

def T1ReIndex (a : Fin b) : Fin (Base.dimension q b) :=
  ControllerProductLinkedJacobiFamilyPolynomialCode.linkedFamilyEmbedding
    (ControllerProductLinkedJacobiFamilyPolynomialCode.linkedBlockEmbedding
      a localT1ReIndex)

def T1ImIndex (a : Fin b) : Fin (Base.dimension q b) :=
  ControllerProductLinkedJacobiFamilyPolynomialCode.linkedFamilyEmbedding
    (ControllerProductLinkedJacobiFamilyPolynomialCode.linkedBlockEmbedding
      a localT1ImIndex)

def T1BaseCode (a : Fin b) :
    ComplexPairCode (Base.dimension q b) :=
  (PolynomialCode.varCode (T1ReIndex a),
    PolynomialCode.varCode (T1ImIndex a))

@[simp]
theorem evalPair_T1BaseCode
    (z : ControllerProductLinkedJacobiFamilyState q b)
    (a : Fin b) :
    evalPair (T1BaseCode a)
        (ControllerProductLinkedJacobiFamilyPolynomialCode.point z) =
      (z.linked a).jacobi.T1 := by
  apply Complex.ext <;>
    simp [evalPair, T1BaseCode, T1ReIndex, T1ImIndex,
      localT1ReIndex, localT1ImIndex, localT1ComplexIndex,
      ControllerProductLinkedJacobiFamilyPolynomialCode.point,
      ControllerProductLinkedJacobiFamilyPolynomialCode.linkedFamilyPoint,
      ControllerProductLinkedJacobiFamilyPolynomialCode.linkedFamilyEmbedding,
      ControllerProductLinkedJacobiFamilyPolynomialCode.linkedBlockEmbedding,
      LinkedJacobiPolynomialCode.point,
      LinkedJacobiPolynomialCode.jacobiEmbedding,
      JacobiPolynomialCode.point,
      JacobiPolynomialCode.T1Index]

/-! ## Complete field, residual, and output codes -/

def fieldCode
    (parameters : Fin q → RationalCode)
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode)
    (gaugeExponents : Fin b → Fin q → ℤ) :
    PolynomialFieldCode (dimension q b) :=
  ComplexGaugeFamilyPolynomialCode.fieldCode
    (ControllerProductLinkedJacobiFamilyPolynomialCode.fieldCode
      parameters omegaWeights numberWeights)
    (gaugeFrequencyBaseCode parameters gaugeExponents)

def gaugeResidualCode
    (scale : Fin b → RationalCode)
    (gaugeExponents : Fin b → Fin q → ℤ) :
    Fin (ComplexGaugeFamilyPolynomialCode.gaugeDimension b) →
      PolynomialCode (dimension q b) :=
  ComplexGaugeFamilyPolynomialCode.residualCode scale
    (gaugeCharacterBaseCode gaugeExponents)

/-- The literal complex polynomial output `GₐT₁,ₐ`. -/
def thetaOutputCode (a : Fin b) :
    ComplexPairCode (dimension q b) :=
  ComplexGaugeFamilyPolynomialCode.outputCode
    (T1BaseCode (q := q)) a

noncomputable def vectorField
    (parameters : Fin q → RationalCode)
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode)
    (gaugeExponents : Fin b → Fin q → ℤ)
    (z : ControllerProductLinkedJacobiGaugeFamilyState q b) :
    ControllerProductLinkedJacobiGaugeFamilyState q b where
  source :=
    ControllerProductLinkedJacobiFamilyPolynomialCode.vectorField
      (fun i ↦ (RationalCode.decode (parameters i) : ℝ))
      (fun a i ↦
        (RationalCode.decode (omegaWeights a i) : ℝ))
      (fun a i ↦
        (RationalCode.decode (numberWeights a i) : ℝ))
      z.source
  gauge := fun a ↦
    Complex.I *
      ((frequencyValue parameters (gaugeExponents a)
          z.source.controllers / 4 : ℝ) : ℂ) *
        z.gauge a

@[simp]
theorem realize_fieldCode
    (parameters : Fin q → RationalCode)
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode)
    (gaugeExponents : Fin b → Fin q → ℤ)
    (z : ControllerProductLinkedJacobiGaugeFamilyState q b) :
    PolynomialFieldCode.realize
        (fieldCode parameters omegaWeights numberWeights gaugeExponents)
        (point z) =
      point
        (vectorField parameters omegaWeights numberWeights
          gaugeExponents z) := by
  rw [fieldCode, point,
    ComplexGaugeFamilyPolynomialCode.realize_fieldCode]
  congr 1
  apply Prod.ext
  · exact
      ControllerProductLinkedJacobiFamilyPolynomialCode.realize_fieldCode
        parameters omegaWeights numberWeights z.source
  · funext a
    simp [ComplexGaugeFamilyPolynomialCode.vectorField,
      ComplexGaugeFamilyPolynomialCode.gaugeVelocity,
      rawState, vectorField,
      ComplexGaugeFamilyPolynomialCode.evalRealObservable]

@[simp]
theorem realize_fieldCode_arbitrary
    (parameters : Fin q → RationalCode)
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode)
    (gaugeExponents : Fin b → Fin q → ℤ)
    (x : Fin (dimension q b) → ℝ) :
    PolynomialFieldCode.realize
        (fieldCode parameters omegaWeights numberWeights gaugeExponents)
        x =
      point
        (vectorField parameters omegaWeights numberWeights
          gaugeExponents (state x)) := by
  simpa using
    realize_fieldCode parameters omegaWeights numberWeights
      gaugeExponents (state x)

@[simp]
theorem evalPair_thetaOutputCode
    (z : ControllerProductLinkedJacobiGaugeFamilyState q b)
    (a : Fin b) :
    evalPair (thetaOutputCode (q := q) a) (point z) =
      z.gauge a * (z.source.linked a).jacobi.T1 := by
  simp [thetaOutputCode, point, rawState,
    ComplexGaugeFamilyPolynomialCode.outputCode]

@[simp]
theorem evalPair_gaugeResidualPairCode
    (scale : Fin b → RationalCode)
    (gaugeExponents : Fin b → Fin q → ℤ)
    (z : ControllerProductLinkedJacobiGaugeFamilyState q b)
    (a : Fin b) :
    evalPair
        (ComplexGaugeFamilyPolynomialCode.residualPairCode scale
          (gaugeCharacterBaseCode gaugeExponents) a)
        (point z) =
      z.gauge a ^ 4 -
        ((RationalCode.decode (scale a) : ℝ) : ℂ) *
          characterValue (gaugeExponents a)
            z.source.controllers := by
  simp [point, rawState,
    ComplexGaugeFamilyPolynomialCode.residual]

end ControllerProductLinkedJacobiGaugeFamilyPolynomialCode

end HGAS.Modular
