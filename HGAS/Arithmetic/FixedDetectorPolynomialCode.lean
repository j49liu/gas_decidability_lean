import HGAS.Arithmetic.DetectorPoissonReciprocalCode
import HGAS.Clocks.RHSOscillatorPolynomialCode
import Mathlib.Tactic

/-!
# The complete fixed-degree detector field and observable

The only input-dependent Fourier exponent in the original detector is the
right-hand-side character `exp(-i c·u)`.  Following the manuscript, this
module represents it by one additional complex oscillator `R` satisfying

```text
                    R' = -4i (∑ row, c_row ν_row) R,
```

where `ν_row` is the frequency of the corresponding *fundamental* equation
clock.  The factor four is exactly the convention
`U_row = ζ_row⁴`.

The complete polynomial detector observable is then

```text
       H♯ = R * ∏ j, [ (GⱼT₁,ⱼ)
                       * (1-η²) Gⱼ,+ Gⱼ,- ].
```

The DQL right-hand side occurs only as a coefficient in the oscillator
field; it does not occur as a state exponent in `H♯`.  Therefore, once the
numbers of rows and variables and the coefficient matrices are fixed, the
state dimension and polynomial degree are fixed independently of the
encoded input.
-/

namespace HGAS

namespace FixedDetectorPolynomialCode

open _root_.MvPolynomial
open Clocks
open Clocks.ControllerPhaseProductCharacterCode
open Modular

variable {eqs vars : ℕ}

abbrev clockCount (eqs vars : ℕ) : ℕ :=
  DetectorPoissonReciprocalCode.clockCount eqs vars

abbrev baseDimension (eqs vars : ℕ) : ℕ :=
  DetectorPoissonReciprocalCode.dimension eqs vars

abbrev dimension (eqs vars : ℕ) : ℕ :=
  RHSOscillatorPolynomialCode.dimension
    (baseDimension eqs vars)

/-- Complete detector state before compactification. -/
@[ext]
structure State (eqs vars : ℕ) where
  base : DetectorPoissonReciprocalCode.State eqs vars
  rhs : Controller.PhaseState ℝ

def point (z : State eqs vars) :
    Fin (dimension eqs vars) → ℝ :=
  RHSOscillatorPolynomialCode.combinedPoint
    (DetectorPoissonReciprocalCode.point z.base) z.rhs

def state (x : Fin (dimension eqs vars) → ℝ) :
    State eqs vars where
  base :=
    DetectorPoissonReciprocalCode.state
      (x ∘ PolynomialBlockCode.leftEmbedding)
  rhs :=
    { c := x (RHSOscillatorPolynomialCode.xIndex
        (baseDimension eqs vars))
      d := x (RHSOscillatorPolynomialCode.yIndex
        (baseDimension eqs vars)) }

@[simp]
theorem state_point (z : State eqs vars) :
    state (point z) = z := by
  apply State.ext
  · change
      DetectorPoissonReciprocalCode.state
          (point z ∘ PolynomialBlockCode.leftEmbedding) =
        z.base
    have hbase :
        point z ∘ PolynomialBlockCode.leftEmbedding =
          DetectorPoissonReciprocalCode.point z.base := by
      funext i
      simp [point]
    rw [hbase]
    simp
  · ext <;> simp [state, point]

@[simp]
theorem point_state
    (x : Fin (dimension eqs vars) → ℝ) :
    point (state x) = x := by
  funext k
  obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective k
  · change
      point (state x)
          (PolynomialBlockCode.leftEmbedding (p := 2) i) =
        x (PolynomialBlockCode.leftEmbedding (p := 2) i)
    simp [point, state]
  · fin_cases j
    · change
        point (state x)
            (RHSOscillatorPolynomialCode.xIndex
              (baseDimension eqs vars)) =
          x (RHSOscillatorPolynomialCode.xIndex
            (baseDimension eqs vars))
      simp [point, state]
    · change
        point (state x)
            (RHSOscillatorPolynomialCode.yIndex
              (baseDimension eqs vars)) =
          x (RHSOscillatorPolynomialCode.yIndex
            (baseDimension eqs vars))
      simp [point, state]

/-! ## Fundamental equation-clock frequencies -/

/-- Unit exponent of the fundamental equation clock belonging to `row`.
Unlike `DetectorCharacterCode.flattenCharacter`, this has no factor four:
the RHS oscillator compiler itself supplies the factor four. -/
def equationBasisExponent
    (row : Fin eqs) :
    Fin (clockCount eqs vars) → ℤ :=
  fun i ↦
    match finSumFinEquiv.symm i with
    | Sum.inl _ => 0
    | Sum.inr k => if k = row then 1 else 0

def liftControllerScalar
    (p : PolynomialCode
      (ControllerProductLinkedJacobiFamilyPolynomialCode.controllerDimension
        (clockCount eqs vars))) :
    PolynomialCode (baseDimension eqs vars) :=
  ComplexReciprocalFamilyPolynomialCode.liftBase
    (ComplexGaugeFamilyPolynomialCode.liftBase
      (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.liftController
        (b := vars) p))

@[simp]
theorem eval₂Hom_liftControllerScalar
    (p : PolynomialCode
      (ControllerProductLinkedJacobiFamilyPolynomialCode.controllerDimension
        (clockCount eqs vars)))
    (z : DetectorPoissonReciprocalCode.State eqs vars) :
    eval₂Hom (algebraMap ℚ ℝ)
        (DetectorPoissonReciprocalCode.point z)
        (PolynomialCode.decode (liftControllerScalar p)) =
      eval₂Hom (algebraMap ℚ ℝ)
        (ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint
          z.base.source)
        (PolynomialCode.decode p) := by
  rw [liftControllerScalar]
  change
    eval₂Hom (algebraMap ℚ ℝ)
        (ComplexReciprocalFamilyPolynomialCode.point
          (DetectorPoissonReciprocalCode.rawState z))
        (PolynomialCode.decode
          (ComplexReciprocalFamilyPolynomialCode.liftBase
            (ComplexGaugeFamilyPolynomialCode.liftBase
              (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.liftController
                p)))) =
      _
  rw [
    ComplexReciprocalFamilyPolynomialCode.eval₂Hom_liftBase_point]
  change
    eval₂Hom (algebraMap ℚ ℝ)
        (ComplexGaugeFamilyPolynomialCode.point
          (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.rawState
            z.base))
        (PolynomialCode.decode
          (ComplexGaugeFamilyPolynomialCode.liftBase
            (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.liftController
              p))) =
      _
  rw [ComplexGaugeFamilyPolynomialCode.eval₂Hom_liftBase_point]
  exact
    ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.eval₂Hom_liftController
      p z.base.source

def equationFrequencyCode
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (row : Fin eqs) :
    PolynomialCode (baseDimension eqs vars) :=
  liftControllerScalar
    (frequencyCode parameters (equationBasisExponent row))

@[simp]
theorem eval₂Hom_equationFrequencyCode
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (z : DetectorPoissonReciprocalCode.State eqs vars)
    (row : Fin eqs) :
    eval₂Hom (algebraMap ℚ ℝ)
        (DetectorPoissonReciprocalCode.point z)
        (PolynomialCode.decode
          (equationFrequencyCode parameters row)) =
      frequencyValue parameters (equationBasisExponent row)
        z.base.source.controllers := by
  rw [equationFrequencyCode, eval₂Hom_liftControllerScalar]
  exact
    eval₂Hom_frequencyCode parameters
      (equationBasisExponent row)
      z.base.source.controllers

def rhsWeightCode
    (I : DQLSystem eqs vars) (row : Fin eqs) :
    RationalCode :=
  RationalCode.encode (I.rhs row : ℚ)

/-! ## Complete field semantics -/

def fieldCode
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars) :
    PolynomialFieldCode (dimension eqs vars) :=
  RHSOscillatorPolynomialCode.fieldCode
    (DetectorPoissonReciprocalCode.fieldCode parameters I)
    (rhsWeightCode I)
    (equationFrequencyCode parameters)

noncomputable def vectorField
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (z : State eqs vars) :
    State eqs vars where
  base :=
    DetectorPoissonReciprocalCode.vectorField parameters I z.base
  rhs :=
    RHSOscillatorPolynomialCode.oscillatorField
      (rhsWeightCode I)
      (equationFrequencyCode parameters)
      (DetectorPoissonReciprocalCode.point z.base)
      z.rhs

@[simp]
theorem realize_fieldCode
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (z : State eqs vars) :
    PolynomialFieldCode.realize
        (fieldCode parameters I) (point z) =
      point (vectorField parameters I z) := by
  rw [fieldCode, point,
    RHSOscillatorPolynomialCode.realize_fieldCode]
  congr 1
  exact DetectorPoissonReciprocalCode.realize_fieldCode
    parameters I z.base

@[simp]
theorem realize_fieldCode_arbitrary
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (x : Fin (dimension eqs vars) → ℝ) :
    PolynomialFieldCode.realize (fieldCode parameters I) x =
      point (vectorField parameters I (state x)) := by
  simpa using realize_fieldCode parameters I (state x)

/-- The semantic RHS frequency is literally
`∑ row, c_row * ν_row`. -/
theorem weightedFrequency_eq
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (z : DetectorPoissonReciprocalCode.State eqs vars) :
    RHSOscillatorPolynomialCode.weightedFrequency
        (rhsWeightCode I)
        (equationFrequencyCode parameters)
        (DetectorPoissonReciprocalCode.point z) =
      ∑ row : Fin eqs,
        (I.rhs row : ℝ) *
          frequencyValue parameters (equationBasisExponent row)
            z.base.source.controllers := by
  unfold RHSOscillatorPolynomialCode.weightedFrequency
  apply Finset.sum_congr rfl
  intro row _
  rw [eval₂Hom_equationFrequencyCode]
  simp [rhsWeightCode]

/-! ## The fixed-degree observable `H♯` -/

def liftBasePair
    (p : ComplexPairCode (baseDimension eqs vars)) :
    ComplexPairCode (dimension eqs vars) :=
  (RHSOscillatorPolynomialCode.liftBase p.1,
    RHSOscillatorPolynomialCode.liftBase p.2)

def rhsOscillatorCode :
    ComplexPairCode (dimension eqs vars) :=
  (RHSOscillatorPolynomialCode.xCode,
    RHSOscillatorPolynomialCode.yCode)

@[simp]
theorem evalPair_liftBasePair
    (p : ComplexPairCode (baseDimension eqs vars))
    (z : State eqs vars) :
    evalPair (liftBasePair p) (point z) =
      evalPair p (DetectorPoissonReciprocalCode.point z.base) := by
  apply Complex.ext <;>
    simp [evalPair, liftBasePair, point]

@[simp]
theorem evalPair_rhsOscillatorCode
    (z : State eqs vars) :
    evalPair (rhsOscillatorCode (eqs := eqs) (vars := vars))
        (point z) =
      ⟨z.rhs.c, z.rhs.d⟩ := by
  apply Complex.ext <;>
    simp [evalPair, rhsOscillatorCode, point]

/-- Complete fixed-degree detector code. -/
def detectorCode :
    ComplexPairCode (dimension eqs vars) :=
  mul rhsOscillatorCode
    (liftBasePair
      (DetectorPoissonReciprocalCode.detectorProductCode
        (eqs := eqs) (vars := vars)))

@[simp]
theorem evalPair_detectorCode
    (z : State eqs vars) :
    evalPair (detectorCode (eqs := eqs) (vars := vars))
        (point z) =
      (⟨z.rhs.c, z.rhs.d⟩ : ℂ) *
        ∏ j : Fin vars,
          ((z.base.base.gauge j *
              (z.base.base.source.linked j).jacobi.T1) *
            (((3 / 4 : ℝ) : ℂ) *
              z.base.reciprocal
                (DetectorPoissonReciprocalCode.positiveIndex j) *
              z.base.reciprocal
                (DetectorPoissonReciprocalCode.negativeIndex j))) := by
  simp [detectorCode]

end FixedDetectorPolynomialCode

end HGAS
