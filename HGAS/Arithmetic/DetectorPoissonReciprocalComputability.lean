import HGAS.Arithmetic.DetectorJacobiGaugeComputability
import HGAS.Arithmetic.DetectorPoissonReciprocalCode
import HGAS.Compiler.ComplexReciprocalFamilyPolynomialComputability
import Mathlib.Computability.Partrec
import Mathlib.Tactic

/-!
# Effectivity of the DQL Poisson-reciprocal compiler

For fixed finite DQL dimensions, this file proves primitive-recursiveness
of the complete gauge-plus-reciprocal detector field in

```text
  (controller parameters, DQL coefficient table).
```

Both characters associated with a Poisson kernel are compiled uniformly:
the positive block uses `W = Q⁻¹S`, while the negative block uses the
pointwise-negated exponent tuple.  Their character codes, derivative codes,
and graph residuals are therefore effective consequences of the common
finite-character and reciprocal-family compilers.

All results concern literal rational sparse-polynomial syntax.  No
real-number evaluation or reciprocal operation is performed by a compiler.
-/

namespace HGAS.DetectorPoissonReciprocalCode

open HGAS.Clocks
open HGAS.Clocks.ControllerPhaseProductCharacterCode
open HGAS.Modular

variable {eqs vars : ℕ}

/-- Runtime input for the complete gauge-plus-Poisson field. -/
abbrev CompilerInput (eqs vars : ℕ) :=
  DetectorJacobiGaugeData.CompilerInput eqs vars

/-! ## Effective exponent families -/

/-- Pointwise negation of a fixed finite integral tuple is primitive
recursive. -/
private theorem negateExponent_primrec {q : ℕ} :
    Primrec
      (fun exponents : Fin q → ℤ ↦
        fun i ↦ -exponents i) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro i
  exact
    DetectorCharacterCode.integerNeg_primrec.comp
      (Primrec.fin_app.comp Primrec.id (Primrec.const i))

/-- The flattened Poisson argument `Qⱼ⁻¹Sⱼ` is primitive recursive in the
DQL table. -/
theorem poissonExponent_primrec (j : Fin vars) :
    Primrec
      (fun I : DQLSystem eqs vars ↦ poissonExponent I j) := by
  exact
    (DetectorCharacterCode.flattenPoissonArgumentCharacter_primrec j).of_eq
      (fun _ ↦ rfl)

/-- The exponent tuple of either reciprocal block is primitive recursive in
the DQL table. -/
theorem reciprocalExponent_primrec
    (k : Fin (reciprocalCount vars)) :
    Primrec
      (fun I : DQLSystem eqs vars ↦ reciprocalExponent I k) := by
  obtain ⟨⟨j, s⟩, rfl⟩ := finProdFinEquiv.surjective k
  fin_cases s
  · exact
      (poissonExponent_primrec j).of_eq
        (by
          intro I
          simp [reciprocalExponent])
  · exact
      (negateExponent_primrec.comp
        (poissonExponent_primrec j)).of_eq
        (by
          intro I
          simp [reciprocalExponent])

/-- Compile all positive and negative reciprocal exponent tuples in one
primitive-recursive call. -/
theorem reciprocalExponentFamily_primrec :
    Primrec
      (fun I : DQLSystem eqs vars ↦
        fun k ↦ reciprocalExponent I k) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro k
  exact reciprocalExponent_primrec k

/-! ## Character and derivative observables in the gauge ambient space -/

/-- Lifting one controller complex-pair code through the linked-Jacobi and
gauge blocks is primitive recursive. -/
theorem liftControllerPair_primrec :
    Primrec
      (liftControllerPair (eqs := eqs) (vars := vars) :
        ComplexPairCode
            (ControllerProductLinkedJacobiFamilyPolynomialCode.controllerDimension
              (clockCount eqs vars)) →
          ComplexPairCode (baseDimension eqs vars)) := by
  exact
    (ComplexGaugeFamilyPolynomialCode.liftBasePair_primrec.comp
      ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.liftControllerPair_primrec).of_eq
      (fun _ ↦ rfl)

/-- A fixed reciprocal character code, lifted into the complete gauge base,
is primitive recursive in the DQL table. -/
theorem characterBaseCode_primrec
    (k : Fin (reciprocalCount vars)) :
    Primrec
      (fun I : DQLSystem eqs vars ↦ characterBaseCode I k) :=
  liftControllerPair_primrec.comp
    (characterCode_primrec.comp
      (reciprocalExponent_primrec k))

/-- Compile the complete family of lifted reciprocal characters. -/
theorem characterBaseCodeFamily_primrec :
    Primrec
      (fun I : DQLSystem eqs vars ↦
        fun k ↦ characterBaseCode I k) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro k
  exact characterBaseCode_primrec k

private theorem derivativeCompilerInput_primrec
    (k : Fin (reciprocalCount vars)) :
    Primrec
      (fun input : CompilerInput eqs vars ↦
        (input.1, reciprocalExponent input.2 k)) :=
  Primrec.pair Primrec.fst
    ((reciprocalExponent_primrec k).comp Primrec.snd)

set_option maxHeartbeats 1200000 in
-- The derivative compiler traverses both a rational and an integral tuple.
/-- The lifted derivative of a fixed reciprocal character is primitive
recursive jointly in the controller parameters and DQL table. -/
theorem derivativeBaseCode_primrec
    (k : Fin (reciprocalCount vars)) :
    Primrec
      (fun input : CompilerInput eqs vars ↦
        derivativeBaseCode input.1 input.2 k) := by
  exact
    (liftControllerPair_primrec.comp
      (derivativeCode_primrec.comp
        (derivativeCompilerInput_primrec k))).of_eq
      (fun _ ↦ rfl)

/-- Compile every positive and negative reciprocal-character derivative in
one primitive-recursive call. -/
theorem derivativeBaseCodeFamily_primrec :
    Primrec
      (fun input : CompilerInput eqs vars ↦
        fun k ↦ derivativeBaseCode input.1 input.2 k) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro k
  exact derivativeBaseCode_primrec k

/-! ## Complete field and graph residual compiler -/

private theorem genericFieldInput_primrec :
    Primrec
      (fun input : CompilerInput eqs vars ↦
        (DetectorJacobiGaugeData.fieldCode input.1 input.2,
          (etaCode (vars := vars),
            fun k ↦ derivativeBaseCode input.1 input.2 k))) :=
  Primrec.pair DetectorJacobiGaugeData.fieldCode_primrec
    (Primrec.pair
      (Primrec.const (etaCode (vars := vars)))
      derivativeBaseCodeFamily_primrec)

set_option maxHeartbeats 1600000 in
-- This composition emits the base field and two complex reciprocal blocks
-- for every DQL variable.
/-- The complete DQL gauge-plus-Poisson field compiler is primitive
recursive in `(parameters, I)`. -/
theorem fieldCode_primrec :
    Primrec
      (fun input : CompilerInput eqs vars ↦
        fieldCode input.1 input.2) := by
  exact
    (ComplexReciprocalFamilyPolynomialCode.fieldCode_primrec.comp
      genericFieldInput_primrec).of_eq
      (fun _ ↦ rfl)

theorem fieldCode_computable :
    Computable
      (fun input : CompilerInput eqs vars ↦
        fieldCode input.1 input.2) :=
  fieldCode_primrec.to_comp

private theorem genericResidualInput_primrec :
    Primrec
      (fun I : DQLSystem eqs vars ↦
        (etaCode (vars := vars),
          fun k ↦ characterBaseCode I k)) :=
  Primrec.pair
    (Primrec.const (etaCode (vars := vars)))
    characterBaseCodeFamily_primrec

set_option maxHeartbeats 1600000 in
-- The result is the flattened family of all real and imaginary graph
-- residual coordinates.
/-- Every positive and negative Poisson reciprocal residual is primitive
recursive in the DQL table. -/
theorem residualCode_primrec :
    Primrec
      (residualCode :
        DQLSystem eqs vars →
          Fin
              (ComplexReciprocalFamilyPolynomialCode.reciprocalDimension
                (reciprocalCount vars)) →
            PolynomialCode (dimension eqs vars)) := by
  exact
    (ComplexReciprocalFamilyPolynomialCode.residualCode_primrec.comp
      genericResidualInput_primrec).of_eq
      (fun _ ↦ rfl)

theorem residualCode_computable :
    Computable
      (residualCode :
        DQLSystem eqs vars →
          Fin
              (ComplexReciprocalFamilyPolynomialCode.reciprocalDimension
                (reciprocalCount vars)) →
            PolynomialCode (dimension eqs vars)) :=
  residualCode_primrec.to_comp

/-! ## Fixed-degree detector syntax -/

/-- The theta--Poisson product contains no runtime DQL coefficient.  As a
compiler output paired with the standard runtime input, it is primitive
recursive by constancy. -/
theorem detectorProductCode_primrec :
    Primrec
      (fun _ : CompilerInput eqs vars ↦
        detectorProductCode (eqs := eqs) (vars := vars)) :=
  Primrec.const _

theorem detectorProductCode_computable :
    Computable
      (fun _ : CompilerInput eqs vars ↦
        detectorProductCode (eqs := eqs) (vars := vars)) :=
  detectorProductCode_primrec.to_comp

/-- Compile the field and its fixed-degree theta--Poisson observable
together. -/
theorem fieldAndDetectorProductCode_primrec :
    Primrec
      (fun input : CompilerInput eqs vars ↦
        (fieldCode input.1 input.2,
          detectorProductCode (eqs := eqs) (vars := vars))) :=
  Primrec.pair fieldCode_primrec detectorProductCode_primrec

theorem fieldAndDetectorProductCode_computable :
    Computable
      (fun input : CompilerInput eqs vars ↦
        (fieldCode input.1 input.2,
          detectorProductCode (eqs := eqs) (vars := vars))) :=
  fieldAndDetectorProductCode_primrec.to_comp

end HGAS.DetectorPoissonReciprocalCode
