import HGAS.Arithmetic.DetectorCharacterComputability
import HGAS.Arithmetic.DetectorJacobiGaugeData
import HGAS.Compiler.ComplexGaugeFamilyPolynomialComputability
import HGAS.Modular.ControllerProductLinkedJacobiGaugeFamilyPolynomialComputability
import Mathlib.Computability.Partrec
import Mathlib.Tactic

/-!
# Effectivity of the DQL-specialized Jacobi gauge compiler

Fix the finite numbers of DQL equations and variables.  The runtime input
to the detector field is then only

```text
  (controller parameters, DQL coefficient table).
```

This file proves that specializing the reusable common-controller Jacobi
gauge compiler to the fourth-power detector characters is primitive
recursive.  It also proves the corresponding result for all fourth-root
graph residuals, with their rational scale tuple left as explicit compiler
input.

The proofs operate only on finite integer and rational tuples and literal
sparse-polynomial syntax.  They perform no real-number evaluation, root
selection, polynomial normalization, or ODE solving.
-/

namespace HGAS.DetectorJacobiGaugeData

open HGAS.Clocks
open HGAS.Clocks.ControllerPhaseProductCharacterCode
open HGAS.Modular

variable {eqs vars : ℕ}

/-- Runtime input for the specialized controller--Jacobi--gauge field. -/
abbrev CompilerInput (eqs vars : ℕ) :=
  (Fin (clockCount eqs vars) → RationalCode) ×
    DQLSystem eqs vars

/-- Runtime input for the complete family of fourth-root residuals. -/
abbrev ResidualCompilerInput (eqs vars : ℕ) :=
  (Fin vars → RationalCode) × DQLSystem eqs vars

/-! ## Effective fourth-power gauge exponents -/

/-- At a fixed detector variable, the complete flattened exponent tuple
`4 * (private + 2 * linear)` is primitive recursive in the DQL table. -/
theorem gaugeExponents_primrec (j : Fin vars) :
    Primrec
      (fun I : DQLSystem eqs vars ↦ gaugeExponents I j) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro i
  have hlinear :
      Primrec
        (fun I : DQLSystem eqs vars ↦
          DetectorCharacterCode.flattenCharacter
            (DetectorCharacterCode.linearCharacter I j) i) :=
    Primrec.fin_app.comp
      (DetectorCharacterCode.flattenLinearCharacter_primrec j)
      (Primrec.const i)
  exact
    (DetectorCharacterCode.integerAdd_primrec.comp
      (Primrec.const
        (DetectorCharacterCode.flattenCharacter
          (DetectorCharacterCode.privateCharacter
            (eqs := eqs) j) i))
      (DetectorCharacterCode.integerMul_primrec.comp
        (Primrec.const 2) hlinear)).of_eq
      (by
        intro I
        rw [gaugeExponents_apply])

/-- Compile the fourth-power gauge exponent tuple for every detector
variable in one primitive-recursive call. -/
theorem gaugeExponentFamily_primrec :
    Primrec
      (fun I : DQLSystem eqs vars ↦
        fun j ↦ gaugeExponents I j) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro j
  exact gaugeExponents_primrec j

/-! ## Complete specialized field -/

/-- Assemble the nested runtime datum expected by the reusable
controller--Jacobi--gauge compiler. -/
private theorem genericFieldInput_primrec :
    Primrec
      (fun input : CompilerInput eqs vars ↦
        (((input.1,
            DetectorCharacterCode.omegaWeights
              (eqs := eqs) (vars := vars)),
          DetectorCharacterCode.numberWeights input.2),
        gaugeExponents input.2)) := by
  exact
    Primrec.pair
      (Primrec.pair
        (Primrec.pair Primrec.fst
          (Primrec.const
            (DetectorCharacterCode.omegaWeights
              (eqs := eqs) (vars := vars))))
        (DetectorCharacterCode.numberWeightFamily_primrec.comp
          Primrec.snd))
      (gaugeExponentFamily_primrec.comp Primrec.snd)

set_option maxHeartbeats 1600000 in
-- This is a composition of three nested finite-family compilers.
/-- The complete DQL-specialized controller, linked-Jacobi, and gauge field
compiler is primitive recursive in `(parameters, I)`. -/
theorem fieldCode_primrec :
    Primrec
      (fun input : CompilerInput eqs vars ↦
        fieldCode input.1 input.2) := by
  exact
    (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.fieldCode_primrec.comp
      genericFieldInput_primrec).of_eq
      (fun _ ↦ rfl)

theorem fieldCode_computable :
    Computable
      (fun input : CompilerInput eqs vars ↦
        fieldCode input.1 input.2) :=
  fieldCode_primrec.to_comp

/-! ## Complete specialized fourth-root residual family -/

/-- A fixed detector gauge character, lifted through the common linked
Jacobi source, is primitive recursive in the DQL table. -/
theorem gaugeCharacterBaseCode_primrec (j : Fin vars) :
    Primrec
      (fun I : DQLSystem eqs vars ↦
        ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.gaugeCharacterBaseCode
          (gaugeExponents I) j) :=
  ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.liftControllerPair_primrec.comp
    (characterCode_primrec.comp
      (gaugeExponents_primrec j))

/-- Compile all lifted gauge characters in one call. -/
theorem gaugeCharacterBaseCodeFamily_primrec :
    Primrec
      (fun I : DQLSystem eqs vars ↦
        fun j ↦
          ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.gaugeCharacterBaseCode
            (gaugeExponents I) j) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro j
  exact gaugeCharacterBaseCode_primrec j

private theorem genericResidualInput_primrec :
    Primrec
      (fun input : ResidualCompilerInput eqs vars ↦
        (input.1,
          fun j ↦
            ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.gaugeCharacterBaseCode
              (gaugeExponents input.2) j)) :=
  Primrec.pair Primrec.fst
    (gaugeCharacterBaseCodeFamily_primrec.comp Primrec.snd)

set_option maxHeartbeats 1600000 in
-- The output is a flattened finite family of real residual coordinates.
/-- Every specialized fourth-root gauge residual is primitive recursive in
the rational scales and the DQL table. -/
theorem residualCode_primrec :
    Primrec
      (fun input : ResidualCompilerInput eqs vars ↦
        residualCode input.1 input.2) := by
  exact
    (ComplexGaugeFamilyPolynomialCode.residualCode_primrec.comp
      genericResidualInput_primrec).of_eq
      (fun _ ↦ rfl)

theorem residualCode_computable :
    Computable
      (fun input : ResidualCompilerInput eqs vars ↦
        residualCode input.1 input.2) :=
  residualCode_primrec.to_comp

/-! ## Literal theta-output family -/

/-- The family of literal outputs `GⱼT₁,ⱼ` contains no runtime data and is
primitive recursive in its finite index. -/
theorem thetaOutputCode_primrec :
    Primrec
      (thetaOutputCode (eqs := eqs) :
        Fin vars → ComplexPairCode (dimension eqs vars)) := by
  simpa [thetaOutputCode] using
    (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.thetaOutputCode_primrec
      (q := clockCount eqs vars) (b := vars))

theorem thetaOutputCode_computable :
    Computable
      (thetaOutputCode (eqs := eqs) :
        Fin vars → ComplexPairCode (dimension eqs vars)) :=
  thetaOutputCode_primrec.to_comp

end HGAS.DetectorJacobiGaugeData
