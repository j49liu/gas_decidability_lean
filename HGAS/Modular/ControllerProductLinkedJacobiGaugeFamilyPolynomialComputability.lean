import HGAS.Clocks.ControllerPhaseProductCharacterComputability
import HGAS.Compiler.ComplexGaugeFamilyPolynomialComputability
import HGAS.Modular.ControllerProductLinkedJacobiFamilyPolynomialComputability
import HGAS.Modular.ControllerProductLinkedJacobiGaugeFamilyPolynomialCode
import Mathlib.Computability.Partrec
import Mathlib.Tactic

/-!
# Effectivity of gauge-completed common-controller Jacobi families

This file turns the semantic construction in
`ControllerProductLinkedJacobiGaugeFamilyPolynomialCode` into one
primitive-recursive compiler.  For fixed finite sizes `q` and `b`, the
runtime data are

* the rational controller parameters;
* the two rational frequency-weight families for the Jacobi blocks; and
* one integral character-exponent tuple for each fourth-root gauge.

The compiled field is obtained by first compiling the common
controller--Jacobi family and then applying the reusable finite-gauge
compiler.  We separately expose the frequency family, so later arithmetic
specializations can reuse it without reopening the finite-block indexing
proof.  Effectivity of the generic fourth-root residual compiler is proved
in `ComplexGaugeFamilyPolynomialComputability`.
-/

namespace HGAS.Modular.ControllerProductLinkedJacobiGaugeFamilyPolynomialCode

open HGAS
open HGAS.Clocks
open HGAS.Clocks.ControllerPhaseProductCharacterCode

variable {q b : ℕ}

/-- Runtime data for the complete gauge-extended field compiler. -/
abbrev CompilerInput (q b : ℕ) :=
  ControllerProductLinkedJacobiFamilyPolynomialCode.CompilerInput q b ×
    (Fin b → Fin q → ℤ)

/-- The smaller input used by the gauge-frequency subcompiler.  Keeping
this projection separate substantially reduces elaboration through the
nested Jacobi-family input. -/
abbrev GaugeFrequencyInput (q b : ℕ) :=
  (Fin q → RationalCode) × (Fin b → Fin q → ℤ)

/-- Inserting one controller polynomial into the common linked-family
ambient variables is primitive recursive. -/
theorem liftController_primrec :
    Primrec
      (liftController (q := q) (b := b) :
        PolynomialCode
            (ControllerProductLinkedJacobiFamilyPolynomialCode.controllerDimension
              q) →
          PolynomialCode (Base.dimension q b)) :=
  PolynomialCode.injectVariables_primrec
    ControllerProductLinkedJacobiFamilyPolynomialCode.controllersEmbedding

/-- The corresponding complex-pair insertion is primitive recursive. -/
theorem liftControllerPair_primrec :
    Primrec
      (liftControllerPair (q := q) (b := b) :
        ComplexPairCode
            (ControllerProductLinkedJacobiFamilyPolynomialCode.controllerDimension
              q) →
          ComplexPairCode (Base.dimension q b)) :=
  Primrec.pair
    (liftController_primrec.comp Primrec.fst)
    (liftController_primrec.comp Primrec.snd)

private theorem compilerGaugeFrequencyInput_primrec :
    Primrec
      (fun input : CompilerInput q b ↦
        (input.1.1.1, input.2)) :=
  Primrec.pair
    (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    Primrec.snd

private theorem gaugeExponentsAt_primrec (a : Fin b) :
    Primrec
      (fun input : GaugeFrequencyInput q b ↦ input.2 a) :=
  Primrec.fin_app.comp Primrec.snd (Primrec.const a)

private theorem gaugeDerivativeInput_primrec (a : Fin b) :
    Primrec
      (fun input : GaugeFrequencyInput q b ↦
        (input.1, input.2 a)) :=
  Primrec.pair Primrec.fst
    (gaugeExponentsAt_primrec a)

set_option maxHeartbeats 1600000 in
-- The exponent family is a nested finite-function encoding.
/-- The polynomial frequency driving a fixed gauge is primitive recursive
in all compiler data. -/
theorem gaugeFrequencyBaseCode_primrec (a : Fin b) :
    Primrec
      (fun input : GaugeFrequencyInput q b ↦
        gaugeFrequencyBaseCode input.1 input.2 a) := by
  exact
    (liftController_primrec.comp
      (frequencyCode_primrec.comp
        (gaugeDerivativeInput_primrec a))).of_eq
      (fun _ ↦ rfl)

set_option maxHeartbeats 1200000 in
-- Currying the nested exponent family requires extra elaboration.
/-- Compile every gauge-frequency polynomial in one primitive-recursive
call. -/
theorem gaugeFrequencyBaseCodeFamily_primrec :
    Primrec
      (fun input : GaugeFrequencyInput q b ↦
        fun a ↦ gaugeFrequencyBaseCode input.1 input.2 a) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro a
  exact gaugeFrequencyBaseCode_primrec a

private theorem baseFieldCode_primrec :
    Primrec
      (fun input : CompilerInput q b ↦
        ControllerProductLinkedJacobiFamilyPolynomialCode.fieldCode
          input.1.1.1 input.1.1.2 input.1.2) :=
  ControllerProductLinkedJacobiFamilyPolynomialCode.fieldCode_primrec.comp
    Primrec.fst

set_option maxHeartbeats 1600000 in
-- This composition joins two independently compiled finite-function fields.
/-- The complete common-controller, Jacobi, and fourth-root-gauge field
compiler is primitive recursive. -/
theorem fieldCode_primrec :
    Primrec
      (fun input : CompilerInput q b ↦
        fieldCode input.1.1.1 input.1.1.2 input.1.2 input.2) := by
  exact
    ComplexGaugeFamilyPolynomialCode.fieldCode_primrec.comp
      (Primrec.pair baseFieldCode_primrec
        (gaugeFrequencyBaseCodeFamily_primrec.comp
          compilerGaugeFrequencyInput_primrec))

theorem fieldCode_computable :
    Computable
      (fun input : CompilerInput q b ↦
        fieldCode input.1.1.1 input.1.1.2 input.1.2 input.2) :=
  fieldCode_primrec.to_comp

/-- The finite family of literal outputs `GₐT₁,ₐ` is itself executable.
It contains no runtime coefficients. -/
theorem thetaOutputCode_primrec :
    Primrec
      (thetaOutputCode (q := q) :
        Fin b → ComplexPairCode (dimension q b)) :=
  Primrec.dom_finite _

theorem thetaOutputCode_computable :
    Computable
      (thetaOutputCode (q := q) :
        Fin b → ComplexPairCode (dimension q b)) :=
  thetaOutputCode_primrec.to_comp

end HGAS.Modular.ControllerProductLinkedJacobiGaugeFamilyPolynomialCode
