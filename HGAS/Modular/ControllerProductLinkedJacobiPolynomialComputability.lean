import HGAS.Modular.ControllerProductLinkedJacobiPolynomialCode
import Mathlib.Computability.Partrec
import Mathlib.Tactic

/-!
# Effectivity of the controller-product linked Jacobi compiler

Fix a finite number `q` of controller--phase clocks.  The semantic
compiler accepts three rational tuples:

* the `q` controller parameters;
* the `q` rational weights defining the modular frequency `ω`; and
* the `q` rational weights defining the auxiliary frequency `N`.

This file proves that the complete compiler is primitive recursive on
those three finite tuples, hence computable.  The proof follows the
literal syntax tree of the construction.  It uses only:

* the primitive-recursive finite-product clock compiler;
* the primitive-recursive rational linear-frequency compiler;
* primitive-recursive sparse-polynomial addition and multiplication; and
* primitive-recursive variable embeddings and finite-coordinate assembly.

In particular, compilation performs no real-number operation, polynomial
normalization, semantic equality test, root extraction, or ODE
calculation.
-/

namespace HGAS.Modular.ControllerProductLinkedJacobiPolynomialCode

open HGAS
open HGAS.Clocks

variable {q : ℕ}

/-- Runtime input to the controller-product linked Jacobi compiler.
The parenthesization exposes the controller parameters and the two
frequency-weight tuples by primitive-recursive product projections. -/
abbrev CompilerInput (q : ℕ) :=
  ((Fin q → RationalCode) × (Fin q → RationalCode)) ×
    (Fin q → RationalCode)

/-- Extract the controller parameters from the three-tuple input. -/
private theorem parameters_primrec :
    Primrec
      (fun input : CompilerInput q ↦ input.1.1) :=
  Primrec.fst.comp Primrec.fst

/-- Extract the modular-frequency weights from the three-tuple input. -/
private theorem omegaWeights_primrec :
    Primrec
      (fun input : CompilerInput q ↦ input.1.2) :=
  Primrec.snd.comp Primrec.fst

/-- Extract the auxiliary-frequency weights from the three-tuple input. -/
private theorem numberWeights_primrec :
    Primrec
      (fun input : CompilerInput q ↦ input.2) :=
  Primrec.snd

/-- Reorder the runtime input into the `(weights, parameters)` pair used by
the reusable linear-frequency compiler. -/
private theorem omegaFrequencyInput_primrec :
    Primrec
      (fun input : CompilerInput q ↦
        (input.1.2, input.1.1)) :=
  Primrec.pair omegaWeights_primrec parameters_primrec

/-- Reorder the runtime input into the `(weights, parameters)` pair for
the auxiliary frequency. -/
private theorem numberFrequencyInput_primrec :
    Primrec
      (fun input : CompilerInput q ↦
        (input.2, input.1.1)) :=
  Primrec.pair numberWeights_primrec parameters_primrec

/-- The block-diagonal controller-product field compiler is primitive
recursive in its parameter tuple. -/
theorem controllerFieldCode_primrec :
    Primrec
      (controllerFieldCode :
        (Fin q → RationalCode) →
          PolynomialFieldCode (controllerDimension q)) :=
  ControllerPhaseProductPolynomialCode.fieldCode_primrec

/-- The modular-frequency polynomial is primitive recursive jointly in
its weights and controller parameters. -/
theorem omegaControllerCode_primrec :
    Primrec
      (fun input :
          (Fin q → RationalCode) ×
            (Fin q → RationalCode) ↦
        omegaControllerCode input.1 input.2) :=
  ControllerPhaseProductLinearFrequencyCode.code_primrec

/-- The auxiliary-frequency polynomial is primitive recursive jointly in
its weights and controller parameters. -/
theorem numberControllerCode_primrec :
    Primrec
      (fun input :
          (Fin q → RationalCode) ×
            (Fin q → RationalCode) ↦
        numberControllerCode input.1 input.2) :=
  ControllerPhaseProductLinearFrequencyCode.code_primrec

set_option maxHeartbeats 800000 in
-- Nested finite-function encodings make this composition expensive to elaborate.
/-- The controller-coordinate code of `(ω+N)/2` is primitive recursive in
all three rational tuples. -/
theorem kappaZControllerCode_primrec :
    Primrec
      (fun input : CompilerInput q ↦
        kappaZControllerCode
          input.1.2 input.2 input.1.1) := by
  exact
    PolynomialCode.mul_primrec.comp
      (Primrec.const
        (PolynomialCode.constant halfCode :
          PolynomialCode (controllerDimension q)))
      (PolynomialCode.add_primrec.comp
        (omegaControllerCode_primrec.comp
          omegaFrequencyInput_primrec)
        (numberControllerCode_primrec.comp
          numberFrequencyInput_primrec))

/-- Embedding the modular-frequency code in the complete ambient space is
primitive recursive. -/
theorem omegaCode_primrec :
    Primrec
      (fun input :
          (Fin q → RationalCode) ×
            (Fin q → RationalCode) ↦
        omegaCode input.1 input.2) :=
  PolynomialBlockCode.left_primrec.comp
    omegaControllerCode_primrec

set_option maxHeartbeats 800000 in
-- Nested finite-function encodings make this composition expensive to elaborate.
/-- Embedding the dynamic `κZ` code in the complete ambient space is
primitive recursive. -/
theorem kappaZCode_primrec :
    Primrec
      (fun input : CompilerInput q ↦
        kappaZCode input.1.2 input.2 input.1.1) :=
  PolynomialBlockCode.left_primrec.comp
    kappaZControllerCode_primrec

set_option maxHeartbeats 800000 in
-- Nested finite-function encodings make this composition expensive to elaborate.
/-- Each dynamically coupled linked coordinate is primitive recursive in
the three rational tuples. -/
theorem linkedFieldComponentCode_primrec
    (j : Fin linkedRealDimension) :
    Primrec
      (fun input : CompilerInput q ↦
        linkedFieldComponentCode
          input.1.1 input.1.2 input.2 j) := by
  have hZbasis :
      Primrec
        (fun (_ : CompilerInput q) ↦
          PolynomialBlockCode.right
            (m := controllerDimension q)
            (linkedZBasisFieldCode j)) :=
    Primrec.const _
  have hPhibasis :
      Primrec
        (fun (_ : CompilerInput q) ↦
          PolynomialBlockCode.right
            (m := controllerDimension q)
            (linkedIPhiBasisFieldCode j)) :=
    Primrec.const _
  have homega :
      Primrec
        (fun input : CompilerInput q ↦
          omegaCode input.1.2 input.1.1) :=
    omegaCode_primrec.comp omegaFrequencyInput_primrec
  exact
    PolynomialCode.add_primrec.comp
      (PolynomialCode.mul_primrec.comp
        kappaZCode_primrec hZbasis)
      (PolynomialCode.mul_primrec.comp
        homega hPhibasis)

set_option maxHeartbeats 800000 in
-- Finite-output currying over a nested three-tuple is expensive to elaborate.
/-- **Effective controller-product linked Jacobi compiler.**

For every fixed number `q` of controller clocks, the complete polynomial
field compiler is primitive recursive in the controller parameters and
the two rational frequency-weight tuples. -/
theorem fieldCode_primrec :
    Primrec
      (fun input : CompilerInput q ↦
        fieldCode input.1.1 input.1.2 input.2) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro k
  obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective k
  · have hcontrollers :
        Primrec
          (fun input : CompilerInput q ↦
            controllerFieldCode input.1.1) :=
      controllerFieldCode_primrec.comp parameters_primrec
    exact
      (PolynomialBlockCode.left_primrec.comp
        (Primrec.fin_app.comp hcontrollers
          (Primrec.const i))).of_eq fun input ↦
            (fieldCode_controllersEmbedding
              input.1.1 input.1.2 input.2 i).symm
  · exact
      (linkedFieldComponentCode_primrec j).of_eq
        fun input ↦
          (fieldCode_linkedRealEmbedding
            input.1.1 input.1.2 input.2 j).symm

/-- The complete compiler is computable on its three finite rational
tuples. -/
theorem fieldCode_computable :
    Computable
      (fun input : CompilerInput q ↦
        fieldCode input.1.1 input.1.2 input.2) :=
  fieldCode_primrec.to_comp

end HGAS.Modular.ControllerProductLinkedJacobiPolynomialCode
