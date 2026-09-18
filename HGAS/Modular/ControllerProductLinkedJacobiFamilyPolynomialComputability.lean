import HGAS.Modular.ControllerProductLinkedJacobiFamilyPolynomialCode
import Mathlib.Computability.Partrec
import Mathlib.Tactic

/-!
# Effectivity of the common-controller finite Jacobi-family compiler

Fix finite numbers `q` and `b`.  The compiler constructed in
`ControllerProductLinkedJacobiFamilyPolynomialCode` accepts:

* one tuple of `q` rational controller parameters;
* for every Jacobi block, a tuple of `q` rational weights defining its
  modular frequency; and
* for every Jacobi block, a tuple of `q` rational weights defining its
  auxiliary frequency.

This file bundles those data into one runtime input and proves that the
complete sparse-polynomial field compiler is primitive recursive, hence
computable.  The proof mirrors the compiler's syntax tree.  Selecting a
block and a clock coordinate is primitive recursive because both index
types are fixed and finite; rational constants, polynomial addition and
multiplication, variable embeddings, and finite-coordinate assembly are
primitive recursive by the reusable algebraic compiler library.

Thus the family construction is effective uniformly in all of its
rational data for each fixed pair `(q,b)`.  Compilation invokes no
real-number computation, root extraction, semantic polynomial equality,
or differential-equation solver.
-/

namespace HGAS.Modular.ControllerProductLinkedJacobiFamilyPolynomialCode

open HGAS
open HGAS.Clocks

variable {q b : ℕ}

/-- Runtime input to the common-controller finite-family compiler.

The nesting

```
((parameters, omegaWeights), numberWeights)
```

is chosen so that every component is obtained by primitive-recursive
product projections.  Each weight family is indexed first by the Jacobi
block and then by the common controller clock. -/
abbrev CompilerInput (q b : ℕ) :=
  ((Fin q → RationalCode) ×
      (Fin b → Fin q → RationalCode)) ×
    (Fin b → Fin q → RationalCode)

/-- Extract the common controller parameters. -/
private theorem parameters_primrec :
    Primrec
      (fun input : CompilerInput q b ↦ input.1.1) :=
  Primrec.fst.comp Primrec.fst

/-- Extract the complete family of modular-frequency weights. -/
private theorem omegaWeights_primrec :
    Primrec
      (fun input : CompilerInput q b ↦ input.1.2) :=
  Primrec.snd.comp Primrec.fst

/-- Extract the complete family of auxiliary-frequency weights. -/
private theorem numberWeights_primrec :
    Primrec
      (fun input : CompilerInput q b ↦ input.2) :=
  Primrec.snd

/-- Select the modular-frequency weight tuple belonging to block `a`. -/
private theorem omegaBlockWeights_primrec (a : Fin b) :
    Primrec
      (fun input : CompilerInput q b ↦ input.1.2 a) :=
  Primrec.fin_app.comp omegaWeights_primrec (Primrec.const a)

/-- Select the auxiliary-frequency weight tuple belonging to block `a`. -/
private theorem numberBlockWeights_primrec (a : Fin b) :
    Primrec
      (fun input : CompilerInput q b ↦ input.2 a) :=
  Primrec.fin_app.comp numberWeights_primrec (Primrec.const a)

/-- Reorder block `a`'s modular weights and the common parameters into the
input pair expected by the reusable linear-frequency compiler. -/
private theorem omegaFrequencyInput_primrec (a : Fin b) :
    Primrec
      (fun input : CompilerInput q b ↦
        (input.1.2 a, input.1.1)) :=
  Primrec.pair (omegaBlockWeights_primrec a) parameters_primrec

/-- Reorder block `a`'s auxiliary weights and the common parameters into
the input pair expected by the reusable linear-frequency compiler. -/
private theorem numberFrequencyInput_primrec (a : Fin b) :
    Primrec
      (fun input : CompilerInput q b ↦
        (input.2 a, input.1.1)) :=
  Primrec.pair (numberBlockWeights_primrec a) parameters_primrec

/-- The common block-diagonal controller field is primitive recursive in
the shared parameter tuple. -/
theorem controllerFieldCode_primrec :
    Primrec
      (controllerFieldCode :
        (Fin q → RationalCode) →
          PolynomialFieldCode (controllerDimension q)) :=
  ControllerPhaseProductPolynomialCode.fieldCode_primrec

/-- The controller-coordinate modular-frequency polynomial for a fixed
Jacobi block is primitive recursive in the complete family input. -/
theorem omegaControllerCode_primrec (a : Fin b) :
    Primrec
      (fun input : CompilerInput q b ↦
        omegaControllerCode input.1.2 input.1.1 a) :=
  ControllerPhaseProductLinearFrequencyCode.code_primrec.comp
    (omegaFrequencyInput_primrec a)

/-- The controller-coordinate auxiliary-frequency polynomial for a fixed
Jacobi block is primitive recursive in the complete family input. -/
theorem numberControllerCode_primrec (a : Fin b) :
    Primrec
      (fun input : CompilerInput q b ↦
        numberControllerCode input.2 input.1.1 a) :=
  ControllerPhaseProductLinearFrequencyCode.code_primrec.comp
    (numberFrequencyInput_primrec a)

set_option maxHeartbeats 1200000 in
-- The input contains two nested finite-function encodings.
/-- The controller-coordinate code of `(ωₐ+Nₐ)/2` is primitive recursive
for every fixed block `a`. -/
theorem kappaZControllerCode_primrec (a : Fin b) :
    Primrec
      (fun input : CompilerInput q b ↦
        kappaZControllerCode
          input.1.2 input.2 input.1.1 a) := by
  exact
    PolynomialCode.mul_primrec.comp
      (Primrec.const
        (PolynomialCode.constant halfCode :
          PolynomialCode (controllerDimension q)))
      (PolynomialCode.add_primrec.comp
        (omegaControllerCode_primrec a)
        (numberControllerCode_primrec a))

/-- Embedding block `a`'s modular-frequency polynomial into the complete
ambient space is primitive recursive. -/
theorem omegaCode_primrec (a : Fin b) :
    Primrec
      (fun input : CompilerInput q b ↦
        omegaCode input.1.2 input.1.1 a) :=
  PolynomialBlockCode.left_primrec.comp
    (omegaControllerCode_primrec a)

set_option maxHeartbeats 1200000 in
-- The input contains two nested finite-function encodings.
/-- Embedding block `a`'s dynamic `κZ` polynomial into the complete
ambient space is primitive recursive. -/
theorem kappaZCode_primrec (a : Fin b) :
    Primrec
      (fun input : CompilerInput q b ↦
        kappaZCode input.1.2 input.2 input.1.1 a) :=
  PolynomialBlockCode.left_primrec.comp
    (kappaZControllerCode_primrec a)

set_option maxHeartbeats 1200000 in
-- Nested finite-function encodings make this composition expensive to elaborate.
/-- Every coordinate `j` of every dynamically coupled linked block `a` is
primitive recursive in the complete family input. -/
theorem linkedFieldComponentCode_primrec
    (a : Fin b) (j : Fin localLinkedRealDimension) :
    Primrec
      (fun input : CompilerInput q b ↦
        linkedFieldComponentCode
          input.1.1 input.1.2 input.2 a j) := by
  have hZbasis :
      Primrec
        (fun (_ : CompilerInput q b) ↦
          linkedBasisCode
            (q := q) a linkedZBasisFieldCode j) :=
    Primrec.const _
  have hPhibasis :
      Primrec
        (fun (_ : CompilerInput q b) ↦
          linkedBasisCode
            (q := q) a linkedIPhiBasisFieldCode j) :=
    Primrec.const _
  exact
    PolynomialCode.add_primrec.comp
      (PolynomialCode.mul_primrec.comp
        (kappaZCode_primrec a) hZbasis)
      (PolynomialCode.mul_primrec.comp
        (omegaCode_primrec a) hPhibasis)

set_option maxHeartbeats 1600000 in
-- Finite-output currying over nested finite-function inputs is expensive.
/-- **Effective common-controller finite Jacobi-family compiler.**

For every fixed pair `(q,b)`, the complete polynomial vector-field
compiler is primitive recursive in the shared controller parameters and
both families of rational frequency weights. -/
theorem fieldCode_primrec :
    Primrec
      (fun input : CompilerInput q b ↦
        fieldCode input.1.1 input.1.2 input.2) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro k
  obtain ⟨i | r, rfl⟩ := finSumFinEquiv.surjective k
  · have hcontrollers :
        Primrec
          (fun input : CompilerInput q b ↦
            controllerFieldCode input.1.1) :=
      controllerFieldCode_primrec.comp parameters_primrec
    exact
      (PolynomialBlockCode.left_primrec.comp
        (Primrec.fin_app.comp hcontrollers
          (Primrec.const i))).of_eq fun input ↦
            (fieldCode_controllersEmbedding
              input.1.1 input.1.2 input.2 i).symm
  · obtain ⟨⟨a, j⟩, rfl⟩ :=
      finProdFinEquiv.surjective r
    exact
      (linkedFieldComponentCode_primrec a j).of_eq
        fun input ↦
          (fieldCode_linkedBlockEmbedding
            input.1.1 input.1.2 input.2 a j).symm

/-- The complete common-controller finite-family compiler is computable
on its bundled rational input. -/
theorem fieldCode_computable :
    Computable
      (fun input : CompilerInput q b ↦
        fieldCode input.1.1 input.1.2 input.2) :=
  fieldCode_primrec.to_comp

end HGAS.Modular.ControllerProductLinkedJacobiFamilyPolynomialCode
