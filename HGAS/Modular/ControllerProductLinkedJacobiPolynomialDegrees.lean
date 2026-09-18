import HGAS.Algebra.PolynomialBlockDegrees
import HGAS.Modular.ControllerProductLinkedJacobiPolynomialCode
import HGAS.Modular.LinkedJacobiPolynomialDegrees
import Mathlib.Tactic

/-!
# Degree ledger for finite-controller linked Jacobi couplings

The number of clocks changes the dimension but not the degree.  With the
variables split into the `4q` controller coordinates and the twenty-eight
linked coordinates, every component of the compiler has bidegree at most

```
                 (controller degree, linked degree) = (3, 8).
```

The controller equations themselves have degree at most three.  Each
linked equation is a degree-eight constant-basis Jacobi equation
multiplied by a linear controller readout, and hence has ordinary total
degree at most nine.  This file records both the sharper blockwise ledger
and the uniform total-degree ledger.
-/

namespace HGAS.Modular.ControllerProductLinkedJacobiPolynomialCode

open HGAS
open HGAS.Clocks

variable {q : ℕ}

theorem controllerFieldCode_termsDegreeLE
    (parameters : Fin q → RationalCode) :
    ∀ i, PolynomialCode.TermsDegreeLE 3
      (controllerFieldCode parameters i) :=
  ControllerPhaseProductPolynomialCode.fieldCode_termsDegreeLE
    parameters

theorem omegaControllerCode_termsDegreeLE
    (omegaWeights parameters : Fin q → RationalCode) :
    PolynomialCode.TermsDegreeLE 1
      (omegaControllerCode omegaWeights parameters) :=
  ControllerPhaseProductLinearFrequencyCode.code_termsDegreeLE
    omegaWeights parameters

theorem numberControllerCode_termsDegreeLE
    (numberWeights parameters : Fin q → RationalCode) :
    PolynomialCode.TermsDegreeLE 1
      (numberControllerCode numberWeights parameters) :=
  ControllerPhaseProductLinearFrequencyCode.code_termsDegreeLE
    numberWeights parameters

theorem kappaZControllerCode_termsDegreeLE
    (omegaWeights numberWeights parameters :
      Fin q → RationalCode) :
    PolynomialCode.TermsDegreeLE 1
      (kappaZControllerCode
        omegaWeights numberWeights parameters) := by
  have hhalf :
      PolynomialCode.TermsDegreeLE 0
        (PolynomialCode.constant halfCode :
          PolynomialCode (controllerDimension q)) :=
    PolynomialCode.termsDegreeLE_constant halfCode
  have hsum :
      PolynomialCode.TermsDegreeLE 1
        (PolynomialCode.add
          (omegaControllerCode omegaWeights parameters)
          (numberControllerCode numberWeights parameters)) :=
    PolynomialCode.termsDegreeLE_add
      (omegaControllerCode_termsDegreeLE
        omegaWeights parameters)
      (numberControllerCode_termsDegreeLE
        numberWeights parameters)
  simpa [kappaZControllerCode] using
    PolynomialCode.termsDegreeLE_mul hhalf hsum

theorem linkedZBasisFieldCode_termsDegreeLE :
    ∀ j, PolynomialCode.TermsDegreeLE 8
      (linkedZBasisFieldCode j) :=
  LinkedJacobiPolynomialCode.compileFieldCode_termsDegreeLE
    GaussianRationalCode.one GaussianRationalCode.zero

theorem linkedIPhiBasisFieldCode_termsDegreeLE :
    ∀ j, PolynomialCode.TermsDegreeLE 8
      (linkedIPhiBasisFieldCode j) :=
  LinkedJacobiPolynomialCode.compileFieldCode_termsDegreeLE
    GaussianRationalCode.zero GaussianRationalCode.I

/-! ## Separate controller and linked-variable degrees -/

theorem omegaCode_termsBidegreeLE
    (omegaWeights parameters : Fin q → RationalCode) :
    PolynomialBlockCode.TermsBidegreeLE 1 0
      (omegaCode omegaWeights parameters) :=
  PolynomialBlockCode.termsBidegreeLE_left
    (omegaControllerCode_termsDegreeLE
      omegaWeights parameters)

theorem kappaZCode_termsBidegreeLE
    (omegaWeights numberWeights parameters :
      Fin q → RationalCode) :
    PolynomialBlockCode.TermsBidegreeLE 1 0
      (kappaZCode omegaWeights numberWeights parameters) :=
  PolynomialBlockCode.termsBidegreeLE_left
    (kappaZControllerCode_termsDegreeLE
      omegaWeights numberWeights parameters)

/-- Every linked coordinate is at most linear in controller variables and
at most degree eight in linked variables. -/
theorem linkedFieldComponentCode_termsBidegreeLE
    (parameters omegaWeights numberWeights :
      Fin q → RationalCode)
    (j : Fin linkedRealDimension) :
    PolynomialBlockCode.TermsBidegreeLE 1 8
      (linkedFieldComponentCode
        parameters omegaWeights numberWeights j) := by
  have hz :
      PolynomialBlockCode.TermsBidegreeLE 0 8
        (PolynomialBlockCode.right
          (m := controllerDimension q)
          (linkedZBasisFieldCode j)) :=
    PolynomialBlockCode.termsBidegreeLE_right
      (linkedZBasisFieldCode_termsDegreeLE j)
  have hphi :
      PolynomialBlockCode.TermsBidegreeLE 0 8
        (PolynomialBlockCode.right
          (m := controllerDimension q)
          (linkedIPhiBasisFieldCode j)) :=
    PolynomialBlockCode.termsBidegreeLE_right
      (linkedIPhiBasisFieldCode_termsDegreeLE j)
  have hZproduct :=
    PolynomialBlockCode.termsBidegreeLE_mul
      (kappaZCode_termsBidegreeLE
        omegaWeights numberWeights parameters) hz
  have hPhiProduct :=
    PolynomialBlockCode.termsBidegreeLE_mul
      (omegaCode_termsBidegreeLE omegaWeights parameters)
      hphi
  simpa [linkedFieldComponentCode] using
    PolynomialBlockCode.termsBidegreeLE_add
      hZproduct hPhiProduct

/-- Uniform blockwise degree ledger `(3,8)` for the complete field. -/
theorem fieldCode_termsBidegreeLE
    (parameters omegaWeights numberWeights :
      Fin q → RationalCode) :
    ∀ k, PolynomialBlockCode.TermsBidegreeLE 3 8
      (fieldCode parameters omegaWeights numberWeights k) := by
  intro k
  obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective k
  · change
      PolynomialBlockCode.TermsBidegreeLE 3 8
        (fieldCode parameters omegaWeights numberWeights
          (controllersEmbedding i))
    rw [fieldCode_controllersEmbedding]
    exact
      (PolynomialBlockCode.termsBidegreeLE_left
        (controllerFieldCode_termsDegreeLE parameters i)).promote
          (by omega) (by omega)
  · change
      PolynomialBlockCode.TermsBidegreeLE 3 8
        (fieldCode parameters omegaWeights numberWeights
          (linkedRealEmbedding j))
    rw [fieldCode_linkedRealEmbedding]
    exact
      (linkedFieldComponentCode_termsBidegreeLE
        parameters omegaWeights numberWeights j).promote
          (by omega) (by omega)

/-! ## Ordinary total degree -/

theorem omegaCode_termsDegreeLE
    (omegaWeights parameters : Fin q → RationalCode) :
    PolynomialCode.TermsDegreeLE 1
      (omegaCode omegaWeights parameters) :=
  PolynomialCode.termsDegreeLE_injectVariables _
    (omegaControllerCode_termsDegreeLE
      omegaWeights parameters)

theorem kappaZCode_termsDegreeLE
    (omegaWeights numberWeights parameters :
      Fin q → RationalCode) :
    PolynomialCode.TermsDegreeLE 1
      (kappaZCode omegaWeights numberWeights parameters) :=
  PolynomialCode.termsDegreeLE_injectVariables _
    (kappaZControllerCode_termsDegreeLE
      omegaWeights numberWeights parameters)

/-- Each dynamically coupled linked coordinate has ordinary degree at
most `1+8=9`. -/
theorem linkedFieldComponentCode_termsDegreeLE
    (parameters omegaWeights numberWeights :
      Fin q → RationalCode)
    (j : Fin linkedRealDimension) :
    PolynomialCode.TermsDegreeLE 9
      (linkedFieldComponentCode
        parameters omegaWeights numberWeights j) := by
  have hz :
      PolynomialCode.TermsDegreeLE 8
        (PolynomialBlockCode.right
          (m := controllerDimension q)
          (linkedZBasisFieldCode j)) :=
    PolynomialCode.termsDegreeLE_injectVariables _
      (linkedZBasisFieldCode_termsDegreeLE j)
  have hphi :
      PolynomialCode.TermsDegreeLE 8
        (PolynomialBlockCode.right
          (m := controllerDimension q)
          (linkedIPhiBasisFieldCode j)) :=
    PolynomialCode.termsDegreeLE_injectVariables _
      (linkedIPhiBasisFieldCode_termsDegreeLE j)
  have hZproduct :=
    PolynomialCode.termsDegreeLE_mul
      (kappaZCode_termsDegreeLE
        omegaWeights numberWeights parameters) hz
  have hPhiProduct :=
    PolynomialCode.termsDegreeLE_mul
      (omegaCode_termsDegreeLE omegaWeights parameters)
      hphi
  simpa [linkedFieldComponentCode] using
    PolynomialCode.termsDegreeLE_add
      hZproduct hPhiProduct

/-- Uniform ordinary total-degree bound nine for the complete field. -/
theorem fieldCode_termsDegreeLE
    (parameters omegaWeights numberWeights :
      Fin q → RationalCode) :
    ∀ k, PolynomialCode.TermsDegreeLE 9
      (fieldCode parameters omegaWeights numberWeights k) := by
  intro k
  obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective k
  · change
      PolynomialCode.TermsDegreeLE 9
        (fieldCode parameters omegaWeights numberWeights
          (controllersEmbedding i))
    rw [fieldCode_controllersEmbedding]
    exact
      (PolynomialCode.termsDegreeLE_injectVariables _
        (controllerFieldCode_termsDegreeLE parameters i)).promote
          (by omega)
  · change
      PolynomialCode.TermsDegreeLE 9
        (fieldCode parameters omegaWeights numberWeights
          (linkedRealEmbedding j))
    rw [fieldCode_linkedRealEmbedding]
    exact
      linkedFieldComponentCode_termsDegreeLE
        parameters omegaWeights numberWeights j

end HGAS.Modular.ControllerProductLinkedJacobiPolynomialCode
