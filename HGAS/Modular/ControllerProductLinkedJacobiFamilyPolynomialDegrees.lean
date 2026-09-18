import HGAS.Algebra.PolynomialBlockDegrees
import HGAS.Modular.ControllerProductLinkedJacobiFamilyPolynomialCode
import HGAS.Modular.LinkedJacobiPolynomialDegrees
import Mathlib.Tactic

/-!
# Degree ledger for a common controller product and finitely many Jacobi blocks

The finite-family compiler has two geometrically different groups of
variables:

* the `4q` coordinates of the common product of controller clocks; and
* the `28b` coordinates of the `b` linked unary--Jacobi blocks.

The size of either family changes the ambient dimension, but it does not
change the polynomial degree.  Each controller equation has degree at
most three.  Each Jacobi basis equation has degree at most eight in its
own linked block, and its dynamic coefficient is a linear readout of the
common controller variables.  Consequently every component has
bidegree at most

```
                 (controller degree, linked degree) = (3, 8)
```

and ordinary total degree at most `1 + 8 = 9`.

The proofs below use raw termwise degree bounds.  In particular, they do
not depend on cancellation between terms, nor on circle or Jacobi
constraint equations.  The bounds are therefore uniform in both `q` and
`b` and apply at every ambient point.
-/

namespace HGAS.Modular.ControllerProductLinkedJacobiFamilyPolynomialCode

open HGAS
open HGAS.Clocks

variable {q b : ℕ}

/-! ## Degree bounds before assembling the variable blocks -/

theorem controllerFieldCode_termsDegreeLE
    (parameters : Fin q → RationalCode) :
    ∀ i, PolynomialCode.TermsDegreeLE 3
      (controllerFieldCode parameters i) :=
  ControllerPhaseProductPolynomialCode.fieldCode_termsDegreeLE
    parameters

theorem omegaControllerCode_termsDegreeLE
    (omegaWeights : Fin b → Fin q → RationalCode)
    (parameters : Fin q → RationalCode)
    (a : Fin b) :
    PolynomialCode.TermsDegreeLE 1
      (omegaControllerCode omegaWeights parameters a) :=
  ControllerPhaseProductLinearFrequencyCode.code_termsDegreeLE
    (omegaWeights a) parameters

theorem numberControllerCode_termsDegreeLE
    (numberWeights : Fin b → Fin q → RationalCode)
    (parameters : Fin q → RationalCode)
    (a : Fin b) :
    PolynomialCode.TermsDegreeLE 1
      (numberControllerCode numberWeights parameters a) :=
  ControllerPhaseProductLinearFrequencyCode.code_termsDegreeLE
    (numberWeights a) parameters

theorem kappaZControllerCode_termsDegreeLE
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode)
    (parameters : Fin q → RationalCode)
    (a : Fin b) :
    PolynomialCode.TermsDegreeLE 1
      (kappaZControllerCode
        omegaWeights numberWeights parameters a) := by
  have hhalf :
      PolynomialCode.TermsDegreeLE 0
        (PolynomialCode.constant halfCode :
          PolynomialCode (controllerDimension q)) :=
    PolynomialCode.termsDegreeLE_constant halfCode
  have hsum :
      PolynomialCode.TermsDegreeLE 1
        (PolynomialCode.add
          (omegaControllerCode omegaWeights parameters a)
          (numberControllerCode numberWeights parameters a)) :=
    PolynomialCode.termsDegreeLE_add
      (omegaControllerCode_termsDegreeLE
        omegaWeights parameters a)
      (numberControllerCode_termsDegreeLE
        numberWeights parameters a)
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

/-!
Embedding a local polynomial into one member of the finite linked family
preserves its raw total degree.  The following two lemmas package that
fact before and after the outer controller/linked block split.
-/

theorem linkedBasisCode_termsBidegreeLE
    {D : ℕ}
    (a : Fin b)
    (F : PolynomialFieldCode localLinkedRealDimension)
    (j : Fin localLinkedRealDimension)
    (hF : PolynomialCode.TermsDegreeLE D (F j)) :
    PolynomialBlockCode.TermsBidegreeLE 0 D
      (linkedBasisCode (q := q) a F j) :=
  PolynomialBlockCode.termsBidegreeLE_right
    (PolynomialFiniteProductCode.termsDegreeLE_lift hF)

theorem linkedBasisCode_termsDegreeLE
    {D : ℕ}
    (a : Fin b)
    (F : PolynomialFieldCode localLinkedRealDimension)
    (j : Fin localLinkedRealDimension)
    (hF : PolynomialCode.TermsDegreeLE D (F j)) :
    PolynomialCode.TermsDegreeLE D
      (linkedBasisCode (q := q) a F j) :=
  PolynomialCode.termsDegreeLE_injectVariables _
    (PolynomialFiniteProductCode.termsDegreeLE_lift hF)

/-! ## Separate controller and linked-family degrees -/

theorem omegaCode_termsBidegreeLE
    (omegaWeights : Fin b → Fin q → RationalCode)
    (parameters : Fin q → RationalCode)
    (a : Fin b) :
    PolynomialBlockCode.TermsBidegreeLE 1 0
      (omegaCode omegaWeights parameters a) :=
  PolynomialBlockCode.termsBidegreeLE_left
    (omegaControllerCode_termsDegreeLE
      omegaWeights parameters a)

theorem kappaZCode_termsBidegreeLE
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode)
    (parameters : Fin q → RationalCode)
    (a : Fin b) :
    PolynomialBlockCode.TermsBidegreeLE 1 0
      (kappaZCode
        omegaWeights numberWeights parameters a) :=
  PolynomialBlockCode.termsBidegreeLE_left
    (kappaZControllerCode_termsDegreeLE
      omegaWeights numberWeights parameters a)

/-- Every coordinate of every linked block is at most linear in the
common controller variables and at most degree eight in all linked
variables. -/
theorem linkedFieldComponentCode_termsBidegreeLE
    (parameters : Fin q → RationalCode)
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode)
    (a : Fin b) (j : Fin localLinkedRealDimension) :
    PolynomialBlockCode.TermsBidegreeLE 1 8
      (linkedFieldComponentCode
        parameters omegaWeights numberWeights a j) := by
  have hz :
      PolynomialBlockCode.TermsBidegreeLE 0 8
        (linkedBasisCode (q := q) a linkedZBasisFieldCode j) :=
    linkedBasisCode_termsBidegreeLE
      a linkedZBasisFieldCode j
      (linkedZBasisFieldCode_termsDegreeLE j)
  have hphi :
      PolynomialBlockCode.TermsBidegreeLE 0 8
        (linkedBasisCode (q := q) a linkedIPhiBasisFieldCode j) :=
    linkedBasisCode_termsBidegreeLE
      a linkedIPhiBasisFieldCode j
      (linkedIPhiBasisFieldCode_termsDegreeLE j)
  have hZproduct :=
    PolynomialBlockCode.termsBidegreeLE_mul
      (kappaZCode_termsBidegreeLE
        omegaWeights numberWeights parameters a) hz
  have hPhiProduct :=
    PolynomialBlockCode.termsBidegreeLE_mul
      (omegaCode_termsBidegreeLE
        omegaWeights parameters a) hphi
  simpa [linkedFieldComponentCode] using
    PolynomialBlockCode.termsBidegreeLE_add
      hZproduct hPhiProduct

/-- Uniform blockwise degree ledger `(3,8)` for the complete
common-controller finite-family field. -/
theorem fieldCode_termsBidegreeLE
    (parameters : Fin q → RationalCode)
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode) :
    ∀ k, PolynomialBlockCode.TermsBidegreeLE 3 8
      (fieldCode parameters omegaWeights numberWeights k) := by
  intro k
  obtain ⟨i | r, rfl⟩ := finSumFinEquiv.surjective k
  · change
      PolynomialBlockCode.TermsBidegreeLE 3 8
        (fieldCode parameters omegaWeights numberWeights
          (controllersEmbedding i))
    rw [fieldCode_controllersEmbedding]
    exact
      (PolynomialBlockCode.termsBidegreeLE_left
        (controllerFieldCode_termsDegreeLE parameters i)).promote
          (by omega) (by omega)
  · obtain ⟨⟨a, j⟩, rfl⟩ :=
      finProdFinEquiv.surjective r
    rw [show
      finSumFinEquiv
          (Sum.inr (finProdFinEquiv (a, j)) :
            Fin (controllerDimension q) ⊕
              Fin (linkedFamilyDimension b)) =
        linkedFamilyEmbedding (linkedBlockEmbedding a j) by rfl]
    rw [fieldCode_linkedBlockEmbedding]
    exact
      (linkedFieldComponentCode_termsBidegreeLE
        parameters omegaWeights numberWeights a j).promote
          (by omega) (by omega)

/-! ## Ordinary total degree -/

theorem omegaCode_termsDegreeLE
    (omegaWeights : Fin b → Fin q → RationalCode)
    (parameters : Fin q → RationalCode)
    (a : Fin b) :
    PolynomialCode.TermsDegreeLE 1
      (omegaCode omegaWeights parameters a) :=
  PolynomialCode.termsDegreeLE_injectVariables _
    (omegaControllerCode_termsDegreeLE
      omegaWeights parameters a)

theorem kappaZCode_termsDegreeLE
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode)
    (parameters : Fin q → RationalCode)
    (a : Fin b) :
    PolynomialCode.TermsDegreeLE 1
      (kappaZCode
        omegaWeights numberWeights parameters a) :=
  PolynomialCode.termsDegreeLE_injectVariables _
    (kappaZControllerCode_termsDegreeLE
      omegaWeights numberWeights parameters a)

/-- A dynamically coupled linked coordinate has ordinary degree at most
`1 + 8 = 9`. -/
theorem linkedFieldComponentCode_termsDegreeLE
    (parameters : Fin q → RationalCode)
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode)
    (a : Fin b) (j : Fin localLinkedRealDimension) :
    PolynomialCode.TermsDegreeLE 9
      (linkedFieldComponentCode
        parameters omegaWeights numberWeights a j) := by
  have hz :
      PolynomialCode.TermsDegreeLE 8
        (linkedBasisCode (q := q) a linkedZBasisFieldCode j) :=
    linkedBasisCode_termsDegreeLE
      a linkedZBasisFieldCode j
      (linkedZBasisFieldCode_termsDegreeLE j)
  have hphi :
      PolynomialCode.TermsDegreeLE 8
        (linkedBasisCode (q := q) a linkedIPhiBasisFieldCode j) :=
    linkedBasisCode_termsDegreeLE
      a linkedIPhiBasisFieldCode j
      (linkedIPhiBasisFieldCode_termsDegreeLE j)
  have hZproduct :=
    PolynomialCode.termsDegreeLE_mul
      (kappaZCode_termsDegreeLE
        omegaWeights numberWeights parameters a) hz
  have hPhiProduct :=
    PolynomialCode.termsDegreeLE_mul
      (omegaCode_termsDegreeLE
        omegaWeights parameters a) hphi
  simpa [linkedFieldComponentCode] using
    PolynomialCode.termsDegreeLE_add
      hZproduct hPhiProduct

/-- Uniform ordinary total-degree bound nine for the complete
common-controller finite-family field. -/
theorem fieldCode_termsDegreeLE
    (parameters : Fin q → RationalCode)
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode) :
    ∀ k, PolynomialCode.TermsDegreeLE 9
      (fieldCode parameters omegaWeights numberWeights k) := by
  intro k
  obtain ⟨i | r, rfl⟩ := finSumFinEquiv.surjective k
  · change
      PolynomialCode.TermsDegreeLE 9
        (fieldCode parameters omegaWeights numberWeights
          (controllersEmbedding i))
    rw [fieldCode_controllersEmbedding]
    exact
      (PolynomialCode.termsDegreeLE_injectVariables _
        (controllerFieldCode_termsDegreeLE parameters i)).promote
          (by omega)
  · obtain ⟨⟨a, j⟩, rfl⟩ :=
      finProdFinEquiv.surjective r
    rw [show
      finSumFinEquiv
          (Sum.inr (finProdFinEquiv (a, j)) :
            Fin (controllerDimension q) ⊕
              Fin (linkedFamilyDimension b)) =
        linkedFamilyEmbedding (linkedBlockEmbedding a j) by rfl]
    rw [fieldCode_linkedBlockEmbedding]
    exact
      linkedFieldComponentCode_termsDegreeLE
        parameters omegaWeights numberWeights a j

end HGAS.Modular.ControllerProductLinkedJacobiFamilyPolynomialCode
