import HGAS.Algebra.PolynomialBlockDegrees
import HGAS.Clocks.ControllerPolynomialDegrees
import HGAS.Modular.LinkedJacobiPolynomialDegrees
import HGAS.Modular.TwoControllerLinkedJacobiPolynomialCode
import Mathlib.Tactic

/-!
# Degree ledger for the two-controller linked Jacobi coupling

The coupled field has two complementary degree statements.

First, with the variables split into the eight controller coordinates and
the twenty-eight linked coordinates, every raw monomial has bidegree at
most

```
  (controller degree, linked-target degree) = (3,8).
```

This is the structural bound used by blockwise compactification.  The
controller equations themselves attain degree three.  A linked equation is
linear in the controller variables and has linked degree at most eight.

Second, ordinary total degree adds the two entries of a product.  Hence
the dynamically scaled linked equations have total degree at most nine,
while the controller equations retain total degree at most three.  The
uniform total-degree bound for the complete field is therefore nine, not
eight.  Recording both statements avoids conflating target degree with
ordinary total degree.
-/

namespace HGAS.Modular.TwoControllerLinkedJacobiPolynomialCode

open HGAS

theorem controllerPairFieldCode_termsDegreeLE
    (pΩ pN : RationalCode) :
    ∀ i, PolynomialCode.TermsDegreeLE 3
      (controllerPairFieldCode pΩ pN i) := by
  apply PolynomialBlockCode.field_termsDegreeLE
  · exact
      HGAS.Clocks.ControllerPolynomialCode.fieldCode_termsDegreeLE pΩ
  · exact
      HGAS.Clocks.ControllerPolynomialCode.fieldCode_termsDegreeLE pN

theorem omegaPairCode_termsDegreeLE
    (pΩ : RationalCode) :
    PolynomialCode.TermsDegreeLE 1 (omegaPairCode pΩ) := by
  have hconstant :
      PolynomialCode.TermsDegreeLE 0
        (PolynomialCode.constant pΩ :
          PolynomialCode controllerPairDimension) :=
    PolynomialCode.termsDegreeLE_constant pΩ
  have hr :
      PolynomialCode.TermsDegreeLE 1
        (PolynomialBlockCode.left
          (p := ControllerCode.dimension)
          HGAS.Clocks.ControllerPolynomialCode.rCode) :=
    PolynomialCode.termsDegreeLE_injectVariables _
      (PolynomialCode.termsDegreeLE_varCode _)
  simpa [omegaPairCode] using
    PolynomialCode.termsDegreeLE_mul hconstant hr

theorem numberPairCode_termsDegreeLE
    (pN : RationalCode) :
    PolynomialCode.TermsDegreeLE 1 (numberPairCode pN) := by
  have hconstant :
      PolynomialCode.TermsDegreeLE 0
        (PolynomialCode.constant pN :
          PolynomialCode controllerPairDimension) :=
    PolynomialCode.termsDegreeLE_constant pN
  have hr :
      PolynomialCode.TermsDegreeLE 1
        (PolynomialBlockCode.right
          (m := ControllerCode.dimension)
          HGAS.Clocks.ControllerPolynomialCode.rCode) :=
    PolynomialCode.termsDegreeLE_injectVariables _
      (PolynomialCode.termsDegreeLE_varCode _)
  simpa [numberPairCode] using
    PolynomialCode.termsDegreeLE_mul hconstant hr

theorem kappaZPairCode_termsDegreeLE
    (pΩ pN : RationalCode) :
    PolynomialCode.TermsDegreeLE 1
      (kappaZPairCode pΩ pN) := by
  have hhalf :
      PolynomialCode.TermsDegreeLE 0
        (PolynomialCode.constant halfCode :
          PolynomialCode controllerPairDimension) :=
    PolynomialCode.termsDegreeLE_constant halfCode
  have hsum :
      PolynomialCode.TermsDegreeLE 1
        (PolynomialCode.add
          (omegaPairCode pΩ) (numberPairCode pN)) :=
    PolynomialCode.termsDegreeLE_add
      (omegaPairCode_termsDegreeLE pΩ)
      (numberPairCode_termsDegreeLE pN)
  simpa [kappaZPairCode] using
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

/-! ## Separate controller and linked-target degrees -/

theorem omegaCode_termsBidegreeLE
    (pΩ : RationalCode) :
    PolynomialBlockCode.TermsBidegreeLE 1 0
      (omegaCode pΩ) :=
  PolynomialBlockCode.termsBidegreeLE_left
    (omegaPairCode_termsDegreeLE pΩ)

theorem kappaZCode_termsBidegreeLE
    (pΩ pN : RationalCode) :
    PolynomialBlockCode.TermsBidegreeLE 1 0
      (kappaZCode pΩ pN) :=
  PolynomialBlockCode.termsBidegreeLE_left
    (kappaZPairCode_termsDegreeLE pΩ pN)

/-- Each dynamically coupled linked coordinate is at most linear in the
controller variables and has linked-target degree at most eight. -/
theorem linkedFieldComponentCode_termsBidegreeLE
    (pΩ pN : RationalCode) (j : Fin linkedRealDimension) :
    PolynomialBlockCode.TermsBidegreeLE 1 8
      (linkedFieldComponentCode pΩ pN j) := by
  have hz :
      PolynomialBlockCode.TermsBidegreeLE 0 8
        (PolynomialBlockCode.right
          (m := controllerPairDimension)
          (linkedZBasisFieldCode j)) :=
    PolynomialBlockCode.termsBidegreeLE_right
      (linkedZBasisFieldCode_termsDegreeLE j)
  have hphi :
      PolynomialBlockCode.TermsBidegreeLE 0 8
        (PolynomialBlockCode.right
          (m := controllerPairDimension)
          (linkedIPhiBasisFieldCode j)) :=
    PolynomialBlockCode.termsBidegreeLE_right
      (linkedIPhiBasisFieldCode_termsDegreeLE j)
  have hZproduct :=
    PolynomialBlockCode.termsBidegreeLE_mul
      (kappaZCode_termsBidegreeLE pΩ pN) hz
  have hPhiProduct :=
    PolynomialBlockCode.termsBidegreeLE_mul
      (omegaCode_termsBidegreeLE pΩ) hphi
  simpa [linkedFieldComponentCode] using
    PolynomialBlockCode.termsBidegreeLE_add
      hZproduct hPhiProduct

/-- Main structural ledger: controller-variable degree at most three and
linked-target-variable degree at most eight in every field component. -/
theorem fieldCode_termsBidegreeLE
    (pΩ pN : RationalCode) :
    ∀ q, PolynomialBlockCode.TermsBidegreeLE 3 8
      (fieldCode pΩ pN q) := by
  intro q
  obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective q
  · change
      PolynomialBlockCode.TermsBidegreeLE 3 8
        (fieldCode pΩ pN (controllersEmbedding i))
    rw [fieldCode_controllersEmbedding]
    exact
      (PolynomialBlockCode.termsBidegreeLE_left
        (controllerPairFieldCode_termsDegreeLE pΩ pN i)).promote
          (by omega) (by omega)
  · change
      PolynomialBlockCode.TermsBidegreeLE 3 8
        (fieldCode pΩ pN (linkedRealEmbedding j))
    rw [fieldCode_linkedRealEmbedding]
    exact
      (linkedFieldComponentCode_termsBidegreeLE pΩ pN j).promote
        (by omega) (by omega)

/-! ## Ordinary total degree -/

theorem omegaCode_termsDegreeLE
    (pΩ : RationalCode) :
    PolynomialCode.TermsDegreeLE 1 (omegaCode pΩ) :=
  PolynomialCode.termsDegreeLE_injectVariables _
    (omegaPairCode_termsDegreeLE pΩ)

theorem kappaZCode_termsDegreeLE
    (pΩ pN : RationalCode) :
    PolynomialCode.TermsDegreeLE 1 (kappaZCode pΩ pN) :=
  PolynomialCode.termsDegreeLE_injectVariables _
    (kappaZPairCode_termsDegreeLE pΩ pN)

/-- A linked component has ordinary total degree at most `1+8=9`. -/
theorem linkedFieldComponentCode_termsDegreeLE
    (pΩ pN : RationalCode) (j : Fin linkedRealDimension) :
    PolynomialCode.TermsDegreeLE 9
      (linkedFieldComponentCode pΩ pN j) := by
  have hz :
      PolynomialCode.TermsDegreeLE 8
        (PolynomialBlockCode.right
          (m := controllerPairDimension)
          (linkedZBasisFieldCode j)) :=
    PolynomialCode.termsDegreeLE_injectVariables _
      (linkedZBasisFieldCode_termsDegreeLE j)
  have hphi :
      PolynomialCode.TermsDegreeLE 8
        (PolynomialBlockCode.right
          (m := controllerPairDimension)
          (linkedIPhiBasisFieldCode j)) :=
    PolynomialCode.termsDegreeLE_injectVariables _
      (linkedIPhiBasisFieldCode_termsDegreeLE j)
  have hZproduct :=
    PolynomialCode.termsDegreeLE_mul
      (kappaZCode_termsDegreeLE pΩ pN) hz
  have hPhiProduct :=
    PolynomialCode.termsDegreeLE_mul
      (omegaCode_termsDegreeLE pΩ) hphi
  simpa [linkedFieldComponentCode] using
    PolynomialCode.termsDegreeLE_add hZproduct hPhiProduct

/-- Uniform ordinary total-degree bound for the full coupled field. -/
theorem fieldCode_termsDegreeLE
    (pΩ pN : RationalCode) :
    ∀ q, PolynomialCode.TermsDegreeLE 9
      (fieldCode pΩ pN q) := by
  intro q
  obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective q
  · change
      PolynomialCode.TermsDegreeLE 9
        (fieldCode pΩ pN (controllersEmbedding i))
    rw [fieldCode_controllersEmbedding]
    exact
      (PolynomialCode.termsDegreeLE_injectVariables _
        (controllerPairFieldCode_termsDegreeLE pΩ pN i)).promote
          (by omega)
  · change
      PolynomialCode.TermsDegreeLE 9
        (fieldCode pΩ pN (linkedRealEmbedding j))
    rw [fieldCode_linkedRealEmbedding]
    exact linkedFieldComponentCode_termsDegreeLE pΩ pN j

end HGAS.Modular.TwoControllerLinkedJacobiPolynomialCode
