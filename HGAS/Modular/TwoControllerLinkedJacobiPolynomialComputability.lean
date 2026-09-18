import HGAS.Clocks.ControllerPolynomialComputability
import HGAS.Modular.LinkedJacobiPolynomialComputability
import HGAS.Modular.TwoControllerLinkedJacobiPolynomialCode
import Mathlib.Computability.Partrec
import Mathlib.Tactic

/-!
# Effectivity of the two-controller linked Jacobi coupling

The two runtime inputs are arbitrary rational codes `pΩ` and `pN`.  Every
operation used to build the thirty-six-coordinate sparse field—variable
embedding, finite block assembly, addition, and multiplication—is
primitive recursive.  This module proves the resulting two-parameter
compiler primitive recursive all the way down to the literal raw
polynomial lists.
-/

namespace HGAS.Modular.TwoControllerLinkedJacobiPolynomialCode

open HGAS

theorem controllerPairFieldCode_primrec :
    Primrec₂ controllerPairFieldCode := by
  change Primrec
    (fun q : RationalCode × RationalCode ↦
      controllerPairFieldCode q.1 q.2)
  exact
    PolynomialBlockCode.field_primrec.comp
      (HGAS.Clocks.ControllerPolynomialCode.fieldCode_primrec.comp
        Primrec.fst)
      (HGAS.Clocks.ControllerPolynomialCode.fieldCode_primrec.comp
        Primrec.snd)

theorem omegaPairCode_primrec :
    Primrec omegaPairCode := by
  exact
    PolynomialCode.mul_primrec.comp
      PolynomialCode.constant_primrec
      (Primrec.const
        (PolynomialBlockCode.left
          (p := ControllerCode.dimension)
          HGAS.Clocks.ControllerPolynomialCode.rCode))

theorem numberPairCode_primrec :
    Primrec numberPairCode := by
  exact
    PolynomialCode.mul_primrec.comp
      PolynomialCode.constant_primrec
      (Primrec.const
        (PolynomialBlockCode.right
          (m := ControllerCode.dimension)
          HGAS.Clocks.ControllerPolynomialCode.rCode))

theorem kappaZPairCode_primrec :
    Primrec₂ kappaZPairCode := by
  change Primrec
    (fun q : RationalCode × RationalCode ↦
      kappaZPairCode q.1 q.2)
  exact
    PolynomialCode.mul_primrec.comp
      (Primrec.const
        (PolynomialCode.constant halfCode :
          PolynomialCode controllerPairDimension))
      (PolynomialCode.add_primrec.comp
        (omegaPairCode_primrec.comp Primrec.fst)
        (numberPairCode_primrec.comp Primrec.snd))

theorem omegaCode_primrec :
    Primrec omegaCode :=
  PolynomialBlockCode.left_primrec.comp omegaPairCode_primrec

theorem kappaZCode_primrec :
    Primrec₂ kappaZCode := by
  change Primrec
    (fun q : RationalCode × RationalCode ↦
      kappaZCode q.1 q.2)
  exact
    PolynomialBlockCode.left_primrec.comp
      kappaZPairCode_primrec

theorem linkedFieldComponentCode_primrec
    (j : Fin linkedRealDimension) :
    Primrec₂ (fun pΩ pN ↦
      linkedFieldComponentCode pΩ pN j) := by
  change Primrec
    (fun q : RationalCode × RationalCode ↦
      linkedFieldComponentCode q.1 q.2 j)
  have hZbasis :
      Primrec
        (fun (_ : RationalCode × RationalCode) ↦
          PolynomialBlockCode.right
            (m := controllerPairDimension)
            (linkedZBasisFieldCode j)) :=
    Primrec.const _
  have hPhibasis :
      Primrec
        (fun (_ : RationalCode × RationalCode) ↦
          PolynomialBlockCode.right
            (m := controllerPairDimension)
            (linkedIPhiBasisFieldCode j)) :=
    Primrec.const _
  exact
    PolynomialCode.add_primrec.comp
      (PolynomialCode.mul_primrec.comp
        kappaZCode_primrec hZbasis)
      (PolynomialCode.mul_primrec.comp
        (omegaCode_primrec.comp Primrec.fst) hPhibasis)

/-- The complete two-parameter field compiler is primitive recursive. -/
theorem fieldCode_primrec :
    Primrec₂ fieldCode := by
  change Primrec
    (fun q : RationalCode × RationalCode ↦
      fieldCode q.1 q.2)
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro q
  obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective q
  · exact
      (PolynomialBlockCode.left_primrec.comp
        (Primrec.fin_app.comp controllerPairFieldCode_primrec
          (Primrec.const i))).of_eq fun p ↦
            (fieldCode_controllersEmbedding p.1 p.2 i).symm
  · have hcomponent :
        Primrec
          (fun p : RationalCode × RationalCode ↦
            linkedFieldComponentCode p.1 p.2 j) :=
      linkedFieldComponentCode_primrec j
    exact
      hcomponent.of_eq fun p ↦
        (fieldCode_linkedRealEmbedding p.1 p.2 j).symm

theorem fieldCode_computable :
    Computable₂ fieldCode :=
  fieldCode_primrec.to_comp

end HGAS.Modular.TwoControllerLinkedJacobiPolynomialCode
