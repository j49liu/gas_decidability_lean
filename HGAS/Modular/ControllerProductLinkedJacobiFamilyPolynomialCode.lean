import HGAS.Modular.ControllerProductLinkedJacobiPolynomialCode
import Mathlib.Tactic

/-!
# A common controller product coupled to a finite family of Jacobi blocks

An arithmetic instance uses many unary theta factors.  Their modular and
Jacobi states are independent, but their frequencies are rational linear
readouts of one common finite product of controller clocks.  Duplicating
the controller product for every theta factor would lose the common Haar
clock and would not model the intended joining-robust construction.

This module therefore compiles, for arbitrary fixed `q` and `b`,

* one product of `q` controller--phase clocks; and
* a family of `b` realified linked unary--Jacobi blocks.

For block `a`, two rational weight vectors define

```
  ωₐ = ∑ i, uₐᵢ pᵢ rᵢ,            Nₐ = ∑ i, vₐᵢ pᵢ rᵢ,
  κZₐ = (ωₐ+Nₐ)/2,                 κΦₐ = iωₐ.
```

The same controller coordinates drive every block.  The total dimension
is

```
                         4q + 28b.
```

All polynomial syntax is literal and rational.  The exact-semantics
theorems apply to every ambient real point; no invariant circle or Jacobi
residual equations are assumed.
-/

namespace HGAS.Modular

open HGAS

/-- A common finite controller family and a finite family of linked
unary--Jacobi states. -/
@[ext]
structure ControllerProductLinkedJacobiFamilyState
    (q b : ℕ) where
  controllers :
    HGAS.Clocks.ControllerPhaseProductPolynomialCode.StateFamily q ℝ
  linked : Fin b → LinkedJacobiState ℂ

namespace ControllerProductLinkedJacobiFamilyPolynomialCode

open HGAS.Clocks

variable {q b : ℕ}

abbrev controllerDimension (q : ℕ) : ℕ :=
  ControllerPhaseProductPolynomialCode.dimension q

abbrev localLinkedRealDimension : ℕ :=
  LinkedJacobiPolynomialCode.dimension +
    LinkedJacobiPolynomialCode.dimension

abbrev linkedFamilyDimension (b : ℕ) : ℕ :=
  b * localLinkedRealDimension

abbrev dimension (q b : ℕ) : ℕ :=
  controllerDimension q + linkedFamilyDimension b

def controllersEmbedding :
    Fin (controllerDimension q) ↪ Fin (dimension q b) :=
  PolynomialBlockCode.leftEmbedding

def linkedFamilyEmbedding :
    Fin (linkedFamilyDimension b) ↪ Fin (dimension q b) :=
  PolynomialBlockCode.rightEmbedding

def linkedBlockEmbedding (a : Fin b) :
    Fin localLinkedRealDimension ↪
      Fin (linkedFamilyDimension b) :=
  PolynomialFiniteProductCode.blockEmbedding a

def controllersPoint
    (z : ControllerProductLinkedJacobiFamilyState q b) :
    Fin (controllerDimension q) → ℝ :=
  ControllerPhaseProductPolynomialCode.point z.controllers

def linkedFamilyPoint
    (z : ControllerProductLinkedJacobiFamilyState q b) :
    Fin (linkedFamilyDimension b) → ℝ :=
  PolynomialFiniteProductCode.flattenPoint
    (fun a ↦
      ComplexCoordinates.realifyPoint
        (LinkedJacobiPolynomialCode.point (z.linked a)))

def point
    (z : ControllerProductLinkedJacobiFamilyState q b) :
    Fin (dimension q b) → ℝ :=
  PolynomialBlockCode.point
    (controllersPoint z) (linkedFamilyPoint z)

def state
    (x : Fin (dimension q b) → ℝ) :
    ControllerProductLinkedJacobiFamilyState q b where
  controllers :=
    ControllerPhaseProductPolynomialCode.state
      (x ∘ controllersEmbedding)
  linked := fun a ↦
    LinkedJacobiPolynomialCode.state
      (ComplexCoordinates.complexifyPoint
        (PolynomialFiniteProductCode.unflattenPoint
          (x ∘ linkedFamilyEmbedding) a))

@[simp]
theorem linkedFamilyPoint_linkedBlockEmbedding
    (z : ControllerProductLinkedJacobiFamilyState q b)
    (a : Fin b) (j : Fin localLinkedRealDimension) :
    linkedFamilyPoint z (linkedBlockEmbedding a j) =
      ComplexCoordinates.realifyPoint
        (LinkedJacobiPolynomialCode.point (z.linked a)) j := by
  simp [linkedFamilyPoint, linkedBlockEmbedding]

@[simp]
theorem state_point
    (z : ControllerProductLinkedJacobiFamilyState q b) :
    state (point z) = z := by
  apply ControllerProductLinkedJacobiFamilyState.ext
  · change
      ControllerPhaseProductPolynomialCode.state
          (point z ∘ controllersEmbedding) =
        z.controllers
    have hcontrollers :
        point z ∘ controllersEmbedding = controllersPoint z := by
      funext i
      simp [point, controllersEmbedding]
    rw [hcontrollers]
    exact
      ControllerPhaseProductPolynomialCode.state_point
        z.controllers
  · funext a
    change
      LinkedJacobiPolynomialCode.state
          (ComplexCoordinates.complexifyPoint
            (PolynomialFiniteProductCode.unflattenPoint
              (point z ∘ linkedFamilyEmbedding) a)) =
        z.linked a
    have hlinked :
        PolynomialFiniteProductCode.unflattenPoint
            (point z ∘ linkedFamilyEmbedding) a =
          ComplexCoordinates.realifyPoint
            (LinkedJacobiPolynomialCode.point (z.linked a)) := by
      funext j
      simp [point, linkedFamilyEmbedding, linkedFamilyPoint]
    rw [hlinked, ComplexCoordinates.complexifyPoint_realifyPoint]
    exact LinkedJacobiPolynomialCode.state_point (z.linked a)

@[simp]
theorem point_state
    (x : Fin (dimension q b) → ℝ) :
    point (state x) = x := by
  unfold point state
  funext k
  obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective k
  · rw [show finSumFinEquiv (Sum.inl i) =
      PolynomialBlockCode.leftEmbedding
        (p := linkedFamilyDimension b) i by rfl]
    simp [controllersPoint, controllersEmbedding]
  · rw [show finSumFinEquiv (Sum.inr j) =
      PolynomialBlockCode.rightEmbedding
        (m := controllerDimension q) j by rfl]
    simp [linkedFamilyPoint, linkedFamilyEmbedding]

/-! ## Structured semantic field -/

def omega
    (weights : Fin b → Fin q → ℝ)
    (parameters : Fin q → ℝ)
    (z : ControllerProductLinkedJacobiFamilyState q b)
    (a : Fin b) : ℝ :=
  ControllerPhaseProductLinearFrequencyCode.value
    (weights a) parameters z.controllers

def number
    (weights : Fin b → Fin q → ℝ)
    (parameters : Fin q → ℝ)
    (z : ControllerProductLinkedJacobiFamilyState q b)
    (a : Fin b) : ℝ :=
  ControllerPhaseProductLinearFrequencyCode.value
    (weights a) parameters z.controllers

noncomputable def kappaZ
    (omegaWeights numberWeights : Fin b → Fin q → ℝ)
    (parameters : Fin q → ℝ)
    (z : ControllerProductLinkedJacobiFamilyState q b)
    (a : Fin b) : ℂ :=
  ((omega omegaWeights parameters z a +
      number numberWeights parameters z a) / 2 : ℝ)

noncomputable def kappaPhi
    (omegaWeights : Fin b → Fin q → ℝ)
    (parameters : Fin q → ℝ)
    (z : ControllerProductLinkedJacobiFamilyState q b)
    (a : Fin b) : ℂ :=
  Complex.I * omega omegaWeights parameters z a

noncomputable def vectorField
    (parameters : Fin q → ℝ)
    (omegaWeights numberWeights : Fin b → Fin q → ℝ)
    (z : ControllerProductLinkedJacobiFamilyState q b) :
    ControllerProductLinkedJacobiFamilyState q b where
  controllers :=
    ControllerPhaseProductPolynomialCode.vectorField
      parameters z.controllers
  linked := fun a ↦
    LinkedJacobiState.combinedVectorField
      (kappaZ omegaWeights numberWeights parameters z a)
      (kappaPhi omegaWeights parameters z a)
      (z.linked a)

/-! ## Literal polynomial compiler -/

def controllerFieldCode
    (parameters : Fin q → RationalCode) :
    PolynomialFieldCode (controllerDimension q) :=
  ControllerPhaseProductPolynomialCode.fieldCode parameters

def omegaControllerCode
    (omegaWeights : Fin b → Fin q → RationalCode)
    (parameters : Fin q → RationalCode)
    (a : Fin b) :
    PolynomialCode (controllerDimension q) :=
  ControllerPhaseProductLinearFrequencyCode.code
    (omegaWeights a) parameters

def numberControllerCode
    (numberWeights : Fin b → Fin q → RationalCode)
    (parameters : Fin q → RationalCode)
    (a : Fin b) :
    PolynomialCode (controllerDimension q) :=
  ControllerPhaseProductLinearFrequencyCode.code
    (numberWeights a) parameters

def halfCode : RationalCode :=
  RationalCode.encode (1 / 2 : ℚ)

def kappaZControllerCode
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode)
    (parameters : Fin q → RationalCode)
    (a : Fin b) :
    PolynomialCode (controllerDimension q) :=
  PolynomialCode.mul
    (PolynomialCode.constant halfCode)
    (PolynomialCode.add
      (omegaControllerCode omegaWeights parameters a)
      (numberControllerCode numberWeights parameters a))

def linkedZBasisFieldCode :
    PolynomialFieldCode localLinkedRealDimension :=
  LinkedJacobiPolynomialCode.compileFieldCode
    GaussianRationalCode.one GaussianRationalCode.zero

def linkedIPhiBasisFieldCode :
    PolynomialFieldCode localLinkedRealDimension :=
  LinkedJacobiPolynomialCode.compileFieldCode
    GaussianRationalCode.zero GaussianRationalCode.I

def omegaCode
    (omegaWeights : Fin b → Fin q → RationalCode)
    (parameters : Fin q → RationalCode)
    (a : Fin b) :
    PolynomialCode (dimension q b) :=
  PolynomialBlockCode.left
    (p := linkedFamilyDimension b)
    (omegaControllerCode omegaWeights parameters a)

def kappaZCode
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode)
    (parameters : Fin q → RationalCode)
    (a : Fin b) :
    PolynomialCode (dimension q b) :=
  PolynomialBlockCode.left
    (p := linkedFamilyDimension b)
    (kappaZControllerCode
      omegaWeights numberWeights parameters a)

def linkedBasisCode
    (a : Fin b)
    (F : PolynomialFieldCode localLinkedRealDimension)
    (j : Fin localLinkedRealDimension) :
    PolynomialCode (dimension q b) :=
  PolynomialBlockCode.right
    (m := controllerDimension q)
    (PolynomialFiniteProductCode.lift a (F j))

def linkedFieldComponentCode
    (parameters : Fin q → RationalCode)
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode)
    (a : Fin b) (j : Fin localLinkedRealDimension) :
    PolynomialCode (dimension q b) :=
  PolynomialCode.add
    (PolynomialCode.mul
      (kappaZCode
        omegaWeights numberWeights parameters a)
      (linkedBasisCode a linkedZBasisFieldCode j))
    (PolynomialCode.mul
      (omegaCode omegaWeights parameters a)
      (linkedBasisCode a linkedIPhiBasisFieldCode j))

def fieldCode
    (parameters : Fin q → RationalCode)
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode) :
    PolynomialFieldCode (dimension q b) :=
  fun k ↦
    match finSumFinEquiv.symm k with
    | Sum.inl i =>
        PolynomialBlockCode.left
          (p := linkedFamilyDimension b)
          (controllerFieldCode parameters i)
    | Sum.inr j =>
        let p := finProdFinEquiv.symm j
        linkedFieldComponentCode
          parameters omegaWeights numberWeights p.1 p.2

@[simp]
theorem fieldCode_controllersEmbedding
    (parameters : Fin q → RationalCode)
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode)
    (i : Fin (controllerDimension q)) :
    fieldCode parameters omegaWeights numberWeights
        (controllersEmbedding i) =
      PolynomialBlockCode.left
        (p := linkedFamilyDimension b)
        (controllerFieldCode parameters i) := by
  simp [fieldCode, controllersEmbedding]

@[simp]
theorem fieldCode_linkedBlockEmbedding
    (parameters : Fin q → RationalCode)
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode)
    (a : Fin b) (j : Fin localLinkedRealDimension) :
    fieldCode parameters omegaWeights numberWeights
        (linkedFamilyEmbedding (linkedBlockEmbedding a j)) =
      linkedFieldComponentCode
        parameters omegaWeights numberWeights a j := by
  simp [fieldCode, linkedFamilyEmbedding, linkedBlockEmbedding,
    PolynomialFiniteProductCode.blockEmbedding]

/-! ## Exact semantics -/

@[simp]
theorem eval_omegaControllerCode
    (omegaWeights : Fin b → Fin q → RationalCode)
    (parameters : Fin q → RationalCode)
    (z : ControllerProductLinkedJacobiFamilyState q b)
    (a : Fin b) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (controllersPoint z)
        (PolynomialCode.decode
          (omegaControllerCode omegaWeights parameters a)) =
      omega
        (fun d i ↦
          (RationalCode.decode (omegaWeights d i) : ℝ))
        (fun i ↦
          (RationalCode.decode (parameters i) : ℝ))
        z a := by
  exact
    ControllerPhaseProductLinearFrequencyCode.eval₂Hom_code
      (omegaWeights a) parameters z.controllers

@[simp]
theorem eval_numberControllerCode
    (numberWeights : Fin b → Fin q → RationalCode)
    (parameters : Fin q → RationalCode)
    (z : ControllerProductLinkedJacobiFamilyState q b)
    (a : Fin b) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (controllersPoint z)
        (PolynomialCode.decode
          (numberControllerCode numberWeights parameters a)) =
      number
        (fun d i ↦
          (RationalCode.decode (numberWeights d i) : ℝ))
        (fun i ↦
          (RationalCode.decode (parameters i) : ℝ))
        z a := by
  exact
    ControllerPhaseProductLinearFrequencyCode.eval₂Hom_code
      (numberWeights a) parameters z.controllers

@[simp]
theorem eval_kappaZControllerCode
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode)
    (parameters : Fin q → RationalCode)
    (z : ControllerProductLinkedJacobiFamilyState q b)
    (a : Fin b) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (controllersPoint z)
        (PolynomialCode.decode
          (kappaZControllerCode
            omegaWeights numberWeights parameters a)) =
      (omega
          (fun d i ↦
            (RationalCode.decode (omegaWeights d i) : ℝ))
          (fun i ↦
            (RationalCode.decode (parameters i) : ℝ))
          z a +
        number
          (fun d i ↦
            (RationalCode.decode (numberWeights d i) : ℝ))
          (fun i ↦
            (RationalCode.decode (parameters i) : ℝ))
          z a) / 2 := by
  rw [kappaZControllerCode,
    PolynomialCode.decode_mul_code, map_mul,
    PolynomialCode.decode_constant,
    PolynomialCode.decode_add_code, map_add,
    eval_omegaControllerCode, eval_numberControllerCode]
  norm_num [halfCode]
  ring

@[simp]
theorem eval_omegaCode
    (omegaWeights : Fin b → Fin q → RationalCode)
    (parameters : Fin q → RationalCode)
    (z : ControllerProductLinkedJacobiFamilyState q b)
    (a : Fin b) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) (point z)
        (PolynomialCode.decode
          (omegaCode omegaWeights parameters a)) =
      omega
        (fun d i ↦
          (RationalCode.decode (omegaWeights d i) : ℝ))
        (fun i ↦
          (RationalCode.decode (parameters i) : ℝ))
        z a := by
  rw [omegaCode, point, PolynomialBlockCode.eval₂Hom_left,
    eval_omegaControllerCode]

@[simp]
theorem eval_kappaZCode
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode)
    (parameters : Fin q → RationalCode)
    (z : ControllerProductLinkedJacobiFamilyState q b)
    (a : Fin b) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) (point z)
        (PolynomialCode.decode
          (kappaZCode
            omegaWeights numberWeights parameters a)) =
      (omega
          (fun d i ↦
            (RationalCode.decode (omegaWeights d i) : ℝ))
          (fun i ↦
            (RationalCode.decode (parameters i) : ℝ))
          z a +
        number
          (fun d i ↦
            (RationalCode.decode (numberWeights d i) : ℝ))
          (fun i ↦
            (RationalCode.decode (parameters i) : ℝ))
          z a) / 2 := by
  rw [kappaZCode, point, PolynomialBlockCode.eval₂Hom_left,
    eval_kappaZControllerCode]

/-- Evaluation of a basis equation embedded into linked block `a` only
sees the state of that block. -/
@[simp]
theorem eval_linkedBasisCode
    (F : PolynomialFieldCode localLinkedRealDimension)
    (z : ControllerProductLinkedJacobiFamilyState q b)
    (a : Fin b) (j : Fin localLinkedRealDimension) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) (point z)
        (PolynomialCode.decode (linkedBasisCode a F j)) =
      PolynomialFieldCode.realize F
        (ComplexCoordinates.realifyPoint
          (LinkedJacobiPolynomialCode.point (z.linked a))) j := by
  rw [linkedBasisCode, point,
    PolynomialBlockCode.eval₂Hom_right,
    PolynomialFiniteProductCode.eval₂Hom_lift]
  simp [linkedFamilyPoint]

@[simp]
theorem realize_localLinkedZBasisFieldCode
    (z : LinkedJacobiState ℂ) :
    PolynomialFieldCode.realize linkedZBasisFieldCode
        (ComplexCoordinates.realifyPoint
          (LinkedJacobiPolynomialCode.point z)) =
      ComplexCoordinates.realifyPoint
        (LinkedJacobiPolynomialCode.point
          (LinkedJacobiState.combinedVectorField 1 0 z)) := by
  have h :=
    LinkedJacobiPolynomialCode.complexify_realize_compileFieldCode
      GaussianRationalCode.one GaussianRationalCode.zero z
  calc
    PolynomialFieldCode.realize linkedZBasisFieldCode
          (ComplexCoordinates.realifyPoint
            (LinkedJacobiPolynomialCode.point z)) =
        ComplexCoordinates.realifyPoint
          (ComplexCoordinates.complexifyPoint
            (PolynomialFieldCode.realize linkedZBasisFieldCode
              (ComplexCoordinates.realifyPoint
                (LinkedJacobiPolynomialCode.point z)))) :=
      (ComplexCoordinates.realifyPoint_complexifyPoint _).symm
    _ = _ := by
      apply congrArg ComplexCoordinates.realifyPoint
      simp [linkedZBasisFieldCode] at h ⊢

@[simp]
theorem realize_localLinkedIPhiBasisFieldCode
    (z : LinkedJacobiState ℂ) :
    PolynomialFieldCode.realize linkedIPhiBasisFieldCode
        (ComplexCoordinates.realifyPoint
          (LinkedJacobiPolynomialCode.point z)) =
      ComplexCoordinates.realifyPoint
        (LinkedJacobiPolynomialCode.point
          (LinkedJacobiState.combinedVectorField
            0 Complex.I z)) := by
  have h :=
    LinkedJacobiPolynomialCode.complexify_realize_compileFieldCode
      GaussianRationalCode.zero GaussianRationalCode.I z
  calc
    PolynomialFieldCode.realize linkedIPhiBasisFieldCode
          (ComplexCoordinates.realifyPoint
            (LinkedJacobiPolynomialCode.point z)) =
        ComplexCoordinates.realifyPoint
          (ComplexCoordinates.complexifyPoint
            (PolynomialFieldCode.realize linkedIPhiBasisFieldCode
              (ComplexCoordinates.realifyPoint
                (LinkedJacobiPolynomialCode.point z)))) :=
      (ComplexCoordinates.realifyPoint_complexifyPoint _).symm
    _ = _ := by
      apply congrArg ComplexCoordinates.realifyPoint
      simp [linkedIPhiBasisFieldCode] at h ⊢

/-- Exact semantics of one coordinate in one dynamically coupled linked
block. -/
theorem realize_linkedFieldComponentCode
    (parameters : Fin q → RationalCode)
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode)
    (z : ControllerProductLinkedJacobiFamilyState q b)
    (a : Fin b) (j : Fin localLinkedRealDimension) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) (point z)
        (PolynomialCode.decode
          (linkedFieldComponentCode
            parameters omegaWeights numberWeights a j)) =
      ComplexCoordinates.realifyPoint
        (LinkedJacobiPolynomialCode.point
          (LinkedJacobiState.combinedVectorField
            (kappaZ
              (fun d i ↦
                (RationalCode.decode (omegaWeights d i) : ℝ))
              (fun d i ↦
                (RationalCode.decode (numberWeights d i) : ℝ))
              (fun i ↦
                (RationalCode.decode (parameters i) : ℝ))
              z a)
            (kappaPhi
              (fun d i ↦
                (RationalCode.decode (omegaWeights d i) : ℝ))
              (fun i ↦
                (RationalCode.decode (parameters i) : ℝ))
              z a)
            (z.linked a))) j := by
  rw [linkedFieldComponentCode,
    PolynomialCode.decode_add_code,
    PolynomialCode.decode_mul_code,
    PolynomialCode.decode_mul_code,
    map_add, map_mul, map_mul,
    eval_kappaZCode,
    eval_linkedBasisCode,
    eval_omegaCode,
    eval_linkedBasisCode,
    realize_localLinkedZBasisFieldCode,
    realize_localLinkedIPhiBasisFieldCode]
  let A :=
    (omega
        (fun d i ↦
          (RationalCode.decode (omegaWeights d i) : ℝ))
        (fun i ↦
          (RationalCode.decode (parameters i) : ℝ))
        z a +
      number
        (fun d i ↦
          (RationalCode.decode (numberWeights d i) : ℝ))
        (fun i ↦
          (RationalCode.decode (parameters i) : ℝ))
        z a) / 2
  let B :=
    omega
      (fun d i ↦
        (RationalCode.decode (omegaWeights d i) : ℝ))
      (fun i ↦
        (RationalCode.decode (parameters i) : ℝ))
      z a
  let u :=
    LinkedJacobiPolynomialCode.point
      (LinkedJacobiState.combinedVectorField
        1 0 (z.linked a))
  let v :=
    LinkedJacobiPolynomialCode.point
      (LinkedJacobiState.combinedVectorField
        0 Complex.I (z.linked a))
  calc
    A * ComplexCoordinates.realifyPoint u j +
          B * ComplexCoordinates.realifyPoint v j =
        ComplexCoordinates.realifyPoint
          (fun i ↦ (A : ℂ) * u i + (B : ℂ) * v i) j :=
      (congrFun
        (ControllerProductLinkedJacobiPolynomialCode.realifyPoint_real_linear
          A B u v) j).symm
    _ = ComplexCoordinates.realifyPoint
          (LinkedJacobiPolynomialCode.point
            (LinkedJacobiState.combinedVectorField
              (A : ℂ) (Complex.I * B) (z.linked a))) j := by
      apply congrFun
      apply congrArg ComplexCoordinates.realifyPoint
      exact
        (ControllerProductLinkedJacobiPolynomialCode.point_combinedVectorField_dynamic_basis
            A B (z.linked a)).symm
    _ = _ := by
      simp [A, B, kappaZ, kappaPhi]

/-- Exact structured-state semantics of the whole common-controller
family field. -/
@[simp]
theorem realize_fieldCode
    (parameters : Fin q → RationalCode)
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode)
    (z : ControllerProductLinkedJacobiFamilyState q b) :
    PolynomialFieldCode.realize
        (fieldCode parameters omegaWeights numberWeights)
        (point z) =
      point
        (vectorField
          (fun i ↦
            (RationalCode.decode (parameters i) : ℝ))
          (fun d i ↦
            (RationalCode.decode (omegaWeights d i) : ℝ))
          (fun d i ↦
            (RationalCode.decode (numberWeights d i) : ℝ))
          z) := by
  funext k
  obtain ⟨i | r, rfl⟩ := finSumFinEquiv.surjective k
  · rw [show finSumFinEquiv (Sum.inl i) =
      controllersEmbedding i by rfl]
    simp only [PolynomialFieldCode.realize_apply,
      fieldCode_controllersEmbedding]
    change
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
          (point z)
          (PolynomialCode.decode
            (PolynomialBlockCode.left
              (controllerFieldCode parameters i))) =
        point
          (vectorField
            (fun k ↦
              (RationalCode.decode (parameters k) : ℝ))
            (fun d k ↦
              (RationalCode.decode (omegaWeights d k) : ℝ))
            (fun d k ↦
              (RationalCode.decode (numberWeights d k) : ℝ))
            z)
          (controllersEmbedding i)
    rw [point, PolynomialBlockCode.eval₂Hom_left]
    simpa [point, controllersEmbedding, controllerFieldCode,
      controllersPoint, vectorField] using
        congrFun
          (ControllerPhaseProductPolynomialCode.realize_fieldCode
            parameters z.controllers) i
  · obtain ⟨⟨a, j⟩, rfl⟩ :=
      finProdFinEquiv.surjective r
    rw [show
      finSumFinEquiv
          (Sum.inr (finProdFinEquiv (a, j)) :
            Fin (controllerDimension q) ⊕
              Fin (linkedFamilyDimension b)) =
        linkedFamilyEmbedding (linkedBlockEmbedding a j) by rfl]
    simp only [PolynomialFieldCode.realize_apply,
      fieldCode_linkedBlockEmbedding]
    change
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
          (point z)
          (PolynomialCode.decode
            (linkedFieldComponentCode
              parameters omegaWeights numberWeights a j)) =
        point
          (vectorField
            (fun k ↦
              (RationalCode.decode (parameters k) : ℝ))
            (fun d k ↦
              (RationalCode.decode (omegaWeights d k) : ℝ))
            (fun d k ↦
              (RationalCode.decode (numberWeights d k) : ℝ))
            z)
          (linkedFamilyEmbedding (linkedBlockEmbedding a j))
    simpa [point, linkedFamilyEmbedding, linkedBlockEmbedding,
      linkedFamilyPoint, vectorField] using
        (realize_linkedFieldComponentCode
          parameters omegaWeights numberWeights z a j)

/-- Ambient semantics with no circle or residual hypothesis. -/
@[simp]
theorem realize_fieldCode_arbitrary
    (parameters : Fin q → RationalCode)
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode)
    (x : Fin (dimension q b) → ℝ) :
    PolynomialFieldCode.realize
        (fieldCode parameters omegaWeights numberWeights) x =
      point
        (vectorField
          (fun i ↦
            (RationalCode.decode (parameters i) : ℝ))
          (fun d i ↦
            (RationalCode.decode (omegaWeights d i) : ℝ))
          (fun d i ↦
            (RationalCode.decode (numberWeights d i) : ℝ))
          (state x)) := by
  simpa using
    realize_fieldCode
      parameters omegaWeights numberWeights (state x)

end ControllerProductLinkedJacobiFamilyPolynomialCode

end HGAS.Modular
