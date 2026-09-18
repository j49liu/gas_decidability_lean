import HGAS.Clocks.ControllerPhaseProductLinearFrequencyCode
import HGAS.Modular.LinkedJacobiPolynomialCode
import Mathlib.Tactic

/-!
# A finite controller product coupled to one linked Jacobi block

The first coupled Jacobi compiler used two dedicated controller clocks:
one supplied the modular angular frequency `ω`, and one supplied the
auxiliary frequency `N`.  A complete arithmetic source needs more
flexibility.  It has one finite product of clocks, while each linked block
reads two rational linear combinations of their signed radical
frequencies.

For `q` controller--phase clocks, rational parameter codes `pᵢ`, and two
rational weight vectors `uᵢ` and `vᵢ`, this module compiles

```
  ω = ∑ i, uᵢ pᵢ rᵢ,              N = ∑ i, vᵢ pᵢ rᵢ,
  κZ = (ω + N) / 2,                κΦ = i ω.
```

The controller product occupies `4q` real coordinates and the realified
linked unary--Jacobi state occupies twenty-eight.  The resulting literal
rational polynomial field therefore lives in dimension `4q + 28`.

The implementation retains the basis-field idea of the two-controller
compiler.  Since the linked Jacobi vector field is linear in `(κZ,κΦ)`,
its dynamically coupled component is

```
               κZ F_Z + ω F_iΦ.
```

This file proves exact semantics at every ambient real point.  In
particular, no circle equation, modular residual, or nonvanishing
hypothesis is used by the compiler.  Degree and effectivity ledgers are
kept in subsequent modules so that the semantic construction can be
reused independently.
-/

namespace HGAS.Modular

open HGAS

/-- Structured state consisting of a finite clock product and one linked
unary--Jacobi state. -/
@[ext]
structure ControllerProductLinkedJacobiState (q : ℕ) where
  controllers :
    HGAS.Clocks.ControllerPhaseProductPolynomialCode.StateFamily q ℝ
  linked : LinkedJacobiState ℂ

namespace ControllerProductLinkedJacobiPolynomialCode

open HGAS.Clocks

variable {q : ℕ}

/-- Number of real coordinates in the controller product. -/
abbrev controllerDimension (q : ℕ) : ℕ :=
  ControllerPhaseProductPolynomialCode.dimension q

/-- Real dimension of the realified linked unary--Jacobi block. -/
abbrev linkedRealDimension : ℕ :=
  LinkedJacobiPolynomialCode.dimension +
    LinkedJacobiPolynomialCode.dimension

/-- Total dimension `4q + 28`. -/
abbrev dimension (q : ℕ) : ℕ :=
  controllerDimension q + linkedRealDimension

def controllersEmbedding :
    Fin (controllerDimension q) ↪ Fin (dimension q) :=
  PolynomialBlockCode.leftEmbedding

def linkedRealEmbedding :
    Fin linkedRealDimension ↪ Fin (dimension q) :=
  PolynomialBlockCode.rightEmbedding

/-- Flatten the finite clock family. -/
def controllersPoint
    (z : ControllerProductLinkedJacobiState q) :
    Fin (controllerDimension q) → ℝ :=
  ControllerPhaseProductPolynomialCode.point z.controllers

/-- Reassemble the finite clock family from arbitrary ambient controller
coordinates. -/
def controllersState
    (x : Fin (controllerDimension q) → ℝ) :
    ControllerPhaseProductPolynomialCode.StateFamily q ℝ :=
  ControllerPhaseProductPolynomialCode.state x

/-- Flatten the complete structured state into real coordinates. -/
def point
    (z : ControllerProductLinkedJacobiState q) :
    Fin (dimension q) → ℝ :=
  PolynomialBlockCode.point
    (controllersPoint z)
    (ComplexCoordinates.realifyPoint
      (LinkedJacobiPolynomialCode.point z.linked))

/-- Reassemble the complete structured state from an arbitrary ambient
real point. -/
def state
    (x : Fin (dimension q) → ℝ) :
    ControllerProductLinkedJacobiState q where
  controllers := controllersState (x ∘ controllersEmbedding)
  linked :=
    LinkedJacobiPolynomialCode.state
      (ComplexCoordinates.complexifyPoint
        (x ∘ linkedRealEmbedding))

@[simp]
theorem controllersState_controllersPoint
    (z : ControllerProductLinkedJacobiState q) :
    controllersState (controllersPoint z) = z.controllers := by
  simp [controllersState, controllersPoint]

@[simp]
theorem controllersPoint_controllersState
    (x : Fin (controllerDimension q) → ℝ) :
    ControllerPhaseProductPolynomialCode.point
        (controllersState x) = x := by
  simp [controllersState]

@[simp]
theorem state_point
    (z : ControllerProductLinkedJacobiState q) :
    state (point z) = z := by
  ext <;>
    simp [state, point, controllersEmbedding, linkedRealEmbedding]

@[simp]
theorem point_state
    (x : Fin (dimension q) → ℝ) :
    point (state x) = x := by
  unfold point state
  funext k
  obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective k
  · rw [show finSumFinEquiv (Sum.inl i) =
      PolynomialBlockCode.leftEmbedding
        (p := linkedRealDimension) i by rfl]
    simp [controllersPoint, controllersState, controllersEmbedding]
  · rw [show finSumFinEquiv (Sum.inr j) =
      PolynomialBlockCode.rightEmbedding
        (m := controllerDimension q) j by rfl]
    simp [linkedRealEmbedding]

/-! ## Dynamic coefficients and semantic vector field -/

/-- The modular angular frequency read from the common controller
product. -/
def omega
    (weights parameters : Fin q → ℝ)
    (z : ControllerProductLinkedJacobiState q) : ℝ :=
  ControllerPhaseProductLinearFrequencyCode.value
    weights parameters z.controllers

/-- The auxiliary linked-Jacobi frequency read from the same controller
product. -/
def number
    (weights parameters : Fin q → ℝ)
    (z : ControllerProductLinkedJacobiState q) : ℝ :=
  ControllerPhaseProductLinearFrequencyCode.value
    weights parameters z.controllers

/-- The real elliptic coefficient `(ω+N)/2`, regarded as complex. -/
noncomputable def kappaZ
    (omegaWeights numberWeights parameters : Fin q → ℝ)
    (z : ControllerProductLinkedJacobiState q) : ℂ :=
  ((omega omegaWeights parameters z +
      number numberWeights parameters z) / 2 : ℝ)

/-- The purely imaginary modular coefficient `iω`. -/
noncomputable def kappaPhi
    (omegaWeights parameters : Fin q → ℝ)
    (z : ControllerProductLinkedJacobiState q) : ℂ :=
  Complex.I * omega omegaWeights parameters z

/-- The desired dynamically coupled structured vector field. -/
noncomputable def vectorField
    (parameters omegaWeights numberWeights : Fin q → ℝ)
    (z : ControllerProductLinkedJacobiState q) :
    ControllerProductLinkedJacobiState q where
  controllers :=
    ControllerPhaseProductPolynomialCode.vectorField
      parameters z.controllers
  linked :=
    LinkedJacobiState.combinedVectorField
      (kappaZ omegaWeights numberWeights parameters z)
      (kappaPhi omegaWeights parameters z)
      z.linked

/-! ## Literal sparse-polynomial construction -/

/-- The block-diagonal field on all controller--phase clocks. -/
def controllerFieldCode
    (parameters : Fin q → RationalCode) :
    PolynomialFieldCode (controllerDimension q) :=
  ControllerPhaseProductPolynomialCode.fieldCode parameters

/-- Polynomial code of `ω` in the controller variables. -/
def omegaControllerCode
    (omegaWeights parameters : Fin q → RationalCode) :
    PolynomialCode (controllerDimension q) :=
  ControllerPhaseProductLinearFrequencyCode.code
    omegaWeights parameters

/-- Polynomial code of `N` in the controller variables. -/
def numberControllerCode
    (numberWeights parameters : Fin q → RationalCode) :
    PolynomialCode (controllerDimension q) :=
  ControllerPhaseProductLinearFrequencyCode.code
    numberWeights parameters

/-- Rational code for one half. -/
def halfCode : RationalCode :=
  RationalCode.encode (1 / 2 : ℚ)

/-- Polynomial code of `(ω+N)/2` in the controller variables. -/
def kappaZControllerCode
    (omegaWeights numberWeights parameters :
      Fin q → RationalCode) :
    PolynomialCode (controllerDimension q) :=
  PolynomialCode.mul
    (PolynomialCode.constant halfCode)
    (PolynomialCode.add
      (omegaControllerCode omegaWeights parameters)
      (numberControllerCode numberWeights parameters))

/-- Dynamic coefficient `ω`, embedded in the complete ambient space. -/
def omegaCode
    (omegaWeights parameters : Fin q → RationalCode) :
    PolynomialCode (dimension q) :=
  PolynomialBlockCode.left
    (p := linkedRealDimension)
    (omegaControllerCode omegaWeights parameters)

/-- Dynamic coefficient `κZ`, embedded in the complete ambient space. -/
def kappaZCode
    (omegaWeights numberWeights parameters :
      Fin q → RationalCode) :
    PolynomialCode (dimension q) :=
  PolynomialBlockCode.left
    (p := linkedRealDimension)
    (kappaZControllerCode omegaWeights numberWeights parameters)

/-- Constant linked basis field for coefficient `(κZ,κΦ)=(1,0)`. -/
def linkedZBasisFieldCode :
    PolynomialFieldCode linkedRealDimension :=
  LinkedJacobiPolynomialCode.compileFieldCode
    GaussianRationalCode.one GaussianRationalCode.zero

/-- Constant linked basis field for coefficient `(κZ,κΦ)=(0,i)`. -/
def linkedIPhiBasisFieldCode :
    PolynomialFieldCode linkedRealDimension :=
  LinkedJacobiPolynomialCode.compileFieldCode
    GaussianRationalCode.zero GaussianRationalCode.I

/-- One linked coordinate of `κZ F_Z + ω F_iΦ`. -/
def linkedFieldComponentCode
    (parameters omegaWeights numberWeights :
      Fin q → RationalCode)
    (j : Fin linkedRealDimension) :
    PolynomialCode (dimension q) :=
  PolynomialCode.add
    (PolynomialCode.mul
      (kappaZCode omegaWeights numberWeights parameters)
      (PolynomialBlockCode.right
        (m := controllerDimension q)
        (linkedZBasisFieldCode j)))
    (PolynomialCode.mul
      (omegaCode omegaWeights parameters)
      (PolynomialBlockCode.right
        (m := controllerDimension q)
        (linkedIPhiBasisFieldCode j)))

/-- Complete `(4q+28)`-coordinate rational polynomial field. -/
def fieldCode
    (parameters omegaWeights numberWeights :
      Fin q → RationalCode) :
    PolynomialFieldCode (dimension q) :=
  fun k ↦
    match finSumFinEquiv.symm k with
    | Sum.inl i =>
        PolynomialBlockCode.left
          (p := linkedRealDimension)
          (controllerFieldCode parameters i)
    | Sum.inr j =>
        linkedFieldComponentCode
          parameters omegaWeights numberWeights j

@[simp]
theorem fieldCode_controllersEmbedding
    (parameters omegaWeights numberWeights :
      Fin q → RationalCode)
    (i : Fin (controllerDimension q)) :
    fieldCode parameters omegaWeights numberWeights
        (controllersEmbedding i) =
      PolynomialBlockCode.left
        (p := linkedRealDimension)
        (controllerFieldCode parameters i) := by
  simp [fieldCode, controllersEmbedding]

@[simp]
theorem fieldCode_linkedRealEmbedding
    (parameters omegaWeights numberWeights :
      Fin q → RationalCode)
    (j : Fin linkedRealDimension) :
    fieldCode parameters omegaWeights numberWeights
        (linkedRealEmbedding j) =
      linkedFieldComponentCode
        parameters omegaWeights numberWeights j := by
  simp [fieldCode, linkedRealEmbedding]

/-! ## Exact semantics -/

@[simp]
theorem eval_omegaControllerCode
    (omegaWeights parameters : Fin q → RationalCode)
    (z : ControllerProductLinkedJacobiState q) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (controllersPoint z)
        (PolynomialCode.decode
          (omegaControllerCode omegaWeights parameters)) =
      omega
        (fun i ↦ (RationalCode.decode (omegaWeights i) : ℝ))
        (fun i ↦ (RationalCode.decode (parameters i) : ℝ))
        z := by
  exact
    ControllerPhaseProductLinearFrequencyCode.eval₂Hom_code
      omegaWeights parameters z.controllers

@[simp]
theorem eval_numberControllerCode
    (numberWeights parameters : Fin q → RationalCode)
    (z : ControllerProductLinkedJacobiState q) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (controllersPoint z)
        (PolynomialCode.decode
          (numberControllerCode numberWeights parameters)) =
      number
        (fun i ↦ (RationalCode.decode (numberWeights i) : ℝ))
        (fun i ↦ (RationalCode.decode (parameters i) : ℝ))
        z := by
  exact
    ControllerPhaseProductLinearFrequencyCode.eval₂Hom_code
      numberWeights parameters z.controllers

@[simp]
theorem eval_kappaZControllerCode
    (omegaWeights numberWeights parameters :
      Fin q → RationalCode)
    (z : ControllerProductLinkedJacobiState q) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (controllersPoint z)
        (PolynomialCode.decode
          (kappaZControllerCode
            omegaWeights numberWeights parameters)) =
      (omega
          (fun i ↦
            (RationalCode.decode (omegaWeights i) : ℝ))
          (fun i ↦
            (RationalCode.decode (parameters i) : ℝ)) z +
        number
          (fun i ↦
            (RationalCode.decode (numberWeights i) : ℝ))
          (fun i ↦
            (RationalCode.decode (parameters i) : ℝ)) z) / 2 := by
  rw [kappaZControllerCode,
    PolynomialCode.decode_mul_code, map_mul,
    PolynomialCode.decode_constant,
    PolynomialCode.decode_add_code, map_add,
    eval_omegaControllerCode, eval_numberControllerCode]
  norm_num [halfCode]
  ring

/-- The linked field is real-linear in the two constant basis fields. -/
theorem point_combinedVectorField_dynamic_basis
    (a b : ℝ) (z : LinkedJacobiState ℂ) :
    LinkedJacobiPolynomialCode.point
        (LinkedJacobiState.combinedVectorField
          (a : ℂ) (Complex.I * b) z) =
      fun i ↦
        (a : ℂ) *
            LinkedJacobiPolynomialCode.point
              (LinkedJacobiState.combinedVectorField 1 0 z) i +
          (b : ℂ) *
            LinkedJacobiPolynomialCode.point
              (LinkedJacobiState.combinedVectorField
                0 Complex.I z) i := by
    funext k
    obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective k
    · rw [show finSumFinEquiv (Sum.inl i) =
        ComplexPolynomialBlockCode.leftEmbedding
          (p := LinkedJacobiPolynomialCode.jacobiDimension) i by rfl]
      fin_cases i <;>
        simp [LinkedJacobiPolynomialCode.point,
          LinkedJacobiState.combinedVectorField,
          UnaryPolynomialCode.modularPoint,
          UnaryModularState.vectorField] <;>
        ring
    · rw [show finSumFinEquiv (Sum.inr j) =
        ComplexPolynomialBlockCode.rightEmbedding
          (m := LinkedJacobiPolynomialCode.unaryDimension) j by rfl]
      fin_cases j <;>
        simp [LinkedJacobiPolynomialCode.point,
          LinkedJacobiState.combinedVectorField,
          JacobiPolynomialCode.point,
          JacobiState.combinedVectorField] <;>
        ring

/-- Realification commutes with real linear combinations. -/
theorem realifyPoint_real_linear
    {n : ℕ} (a b : ℝ) (u v : Fin n → ℂ) :
    ComplexCoordinates.realifyPoint
        (fun i ↦ (a : ℂ) * u i + (b : ℂ) * v i) =
      fun k ↦
        a * ComplexCoordinates.realifyPoint u k +
          b * ComplexCoordinates.realifyPoint v k := by
    funext k
    cases hk : finSumFinEquiv.symm k with
    | inl i =>
        have hki : k = ComplexCoordinates.realIndex i := by
          apply finSumFinEquiv.symm.injective
          simpa using hk
        subst k
        simp [ComplexCoordinates.realifyPoint]
    | inr i =>
        have hki : k = ComplexCoordinates.imagIndex i := by
          apply finSumFinEquiv.symm.injective
          simpa using hk
        subst k
        simp [ComplexCoordinates.realifyPoint]

@[simp]
theorem realize_linkedZBasisFieldCode
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
theorem realize_linkedIPhiBasisFieldCode
    (z : LinkedJacobiState ℂ) :
    PolynomialFieldCode.realize linkedIPhiBasisFieldCode
        (ComplexCoordinates.realifyPoint
          (LinkedJacobiPolynomialCode.point z)) =
      ComplexCoordinates.realifyPoint
        (LinkedJacobiPolynomialCode.point
          (LinkedJacobiState.combinedVectorField 0 Complex.I z)) := by
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

/-- Exact semantics of one dynamically coupled linked coordinate. -/
theorem realize_linkedFieldComponentCode
    (parameters omegaWeights numberWeights :
      Fin q → RationalCode)
    (z : ControllerProductLinkedJacobiState q)
    (j : Fin linkedRealDimension) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) (point z)
        (PolynomialCode.decode
          (linkedFieldComponentCode
            parameters omegaWeights numberWeights j)) =
      ComplexCoordinates.realifyPoint
        (LinkedJacobiPolynomialCode.point
          (LinkedJacobiState.combinedVectorField
            (kappaZ
              (fun i ↦
                (RationalCode.decode (omegaWeights i) : ℝ))
              (fun i ↦
                (RationalCode.decode (numberWeights i) : ℝ))
              (fun i ↦
                (RationalCode.decode (parameters i) : ℝ))
              z)
            (kappaPhi
              (fun i ↦
                (RationalCode.decode (omegaWeights i) : ℝ))
              (fun i ↦
                (RationalCode.decode (parameters i) : ℝ))
              z)
            z.linked)) j := by
  rw [linkedFieldComponentCode,
    PolynomialCode.decode_add_code,
    PolynomialCode.decode_mul_code,
    PolynomialCode.decode_mul_code,
    map_add, map_mul, map_mul]
  change
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (PolynomialBlockCode.point
          (controllersPoint z)
          (ComplexCoordinates.realifyPoint
            (LinkedJacobiPolynomialCode.point z.linked)))
        (PolynomialCode.decode
          (PolynomialBlockCode.left
            (kappaZControllerCode
              omegaWeights numberWeights parameters))) *
        MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
          (PolynomialBlockCode.point
            (controllersPoint z)
            (ComplexCoordinates.realifyPoint
              (LinkedJacobiPolynomialCode.point z.linked)))
          (PolynomialCode.decode
            (PolynomialBlockCode.right
              (linkedZBasisFieldCode j))) +
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (PolynomialBlockCode.point
          (controllersPoint z)
          (ComplexCoordinates.realifyPoint
            (LinkedJacobiPolynomialCode.point z.linked)))
        (PolynomialCode.decode
          (PolynomialBlockCode.left
            (omegaControllerCode omegaWeights parameters))) *
        MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
          (PolynomialBlockCode.point
            (controllersPoint z)
            (ComplexCoordinates.realifyPoint
              (LinkedJacobiPolynomialCode.point z.linked)))
          (PolynomialCode.decode
            (PolynomialBlockCode.right
              (linkedIPhiBasisFieldCode j))) =
      _
  rw [PolynomialBlockCode.eval₂Hom_left,
    PolynomialBlockCode.eval₂Hom_right,
    PolynomialBlockCode.eval₂Hom_left,
    PolynomialBlockCode.eval₂Hom_right,
    eval_kappaZControllerCode, eval_omegaControllerCode]
  rw [show
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
          (ComplexCoordinates.realifyPoint
            (LinkedJacobiPolynomialCode.point z.linked))
          (PolynomialCode.decode (linkedZBasisFieldCode j)) =
        PolynomialFieldCode.realize linkedZBasisFieldCode
          (ComplexCoordinates.realifyPoint
            (LinkedJacobiPolynomialCode.point z.linked)) j by rfl,
    show
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
          (ComplexCoordinates.realifyPoint
            (LinkedJacobiPolynomialCode.point z.linked))
          (PolynomialCode.decode
            (linkedIPhiBasisFieldCode j)) =
        PolynomialFieldCode.realize linkedIPhiBasisFieldCode
          (ComplexCoordinates.realifyPoint
            (LinkedJacobiPolynomialCode.point z.linked)) j by rfl,
    realize_linkedZBasisFieldCode,
    realize_linkedIPhiBasisFieldCode]
  let a :=
    (omega
        (fun i ↦
          (RationalCode.decode (omegaWeights i) : ℝ))
        (fun i ↦
          (RationalCode.decode (parameters i) : ℝ)) z +
      number
        (fun i ↦
          (RationalCode.decode (numberWeights i) : ℝ))
        (fun i ↦
          (RationalCode.decode (parameters i) : ℝ)) z) / 2
  let b :=
    omega
      (fun i ↦
        (RationalCode.decode (omegaWeights i) : ℝ))
      (fun i ↦
        (RationalCode.decode (parameters i) : ℝ)) z
  let u :=
    LinkedJacobiPolynomialCode.point
      (LinkedJacobiState.combinedVectorField 1 0 z.linked)
  let v :=
    LinkedJacobiPolynomialCode.point
      (LinkedJacobiState.combinedVectorField
        0 Complex.I z.linked)
  calc
    a * ComplexCoordinates.realifyPoint u j +
          b * ComplexCoordinates.realifyPoint v j =
        ComplexCoordinates.realifyPoint
          (fun i ↦ (a : ℂ) * u i + (b : ℂ) * v i) j :=
      (congrFun (realifyPoint_real_linear a b u v) j).symm
    _ = ComplexCoordinates.realifyPoint
          (LinkedJacobiPolynomialCode.point
            (LinkedJacobiState.combinedVectorField
              (a : ℂ) (Complex.I * b) z.linked)) j := by
      apply congrFun
      apply congrArg ComplexCoordinates.realifyPoint
      exact
        (point_combinedVectorField_dynamic_basis
          a b z.linked).symm
    _ = _ := by
      simp [a, b, kappaZ, kappaPhi]

/-- Exact structured-state semantics of every component. -/
@[simp]
theorem realize_fieldCode
    (parameters omegaWeights numberWeights :
      Fin q → RationalCode)
    (z : ControllerProductLinkedJacobiState q) :
    PolynomialFieldCode.realize
        (fieldCode parameters omegaWeights numberWeights)
        (point z) =
      point
        (vectorField
          (fun i ↦
            (RationalCode.decode (parameters i) : ℝ))
          (fun i ↦
            (RationalCode.decode (omegaWeights i) : ℝ))
          (fun i ↦
            (RationalCode.decode (numberWeights i) : ℝ))
          z) := by
  funext k
  obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective k
  · rw [show finSumFinEquiv (Sum.inl i) =
      controllersEmbedding i by rfl]
    simp only [PolynomialFieldCode.realize_apply,
      fieldCode_controllersEmbedding]
    change
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
          (PolynomialBlockCode.point
            (controllersPoint z)
            (ComplexCoordinates.realifyPoint
              (LinkedJacobiPolynomialCode.point z.linked)))
          (PolynomialCode.decode
            (PolynomialBlockCode.left
              (controllerFieldCode parameters i))) =
        PolynomialBlockCode.point
          (controllersPoint
            (vectorField
              (fun k ↦
                (RationalCode.decode (parameters k) : ℝ))
              (fun k ↦
                (RationalCode.decode (omegaWeights k) : ℝ))
              (fun k ↦
                (RationalCode.decode (numberWeights k) : ℝ))
              z))
          (ComplexCoordinates.realifyPoint
            (LinkedJacobiPolynomialCode.point
              (vectorField
                (fun k ↦
                  (RationalCode.decode (parameters k) : ℝ))
                (fun k ↦
                  (RationalCode.decode (omegaWeights k) : ℝ))
                (fun k ↦
                  (RationalCode.decode (numberWeights k) : ℝ))
                z).linked))
          (PolynomialBlockCode.leftEmbedding i)
    rw [PolynomialBlockCode.eval₂Hom_left,
      PolynomialBlockCode.point_leftEmbedding]
    rw [show
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
          (controllersPoint z)
          (PolynomialCode.decode
            (controllerFieldCode parameters i)) =
        PolynomialFieldCode.realize
          (controllerFieldCode parameters)
          (controllersPoint z) i by rfl]
    exact congrFun
      (ControllerPhaseProductPolynomialCode.realize_fieldCode
        parameters z.controllers) i
  · rw [show finSumFinEquiv (Sum.inr j) =
      linkedRealEmbedding j by rfl]
    simp only [PolynomialFieldCode.realize_apply,
      fieldCode_linkedRealEmbedding]
    simpa [point, linkedRealEmbedding, vectorField] using
      (realize_linkedFieldComponentCode
        parameters omegaWeights numberWeights z j)

/-- Ambient semantics with no invariant-set hypothesis. -/
@[simp]
theorem realize_fieldCode_arbitrary
    (parameters omegaWeights numberWeights :
      Fin q → RationalCode)
    (x : Fin (dimension q) → ℝ) :
    PolynomialFieldCode.realize
        (fieldCode parameters omegaWeights numberWeights) x =
      point
        (vectorField
          (fun i ↦
            (RationalCode.decode (parameters i) : ℝ))
          (fun i ↦
            (RationalCode.decode (omegaWeights i) : ℝ))
          (fun i ↦
            (RationalCode.decode (numberWeights i) : ℝ))
          (state x)) := by
  simpa using
    realize_fieldCode parameters omegaWeights numberWeights (state x)

end ControllerProductLinkedJacobiPolynomialCode

end HGAS.Modular
