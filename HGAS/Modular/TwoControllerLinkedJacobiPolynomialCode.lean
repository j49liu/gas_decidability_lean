import HGAS.Algebra.PolynomialVariableEmbedding
import HGAS.Clocks.ControllerPolynomialCode
import HGAS.Modular.LinkedJacobiPolynomialCode
import Mathlib.Tactic

/-!
# Two dynamic radical controllers coupled to the linked Jacobi field

This module assembles the polynomial source used by the two-clock
construction without substituting radicals into polynomial coefficients.
There are three blocks:

* a four-real-coordinate controller for the angular parameter `pΩ`;
* a four-real-coordinate controller for the auxiliary parameter `pN`; and
* the twenty-eight-real-coordinate realification of the linked
  unary--Jacobi state.

Thus the complete ambient space has dimension `4 + 4 + 28 = 36`.

If `rΩ` and `rN` are the locking coordinates of the two controllers, put

```
  omega = pΩ rΩ,       n = pN rN,
  kappaZ = (omega+n)/2,       kappaPhi = i omega.
```

The existing linked compiler accepts *constant* Gaussian-rational
coefficients.  To make the two coefficients state dependent while keeping
literal rational polynomial syntax, we use its two constant basis fields:

```
  F_Z   = compileFieldCode 1 0,
  F_iΦ  = compileFieldCode 0 i.
```

The linked part of the new field is then

```
  kappaZ F_Z + omega F_iΦ.
```

Linearity of `LinkedJacobiState.combinedVectorField` proves that this is
exactly the desired field with coefficients `kappaZ` and `i omega`.  This
basis-field construction is reusable whenever a polynomial state variable
must replace a scalar parameter of a linearly parameterized compiler.
-/

namespace HGAS.Modular

open HGAS

/-- Structured state represented by the thirty-six real coordinates. -/
@[ext]
structure TwoControllerLinkedJacobiState where
  omegaController : HGAS.Clocks.ControllerPhaseState ℝ
  numberController : HGAS.Clocks.ControllerPhaseState ℝ
  linked : LinkedJacobiState ℂ

namespace TwoControllerLinkedJacobiPolynomialCode

namespace ControllerCode

abbrev dimension : ℕ :=
  HGAS.Clocks.ControllerPolynomialCode.dimension

end ControllerCode

/-- Dimension of the two adjacent four-coordinate controller blocks. -/
abbrev controllerPairDimension : ℕ :=
  ControllerCode.dimension + ControllerCode.dimension

/-- Real dimension of the realified linked unary--Jacobi block. -/
abbrev linkedRealDimension : ℕ :=
  LinkedJacobiPolynomialCode.dimension +
    LinkedJacobiPolynomialCode.dimension

/-- Complete ambient dimension: `4 + 4 + 28 = 36`. -/
abbrev dimension : ℕ :=
  controllerPairDimension + linkedRealDimension

def omegaControllerEmbedding :
    Fin ControllerCode.dimension ↪ Fin controllerPairDimension :=
  PolynomialBlockCode.leftEmbedding

def numberControllerEmbedding :
    Fin ControllerCode.dimension ↪ Fin controllerPairDimension :=
  PolynomialBlockCode.rightEmbedding

def controllersEmbedding :
    Fin controllerPairDimension ↪ Fin dimension :=
  PolynomialBlockCode.leftEmbedding

def linkedRealEmbedding :
    Fin linkedRealDimension ↪ Fin dimension :=
  PolynomialBlockCode.rightEmbedding

/-- Flatten the two controller states into eight real coordinates. -/
def controllersPoint
    (z : TwoControllerLinkedJacobiState) :
    Fin controllerPairDimension → ℝ :=
  PolynomialBlockCode.point
    (HGAS.Clocks.ControllerPolynomialCode.point z.omegaController)
    (HGAS.Clocks.ControllerPolynomialCode.point z.numberController)

/-- Reassemble the two controller states from eight real coordinates. -/
def controllersState
    (x : Fin controllerPairDimension → ℝ) :
    HGAS.Clocks.ControllerPhaseState ℝ ×
      HGAS.Clocks.ControllerPhaseState ℝ :=
  (HGAS.Clocks.ControllerPolynomialCode.state
      (x ∘ omegaControllerEmbedding),
    HGAS.Clocks.ControllerPolynomialCode.state
      (x ∘ numberControllerEmbedding))

/-- Flatten the complete structured state into thirty-six real
coordinates. -/
def point
    (z : TwoControllerLinkedJacobiState) :
    Fin dimension → ℝ :=
  PolynomialBlockCode.point
    (controllersPoint z)
    (ComplexCoordinates.realifyPoint
      (LinkedJacobiPolynomialCode.point z.linked))

/-- Reassemble a structured state from an arbitrary ambient real point. -/
def state
    (x : Fin dimension → ℝ) :
    TwoControllerLinkedJacobiState :=
  let controllers :=
    controllersState (x ∘ controllersEmbedding)
  { omegaController := controllers.1
    numberController := controllers.2
    linked :=
      LinkedJacobiPolynomialCode.state
        (ComplexCoordinates.complexifyPoint
          (x ∘ linkedRealEmbedding)) }

@[simp]
theorem controllersState_controllersPoint
    (z : TwoControllerLinkedJacobiState) :
    controllersState (controllersPoint z) =
      (z.omegaController, z.numberController) := by
  apply Prod.ext <;>
    simp [controllersState, controllersPoint,
      omegaControllerEmbedding, numberControllerEmbedding]

@[simp]
theorem controllersPoint_controllersState
    (x : Fin controllerPairDimension → ℝ) :
    PolynomialBlockCode.point
        (HGAS.Clocks.ControllerPolynomialCode.point
          (controllersState x).1)
        (HGAS.Clocks.ControllerPolynomialCode.point
          (controllersState x).2) =
      x := by
  unfold controllersState
  funext q
  obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective q
  · rw [show finSumFinEquiv (Sum.inl i) =
      PolynomialBlockCode.leftEmbedding
        (p := ControllerCode.dimension) i by rfl]
    simp [omegaControllerEmbedding]
  · rw [show finSumFinEquiv (Sum.inr j) =
      PolynomialBlockCode.rightEmbedding
        (m := ControllerCode.dimension) j by rfl]
    simp [numberControllerEmbedding]

@[simp]
theorem state_point (z : TwoControllerLinkedJacobiState) :
    state (point z) = z := by
  ext <;>
    simp [state, point, controllersEmbedding, linkedRealEmbedding]

@[simp]
theorem point_state (x : Fin dimension → ℝ) :
    point (state x) = x := by
  unfold point state
  funext q
  obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective q
  · rw [show finSumFinEquiv (Sum.inl i) =
      PolynomialBlockCode.leftEmbedding
        (p := linkedRealDimension) i by rfl]
    simp [controllersPoint, controllersEmbedding]
  · rw [show finSumFinEquiv (Sum.inr j) =
      PolynomialBlockCode.rightEmbedding
        (m := controllerPairDimension) j by rfl]
    simp [linkedRealEmbedding]

theorem dimension_eq_thirty_six :
    dimension = 36 := by
  norm_num [dimension, controllerPairDimension,
    ControllerCode.dimension, linkedRealDimension,
    LinkedJacobiPolynomialCode.dimension,
    LinkedJacobiPolynomialCode.unaryDimension,
    LinkedJacobiPolynomialCode.jacobiDimension,
    HGAS.Clocks.ControllerPolynomialCode.dimension,
    UnaryPolynomialCode.modularDimension,
    JacobiPolynomialCode.dimension]

/-! ## The dynamic coefficients and their semantic vector field -/

/-- Signed angular frequency supplied by the first controller. -/
def omega
    (pΩ : ℝ) (z : TwoControllerLinkedJacobiState) : ℝ :=
  pΩ * z.omegaController.controller.r

/-- Signed auxiliary integer/radical frequency supplied by the second
controller. -/
def number
    (pN : ℝ) (z : TwoControllerLinkedJacobiState) : ℝ :=
  pN * z.numberController.controller.r

/-- The real elliptic coefficient `(omega+n)/2`, viewed in `ℂ`. -/
noncomputable def kappaZ
    (pΩ pN : ℝ) (z : TwoControllerLinkedJacobiState) : ℂ :=
  ((omega pΩ z + number pN z) / 2 : ℝ)

/-- The purely imaginary modular coefficient `i omega`. -/
noncomputable def kappaPhi
    (pΩ : ℝ) (z : TwoControllerLinkedJacobiState) : ℂ :=
  Complex.I * omega pΩ z

/-- The desired coupled vector field on the structured state. -/
noncomputable def vectorField
    (pΩ pN : ℝ) (z : TwoControllerLinkedJacobiState) :
    TwoControllerLinkedJacobiState where
  omegaController :=
    HGAS.Clocks.ControllerPolynomialCode.vectorField pΩ
      z.omegaController
  numberController :=
    HGAS.Clocks.ControllerPolynomialCode.vectorField pN
      z.numberController
  linked :=
    LinkedJacobiState.combinedVectorField
      (kappaZ pΩ pN z) (kappaPhi pΩ z) z.linked

/-! ## Literal sparse-polynomial construction -/

/-- The two independent controller fields on their eight-coordinate
product. -/
def controllerPairFieldCode
    (pΩ pN : RationalCode) :
    PolynomialFieldCode controllerPairDimension :=
  PolynomialBlockCode.field
    (HGAS.Clocks.ControllerPolynomialCode.fieldCode pΩ)
    (HGAS.Clocks.ControllerPolynomialCode.fieldCode pN)

/-- Polynomial `pΩ rΩ` on the eight-coordinate controller product. -/
def omegaPairCode
    (pΩ : RationalCode) :
    PolynomialCode controllerPairDimension :=
  PolynomialCode.mul
    (PolynomialCode.constant pΩ)
    (PolynomialBlockCode.left
      (p := ControllerCode.dimension)
      HGAS.Clocks.ControllerPolynomialCode.rCode)

/-- Polynomial `pN rN` on the eight-coordinate controller product. -/
def numberPairCode
    (pN : RationalCode) :
    PolynomialCode controllerPairDimension :=
  PolynomialCode.mul
    (PolynomialCode.constant pN)
    (PolynomialBlockCode.right
      (m := ControllerCode.dimension)
      HGAS.Clocks.ControllerPolynomialCode.rCode)

/-- Rational code of one half. -/
def halfCode : RationalCode :=
  RationalCode.encode (1 / 2 : ℚ)

/-- Polynomial `(pΩ rΩ + pN rN)/2` on the controller product. -/
def kappaZPairCode
    (pΩ pN : RationalCode) :
    PolynomialCode controllerPairDimension :=
  PolynomialCode.mul
    (PolynomialCode.constant halfCode)
    (PolynomialCode.add (omegaPairCode pΩ) (numberPairCode pN))

/-- The dynamic real coefficient `omega`, embedded in all thirty-six
variables. -/
def omegaCode
    (pΩ : RationalCode) :
    PolynomialCode dimension :=
  PolynomialBlockCode.left
    (p := linkedRealDimension) (omegaPairCode pΩ)

/-- The dynamic real coefficient `kappaZ`, embedded in all thirty-six
variables. -/
def kappaZCode
    (pΩ pN : RationalCode) :
    PolynomialCode dimension :=
  PolynomialBlockCode.left
    (p := linkedRealDimension) (kappaZPairCode pΩ pN)

/-- Constant linked basis field for the elliptic coefficient. -/
def linkedZBasisFieldCode :
    PolynomialFieldCode linkedRealDimension :=
  LinkedJacobiPolynomialCode.compileFieldCode
    GaussianRationalCode.one GaussianRationalCode.zero

/-- Constant linked basis field for the purely imaginary modular
coefficient. -/
def linkedIPhiBasisFieldCode :
    PolynomialFieldCode linkedRealDimension :=
  LinkedJacobiPolynomialCode.compileFieldCode
    GaussianRationalCode.zero GaussianRationalCode.I

/-- One linked real coordinate of
`kappaZ F_Z + omega F_iPhi`, embedded in all variables. -/
def linkedFieldComponentCode
    (pΩ pN : RationalCode) (j : Fin linkedRealDimension) :
    PolynomialCode dimension :=
  PolynomialCode.add
    (PolynomialCode.mul
      (kappaZCode pΩ pN)
      (PolynomialBlockCode.right
        (m := controllerPairDimension)
        (linkedZBasisFieldCode j)))
    (PolynomialCode.mul
      (omegaCode pΩ)
      (PolynomialBlockCode.right
        (m := controllerPairDimension)
        (linkedIPhiBasisFieldCode j)))

/-- Complete thirty-six-coordinate rational polynomial field. -/
def fieldCode
    (pΩ pN : RationalCode) :
    PolynomialFieldCode dimension :=
  fun q ↦
    match finSumFinEquiv.symm q with
    | Sum.inl i =>
        PolynomialBlockCode.left
          (p := linkedRealDimension)
          (controllerPairFieldCode pΩ pN i)
    | Sum.inr j => linkedFieldComponentCode pΩ pN j

@[simp]
theorem fieldCode_controllersEmbedding
    (pΩ pN : RationalCode) (i : Fin controllerPairDimension) :
    fieldCode pΩ pN (controllersEmbedding i) =
      PolynomialBlockCode.left
        (p := linkedRealDimension)
        (controllerPairFieldCode pΩ pN i) := by
  simp [fieldCode, controllersEmbedding]

@[simp]
theorem fieldCode_linkedRealEmbedding
    (pΩ pN : RationalCode) (j : Fin linkedRealDimension) :
    fieldCode pΩ pN (linkedRealEmbedding j) =
      linkedFieldComponentCode pΩ pN j := by
  simp [fieldCode, linkedRealEmbedding]

/-! ## Exact semantics -/

@[simp]
theorem eval_omegaPairCode
    (pΩ : RationalCode) (z : TwoControllerLinkedJacobiState) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) (controllersPoint z)
        (PolynomialCode.decode (omegaPairCode pΩ)) =
      omega (RationalCode.decode pΩ) z := by
  rw [omegaPairCode, PolynomialCode.decode_mul_code, map_mul,
    PolynomialCode.decode_constant]
  change
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (PolynomialBlockCode.point
          (HGAS.Clocks.ControllerPolynomialCode.point z.omegaController)
          (HGAS.Clocks.ControllerPolynomialCode.point z.numberController))
        (MvPolynomial.C (RationalCode.decode pΩ)) *
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (PolynomialBlockCode.point
          (HGAS.Clocks.ControllerPolynomialCode.point z.omegaController)
          (HGAS.Clocks.ControllerPolynomialCode.point z.numberController))
        (PolynomialCode.decode
          (PolynomialBlockCode.left
            HGAS.Clocks.ControllerPolynomialCode.rCode)) =
      omega (RationalCode.decode pΩ) z
  rw [PolynomialBlockCode.eval₂Hom_left]
  simp [omega,
    HGAS.Clocks.ControllerPolynomialCode.rCode,
    HGAS.Clocks.ControllerPolynomialCode.point,
    HGAS.Clocks.ControllerPolynomialCode.rIndex]

@[simp]
theorem eval_numberPairCode
    (pN : RationalCode) (z : TwoControllerLinkedJacobiState) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) (controllersPoint z)
        (PolynomialCode.decode (numberPairCode pN)) =
      number (RationalCode.decode pN) z := by
  rw [numberPairCode, PolynomialCode.decode_mul_code, map_mul,
    PolynomialCode.decode_constant]
  change
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (PolynomialBlockCode.point
          (HGAS.Clocks.ControllerPolynomialCode.point z.omegaController)
          (HGAS.Clocks.ControllerPolynomialCode.point z.numberController))
        (MvPolynomial.C (RationalCode.decode pN)) *
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (PolynomialBlockCode.point
          (HGAS.Clocks.ControllerPolynomialCode.point z.omegaController)
          (HGAS.Clocks.ControllerPolynomialCode.point z.numberController))
        (PolynomialCode.decode
          (PolynomialBlockCode.right
            HGAS.Clocks.ControllerPolynomialCode.rCode)) =
      number (RationalCode.decode pN) z
  rw [PolynomialBlockCode.eval₂Hom_right]
  simp [number,
    HGAS.Clocks.ControllerPolynomialCode.rCode,
    HGAS.Clocks.ControllerPolynomialCode.point,
    HGAS.Clocks.ControllerPolynomialCode.rIndex]

@[simp]
theorem eval_kappaZPairCode
    (pΩ pN : RationalCode) (z : TwoControllerLinkedJacobiState) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) (controllersPoint z)
        (PolynomialCode.decode (kappaZPairCode pΩ pN)) =
      (omega (RationalCode.decode pΩ) z +
        number (RationalCode.decode pN) z) / 2 := by
  rw [kappaZPairCode, PolynomialCode.decode_mul_code, map_mul,
    PolynomialCode.decode_constant, PolynomialCode.decode_add_code,
    map_add, eval_omegaPairCode, eval_numberPairCode]
  norm_num [halfCode]
  ring

/-- The linked combined field is real-linear in the two selected basis
fields. -/
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
              (LinkedJacobiState.combinedVectorField 0 Complex.I z) i := by
  funext q
  obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective q
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

/-- Realification commutes with real linear combinations of complex
coordinate vectors. -/
theorem realifyPoint_real_linear
    {n : ℕ} (a b : ℝ) (u v : Fin n → ℂ) :
    ComplexCoordinates.realifyPoint
        (fun i ↦ (a : ℂ) * u i + (b : ℂ) * v i) =
      fun q ↦
        a * ComplexCoordinates.realifyPoint u q +
          b * ComplexCoordinates.realifyPoint v q := by
  funext q
  cases hq : finSumFinEquiv.symm q with
  | inl i =>
      have hqi : q = ComplexCoordinates.realIndex i := by
        apply finSumFinEquiv.symm.injective
        simpa using hq
      subst q
      simp [ComplexCoordinates.realifyPoint]
  | inr i =>
      have hqi : q = ComplexCoordinates.imagIndex i := by
        apply finSumFinEquiv.symm.injective
        simpa using hq
      subst q
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

/-- Exact semantics of the dynamically coupled linked block. -/
theorem realize_linkedFieldComponentCode
    (pΩ pN : RationalCode)
    (z : TwoControllerLinkedJacobiState)
    (j : Fin linkedRealDimension) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) (point z)
        (PolynomialCode.decode
          (linkedFieldComponentCode pΩ pN j)) =
      ComplexCoordinates.realifyPoint
        (LinkedJacobiPolynomialCode.point
          (LinkedJacobiState.combinedVectorField
            (kappaZ (RationalCode.decode pΩ)
              (RationalCode.decode pN) z)
            (kappaPhi (RationalCode.decode pΩ) z)
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
          (PolynomialBlockCode.left (kappaZPairCode pΩ pN))) *
        MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
          (PolynomialBlockCode.point
            (controllersPoint z)
            (ComplexCoordinates.realifyPoint
              (LinkedJacobiPolynomialCode.point z.linked)))
          (PolynomialCode.decode
            (PolynomialBlockCode.right (linkedZBasisFieldCode j))) +
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (PolynomialBlockCode.point
          (controllersPoint z)
          (ComplexCoordinates.realifyPoint
            (LinkedJacobiPolynomialCode.point z.linked)))
        (PolynomialCode.decode
          (PolynomialBlockCode.left (omegaPairCode pΩ))) *
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
    eval_kappaZPairCode, eval_omegaPairCode]
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
          (PolynomialCode.decode (linkedIPhiBasisFieldCode j)) =
        PolynomialFieldCode.realize linkedIPhiBasisFieldCode
          (ComplexCoordinates.realifyPoint
            (LinkedJacobiPolynomialCode.point z.linked)) j by rfl,
    realize_linkedZBasisFieldCode, realize_linkedIPhiBasisFieldCode]
  let a :=
    (omega (RationalCode.decode pΩ) z +
      number (RationalCode.decode pN) z) / 2
  let b := omega (RationalCode.decode pΩ) z
  let u :=
    LinkedJacobiPolynomialCode.point
      (LinkedJacobiState.combinedVectorField 1 0 z.linked)
  let v :=
    LinkedJacobiPolynomialCode.point
      (LinkedJacobiState.combinedVectorField 0 Complex.I z.linked)
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
      exact (point_combinedVectorField_dynamic_basis a b z.linked).symm
    _ = _ := by
      simp [a, b, kappaZ, kappaPhi]

/-- Exact structured-state semantics of every one of the thirty-six
components. -/
@[simp]
theorem realize_fieldCode
    (pΩ pN : RationalCode)
    (z : TwoControllerLinkedJacobiState) :
    PolynomialFieldCode.realize (fieldCode pΩ pN) (point z) =
      point
        (vectorField (RationalCode.decode pΩ)
          (RationalCode.decode pN) z) := by
  funext q
  obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective q
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
              (controllerPairFieldCode pΩ pN i))) =
        PolynomialBlockCode.point
          (controllersPoint
            (vectorField (RationalCode.decode pΩ)
              (RationalCode.decode pN) z))
          (ComplexCoordinates.realifyPoint
            (LinkedJacobiPolynomialCode.point
              (vectorField (RationalCode.decode pΩ)
                (RationalCode.decode pN) z).linked))
          (PolynomialBlockCode.leftEmbedding i)
    rw [PolynomialBlockCode.eval₂Hom_left,
      PolynomialBlockCode.point_leftEmbedding]
    rw [show
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
          (controllersPoint z)
          (PolynomialCode.decode
            (controllerPairFieldCode pΩ pN i)) =
        PolynomialFieldCode.realize
          (controllerPairFieldCode pΩ pN)
          (controllersPoint z) i by rfl]
    unfold controllerPairFieldCode controllersPoint
    rw [
      PolynomialBlockCode.realize_field,
      HGAS.Clocks.ControllerPolynomialCode.realize_fieldCode,
      HGAS.Clocks.ControllerPolynomialCode.realize_fieldCode]
    simp [vectorField]
  · rw [show finSumFinEquiv (Sum.inr j) =
      linkedRealEmbedding j by rfl]
    simp only [PolynomialFieldCode.realize_apply,
      fieldCode_linkedRealEmbedding]
    change
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) (point z)
          (PolynomialCode.decode
            (linkedFieldComponentCode pΩ pN j)) =
        PolynomialBlockCode.point
          (controllersPoint
            (vectorField (RationalCode.decode pΩ)
              (RationalCode.decode pN) z))
          (ComplexCoordinates.realifyPoint
            (LinkedJacobiPolynomialCode.point
              (vectorField (RationalCode.decode pΩ)
                (RationalCode.decode pN) z).linked))
          (PolynomialBlockCode.rightEmbedding j)
    rw [PolynomialBlockCode.point_rightEmbedding]
    change
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) (point z)
          (PolynomialCode.decode
            (linkedFieldComponentCode pΩ pN j)) =
        ComplexCoordinates.realifyPoint
          (LinkedJacobiPolynomialCode.point
            (LinkedJacobiState.combinedVectorField
              (kappaZ (RationalCode.decode pΩ)
                (RationalCode.decode pN) z)
              (kappaPhi (RationalCode.decode pΩ) z)
              z.linked)) j
    exact realize_linkedFieldComponentCode pΩ pN z j

/-- Ambient semantics: no controller-circle or Jacobi residual hypothesis
is needed.  Every real point is first reassembled into the structured
state. -/
@[simp]
theorem realize_fieldCode_arbitrary
    (pΩ pN : RationalCode) (x : Fin dimension → ℝ) :
    PolynomialFieldCode.realize (fieldCode pΩ pN) x =
      point
        (vectorField (RationalCode.decode pΩ)
          (RationalCode.decode pN) (state x)) := by
  have h := realize_fieldCode pΩ pN (state x)
  simpa using h

end TwoControllerLinkedJacobiPolynomialCode

end HGAS.Modular
