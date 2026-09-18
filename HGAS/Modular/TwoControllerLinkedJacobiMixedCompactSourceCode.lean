import HGAS.Compactification.RightAffineLeftCompactLayout
import HGAS.Compiler.CompactAccumulatorPipelineComputability
import HGAS.Compiler.CompactAccumulatorPipelineGapCertificate
import HGAS.Modular.LinkedJacobiPolynomialComputability
import HGAS.Modular.LinkedJacobiPolynomialDegrees
import HGAS.Modular.TwoControllerLinkedJacobiPolynomialComputability
import HGAS.Modular.TwoControllerLinkedJacobiPolynomialDegrees
import Mathlib.Tactic

/-!
# Faithful mixed compactification of the two-controller linked-Jacobi source

The thirty-six real source coordinates have two genuinely different
geometric roles.

* The first eight coordinates are two controller--phase pairs.  They
  already lie on four invariant circles: the first controller circle, its
  phase circle, the second controller circle, and its phase circle.
* The remaining twenty-eight linked unary--Jacobi coordinates are affine
  and must be centrally compactified.

Accordingly this module uses four already compact source blocks and one
right affine block.  This is more faithful than putting all thirty-six
coordinates into one projective sphere.  The structural bidegree bound
`(3,8)` shows that the even clearing exponent `8` is sufficient: only
degree in the right affine variables creates denominators.

The delicate point is global tangency at the affine equator.  The four
controller--phase components use no right affine variable.  The
compact-support homogenization theorem therefore identifies each cleared
component with the original component times the common slowdown at every
ambient point, including `w=0`.  Exact controller and phase-circle
tangency then proves the pipeline's `BaseCompactTangency` premise without
division or a chart-interior hypothesis.

As in the all-affine finite-code instance, the final pipeline has

```
  (36 + 1) + (20 + 1) = 58
```

real coordinates.  Its source product has five base sphere blocks (one
new affine sphere and four inherited circles) plus the accumulator sphere.
-/

namespace HGAS.Modular

open HGAS

namespace TwoControllerLinkedJacobiMixedCompactSourceCode

abbrev sourceDimension : ℕ :=
  TwoControllerLinkedJacobiPolynomialCode.dimension
abbrev residualDimension : ℕ := 10 + 10
abbrev affineBlockCount : ℕ := 1
abbrev compactBlockCount : ℕ := 4
abbrev localCircleCount : ℕ := 2
abbrev controllerDimension : ℕ :=
  TwoControllerLinkedJacobiPolynomialCode.controllerPairDimension
abbrev linkedDimension : ℕ :=
  TwoControllerLinkedJacobiPolynomialCode.linkedRealDimension

/-- Sharp degree in the right affine linked-Jacobi variables. -/
abbrev affineDegreeBound : ℕ := 8

/-- Even denominator-clearing exponent for the unique affine block. -/
abbrev clearingExponent : ℕ := 8

/-- Dimension of the compactified source together with its accumulator. -/
abbrev finalDimension : ℕ :=
  (sourceDimension + affineBlockCount) + (residualDimension + 1)

theorem sourceDimension_eq_thirty_six :
    sourceDimension = 36 :=
  TwoControllerLinkedJacobiPolynomialCode.dimension_eq_thirty_six

theorem residualDimension_eq_twenty :
    residualDimension = 20 := by
  norm_num [residualDimension]

theorem clearingExponent_even :
    clearingExponent % 2 = 0 := by
  norm_num [clearingExponent]

theorem finalDimension_eq_fifty_eight :
    finalDimension = (36 + 1) + (20 + 1) ∧
      finalDimension = 58 := by
  constructor <;>
    norm_num [finalDimension, sourceDimension,
      affineBlockCount, residualDimension,
      TwoControllerLinkedJacobiPolynomialCode.dimension,
      TwoControllerLinkedJacobiPolynomialCode.controllerPairDimension,
      TwoControllerLinkedJacobiPolynomialCode.ControllerCode.dimension,
      TwoControllerLinkedJacobiPolynomialCode.linkedRealDimension,
      LinkedJacobiPolynomialCode.dimension,
      LinkedJacobiPolynomialCode.unaryDimension,
      LinkedJacobiPolynomialCode.jacobiDimension,
      HGAS.Clocks.ControllerPolynomialCode.dimension,
      UnaryPolynomialCode.modularDimension,
      JacobiPolynomialCode.dimension]

/-- Within one controller--phase state, assign `(r,s)` to the controller
circle and `(c,d)` to the phase circle. -/
def localCircleBlock :
    Fin HGAS.Clocks.ControllerPolynomialCode.dimension →
      Fin localCircleCount :=
  ![0, 0, 1, 1]

/-- Assignment of the two four-coordinate controller--phase states to four
circle blocks.  The outer sum distinguishes the omega and number
controllers; `localCircleBlock` distinguishes their controller and phase
circles. -/
def controllerCompactBlock :
    Fin controllerDimension → Fin compactBlockCount :=
  fun i ↦
    match finSumFinEquiv.symm i with
    | Sum.inl q =>
        finSumFinEquiv
          (Sum.inl (localCircleBlock q) :
            Fin localCircleCount ⊕ Fin localCircleCount)
    | Sum.inr q =>
        finSumFinEquiv
          (Sum.inr (localCircleBlock q) :
            Fin localCircleCount ⊕ Fin localCircleCount)

@[simp]
theorem controllerCompactBlock_finSum_inl
    (q : Fin HGAS.Clocks.ControllerPolynomialCode.dimension) :
    controllerCompactBlock
        (finSumFinEquiv
          (Sum.inl q :
            Fin HGAS.Clocks.ControllerPolynomialCode.dimension ⊕
              Fin HGAS.Clocks.ControllerPolynomialCode.dimension)) =
      finSumFinEquiv
        (Sum.inl (localCircleBlock q) :
          Fin localCircleCount ⊕ Fin localCircleCount) := by
  simp only [controllerCompactBlock, Equiv.symm_apply_apply]

@[simp]
theorem controllerCompactBlock_finSum_inr
    (q : Fin HGAS.Clocks.ControllerPolynomialCode.dimension) :
    controllerCompactBlock
        (finSumFinEquiv
          (Sum.inr q :
            Fin HGAS.Clocks.ControllerPolynomialCode.dimension ⊕
              Fin HGAS.Clocks.ControllerPolynomialCode.dimension)) =
      finSumFinEquiv
        (Sum.inr (localCircleBlock q) :
          Fin localCircleCount ⊕ Fin localCircleCount) := by
  simp only [controllerCompactBlock, Equiv.symm_apply_apply]

@[simp]
theorem controllerCompactBlock_castAdd
    (q : Fin HGAS.Clocks.ControllerPolynomialCode.dimension) :
    controllerCompactBlock
        (Fin.castAdd
          HGAS.Clocks.ControllerPolynomialCode.dimension q) =
      Fin.castAdd localCircleCount (localCircleBlock q) := by
  simpa only [finSumFinEquiv_apply_left] using
    controllerCompactBlock_finSum_inl q

@[simp]
theorem controllerCompactBlock_natAdd
    (q : Fin HGAS.Clocks.ControllerPolynomialCode.dimension) :
    controllerCompactBlock
        (Fin.natAdd
          HGAS.Clocks.ControllerPolynomialCode.dimension q) =
      Fin.natAdd localCircleCount (localCircleBlock q) := by
  simpa only [finSumFinEquiv_apply_right] using
    controllerCompactBlock_finSum_inr q

@[simp]
theorem controllerCompactBlock_addNat
    (q : Fin HGAS.Clocks.ControllerPolynomialCode.dimension) :
    controllerCompactBlock
        (Fin.addNat q
          HGAS.Clocks.ControllerPolynomialCode.dimension) =
      Fin.addNat (localCircleBlock q) localCircleCount := by
  simpa only [Fin.natAdd_eq_addNat] using
    controllerCompactBlock_natAdd q

theorem addNat_ne_castAdd
    (a b : Fin localCircleCount) :
    Fin.addNat a localCircleCount ≠
      Fin.castAdd localCircleCount b := by
  intro h
  have hv := congrArg Fin.val h
  have ha : localCircleCount ≤
      (Fin.addNat a localCircleCount).val := by
    simp [Fin.addNat]
  have hb : (Fin.castAdd localCircleCount b).val <
      localCircleCount :=
    b.isLt
  omega

theorem castAdd_ne_addNat
    (a b : Fin localCircleCount) :
    Fin.castAdd localCircleCount a ≠
      Fin.addNat b localCircleCount :=
  (addNat_ne_castAdd b a).symm

/-- Four compact circles on the left and one affine linked block on the
right. -/
def layout :
    Fin sourceDimension →
      Fin affineBlockCount ⊕ Fin compactBlockCount :=
  RightAffineLeftCompactLayout.layout controllerCompactBlock

/-- Exact dynamically coupled source field on thirty-six coordinates. -/
def sourceFieldCode
    (pΩ pN : RationalCode) :
    PolynomialFieldCode sourceDimension :=
  TwoControllerLinkedJacobiPolynomialCode.fieldCode pΩ pN

/-- The twenty real validity residuals depend only on the right linked
block. -/
def residualCode
    (i : Fin residualDimension) :
    PolynomialCode sourceDimension :=
  PolynomialBlockCode.right
    (m := controllerDimension)
    (LinkedJacobiPolynomialCode.realResidualCode i)

/-! ## Coordinate geometry of the four compact circles -/

/-- Dot product in one of the two circles of a four-coordinate
controller--phase block. -/
def localCircleDot
    {R : Type*} [CommRing R]
    (x v : Fin HGAS.Clocks.ControllerPolynomialCode.dimension → R)
    (c : Fin localCircleCount) : R :=
  ∑ q, if localCircleBlock q = c then x q * v q else 0

@[simp]
theorem localCircleDot_controller
    {R : Type*} [CommRing R]
    (x v : Fin HGAS.Clocks.ControllerPolynomialCode.dimension → R) :
    localCircleDot x v 0 =
      x HGAS.Clocks.ControllerPolynomialCode.rIndex *
          v HGAS.Clocks.ControllerPolynomialCode.rIndex +
        x HGAS.Clocks.ControllerPolynomialCode.sIndex *
          v HGAS.Clocks.ControllerPolynomialCode.sIndex := by
  simp [localCircleDot, localCircleBlock,
    HGAS.Clocks.ControllerPolynomialCode.dimension,
    HGAS.Clocks.ControllerPolynomialCode.rIndex,
    HGAS.Clocks.ControllerPolynomialCode.sIndex,
    Fin.sum_univ_succ]

@[simp]
theorem localCircleDot_phase
    {R : Type*} [CommRing R]
    (x v : Fin HGAS.Clocks.ControllerPolynomialCode.dimension → R) :
    localCircleDot x v 1 =
      x HGAS.Clocks.ControllerPolynomialCode.cIndex *
          v HGAS.Clocks.ControllerPolynomialCode.cIndex +
        x HGAS.Clocks.ControllerPolynomialCode.dIndex *
          v HGAS.Clocks.ControllerPolynomialCode.dIndex := by
  simp [localCircleDot, localCircleBlock,
    HGAS.Clocks.ControllerPolynomialCode.dimension,
    HGAS.Clocks.ControllerPolynomialCode.cIndex,
    HGAS.Clocks.ControllerPolynomialCode.dIndex,
    Fin.sum_univ_succ]

/-- The compact dot product in one omega-controller circle is the local
four-coordinate dot product. -/
theorem compactBlockDot_omega
    {R : Type*} [CommRing R]
    (x v : Fin sourceDimension → R)
    (c : Fin localCircleCount) :
    MixedCentralPolynomialCode.compactBlockDot layout x v
        (finSumFinEquiv
          (Sum.inl c :
            Fin localCircleCount ⊕ Fin localCircleCount)) =
      localCircleDot
        (fun q ↦ x
          (TwoControllerLinkedJacobiPolynomialCode.controllersEmbedding
            (TwoControllerLinkedJacobiPolynomialCode.omegaControllerEmbedding
              q)))
        (fun q ↦ v
          (TwoControllerLinkedJacobiPolynomialCode.controllersEmbedding
            (TwoControllerLinkedJacobiPolynomialCode.omegaControllerEmbedding
              q)))
        c := by
  unfold layout
  rw [RightAffineLeftCompactLayout.compactBlockDot_layout]
  unfold localCircleDot
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [controllerCompactBlock_finSum_inl,
    controllerCompactBlock_finSum_inr]
  let A :
      Fin HGAS.Clocks.ControllerPolynomialCode.dimension → R :=
    fun q ↦
      x
          (TwoControllerLinkedJacobiPolynomialCode.controllersEmbedding
            (TwoControllerLinkedJacobiPolynomialCode.omegaControllerEmbedding
              q)) *
        v
          (TwoControllerLinkedJacobiPolynomialCode.controllersEmbedding
            (TwoControllerLinkedJacobiPolynomialCode.omegaControllerEmbedding
              q))
  let B :
      Fin HGAS.Clocks.ControllerPolynomialCode.dimension → R :=
    fun q ↦
      x
          (TwoControllerLinkedJacobiPolynomialCode.controllersEmbedding
            (TwoControllerLinkedJacobiPolynomialCode.numberControllerEmbedding
              q)) *
        v
          (TwoControllerLinkedJacobiPolynomialCode.controllersEmbedding
            (TwoControllerLinkedJacobiPolynomialCode.numberControllerEmbedding
              q))
  change
    (∑ q,
        if finSumFinEquiv
              (Sum.inl (localCircleBlock q) :
                Fin localCircleCount ⊕ Fin localCircleCount) =
            finSumFinEquiv
              (Sum.inl c :
                Fin localCircleCount ⊕ Fin localCircleCount)
        then A q else 0) +
      (∑ q,
        if finSumFinEquiv
              (Sum.inr (localCircleBlock q) :
                Fin localCircleCount ⊕ Fin localCircleCount) =
            finSumFinEquiv
              (Sum.inl c :
                Fin localCircleCount ⊕ Fin localCircleCount)
        then B q else 0) =
      ∑ q, if localCircleBlock q = c then A q else 0
  have hA :
      (∑ q,
        if finSumFinEquiv
              (Sum.inl (localCircleBlock q) :
                Fin localCircleCount ⊕ Fin localCircleCount) =
            finSumFinEquiv
              (Sum.inl c :
                Fin localCircleCount ⊕ Fin localCircleCount)
        then A q else 0) =
      ∑ q, if localCircleBlock q = c then A q else 0 := by
    apply Finset.sum_congr rfl
    intro q _
    by_cases hq : localCircleBlock q = c
    · subst c
      simp
    · have hne :
          finSumFinEquiv
              (Sum.inl (localCircleBlock q) :
                Fin localCircleCount ⊕ Fin localCircleCount) ≠
            finSumFinEquiv
              (Sum.inl c :
                Fin localCircleCount ⊕ Fin localCircleCount) := by
          intro h
          exact hq (Sum.inl.inj (finSumFinEquiv.injective h))
      rw [if_neg hne, if_neg hq]
  have hB :
      (∑ q,
        if finSumFinEquiv
              (Sum.inr (localCircleBlock q) :
                Fin localCircleCount ⊕ Fin localCircleCount) =
            finSumFinEquiv
              (Sum.inl c :
                Fin localCircleCount ⊕ Fin localCircleCount)
        then B q else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro q _
    have hne :
        finSumFinEquiv
            (Sum.inr (localCircleBlock q) :
              Fin localCircleCount ⊕ Fin localCircleCount) ≠
          finSumFinEquiv
            (Sum.inl c :
              Fin localCircleCount ⊕ Fin localCircleCount) := by
      intro h
      exact Sum.inr_ne_inl (finSumFinEquiv.injective h)
    rw [if_neg hne]
  rw [hA, hB, add_zero]

/-- The analogous identity for one number-controller circle. -/
theorem compactBlockDot_number
    {R : Type*} [CommRing R]
    (x v : Fin sourceDimension → R)
    (c : Fin localCircleCount) :
    MixedCentralPolynomialCode.compactBlockDot layout x v
        (finSumFinEquiv
          (Sum.inr c :
            Fin localCircleCount ⊕ Fin localCircleCount)) =
      localCircleDot
        (fun q ↦ x
          (TwoControllerLinkedJacobiPolynomialCode.controllersEmbedding
            (TwoControllerLinkedJacobiPolynomialCode.numberControllerEmbedding
              q)))
        (fun q ↦ v
          (TwoControllerLinkedJacobiPolynomialCode.controllersEmbedding
            (TwoControllerLinkedJacobiPolynomialCode.numberControllerEmbedding
              q)))
        c := by
  unfold layout
  rw [RightAffineLeftCompactLayout.compactBlockDot_layout]
  unfold localCircleDot
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [controllerCompactBlock_finSum_inl,
    controllerCompactBlock_finSum_inr]
  let A :
      Fin HGAS.Clocks.ControllerPolynomialCode.dimension → R :=
    fun q ↦
      x
          (TwoControllerLinkedJacobiPolynomialCode.controllersEmbedding
            (TwoControllerLinkedJacobiPolynomialCode.omegaControllerEmbedding
              q)) *
        v
          (TwoControllerLinkedJacobiPolynomialCode.controllersEmbedding
            (TwoControllerLinkedJacobiPolynomialCode.omegaControllerEmbedding
              q))
  let B :
      Fin HGAS.Clocks.ControllerPolynomialCode.dimension → R :=
    fun q ↦
      x
          (TwoControllerLinkedJacobiPolynomialCode.controllersEmbedding
            (TwoControllerLinkedJacobiPolynomialCode.numberControllerEmbedding
              q)) *
        v
          (TwoControllerLinkedJacobiPolynomialCode.controllersEmbedding
            (TwoControllerLinkedJacobiPolynomialCode.numberControllerEmbedding
              q))
  change
    (∑ q,
        if finSumFinEquiv
              (Sum.inl (localCircleBlock q) :
                Fin localCircleCount ⊕ Fin localCircleCount) =
            finSumFinEquiv
              (Sum.inr c :
                Fin localCircleCount ⊕ Fin localCircleCount)
        then A q else 0) +
      (∑ q,
        if finSumFinEquiv
              (Sum.inr (localCircleBlock q) :
                Fin localCircleCount ⊕ Fin localCircleCount) =
            finSumFinEquiv
              (Sum.inr c :
                Fin localCircleCount ⊕ Fin localCircleCount)
        then B q else 0) =
      ∑ q, if localCircleBlock q = c then B q else 0
  have hA :
      (∑ q,
        if finSumFinEquiv
              (Sum.inl (localCircleBlock q) :
                Fin localCircleCount ⊕ Fin localCircleCount) =
            finSumFinEquiv
              (Sum.inr c :
                Fin localCircleCount ⊕ Fin localCircleCount)
        then A q else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro q _
    have hne :
        finSumFinEquiv
            (Sum.inl (localCircleBlock q) :
              Fin localCircleCount ⊕ Fin localCircleCount) ≠
          finSumFinEquiv
            (Sum.inr c :
              Fin localCircleCount ⊕ Fin localCircleCount) := by
      intro h
      exact Sum.inl_ne_inr (finSumFinEquiv.injective h)
    rw [if_neg hne]
  have hB :
      (∑ q,
        if finSumFinEquiv
              (Sum.inr (localCircleBlock q) :
                Fin localCircleCount ⊕ Fin localCircleCount) =
            finSumFinEquiv
              (Sum.inr c :
                Fin localCircleCount ⊕ Fin localCircleCount)
        then B q else 0) =
      ∑ q, if localCircleBlock q = c then B q else 0 := by
    apply Finset.sum_congr rfl
    intro q _
    by_cases hq : localCircleBlock q = c
    · subst c
      simp
    · have hne :
          finSumFinEquiv
              (Sum.inr (localCircleBlock q) :
                Fin localCircleCount ⊕ Fin localCircleCount) ≠
            finSumFinEquiv
              (Sum.inr c :
                Fin localCircleCount ⊕ Fin localCircleCount) := by
          intro h
          exact hq (Sum.inr.inj (finSumFinEquiv.injective h))
      rw [if_neg hne, if_neg hq]
  rw [hA, hB, zero_add]

/-! ## Exact source and residual semantics -/

@[simp]
theorem realize_sourceFieldCode
    (pΩ pN : RationalCode)
    (x : Fin sourceDimension → ℝ) :
    PolynomialFieldCode.realize
        (sourceFieldCode pΩ pN) x =
      TwoControllerLinkedJacobiPolynomialCode.point
        (TwoControllerLinkedJacobiPolynomialCode.vectorField
          (RationalCode.decode pΩ)
          (RationalCode.decode pN)
          (TwoControllerLinkedJacobiPolynomialCode.state x)) :=
  TwoControllerLinkedJacobiPolynomialCode.realize_fieldCode_arbitrary
    pΩ pN x

@[simp]
theorem point_omegaControllerEmbedding
    (z : TwoControllerLinkedJacobiState)
    (q : Fin HGAS.Clocks.ControllerPolynomialCode.dimension) :
    TwoControllerLinkedJacobiPolynomialCode.point z
        (TwoControllerLinkedJacobiPolynomialCode.controllersEmbedding
          (TwoControllerLinkedJacobiPolynomialCode.omegaControllerEmbedding
            q)) =
      HGAS.Clocks.ControllerPolynomialCode.point
        z.omegaController q := by
  simp [TwoControllerLinkedJacobiPolynomialCode.point,
    TwoControllerLinkedJacobiPolynomialCode.controllersPoint,
    TwoControllerLinkedJacobiPolynomialCode.controllersEmbedding,
    TwoControllerLinkedJacobiPolynomialCode.omegaControllerEmbedding]

@[simp]
theorem point_numberControllerEmbedding
    (z : TwoControllerLinkedJacobiState)
    (q : Fin HGAS.Clocks.ControllerPolynomialCode.dimension) :
    TwoControllerLinkedJacobiPolynomialCode.point z
        (TwoControllerLinkedJacobiPolynomialCode.controllersEmbedding
          (TwoControllerLinkedJacobiPolynomialCode.numberControllerEmbedding
            q)) =
      HGAS.Clocks.ControllerPolynomialCode.point
        z.numberController q := by
  simp [TwoControllerLinkedJacobiPolynomialCode.point,
    TwoControllerLinkedJacobiPolynomialCode.controllersPoint,
    TwoControllerLinkedJacobiPolynomialCode.controllersEmbedding,
    TwoControllerLinkedJacobiPolynomialCode.numberControllerEmbedding]

/-- Exact original-field tangency to each of the four inherited circle
blocks at every ambient point. -/
theorem sourceFieldCode_compactBlockDot
    (pΩ pN : RationalCode)
    (x : Fin sourceDimension → ℝ) :
    ∀ c,
      MixedCentralPolynomialCode.compactBlockDot layout x
        (PolynomialFieldCode.realize
          (sourceFieldCode pΩ pN) x) c = 0 := by
  intro c
  let z := TwoControllerLinkedJacobiPolynomialCode.state x
  have hx :
      TwoControllerLinkedJacobiPolynomialCode.point z = x :=
    TwoControllerLinkedJacobiPolynomialCode.point_state x
  rw [← hx]
  change
    MixedCentralPolynomialCode.compactBlockDot layout
      (TwoControllerLinkedJacobiPolynomialCode.point z)
      (PolynomialFieldCode.realize
        (TwoControllerLinkedJacobiPolynomialCode.fieldCode pΩ pN)
        (TwoControllerLinkedJacobiPolynomialCode.point z)) c = 0
  rw [TwoControllerLinkedJacobiPolynomialCode.realize_fieldCode]
  obtain ⟨d | d, rfl⟩ :=
    (@finSumFinEquiv localCircleCount localCircleCount).surjective c
  · rw [compactBlockDot_omega]
    fin_cases d
    · simpa [
        TwoControllerLinkedJacobiPolynomialCode.vectorField,
        HGAS.Clocks.ControllerPolynomialCode.point,
        HGAS.Clocks.ControllerPolynomialCode.vectorField,
        HGAS.Clocks.ControllerPolynomialCode.rIndex,
        HGAS.Clocks.ControllerPolynomialCode.sIndex,
        HGAS.Clocks.Controller.controllerDot] using
          HGAS.Clocks.Controller.controllerField_tangent
            (RationalCode.decode pΩ : ℝ)
            z.omegaController.controller
    · simpa [
        TwoControllerLinkedJacobiPolynomialCode.vectorField,
        HGAS.Clocks.ControllerPolynomialCode.point,
        HGAS.Clocks.ControllerPolynomialCode.vectorField,
        HGAS.Clocks.ControllerPolynomialCode.cIndex,
        HGAS.Clocks.ControllerPolynomialCode.dIndex,
        HGAS.Clocks.Controller.phaseDot] using
          HGAS.Clocks.Controller.lockedPhaseField_tangent
            (RationalCode.decode pΩ : ℝ)
            z.omegaController.controller z.omegaController.phase
  · rw [compactBlockDot_number]
    fin_cases d
    · simpa [
        TwoControllerLinkedJacobiPolynomialCode.vectorField,
        HGAS.Clocks.ControllerPolynomialCode.point,
        HGAS.Clocks.ControllerPolynomialCode.vectorField,
        HGAS.Clocks.ControllerPolynomialCode.rIndex,
        HGAS.Clocks.ControllerPolynomialCode.sIndex,
        HGAS.Clocks.Controller.controllerDot] using
          HGAS.Clocks.Controller.controllerField_tangent
            (RationalCode.decode pN : ℝ)
            z.numberController.controller
    · simpa [
        TwoControllerLinkedJacobiPolynomialCode.vectorField,
        HGAS.Clocks.ControllerPolynomialCode.point,
        HGAS.Clocks.ControllerPolynomialCode.vectorField,
        HGAS.Clocks.ControllerPolynomialCode.cIndex,
        HGAS.Clocks.ControllerPolynomialCode.dIndex,
        HGAS.Clocks.Controller.phaseDot] using
          HGAS.Clocks.Controller.lockedPhaseField_tangent
            (RationalCode.decode pN : ℝ)
            z.numberController.controller z.numberController.phase

/-! ## Exact validity-residual semantics -/

/-- A lifted scalar residual ignores the eight controller coordinates. -/
@[simp]
theorem eval_residualCode
    (z : TwoControllerLinkedJacobiState)
    (i : Fin residualDimension) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (TwoControllerLinkedJacobiPolynomialCode.point z)
        (PolynomialCode.decode (residualCode i)) =
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (ComplexCoordinates.realifyPoint
          (LinkedJacobiPolynomialCode.point z.linked))
        (PolynomialCode.decode
          (LinkedJacobiPolynomialCode.realResidualCode i)) := by
  rw [residualCode,
    TwoControllerLinkedJacobiPolynomialCode.point,
    PolynomialBlockCode.eval₂Hom_right]

/-- Reassembling the twenty scalar evaluations gives the ten named
complex linked-Jacobi residuals. -/
@[simp]
theorem complexifyPoint_eval_residualCode
    (z : TwoControllerLinkedJacobiState) :
    ComplexCoordinates.complexifyPoint
        (fun q ↦
          MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
            (TwoControllerLinkedJacobiPolynomialCode.point z)
            (PolynomialCode.decode (residualCode q))) =
      fun i ↦
        linkedJacobiResidual
          (LinkedJacobiPolynomialCode.residualIndex i) z.linked := by
  simpa only [eval_residualCode] using
    LinkedJacobiPolynomialCode.complexifyPoint_eval_realResidualCode
      z.linked

/-- Ambient version of the residual semantics theorem. -/
@[simp]
theorem complexifyPoint_eval_residualCode_arbitrary
    (x : Fin sourceDimension → ℝ) :
    ComplexCoordinates.complexifyPoint
        (fun q ↦
          MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x
            (PolynomialCode.decode (residualCode q))) =
      fun i ↦
        linkedJacobiResidual
          (LinkedJacobiPolynomialCode.residualIndex i)
          (TwoControllerLinkedJacobiPolynomialCode.state x).linked := by
  have h :=
    complexifyPoint_eval_residualCode
      (TwoControllerLinkedJacobiPolynomialCode.state x)
  simpa using h

/-- Simultaneous scalar vanishing is exactly validity of every named
linked-Jacobi residual. -/
theorem forall_eval_residualCode_eq_zero_iff
    (z : TwoControllerLinkedJacobiState) :
    (∀ q,
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (TwoControllerLinkedJacobiPolynomialCode.point z)
        (PolynomialCode.decode (residualCode q)) = 0) ↔
      ∀ r : LinkedJacobiResidualIndex,
        linkedJacobiResidual r z.linked = 0 := by
  simpa only [eval_residualCode] using
    LinkedJacobiPolynomialCode.forall_eval_realResidualCode_eq_zero_iff
      z.linked

/-- Ambient form of the simultaneous-vanishing criterion. -/
theorem forall_eval_residualCode_eq_zero_iff_arbitrary
    (x : Fin sourceDimension → ℝ) :
    (∀ q,
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode (residualCode q)) = 0) ↔
      ∀ r : LinkedJacobiResidualIndex,
        linkedJacobiResidual r
          (TwoControllerLinkedJacobiPolynomialCode.state x).linked = 0 := by
  have h :=
    forall_eval_residualCode_eq_zero_iff
      (TwoControllerLinkedJacobiPolynomialCode.state x)
  simpa using h

/-! ## Structural degree ledger -/

/-- The full source has controller/right-affine bidegree at most `(3,8)`.
Only the second entry is relevant to denominator clearing. -/
theorem sourceFieldCode_termsBidegreeLE
    (pΩ pN : RationalCode) :
    ∀ j, PolynomialBlockCode.TermsBidegreeLE 3 8
      (sourceFieldCode pΩ pN j) :=
  TwoControllerLinkedJacobiPolynomialCode.fieldCode_termsBidegreeLE
    pΩ pN

/-- For reference, the ordinary total degree is still at most nine. -/
theorem sourceFieldCode_termsDegreeLE
    (pΩ pN : RationalCode) :
    ∀ j, PolynomialCode.TermsDegreeLE 9
      (sourceFieldCode pΩ pN j) :=
  TwoControllerLinkedJacobiPolynomialCode.fieldCode_termsDegreeLE
    pΩ pN

/-- A controller-output component has right affine degree exactly zero as
a raw sparse bound. -/
theorem sourceFieldCode_controller_termsBidegreeLE
    (pΩ pN : RationalCode)
    (i : Fin controllerDimension) :
    PolynomialBlockCode.TermsBidegreeLE 3 0
      (sourceFieldCode pΩ pN
        (TwoControllerLinkedJacobiPolynomialCode.controllersEmbedding i)) := by
  rw [sourceFieldCode,
    TwoControllerLinkedJacobiPolynomialCode.fieldCode_controllersEmbedding]
  exact
    PolynomialBlockCode.termsBidegreeLE_left
      (TwoControllerLinkedJacobiPolynomialCode.controllerPairFieldCode_termsDegreeLE
        pΩ pN i)

/-- Every source component satisfies the sharp affine clearing bound
`M=8`. -/
theorem sourceFieldCode_termsAffineBlockDegreeLE
    (pΩ pN : RationalCode) :
    ∀ j,
      MixedCentralPolynomialCode.TermsAffineBlockDegreeLE
        layout clearingExponent
        (sourceFieldCode pΩ pN j) := by
  intro j
  unfold layout
  exact
    RightAffineLeftCompactLayout.termsAffineBlockDegreeLE_of_termsBidegreeLE
        controllerCompactBlock
        (sourceFieldCode_termsBidegreeLE pΩ pN j)

/-- The transported residuals have bidegree `(0,4)`. -/
theorem residualCode_termsBidegreeLE :
    ∀ i, PolynomialBlockCode.TermsBidegreeLE 0 4
      (residualCode i) := by
  intro i
  exact
    PolynomialBlockCode.termsBidegreeLE_right
      (LinkedJacobiPolynomialCode.realResidualCode_termsDegreeLE i)

/-- Hence every residual also satisfies the common affine clearing
bound `M=8`. -/
theorem residualCode_termsAffineBlockDegreeLE :
    ∀ i,
      MixedCentralPolynomialCode.TermsAffineBlockDegreeLE
        layout clearingExponent (residualCode i) := by
  intro i
  unfold layout
  exact
    RightAffineLeftCompactLayout.termsAffineBlockDegreeLE_of_termsBidegreeLE_of_le
        controllerCompactBlock
        (residualCode_termsBidegreeLE i)
        (by norm_num [clearingExponent])

/-- Any component selected by a compact layout block uses no affine
variable at all. -/
theorem sourceFieldCode_termsAffineDegreeZero_of_compact
    (pΩ pN : RationalCode)
    (j : Fin sourceDimension) (c : Fin compactBlockCount)
    (hj : layout j = Sum.inr c) :
    MixedCentralPolynomialCode.TermsAffineDegreeZero
      layout (sourceFieldCode pΩ pN j) := by
  obtain ⟨i | q, rfl⟩ := finSumFinEquiv.surjective j
  · unfold layout
    exact
      RightAffineLeftCompactLayout.termsAffineDegreeZero_of_termsBidegreeLE
          controllerCompactBlock
          (sourceFieldCode_controller_termsBidegreeLE pΩ pN i)
  · have hright :
        layout
            (finSumFinEquiv
              (Sum.inr q :
                Fin controllerDimension ⊕ Fin linkedDimension)) =
          Sum.inl (0 : Fin affineBlockCount) := by
      simp [layout, RightAffineLeftCompactLayout.layout]
    rw [hright] at hj
    exact (Sum.inl_ne_inr hj).elim

/-! ## Global tangency after denominator clearing -/

/-- The denominator-cleared velocity remains tangent to all four compact
circles at every chart point, including `w=0`. -/
theorem clearedSourceVelocity_compactBlockDot
    (pΩ pN : RationalCode)
    (x : Fin sourceDimension → ℝ)
    (w : Fin affineBlockCount → ℝ) :
    ∀ c,
      MixedCentralPolynomialCode.compactBlockDot layout x
        (MixedCentralPolynomialCode.clearedSourceVelocity
          layout clearingExponent
          (sourceFieldCode pΩ pN)
          (MixedCentralPolynomialCode.chartPoint x w)) c = 0 := by
  intro c
  exact
    MixedCentralPolynomialCode.compactBlockDot_clearedSourceVelocity_eq_zero
        layout clearingExponent (sourceFieldCode pΩ pN)
        x w c
        (fun j hj ↦
          sourceFieldCode_termsAffineDegreeZero_of_compact
            pΩ pN j c hj)
        (sourceFieldCode_compactBlockDot pΩ pN x c)

/-- The exact source-specific premise required by the compact accumulator
pipeline. -/
theorem baseCompactTangency
    (pΩ pN : RationalCode) :
    CompactAccumulatorPipelineCode.BaseCompactTangency
      layout clearingExponent
      (sourceFieldCode pΩ pN) := by
  intro y
  dsimp
  intro c
  let x : Fin sourceDimension → ℝ :=
    fun j ↦
      y.1 (MixedCentralPolynomialCode.xIndex
        (k := affineBlockCount) j)
  let w : Fin affineBlockCount → ℝ :=
    fun b ↦
      y.1 (MixedCentralPolynomialCode.wIndex
        (n := sourceDimension) b)
  have hy :
      MixedCentralPolynomialCode.chartPoint x w = y.1 :=
    MixedCentralPolynomialCode.chartPoint_decompose y.1
  rw [← hy]
  exact clearedSourceVelocity_compactBlockDot pΩ pN x w c

/-! ## One primitive-recursive mixed compactification pipeline -/

/-- Runtime data, in order: `pΩ`, `pN`, accumulator scale `kappa`, and
strict-sign margin `epsilon`. -/
abbrev CompilerInput :=
  ((RationalCode × RationalCode) × RationalCode) × RationalCode

def toPipelineInput
    (u : CompilerInput) :
    CompactAccumulatorPipelineCode.CompilerInput
      sourceDimension residualDimension :=
  (((u.1.2,
      sourceFieldCode u.1.1.1 u.1.1.2),
    residualCode),
    u.2)

/-- Complete mixed compactification and accumulator compiler. -/
def compile
    (u : CompilerInput) :
    PolynomialFieldCode finalDimension ×
      PolynomialCode finalDimension :=
  CompactAccumulatorPipelineCode.compile
    layout clearingExponent (toPipelineInput u)

theorem residualCode_primrec :
    Primrec residualCode :=
  PolynomialBlockCode.right_primrec.comp
    LinkedJacobiPolynomialCode.realResidualCode_primrec

theorem toPipelineInput_primrec :
    Primrec toPipelineInput := by
  have hparameters :
      Primrec (fun u : CompilerInput ↦ u.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hsource :
      Primrec
        (fun u : CompilerInput ↦
          sourceFieldCode u.1.1.1 u.1.1.2) :=
    TwoControllerLinkedJacobiPolynomialCode.fieldCode_primrec.comp
      (Primrec.fst.comp hparameters)
      (Primrec.snd.comp hparameters)
  have hscale :
      Primrec (fun u : CompilerInput ↦ u.1.2) :=
    Primrec.snd.comp Primrec.fst
  exact
    Primrec.pair
      (Primrec.pair
        (Primrec.pair hscale hsource)
        (Primrec.const residualCode))
      Primrec.snd

theorem compile_primrec :
    Primrec compile :=
  (CompactAccumulatorPipelineCode.compile_primrec
    (m := residualDimension)
    layout clearingExponent).comp
      toPipelineInput_primrec

theorem compile_computable :
    Computable compile :=
  compile_primrec.to_comp

/-- The mixed source has five base sphere blocks, and the pipeline adds
one accumulator sphere. -/
theorem sphereBlockCounts :
    affineBlockCount + compactBlockCount = 5 ∧
      (affineBlockCount + compactBlockCount) + 1 = 6 := by
  norm_num [affineBlockCount, compactBlockCount]

end TwoControllerLinkedJacobiMixedCompactSourceCode

end HGAS.Modular
