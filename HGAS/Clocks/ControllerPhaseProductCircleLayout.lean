import HGAS.Clocks.ControllerPhaseProductPolynomialCode
import Mathlib.Tactic

/-!
# The canonical circle layout of a finite controller--phase product

Each four-coordinate clock block consists of two geometrically distinct
circles:

```
              controller circle (r,s),   phase circle (c,d).
```

Thus a product of `q` clocks has `2q` compact circle blocks.  This module
defines the canonical assignment

```
             Fin (q * 4) → Fin (q * 2)
```

using the same `finProdFinEquiv` convention as the polynomial product
compiler.  It proves that the corresponding block dot product restricts
to the expected two-coordinate dot product and that the compiled product
field is tangent to every one of these circles at every ambient point.

The result is intended for mixed compactifications: controller and phase
coordinates can remain literal compact blocks while unrelated affine
coordinates are centrally compactified.
-/

namespace HGAS.Clocks.ControllerPhaseProductCircleLayout

open HGAS

variable {q : ℕ}

/-- Two circle blocks occur inside each four-coordinate clock. -/
abbrev localCircleCount : ℕ := 2

/-- Total number of inherited circle blocks in a `q`-clock product. -/
abbrev circleCount (q : ℕ) : ℕ :=
  q * localCircleCount

/-- The local controller coordinates `(r,s)` belong to circle zero and
the phase coordinates `(c,d)` belong to circle one. -/
def localCircleBlock :
    Fin ControllerPolynomialCode.dimension →
      Fin localCircleCount :=
  ![0, 0, 1, 1]

/-- The global circle containing coordinate `j`. -/
def circleBlock
    (j : Fin (ControllerPhaseProductPolynomialCode.dimension q)) :
    Fin (circleCount q) :=
  let p := finProdFinEquiv.symm j
  finProdFinEquiv (p.1, localCircleBlock p.2)

/-- The global circle indexed by clock `a` and local circle `c`. -/
def circleEmbedding
    (a : Fin q) (c : Fin localCircleCount) :
    Fin (circleCount q) :=
  finProdFinEquiv (a, c)

@[simp]
theorem circleBlock_blockEmbedding
    (a : Fin q) (i : Fin ControllerPolynomialCode.dimension) :
    circleBlock
        (ControllerPhaseProductPolynomialCode.blockEmbedding a i) =
      circleEmbedding a (localCircleBlock i) := by
  simp [circleBlock, circleEmbedding,
    ControllerPhaseProductPolynomialCode.blockEmbedding,
    PolynomialFiniteProductCode.blockEmbedding]

/-- Dot product restricted to one local circle of one clock. -/
def localCircleDot
    {R : Type*} [CommRing R]
    (x v : Fin ControllerPolynomialCode.dimension → R)
    (c : Fin localCircleCount) : R :=
  ∑ i, if localCircleBlock i = c then x i * v i else 0

@[simp]
theorem localCircleDot_controller
    {R : Type*} [CommRing R]
    (x v : Fin ControllerPolynomialCode.dimension → R) :
    localCircleDot x v 0 =
      x ControllerPolynomialCode.rIndex *
          v ControllerPolynomialCode.rIndex +
        x ControllerPolynomialCode.sIndex *
          v ControllerPolynomialCode.sIndex := by
  simp [localCircleDot, localCircleBlock,
    ControllerPolynomialCode.dimension,
    ControllerPolynomialCode.rIndex,
    ControllerPolynomialCode.sIndex,
    Fin.sum_univ_succ]

@[simp]
theorem localCircleDot_phase
    {R : Type*} [CommRing R]
    (x v : Fin ControllerPolynomialCode.dimension → R) :
    localCircleDot x v 1 =
      x ControllerPolynomialCode.cIndex *
          v ControllerPolynomialCode.cIndex +
        x ControllerPolynomialCode.dIndex *
          v ControllerPolynomialCode.dIndex := by
  simp [localCircleDot, localCircleBlock,
    ControllerPolynomialCode.dimension,
    ControllerPolynomialCode.cIndex,
    ControllerPolynomialCode.dIndex,
    Fin.sum_univ_succ]

/-- Dot product restricted to one global circle block. -/
def circleDot
    {R : Type*} [CommRing R]
    (x v :
      Fin (ControllerPhaseProductPolynomialCode.dimension q) → R)
    (c : Fin (circleCount q)) : R :=
  ∑ j, if circleBlock j = c then x j * v j else 0

/-- A global circle dot product is exactly the corresponding local
four-coordinate dot product. -/
theorem circleDot_circleEmbedding
    {R : Type*} [CommRing R]
    (x v :
      Fin (ControllerPhaseProductPolynomialCode.dimension q) → R)
    (a : Fin q) (c : Fin localCircleCount) :
    circleDot x v (circleEmbedding a c) =
      localCircleDot
        (x ∘
          ControllerPhaseProductPolynomialCode.blockEmbedding a)
        (v ∘
          ControllerPhaseProductPolynomialCode.blockEmbedding a)
        c := by
  unfold circleDot localCircleDot
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  simp only [circleBlock, circleEmbedding,
    finProdFinEquiv.symm_apply_apply,
    ControllerPhaseProductPolynomialCode.blockEmbedding,
    PolynomialFiniteProductCode.blockEmbedding,
    Function.comp_apply]
  simp only [Equiv.apply_eq_iff_eq, Prod.mk.injEq]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hba
    simp [hba]
  · simp

/-- The finite-product controller field is tangent to every inherited
controller and phase circle on structured states. -/
theorem fieldCode_circleDot
    (parameters : Fin q → RationalCode)
    (z :
      ControllerPhaseProductPolynomialCode.StateFamily q ℝ)
    (a : Fin q) (c : Fin localCircleCount) :
    circleDot
        (ControllerPhaseProductPolynomialCode.point z)
        (PolynomialFieldCode.realize
          (ControllerPhaseProductPolynomialCode.fieldCode parameters)
          (ControllerPhaseProductPolynomialCode.point z))
        (circleEmbedding a c) = 0 := by
  rw [circleDot_circleEmbedding]
  rw [ControllerPhaseProductPolynomialCode.realize_fieldCode]
  fin_cases c
  · simpa [ControllerPhaseProductPolynomialCode.point,
      ControllerPhaseProductPolynomialCode.blockEmbedding,
      ControllerPhaseProductPolynomialCode.vectorField,
      ControllerPolynomialCode.point,
      ControllerPolynomialCode.vectorField,
      ControllerPolynomialCode.rIndex,
      ControllerPolynomialCode.sIndex,
      Controller.controllerDot] using
      (Controller.controllerField_tangent
        (RationalCode.decode (parameters a) : ℝ)
        (z a).controller)
  · simpa [ControllerPhaseProductPolynomialCode.point,
      ControllerPhaseProductPolynomialCode.blockEmbedding,
      ControllerPhaseProductPolynomialCode.vectorField,
      ControllerPolynomialCode.point,
      ControllerPolynomialCode.vectorField,
      ControllerPolynomialCode.cIndex,
      ControllerPolynomialCode.dIndex,
      Controller.phaseDot] using
      (Controller.lockedPhaseField_tangent
        (RationalCode.decode (parameters a) : ℝ)
        (z a).controller (z a).phase)

/-- Ambient form: tangency holds without assuming any circle equation. -/
theorem fieldCode_circleDot_arbitrary
    (parameters : Fin q → RationalCode)
    (x :
      Fin (ControllerPhaseProductPolynomialCode.dimension q) → ℝ)
    (c : Fin (circleCount q)) :
    circleDot x
        (PolynomialFieldCode.realize
          (ControllerPhaseProductPolynomialCode.fieldCode parameters) x)
        c = 0 := by
  obtain ⟨⟨a, d⟩, rfl⟩ := finProdFinEquiv.surjective c
  let z := ControllerPhaseProductPolynomialCode.state x
  have hx :
      ControllerPhaseProductPolynomialCode.point z = x :=
    ControllerPhaseProductPolynomialCode.point_state x
  rw [← hx]
  exact fieldCode_circleDot parameters z a d

end HGAS.Clocks.ControllerPhaseProductCircleLayout
