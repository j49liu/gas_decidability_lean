import HGAS.Algebra.PolynomialFiniteProductCode
import HGAS.Clocks.ControllerPolynomialComputability
import HGAS.Clocks.ControllerPolynomialDegrees
import Mathlib.Tactic

/-!
# A finite product compiler for controller--phase clocks

One controller--phase clock occupies four real coordinates
`(r, s, c, d)`.  The first pair is the controller circle and the second is
the phase circle driven by that controller.  The complete construction uses
a fixed finite family of such clocks, with a different rational parameter
in each block.

This file packages an arbitrary `q`-tuple of clock parameters into one
literal rational polynomial vector field on `4q` coordinates.  The blocks
are flattened with the canonical equivalence

```
Fin q × Fin 4 ≃ Fin (q * 4).
```

The main interfaces deliberately expose both structured states and raw
Euclidean coordinates:

* `point` and `state` are mutually inverse;
* `realize_fieldCode` gives exact blockwise semantics;
* every controller and phase circle remains tangent block by block;
* the uniform raw degree is at most three; and
* for each fixed `q`, the compiler from a finite parameter tuple is
  primitive recursive, hence computable.

The construction is reusable: no primality, distinctness, positivity, or
invariant-measure hypothesis is needed at the algebraic compilation stage.
-/

namespace HGAS.Clocks.ControllerPhaseProductPolynomialCode

open HGAS

variable {q : ℕ}

/-- Total number of real coordinates occupied by `q` clocks. -/
abbrev dimension (q : ℕ) : ℕ :=
  q * ControllerPolynomialCode.dimension

/-- A structured family of `q` controller--phase states. -/
abbrev StateFamily (q : ℕ) (R : Type*) :=
  Fin q → ControllerPhaseState R

/-- The ambient coordinate occupied by local coordinate `i` in block `a`. -/
def blockEmbedding (a : Fin q) :
    Fin ControllerPolynomialCode.dimension ↪ Fin (dimension q) :=
  PolynomialFiniteProductCode.blockEmbedding a

/-- Flatten a structured clock family into its `4q` real coordinates. -/
def point (z : StateFamily q ℝ) : Fin (dimension q) → ℝ :=
  PolynomialFiniteProductCode.flattenPoint
    (fun a ↦ ControllerPolynomialCode.point (z a))

/-- Reassemble an arbitrary ambient point into its `q` clock blocks. -/
def state (x : Fin (dimension q) → ℝ) : StateFamily q ℝ :=
  fun a ↦
    ControllerPolynomialCode.state
      (PolynomialFiniteProductCode.unflattenPoint x a)

@[simp]
theorem state_point (z : StateFamily q ℝ) :
    state (point z) = z := by
  funext a
  simp [state, point]

@[simp]
theorem point_state (x : Fin (dimension q) → ℝ) :
    point (state x) = x := by
  simp [point, state]

/-- The family of four-dimensional local fields before variable lifting. -/
def localFieldFamily
    (p : Fin q → RationalCode) :
    Fin q → PolynomialFieldCode ControllerPolynomialCode.dimension :=
  fun a ↦ ControllerPolynomialCode.fieldCode (p a)

/-- Compile the block-diagonal `4q`-dimensional polynomial field. -/
def fieldCode
    (p : Fin q → RationalCode) :
    PolynomialFieldCode (dimension q) :=
  PolynomialFiniteProductCode.field (localFieldFamily p)

/-- The corresponding structured blockwise vector field. -/
def vectorField
    (p : Fin q → ℝ)
    (z : StateFamily q ℝ) :
    StateFamily q ℝ :=
  fun a ↦ ControllerPolynomialCode.vectorField (p a) (z a)

/-- Exact semantics on a structured family of clock states. -/
@[simp]
theorem realize_fieldCode
    (p : Fin q → RationalCode)
    (z : StateFamily q ℝ) :
    PolynomialFieldCode.realize (fieldCode p) (point z) =
      point
        (vectorField
          (fun a ↦ RationalCode.decode (p a)) z) := by
  simp [fieldCode, localFieldFamily, point, vectorField]

/-- Exact ambient semantics, with no circle equations imposed. -/
@[simp]
theorem realize_fieldCode_arbitrary
    (p : Fin q → RationalCode)
    (x : Fin (dimension q) → ℝ) :
    PolynomialFieldCode.realize (fieldCode p) x =
      point
        (vectorField
          (fun a ↦ RationalCode.decode (p a))
          (state x)) := by
  simpa using realize_fieldCode p (state x)

/-- Evaluation of one output coordinate only sees its own local block. -/
@[simp]
theorem realize_fieldCode_blockEmbedding
    (p : Fin q → RationalCode)
    (x : Fin (dimension q) → ℝ)
    (a : Fin q) (i : Fin ControllerPolynomialCode.dimension) :
    PolynomialFieldCode.realize (fieldCode p) x
        (blockEmbedding a i) =
      PolynomialFieldCode.realize
        (ControllerPolynomialCode.fieldCode (p a))
        (PolynomialFiniteProductCode.unflattenPoint x a) i := by
  have h :=
    congrFun
      (PolynomialFiniteProductCode.realize_field
        (F := localFieldFamily p) x)
      (PolynomialFiniteProductCode.blockEmbedding a i)
  simpa only [fieldCode, blockEmbedding,
    PolynomialFiniteProductCode.flattenPoint_blockEmbedding,
    localFieldFamily] using h

/-- Each controller output pair is tangent to its own controller circle. -/
theorem controller_tangent
    (p : Fin q → RationalCode)
    (z : StateFamily q ℝ)
    (a : Fin q) :
    (z a).controller.r *
          (PolynomialFieldCode.realize (fieldCode p) (point z)
            (blockEmbedding a ControllerPolynomialCode.rIndex)) +
        (z a).controller.s *
          (PolynomialFieldCode.realize (fieldCode p) (point z)
            (blockEmbedding a ControllerPolynomialCode.sIndex)) = 0 := by
  rw [realize_fieldCode_blockEmbedding,
    realize_fieldCode_blockEmbedding]
  simpa [point] using
    ControllerPolynomialCode.controller_tangent (p a) (z a)

/-- Each driven phase output pair is tangent to its own phase circle. -/
theorem phase_tangent
    (p : Fin q → RationalCode)
    (z : StateFamily q ℝ)
    (a : Fin q) :
    (z a).phase.c *
          (PolynomialFieldCode.realize (fieldCode p) (point z)
            (blockEmbedding a ControllerPolynomialCode.cIndex)) +
        (z a).phase.d *
          (PolynomialFieldCode.realize (fieldCode p) (point z)
            (blockEmbedding a ControllerPolynomialCode.dIndex)) = 0 := by
  rw [realize_fieldCode_blockEmbedding,
    realize_fieldCode_blockEmbedding]
  simpa [point] using
    ControllerPolynomialCode.phase_tangent (p a) (z a)

/-! ## Degree and effectivity ledgers -/

/-- A finite family of controller clocks still has uniform raw degree at
most three, independently of the number of blocks. -/
theorem fieldCode_termsDegreeLE
    (p : Fin q → RationalCode) :
    ∀ i, PolynomialCode.TermsDegreeLE 3 (fieldCode p i) := by
  apply PolynomialFiniteProductCode.field_termsDegreeLE
  intro a i
  exact ControllerPolynomialCode.fieldCode_termsDegreeLE (p a) i

/-- Constructing all local four-dimensional fields from the parameter tuple
is primitive recursive for each fixed number of blocks. -/
theorem localFieldFamily_primrec :
    Primrec (localFieldFamily :
      (Fin q → RationalCode) →
        (Fin q →
          PolynomialFieldCode ControllerPolynomialCode.dimension)) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro a
  exact
    ControllerPolynomialCode.fieldCode_primrec.comp
      (Primrec.fin_app.comp Primrec.id (Primrec.const a))

/-- The complete `q`-clock polynomial compiler is primitive recursive. -/
theorem fieldCode_primrec :
    Primrec (fieldCode :
      (Fin q → RationalCode) →
        PolynomialFieldCode (dimension q)) :=
  PolynomialFiniteProductCode.field_primrec.comp
    localFieldFamily_primrec

theorem fieldCode_computable :
    Computable (fieldCode :
      (Fin q → RationalCode) →
        PolynomialFieldCode (dimension q)) :=
  fieldCode_primrec.to_comp

end HGAS.Clocks.ControllerPhaseProductPolynomialCode
