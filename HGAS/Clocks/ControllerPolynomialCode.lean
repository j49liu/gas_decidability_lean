import HGAS.Clocks.Controller
import HGAS.Foundation.PolynomialDifferentiationCode
import Mathlib.Tactic

/-!
# Finite polynomial syntax for one radical controller and phase clock

For a rational parameter `p`, the clock block consists of two unit circles:

```
 r' = -s (p r² - 1),       s' = r (p r² - 1),
 c' = -(p r) d,            d' = (p r) c.
```

The first circle forces every invariant probability onto the four locked
controller equilibria.  At such an equilibrium the second circle rotates
with signed frequency `√p`.  The analytic invariant-measure statements are
proved in `ControllerFlow` and `RadicalClock`; this file supplies their
literal rational sparse-polynomial implementation.

The four real coordinates are ordered `(r,s,c,d)`.  We prove exact ambient
semantics without imposing the two circle equations, and record tangency of
both two-coordinate blocks.
-/

namespace HGAS.Clocks

open HGAS

/-- One controller circle together with the phase circle it drives. -/
@[ext]
structure ControllerPhaseState (R : Type*) where
  controller : Controller.ControllerState R
  phase : Controller.PhaseState R

namespace ControllerPolynomialCode

abbrev dimension : ℕ := 4

def rIndex : Fin dimension := 0
def sIndex : Fin dimension := 1
def cIndex : Fin dimension := 2
def dIndex : Fin dimension := 3

def point
    (z : ControllerPhaseState ℝ) : Fin dimension → ℝ :=
  ![z.controller.r, z.controller.s, z.phase.c, z.phase.d]

def state
    (x : Fin dimension → ℝ) : ControllerPhaseState ℝ where
  controller := ⟨x rIndex, x sIndex⟩
  phase := ⟨x cIndex, x dIndex⟩

@[simp]
theorem state_point (z : ControllerPhaseState ℝ) :
    state (point z) = z := by
  ext <;>
    simp [state, point, rIndex, sIndex, cIndex, dIndex]

@[simp]
theorem point_state (x : Fin dimension → ℝ) :
    point (state x) = x := by
  funext i
  fin_cases i <;> change x _ = x _ <;>
    apply congrArg x <;> rfl

def rCode : PolynomialCode dimension :=
  PolynomialCode.varCode rIndex

def sCode : PolynomialCode dimension :=
  PolynomialCode.varCode sIndex

def cCode : PolynomialCode dimension :=
  PolynomialCode.varCode cIndex

def dCode : PolynomialCode dimension :=
  PolynomialCode.varCode dIndex

/-- Code of `p r²-1`. -/
def mismatchCode (p : RationalCode) :
    PolynomialCode dimension :=
  PolynomialCode.sub
    (PolynomialCode.mul
      (PolynomialCode.constant p)
      (PolynomialCode.pow rCode 2))
    PolynomialCode.one

def rFieldCode (p : RationalCode) :
    PolynomialCode dimension :=
  PolynomialCode.neg
    (PolynomialCode.mul sCode (mismatchCode p))

def sFieldCode (p : RationalCode) :
    PolynomialCode dimension :=
  PolynomialCode.mul rCode (mismatchCode p)

def cFieldCode (p : RationalCode) :
    PolynomialCode dimension :=
  PolynomialCode.neg
    (PolynomialCode.mul
      (PolynomialCode.mul
        (PolynomialCode.constant p) rCode)
      dCode)

def dFieldCode (p : RationalCode) :
    PolynomialCode dimension :=
  PolynomialCode.mul
    (PolynomialCode.mul
      (PolynomialCode.constant p) rCode)
    cCode

/-- Complete rational polynomial field on `(r,s,c,d)`. -/
def fieldCode (p : RationalCode) :
    PolynomialFieldCode dimension :=
  ![rFieldCode p, sFieldCode p, cFieldCode p, dFieldCode p]

/-- Structured algebraic velocity of the controller--phase block. -/
def vectorField
    (p : ℝ) (z : ControllerPhaseState ℝ) :
    ControllerPhaseState ℝ where
  controller := Controller.controllerField p z.controller
  phase := Controller.lockedPhaseField p z.controller z.phase

@[simp]
theorem realize_fieldCode
    (p : RationalCode) (z : ControllerPhaseState ℝ) :
    PolynomialFieldCode.realize (fieldCode p) (point z) =
      point (vectorField (RationalCode.decode p) z) := by
  funext i
  fin_cases i <;>
    simp [PolynomialFieldCode.realize_apply, fieldCode,
      rFieldCode, sFieldCode, cFieldCode, dFieldCode,
      mismatchCode, rCode, sCode, cCode, dCode,
      point, vectorField, rIndex, sIndex, cIndex, dIndex,
      Controller.controllerField, Controller.mismatch,
      Controller.lockedPhaseField, Controller.phaseField,
      Controller.lockedFrequency]

/-- Ambient version: every real point is first reassembled into the
structured state. -/
@[simp]
theorem realize_fieldCode_arbitrary
    (p : RationalCode) (x : Fin dimension → ℝ) :
    PolynomialFieldCode.realize (fieldCode p) x =
      point
        (vectorField (RationalCode.decode p) (state x)) := by
  have h := realize_fieldCode p (state x)
  simpa using h

/-- The controller component of the coded field is tangent to its circle. -/
theorem controller_tangent
    (p : RationalCode) (z : ControllerPhaseState ℝ) :
    z.controller.r *
          (PolynomialFieldCode.realize
            (fieldCode p) (point z) rIndex) +
        z.controller.s *
          (PolynomialFieldCode.realize
            (fieldCode p) (point z) sIndex) = 0 := by
  rw [realize_fieldCode]
  exact Controller.controllerField_tangent
    (RationalCode.decode p : ℝ) z.controller

/-- The driven phase component is tangent to its circle. -/
theorem phase_tangent
    (p : RationalCode) (z : ControllerPhaseState ℝ) :
    z.phase.c *
          (PolynomialFieldCode.realize
            (fieldCode p) (point z) cIndex) +
        z.phase.d *
          (PolynomialFieldCode.realize
            (fieldCode p) (point z) dIndex) = 0 := by
  rw [realize_fieldCode]
  exact Controller.lockedPhaseField_tangent
    (RationalCode.decode p : ℝ) z.controller z.phase

end ControllerPolynomialCode

end HGAS.Clocks
