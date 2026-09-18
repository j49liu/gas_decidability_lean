import HGAS.Clocks.Controller
import HGAS.Clocks.RadicalClock
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# Exact flow and normalization of one phase clock

The polynomial phase equation

```
  c' = -ω d,      d' = ω c
```

has angular velocity `ω` in radians.  Mathlib's standard
`UnitAddCircle = ℝ/ℤ`, however, measures angles in turns.  Consequently its
translation frequency is `ω/(2π)`.

This module makes that conversion explicit.  It defines the literal circle
rotation flow, proves that its complex derivative is exactly the polynomial
phase field, and constructs the homeomorphic semiconjugacy from the
turn-coordinate translation flow.  The result is the missing normalization
bridge needed to instantiate the radical-clock Haar theorem with the actual
polynomial ODE.
-/

noncomputable section

open Complex Function

namespace HGAS.Clocks.PhaseClockFlow

/-- Rotation of the complex unit circle with angular velocity `ω`. -/
def phaseRotationFlow (ω : ℝ) : Flow ℝ Circle where
  toFun t z := Circle.exp (ω * t) * z
  cont' := by
    apply Continuous.mul
    · exact Circle.exp.continuous.comp
        (continuous_const.mul continuous_fst)
    · exact continuous_snd
  map_add' := by
    intro t u z
    rw [mul_add, Circle.exp_add]
    simp only [mul_assoc]
  map_zero' := by
    intro z
    simp

@[simp]
theorem phaseRotationFlow_apply
    (ω t : ℝ) (z : Circle) :
    phaseRotationFlow ω t z = Circle.exp (ω * t) * z :=
  rfl

/-- Translation of the unit additive circle with frequency measured in
turns per unit time. -/
def turnTranslationFlow (v : ℝ) : Flow ℝ UnitAddCircle where
  toFun t x := x + (t * v : UnitAddCircle)
  cont' := by
    apply Continuous.add
    · exact continuous_snd
    · exact QuotientAddGroup.continuous_mk.comp
        (continuous_fst.mul continuous_const)
  map_add' := by
    intro t u x
    rw [add_mul]
    simp only [QuotientAddGroup.mk_add]
    abel
  map_zero' := by
    intro x
    simp

@[simp]
theorem turnTranslationFlow_apply
    (v t : ℝ) (x : UnitAddCircle) :
    turnTranslationFlow v t x =
      x + (t * v : UnitAddCircle) :=
  rfl

/-- Convert angular velocity in radians to translation frequency in turns. -/
def radiansToTurnsFrequency (ω : ℝ) : ℝ :=
  ω / (2 * Real.pi)

/-- The canonical homeomorphism from the unit additive circle to the
complex unit circle. -/
def unitAddCircleHomeomorph : UnitAddCircle ≃ₜ Circle :=
  AddCircle.homeomorphCircle one_ne_zero

@[simp]
theorem unitAddCircleHomeomorph_apply
    (x : UnitAddCircle) :
    unitAddCircleHomeomorph x = AddCircle.toCircle x := by
  exact AddCircle.homeomorphCircle_apply one_ne_zero x

/-- Exact semiconjugacy, including the required factor `1/(2π)`. -/
theorem unitAddCircleHomeomorph_semiconj
    (ω t : ℝ) :
    Function.Semiconj unitAddCircleHomeomorph
      (turnTranslationFlow (radiansToTurnsFrequency ω) t)
      (phaseRotationFlow ω t) := by
  intro x
  simp only [turnTranslationFlow_apply, phaseRotationFlow_apply,
    unitAddCircleHomeomorph_apply, AddCircle.toCircle_add]
  rw [AddCircle.toCircle_apply_mk]
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by
    positivity
  have hangle :
      2 * Real.pi / 1 *
          (t * radiansToTurnsFrequency ω) =
        ω * t := by
    unfold radiansToTurnsFrequency
    field_simp [hpi]
  rw [hangle]
  exact mul_comm _ _

/-- Flow-semiconjugacy package for the same homeomorphism. -/
theorem unitAddCircleHomeomorph_isSemiconjugacy
    (ω : ℝ) :
    Flow.IsSemiconjugacy unitAddCircleHomeomorph
      (turnTranslationFlow (radiansToTurnsFrequency ω))
      (phaseRotationFlow ω) :=
  ⟨unitAddCircleHomeomorph.continuous,
    unitAddCircleHomeomorph.surjective,
    unitAddCircleHomeomorph_semiconj ω⟩

/-! ## Exact differential equation -/

/-- Reassemble a real phase-state vector as one complex number. -/
def phaseStateComplex
    (z : HGAS.Clocks.Controller.PhaseState ℝ) : ℂ :=
  Complex.ofReal z.c + Complex.ofReal z.d * Complex.I

/-- Read a circle point as the two real phase coordinates. -/
def circlePhaseState
    (z : Circle) : HGAS.Clocks.Controller.PhaseState ℝ :=
  ⟨(z : ℂ).re, (z : ℂ).im⟩

@[simp]
theorem phaseStateComplex_circlePhaseState
    (z : Circle) :
    phaseStateComplex (circlePhaseState z) = (z : ℂ) := by
  apply Complex.ext <;>
    simp [phaseStateComplex, circlePhaseState]

/-- Complex form of the real phase field. -/
theorem phaseStateComplex_phaseField
    (ω : ℝ) (z : HGAS.Clocks.Controller.PhaseState ℝ) :
    phaseStateComplex (HGAS.Clocks.Controller.phaseField ω z) =
      (ω : ℂ) * Complex.I * phaseStateComplex z := by
  apply Complex.ext <;>
    simp [phaseStateComplex, HGAS.Clocks.Controller.phaseField]

/-- The complex-valued circle orbit has the expected derivative at every
time. -/
theorem hasDerivAt_phaseRotationFlow_coe
    (ω t : ℝ) (z : Circle) :
    HasDerivAt
      (fun u : ℝ ↦ (phaseRotationFlow ω u z : ℂ))
      (((ω : ℂ) * Complex.I) *
        (phaseRotationFlow ω t z : ℂ)) t := by
  have hlinear :
      HasDerivAt
        (fun u : ℝ ↦ ((ω : ℂ) * (u : ℂ)) * Complex.I)
        ((ω : ℂ) * Complex.I) t := by
    have hmul :
        HasDerivAt
          (fun u : ℝ ↦ (ω : ℂ) * (u : ℂ))
          (ω : ℂ) t := by
      simpa only [mul_one] using
        ((hasDerivAt_id (t : ℂ)).const_mul (ω : ℂ)).comp_ofReal
    exact hmul.mul_const Complex.I
  have hexp :
      HasDerivAt
        (fun u : ℝ ↦
          Complex.exp
            (((ω : ℂ) * (u : ℂ)) * Complex.I))
        (Complex.exp
            (((ω : ℂ) * (t : ℂ)) * Complex.I) *
          ((ω : ℂ) * Complex.I)) t :=
    (Complex.hasDerivAt_exp _).comp t hlinear
  have hproduct := hexp.mul_const (z : ℂ)
  convert hproduct using 1
  · funext u
    simp only [phaseRotationFlow_apply, Circle.coe_mul,
      Circle.coe_exp]
    congr 2
    push_cast
    ring
  · simp only [phaseRotationFlow_apply, Circle.coe_mul,
      Circle.coe_exp]
    have harg :
        ((ω * t : ℝ) : ℂ) * Complex.I =
          (ω : ℂ) * (t : ℂ) * Complex.I := by
      push_cast
      ring
    rw [harg]
    ring

/-- Manuscript-facing ODE statement: the derivative of the literal circle
flow is exactly the complexification of `phaseField`. -/
theorem phaseRotationFlow_solves_phaseField
    (ω t : ℝ) (z : Circle) :
    HasDerivAt
      (fun u : ℝ ↦ (phaseRotationFlow ω u z : ℂ))
      (phaseStateComplex
        (HGAS.Clocks.Controller.phaseField ω
          (circlePhaseState (phaseRotationFlow ω t z)))) t := by
  rw [phaseStateComplex_phaseField,
    phaseStateComplex_circlePhaseState]
  exact hasDerivAt_phaseRotationFlow_coe ω t z

end HGAS.Clocks.PhaseClockFlow
