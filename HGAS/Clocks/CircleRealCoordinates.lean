import Mathlib.Analysis.Complex.Circle
import Mathlib.Tactic

/-!
# Real coordinate charts for the unit circle

The clock compilers use two real coordinates while the analytic flows use
Mathlib's multiplicative unit circle `Circle`.  This file gives the exact
homeomorphism between those representations.  It is intentionally
independent of any particular vector field.
-/

noncomputable section

open Complex

namespace HGAS.Clocks.CircleRealCoordinates

/-- A pair of real coordinates satisfying the unit-circle equation. -/
abbrev State :=
  {x : Fin 2 → ℝ // x 0 ^ 2 + x 1 ^ 2 = 1}

/-- Real and imaginary parts of a unit complex number. -/
def point (z : Circle) : Fin 2 → ℝ :=
  ![(z : ℂ).re, (z : ℂ).im]

theorem point_mem (z : Circle) :
    point z 0 ^ 2 + point z 1 ^ 2 = 1 := by
  simpa [point, Complex.normSq_apply, pow_two] using
    Circle.normSq_coe z

/-- Reassemble a unit complex number from two real circle coordinates. -/
def circle (x : State) : Circle :=
  ⟨Complex.ofReal (x.1 0) + Complex.ofReal (x.1 1) * Complex.I, by
    apply mem_sphere_zero_iff_norm.2
    have hsquare :
        ‖Complex.ofReal (x.1 0) +
            Complex.ofReal (x.1 1) * Complex.I‖ ^ 2 = 1 := by
      rw [← normSq_eq_norm_sq]
      simpa [Complex.normSq_apply, pow_two] using x.2
    nlinarith [norm_nonneg
      (Complex.ofReal (x.1 0) +
        Complex.ofReal (x.1 1) * Complex.I)]⟩

@[simp]
theorem circle_coe (x : State) :
    (circle x : ℂ) =
      Complex.ofReal (x.1 0) +
        Complex.ofReal (x.1 1) * Complex.I :=
  rfl

@[simp]
theorem circle_re (x : State) :
    (circle x : ℂ).re = x.1 0 := by
  simp [circle]

@[simp]
theorem circle_im (x : State) :
    (circle x : ℂ).im = x.1 1 := by
  simp [circle]

@[simp]
theorem circle_point (z : Circle) :
    circle ⟨point z, point_mem z⟩ = z := by
  apply Circle.ext
  apply Complex.ext <;>
    simp [circle, point]

@[simp]
theorem point_circle (x : State) :
    point (circle x) = x.1 := by
  funext i
  fin_cases i <;>
    simp [point]

theorem continuous_point :
    Continuous point := by
  unfold point
  fun_prop

theorem continuous_circle :
    Continuous circle := by
  apply Continuous.subtype_mk
  have h0 : Continuous (fun x : State ↦ x.1 0) :=
    (continuous_apply 0).comp continuous_subtype_val
  have h1 : Continuous (fun x : State ↦ x.1 1) :=
    (continuous_apply 1).comp continuous_subtype_val
  exact
    (Complex.continuous_ofReal.comp h0).add
      ((Complex.continuous_ofReal.comp h1).mul continuous_const)

/-- Exact homeomorphism between `Circle` and a real algebraic circle. -/
def homeomorph : Circle ≃ₜ State where
  toFun z := ⟨point z, point_mem z⟩
  invFun := circle
  left_inv := circle_point
  right_inv x := by
    apply Subtype.ext
    exact point_circle x
  continuous_toFun :=
    continuous_point.subtype_mk _
  continuous_invFun :=
    continuous_circle

/-- The real algebraic circle is compact, transported from Mathlib's
multiplicative unit circle.  Exporting this instance lets finite clock
products inherit compactness automatically. -/
noncomputable instance instCompactSpaceState : CompactSpace State :=
  homeomorph.compactSpace

@[simp]
theorem homeomorph_apply (z : Circle) :
    (homeomorph z).1 = point z :=
  rfl

@[simp]
theorem homeomorph_symm_apply (x : State) :
    homeomorph.symm x = circle x :=
  rfl

end HGAS.Clocks.CircleRealCoordinates
