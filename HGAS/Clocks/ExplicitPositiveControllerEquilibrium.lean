import HGAS.Clocks.ControllerFlow
import Mathlib.Tactic

/-!
# An explicit unit controller equilibrium

For a controller parameter `p > 1`, the polynomial controller field has
four equilibria on the unit circle.  This file names one of them without
introducing square-root coordinate bookkeeping.

Let `a = √(p - 1)`.  The vector `(1,a)` lies on the contracting
eigendirection because `a - a · 1 = 0`.  Radially normalizing this nonzero
vector gives a point of the unit circle, hence a controller state of unit
radius.  The eigendirection characterization then proves that this state
is an equilibrium of the literal cubic controller field.
-/

noncomputable section

namespace HGAS.Clocks.ExplicitPositiveControllerEquilibrium

open Controller
open ControllerFlow

/-- The unnormalized positive contracting eigenvector `(1,√(p-1))`. -/
def eigenvector (p : ℝ) : ℂ :=
  ⟨1, controllerExponent p⟩

theorem eigenvector_ne_zero (p : ℝ) :
    eigenvector p ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num [eigenvector] at hre

/-- The chosen positive eigendirection on the unit circle. -/
def circle (p : ℝ) : Circle :=
  normalizeToCircle (eigenvector p) (eigenvector_ne_zero p)

/-- The corresponding real two-coordinate controller state. -/
def state (p : ℝ) : ControllerState ℝ :=
  circleControllerState (circle p)

/-- The chosen state has unit squared radius by construction. -/
theorem state_radiusSq (p : ℝ) :
    controllerRadiusSq (state p) = 1 := by
  exact controllerRadiusSq_circleControllerState (circle p)

/-- The normalized eigenvector belongs to the controller equilibrium
set whenever `p > 1`. -/
theorem circle_mem_controllerEquilibria
    (p : ℝ) :
    circle p ∈ controllerEquilibria p := by
  rw [mem_controllerEquilibria_iff]
  right
  unfold circle
  rw [coe_normalizeToCircle]
  rw [contractingCoordinate_real_smul]
  simp [eigenvector, contractingCoordinate]

/-- The chosen state is an equilibrium of the literal polynomial
controller field. -/
theorem state_isControllerEquilibrium
    (p : ℝ) (hp : 1 < p) :
    IsControllerEquilibrium p (state p) := by
  exact
    (mem_controllerEquilibria_iff_polynomialEquilibrium
      p hp (circle p)).mp
      (circle_mem_controllerEquilibria p)

end HGAS.Clocks.ExplicitPositiveControllerEquilibrium
