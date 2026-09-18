import HGAS.Clocks.ControllerFlow
import HGAS.Clocks.PhaseClockFlow
import HGAS.Dynamics.ContinuousPhaseSkewFlow
import Mathlib.Tactic

/-!
# The literal coupled controller--phase flow

For each index `i`, the polynomial clock block consists of a controller
circle `(rᵢ,sᵢ)` and a physical phase circle `(cᵢ,dᵢ)`.  The controller
follows

```text
 rᵢ' = -sᵢ (pᵢ rᵢ² - 1),    sᵢ' = rᵢ (pᵢ rᵢ² - 1),
```

and the phase has the time-dependent angular velocity `pᵢ rᵢ`:

```text
 cᵢ' = -(pᵢ rᵢ)dᵢ,          dᵢ' = (pᵢ rᵢ)cᵢ.
```

`ControllerFlow` gives the explicit controller flow.  We integrate the
continuous angular velocity along that flow and use the reusable
`ContinuousPhaseSkewFlow` construction.  The resulting object is a genuine
global continuous flow, not merely a formal vector-field expression.
-/

noncomputable section

open Complex Function
open scoped BoundedContinuousFunction

namespace HGAS.Clocks.ControllerPhaseFlow

variable {d : Type*} [Fintype d]

/-- Product of the explicit controller flows. -/
def controllerTorusFlow
    (p : d → ℝ) (hp : ∀ i, 1 < p i) :
    Flow ℝ (d → Circle) where
  toFun t z := fun i ↦
    HGAS.Clocks.ControllerFlow.controllerFlow (p i) (hp i) t (z i)
  cont' := by
    apply continuous_pi
    intro i
    exact
      (HGAS.Clocks.ControllerFlow.controllerFlow (p i) (hp i)).continuous
        continuous_fst
        ((continuous_apply i).comp continuous_snd)
  map_add' := by
    intro t u z
    funext i
    exact
      (HGAS.Clocks.ControllerFlow.controllerFlow (p i) (hp i)).map_add
        t u (z i)
  map_zero' := by
    intro z
    funext i
    exact
      (HGAS.Clocks.ControllerFlow.controllerFlow (p i) (hp i)).map_zero_apply
        (z i)

omit [Fintype d] in
@[simp]
theorem controllerTorusFlow_apply
    (p : d → ℝ) (hp : ∀ i, 1 < p i)
    (t : ℝ) (z : d → Circle) (i : d) :
    controllerTorusFlow p hp t z i =
      HGAS.Clocks.ControllerFlow.controllerFlow
        (p i) (hp i) t (z i) :=
  rfl

/-- The physical angular velocity supplied by controller `i`. -/
def angularVelocity
    (p : d → ℝ) (i : d) :
    (d → Circle) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun z ↦ p i * (z i : ℂ).re,
      continuous_const.mul
        (Complex.continuous_re.comp
          (continuous_subtype_val.comp (continuous_apply i)))⟩

omit [Fintype d] in
@[simp]
theorem angularVelocity_apply
    (p : d → ℝ) (i : d) (z : d → Circle) :
    angularVelocity p i z = p i * (z i : ℂ).re :=
  rfl

/-- State space: all controller circles followed by all physical phase
circles. -/
abbrev State (d : Type*) :=
  (d → Circle) × (d → Circle)

/-- The exact coupled controller--phase flow. -/
def controllerPhaseFlow
    (p : d → ℝ) (hp : ∀ i, 1 < p i) :
    Flow ℝ (State d) :=
  HGAS.Dynamics.ContinuousPhaseSkewFlow.phaseSkewFlow
    (controllerTorusFlow p hp) (angularVelocity p)

omit [Fintype d] in
@[simp]
theorem controllerPhaseFlow_controller
    (p : d → ℝ) (hp : ∀ i, 1 < p i)
    (t : ℝ) (z : State d) (i : d) :
    (controllerPhaseFlow p hp t z).1 i =
      HGAS.Clocks.ControllerFlow.controllerFlow
        (p i) (hp i) t (z.1 i) :=
  rfl

omit [Fintype d] in
@[simp]
theorem controllerPhaseFlow_phase
    (p : d → ℝ) (hp : ∀ i, 1 < p i)
    (t : ℝ) (z : State d) (i : d) :
    (controllerPhaseFlow p hp t z).2 i =
      Circle.exp
          (HGAS.Dynamics.orbitIntegral
            (controllerTorusFlow p hp)
            (angularVelocity p i) t z.1) *
        z.2 i :=
  rfl

omit [Fintype d] in
/-- Each controller coordinate is a continuous equivariant factor of the
coupled flow. -/
theorem controllerProjection_semiconj
    (p : d → ℝ) (hp : ∀ i, 1 < p i)
    (i : d) (t : ℝ) :
    Function.Semiconj (fun z : State d ↦ z.1 i)
      (controllerPhaseFlow p hp t)
      (HGAS.Clocks.ControllerFlow.controllerFlow
        (p i) (hp i) t) := by
  intro z
  rfl

omit [Fintype d] in
theorem continuous_controllerProjection
    (i : d) :
    Continuous (fun z : State d ↦ z.1 i) :=
  (continuous_apply i).comp continuous_fst

/-! ## Exact ODE semantics -/

omit [Fintype d] in
/-- The controller coordinates solve the literal cubic controller field. -/
theorem controllerPhaseFlow_solves_controllerField
    (p : d → ℝ) (hp : ∀ i, 1 < p i)
    (z : State d) (i : d) (t : ℝ) :
    HasDerivAt
        (fun u : ℝ ↦
          (HGAS.Clocks.ControllerFlow.circleControllerState
            ((controllerPhaseFlow p hp u z).1 i)).r)
        (HGAS.Clocks.Controller.controllerField (p i)
          (HGAS.Clocks.ControllerFlow.circleControllerState
            ((controllerPhaseFlow p hp t z).1 i))).r t ∧
      HasDerivAt
        (fun u : ℝ ↦
          (HGAS.Clocks.ControllerFlow.circleControllerState
            ((controllerPhaseFlow p hp u z).1 i)).s)
        (HGAS.Clocks.Controller.controllerField (p i)
          (HGAS.Clocks.ControllerFlow.circleControllerState
            ((controllerPhaseFlow p hp t z).1 i))).s t := by
  simpa only [controllerPhaseFlow_controller] using
    HGAS.Clocks.ControllerFlow.controllerFlow_solves_controllerField
      (p i) (hp i) (z.1 i) t

omit [Fintype d] in
/-- The physical phase coordinate solves the controller-driven phase
equation, in exact complex form. -/
theorem controllerPhaseFlow_solves_lockedPhaseField
    (p : d → ℝ) (hp : ∀ i, 1 < p i)
    (z : State d) (i : d) (t : ℝ) :
    HasDerivAt
      (fun u : ℝ ↦ ((controllerPhaseFlow p hp u z).2 i : ℂ))
      (HGAS.Clocks.PhaseClockFlow.phaseStateComplex
        (HGAS.Clocks.Controller.lockedPhaseField
          (p i)
          (HGAS.Clocks.ControllerFlow.circleControllerState
            ((controllerPhaseFlow p hp t z).1 i))
          (HGAS.Clocks.PhaseClockFlow.circlePhaseState
            ((controllerPhaseFlow p hp t z).2 i)))) t := by
  have h :=
    HGAS.Dynamics.ContinuousPhaseSkewFlow.hasDerivAt_phaseSkewFlow_coe
      (controllerTorusFlow p hp) (angularVelocity p) z i t
  simp only [HGAS.Clocks.Controller.lockedPhaseField]
  rw [HGAS.Clocks.PhaseClockFlow.phaseStateComplex_phaseField,
    HGAS.Clocks.PhaseClockFlow.phaseStateComplex_circlePhaseState]
  simpa only [controllerPhaseFlow, angularVelocity_apply,
    controllerPhaseFlow_controller,
    HGAS.Clocks.Controller.lockedPhaseField,
    HGAS.Clocks.Controller.lockedFrequency,
    HGAS.Clocks.ControllerFlow.circleControllerState_r] using h

end HGAS.Clocks.ControllerPhaseFlow
