import HGAS.Clocks.ControllerFlow
import HGAS.Dynamics.Recurrence
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# Forward-recurrent controller orbits are locked

For a controller parameter `p > 1`, the normalized controller flow on the
unit circle has four equilibria.  This file proves the pointwise statement
needed by the detector reduction:

> an orbit which returns arbitrarily late to its initial point must start
> at one of those four equilibria.

The proof uses the explicit hyperbolic coordinates from `ControllerFlow`.
Off the two eigenlines, the logarithmic height

```
  log |s + √(p-1) r| - log |s - √(p-1) r|
```

increases at the strictly positive constant speed `2 √(p-1)`.  Continuity
of this height at the initial point transports recurrence to the height
trajectory, while its linear escape rules recurrence out.

Only continuity at the returned-to point is needed.  The small local
mapping lemma below is therefore useful beyond this particular flow.
-/

noncomputable section

open Filter Topology

namespace HGAS

/-- Forward recurrence is preserved by an observation which is continuous
at the particular state to which the trajectory returns.  Global
continuity of the observation is unnecessary. -/
theorem ForwardRecurrentAt.map_continuousAt
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {γ : ℝ → X} {t₀ : ℝ}
    (hγ : ForwardRecurrentAt γ t₀)
    {f : X → Y} (hf : ContinuousAt f (γ t₀)) :
    ForwardRecurrentAt (fun t ↦ f (γ t)) t₀ := by
  obtain ⟨τ, hτ, hreturn⟩ := hγ
  exact ⟨τ, hτ, hf.tendsto.comp hreturn⟩

namespace Clocks.ControllerFlow

open Complex

/-- The controller height is continuous at every point off the two
eigenlines. -/
theorem continuousAt_controllerHeight
    (p : ℝ) (z : Circle)
    (hplus :
      expandingCoordinate (controllerExponent p) (z : ℂ) ≠ 0)
    (hminus :
      contractingCoordinate (controllerExponent p) (z : ℂ) ≠ 0) :
    ContinuousAt (controllerHeight p) z := by
  have hplusCont :
      ContinuousAt
        (fun w : Circle ↦
          expandingCoordinate (controllerExponent p) (w : ℂ)) z := by
    unfold expandingCoordinate
    fun_prop
  have hminusCont :
      ContinuousAt
        (fun w : Circle ↦
          contractingCoordinate (controllerExponent p) (w : ℂ)) z := by
    unfold contractingCoordinate
    fun_prop
  exact
    (hplusCont.log hplus).sub
      (hminusCont.log hminus)

/-- Off the equilibrium set, controller height tends to `+∞` along the
positive-time orbit. -/
theorem controllerHeight_flow_tendsto_atTop
    (p : ℝ) (hp : 1 < p) (z : Circle)
    (hz : z ∉ controllerEquilibria p) :
    Tendsto
      (fun t : ℝ ↦
        controllerHeight p (controllerFlow p hp t z))
      atTop atTop := by
  have hplus :
      expandingCoordinate (controllerExponent p) (z : ℂ) ≠ 0 := by
    intro hzero
    exact hz (Or.inl hzero)
  have hminus :
      contractingCoordinate (controllerExponent p) (z : ℂ) ≠ 0 := by
    intro hzero
    exact hz (Or.inr hzero)
  have hslope :
      0 < 2 * controllerExponent p :=
    mul_pos (by norm_num) (controllerExponent_pos hp)
  have hlinear :
      (fun t : ℝ ↦
        controllerHeight p (controllerFlow p hp t z)) =
      (fun t : ℝ ↦
        controllerHeight p z +
          (2 * controllerExponent p) * t) := by
    funext t
    rw [controllerHeight_flow p hp t z hplus hminus]
  rw [hlinear]
  exact
    tendsto_const_nhds.add_atTop
      (tendsto_id.const_mul_atTop hslope)

/-- A controller orbit outside the four equilibria is not forward
recurrent at time zero. -/
theorem not_forwardRecurrentAt_controllerFlow_of_not_mem
    (p : ℝ) (hp : 1 < p) (z : Circle)
    (hz : z ∉ controllerEquilibria p) :
    ¬ ForwardRecurrentAt
      (fun t : ℝ ↦ controllerFlow p hp t z) 0 := by
  have hplus :
      expandingCoordinate (controllerExponent p) (z : ℂ) ≠ 0 := by
    intro hzero
    exact hz (Or.inl hzero)
  have hminus :
      contractingCoordinate (controllerExponent p) (z : ℂ) ≠ 0 := by
    intro hzero
    exact hz (Or.inr hzero)
  intro hrec
  have hheightRec :
      ForwardRecurrentAt
        (fun t : ℝ ↦
          controllerHeight p (controllerFlow p hp t z)) 0 := by
    apply hrec.map_continuousAt
    rw [(controllerFlow p hp).map_zero_apply]
    exact continuousAt_controllerHeight p z hplus hminus
  exact
    not_forwardRecurrentAt_of_norm_tendsto_atTop
      (tendsto_norm_atTop_atTop.comp
        (controllerHeight_flow_tendsto_atTop p hp z hz))
      hheightRec

/-- **Pointwise controller locking.**  Every forward-recurrent orbit of
the normalized controller flow starts at a polynomial-controller
equilibrium. -/
theorem mem_controllerEquilibria_of_forwardRecurrentAt
    (p : ℝ) (hp : 1 < p) (z : Circle)
    (hrec :
      ForwardRecurrentAt
        (fun t : ℝ ↦ controllerFlow p hp t z) 0) :
    z ∈ controllerEquilibria p := by
  by_contra hz
  exact
    not_forwardRecurrentAt_controllerFlow_of_not_mem
      p hp z hz hrec

/-- Polynomial-language version of pointwise controller locking. -/
theorem polynomialEquilibrium_of_forwardRecurrentAt
    (p : ℝ) (hp : 1 < p) (z : Circle)
    (hrec :
      ForwardRecurrentAt
        (fun t : ℝ ↦ controllerFlow p hp t z) 0) :
    HGAS.Clocks.Controller.IsControllerEquilibrium p
      (circleControllerState z) := by
  exact
    (mem_controllerEquilibria_iff_polynomialEquilibrium p hp z).1
      (mem_controllerEquilibria_of_forwardRecurrentAt p hp z hrec)

end Clocks.ControllerFlow

end HGAS
