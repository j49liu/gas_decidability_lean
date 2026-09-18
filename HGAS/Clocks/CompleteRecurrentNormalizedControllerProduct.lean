import HGAS.Clocks.RecurrentNormalizedControllerProduct
import Mathlib.Tactic

/-!
# Complete recurrent normalized clock products have constant controllers

`RecurrentNormalizedControllerProduct` proves that recurrence locks every
initial controller.  For a complete integral curve one can say more:
uniqueness identifies the ambient polynomial trajectory with the
canonical clock-sphere flow for all real times, rather than only on the
positive ray.  Since a locked controller is a fixed point of its
one-controller flow, every controller pair is constant on the whole
trajectory.

This all-time statement is the interface needed by the complete
linked-Jacobi reverse crosswalk: its two controller readouts become fixed
complex scaling constants.
-/

noncomputable section

open Set

namespace HGAS.Clocks.CompleteRecurrentNormalizedControllerProduct

open HGAS
open ControllerPhaseProductSphereFlow
open RecurrentNormalizedControllerProduct

variable {q : ℕ}

/-- Two complete solutions of the same compiled clock field, with the
same value at time zero, agree at every real time.  Here the second
solution is the canonical clock-sphere orbit. -/
theorem sphereCurve_eq_clockSphereFlow
    (parameters : Fin q → RationalCode)
    (hp : ∀ i,
      (1 : ℝ) < (RationalCode.decode (parameters i) : ℝ))
    (x :
      ℝ →
        Fin (ControllerPhaseProductPolynomialCode.dimension q) → ℝ)
    (hnormalized : ∀ t, OnClockCircles (x t))
    (hx :
      IsIntegralCurve x
        (fun _ y ↦
          PolynomialFieldCode.realize
            (ControllerPhaseProductPolynomialCode.fieldCode parameters)
            y)) :
    ∀ t,
      sphereCurve x hnormalized t =
        clockSphereFlow
          (fun i ↦ (RationalCode.decode (parameters i) : ℝ))
          hp t (sphereCurve x hnormalized 0) := by
  let F :=
    PolynomialFieldCode.realize
      (ControllerPhaseProductPolynomialCode.fieldCode parameters)
  let canonical :
      ℝ →
        Fin (ControllerPhaseProductPolynomialCode.dimension q) → ℝ :=
    fun t ↦
      (clockSphereFlow
        (fun i ↦ (RationalCode.decode (parameters i) : ℝ))
        hp t (sphereCurve x hnormalized 0)).1
  have hcanonical :
      IsIntegralCurve canonical (fun _ y ↦ F y) :=
    clockSphereFlow_isIntegralCurve parameters hp
      (sphereCurve x hnormalized 0)
  have hzero : x 0 = canonical 0 := by
    change
      x 0 =
        (clockSphereFlow
          (fun i ↦ (RationalCode.decode (parameters i) : ℝ))
          hp 0 (sphereCurve x hnormalized 0)).1
    rw [(clockSphereFlow
      (fun i ↦ (RationalCode.decode (parameters i) : ℝ))
      hp).map_zero_apply]
    rfl
  have hF :
      ContDiff ℝ 1 F :=
    contDiff_polynomialFieldCode_realize
      (ControllerPhaseProductPolynomialCode.fieldCode parameters)
  intro t
  apply Subtype.ext
  change x t = canonical t
  by_cases ht : 0 ≤ t
  · have heq :=
      ode_solution_unique_Icc_right_of_contDiff
        (γ := x) (η := canonical) (a := 0) (b := t) hF
        hx.continuous.continuousOn
        (by
          intro s _
          exact (hx s).hasDerivWithinAt)
        hcanonical.continuous.continuousOn
        (by
          intro s _
          exact (hcanonical s).hasDerivWithinAt)
        hzero
    exact heq ⟨ht, le_rfl⟩
  · have ht' : t ≤ 0 := le_of_not_ge ht
    have heq :=
      ode_solution_unique_Icc_left_of_contDiff
        (γ := x) (η := canonical) (a := t) (b := 0) hF
        hx.continuous.continuousOn
        (by
          intro s _
          exact (hx s).hasDerivWithinAt)
        hcanonical.continuous.continuousOn
        (by
          intro s _
          exact (hcanonical s).hasDerivWithinAt)
        hzero
    exact heq ⟨le_rfl, ht'⟩

/-- Every controller block of a complete recurrent normalized polynomial
clock trajectory is constant for all real times. -/
theorem controller_state_eq_zero
    (parameters : Fin q → RationalCode)
    (hp : ∀ i,
      (1 : ℝ) < (RationalCode.decode (parameters i) : ℝ))
    (x :
      ℝ →
        Fin (ControllerPhaseProductPolynomialCode.dimension q) → ℝ)
    (hnormalized : ∀ t, OnClockCircles (x t))
    (hx :
      IsIntegralCurve x
        (fun _ y ↦
          PolynomialFieldCode.realize
            (ControllerPhaseProductPolynomialCode.fieldCode parameters)
            y))
    (hrec : ForwardRecurrentAt x 0)
    (t : ℝ) (i : Fin q) :
    (ControllerPhaseProductPolynomialCode.state (x t) i).controller =
      (ControllerPhaseProductPolynomialCode.state (x 0) i).controller := by
  let p : Fin q → ℝ :=
    fun j ↦ (RationalCode.decode (parameters j) : ℝ)
  let y₀ : ClockProductSphere q :=
    sphereCurve x hnormalized 0
  have hlock :
      Controller.IsControllerEquilibrium (p i)
        (ControllerPhaseProductPolynomialCode.state (x 0) i).controller := by
    exact
      controller_equilibrium_at_zero parameters hp x hnormalized
        ⟨rfl, fun s _ ↦ (hx s).hasDerivWithinAt⟩ hrec i
  have hmem :
      controllerProjection i y₀ ∈
        ControllerFlow.controllerEquilibria (p i) := by
    rw [ControllerFlow.mem_controllerEquilibria_iff_polynomialEquilibrium
      (p i) (hp i)]
    simpa [y₀,
      circleControllerState_controllerProjection] using hlock
  have hfixed :=
    ControllerFlow.isFlowFixedPoint_of_mem_controllerEquilibria
      (p i) (hp i) hmem t
  have hsphere :=
    sphereCurve_eq_clockSphereFlow
      parameters hp x hnormalized hx t
  have hprojected :=
    congrArg (controllerProjection i) hsphere
  rw [controllerProjection_clockSphereFlow p hp i t y₀] at hprojected
  rw [hfixed] at hprojected
  have hstates :=
    congrArg ControllerFlow.circleControllerState hprojected
  simpa [y₀,
    circleControllerState_controllerProjection] using hstates

end HGAS.Clocks.CompleteRecurrentNormalizedControllerProduct
