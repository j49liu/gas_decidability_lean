import HGAS.Clocks.RecurrentControllerFlow
import HGAS.Clocks.ControllerPhaseProductSphereFlow
import HGAS.Dynamics.ForwardRecurrenceEventualEquality
import HGAS.Lyapunov.CheckedRationalCertificateSoundness
import Mathlib.Tactic

/-!
# Recurrent normalized polynomial clock products are locked

This file bridges the ambient polynomial clock compiler and the explicit
circle flow.  It is phrased for an arbitrary trajectory in `ℝ^(4q)`, so it
can be reused independently of the arithmetic detector.

Assume:

* the trajectory solves the compiled controller--phase polynomial field
  for nonnegative time;
* every controller pair and every phase pair has squared radius one at
  every time; and
* the ambient trajectory is forward recurrent at time zero.

The radius equations turn the trajectory into a curve in the compact
clock-product sphere.  ODE uniqueness identifies its positive-time tail
with the canonical global sphere flow.  Recurrence then passes through
the continuous controller projection, and
`RecurrentControllerFlow` forces every initial controller to be one of
the four polynomial equilibria.
-/

noncomputable section

open Set

namespace HGAS.Clocks.RecurrentNormalizedControllerProduct

open HGAS
open ControllerPhaseProductSphereFlow

variable {q : ℕ}

/-- Lift an ambient normalized clock trajectory to the literal compact
clock-product sphere. -/
def sphereCurve
    (x :
      ℝ →
        Fin (ControllerPhaseProductPolynomialCode.dimension q) → ℝ)
    (hnormalized : ∀ t, OnClockCircles (x t))
    (t : ℝ) :
    ClockProductSphere q :=
  ⟨x t, hnormalized t⟩

@[simp]
theorem sphereCurve_val
    (x :
      ℝ →
        Fin (ControllerPhaseProductPolynomialCode.dimension q) → ℝ)
    (hnormalized : ∀ t, OnClockCircles (x t))
    (t : ℝ) :
    (sphereCurve x hnormalized t).1 = x t :=
  rfl

/-- Ambient recurrence lifts through the subtype once the entire curve
satisfies the defining radius equations. -/
theorem sphereCurve_forwardRecurrentAt
    (x :
      ℝ →
        Fin (ControllerPhaseProductPolynomialCode.dimension q) → ℝ)
    (hnormalized : ∀ t, OnClockCircles (x t))
    (hrec : ForwardRecurrentAt x 0) :
    ForwardRecurrentAt (sphereCurve x hnormalized) 0 := by
  obtain ⟨τ, hτ, hreturn⟩ := hrec
  refine ⟨τ, hτ, ?_⟩
  exact tendsto_subtype_rng.2 hreturn

/-- Read the `i`th analytic controller circle from a literal point of the
polynomial clock-product sphere. -/
def controllerProjection
    (i : Fin q) (x : ClockProductSphere q) : Circle :=
  (ControllerPhaseProductFlowPolynomial.analyticHomeomorph.symm
      (clockSphereHomeomorph x)).1 i

theorem continuous_controllerProjection (i : Fin q) :
    Continuous (controllerProjection i :
      ClockProductSphere q → Circle) := by
  exact
    (ControllerPhaseFlow.continuous_controllerProjection i).comp
      continuous_toAnalytic

/-- The projected circle coordinates are exactly the controller pair in
the corresponding ambient polynomial block. -/
theorem circleControllerState_controllerProjection
    (i : Fin q) (x : ClockProductSphere q) :
    ControllerFlow.circleControllerState
        (controllerProjection i x) =
      (ControllerPhaseProductPolynomialCode.state x.1 i).controller := by
  have h :=
    ControllerPhaseProductFlowPolynomial.structuredState_analyticHomeomorph
      (ControllerPhaseProductFlowPolynomial.analyticHomeomorph.symm
        (clockSphereHomeomorph x)) i
  have hcontroller := congrArg ControllerPhaseState.controller h
  simpa [controllerProjection, clockSphereHomeomorph] using
    hcontroller.symm

/-- The controller projection semiconjugates the sphere flow to the
one-controller flow. -/
theorem controllerProjection_clockSphereFlow
    (p : Fin q → ℝ) (hp : ∀ i, 1 < p i)
    (i : Fin q) (t : ℝ) (x : ClockProductSphere q) :
    controllerProjection i
        (clockSphereFlow p hp t x) =
      ControllerFlow.controllerFlow (p i) (hp i) t
        (controllerProjection i x) := by
  have h :=
    ControllerPhaseProductSphereFlow.toAnalytic_semiconj
      p hp t x
  exact congrArg (fun z ↦ z.1 i) h

/-- A normalized forward solution agrees on the positive ray with the
canonical global sphere-flow orbit through its initial state. -/
theorem sphereCurve_eq_clockSphereFlow_on_Ici
    (parameters : Fin q → RationalCode)
    (hp : ∀ i,
      (1 : ℝ) < (RationalCode.decode (parameters i) : ℝ))
    (x :
      ℝ →
        Fin (ControllerPhaseProductPolynomialCode.dimension q) → ℝ)
    (hnormalized : ∀ t, OnClockCircles (x t))
    (hx :
      IsForwardTrajectory
        (PolynomialFieldCode.realize
          (ControllerPhaseProductPolynomialCode.fieldCode parameters))
        x (x 0)) :
    ∀ t, 0 ≤ t →
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
      IsForwardTrajectory F canonical (x 0) := by
    constructor
    · change
        (clockSphereFlow
          (fun i ↦ (RationalCode.decode (parameters i) : ℝ))
          hp 0 (sphereCurve x hnormalized 0)).1 =
          x 0
      rw [(clockSphereFlow
        (fun i ↦ (RationalCode.decode (parameters i) : ℝ))
        hp).map_zero_apply]
      rfl
    · intro t ht
      exact
        (clockSphereFlow_isIntegralCurve parameters hp
          (sphereCurve x hnormalized 0) t).hasDerivWithinAt
  have heq :
      EqOn x canonical (Ici (0 : ℝ)) :=
    hx.eqOn_Ici_of_contDiff
      (contDiff_polynomialFieldCode_realize
        (ControllerPhaseProductPolynomialCode.fieldCode parameters))
      hcanonical
  intro t ht
  apply Subtype.ext
  exact heq ht

/-- **Reusable locking theorem.**  Every controller block of a recurrent,
unit-radius polynomial clock-product trajectory is locked at time zero. -/
theorem controller_equilibrium_at_zero
    (parameters : Fin q → RationalCode)
    (hp : ∀ i,
      (1 : ℝ) < (RationalCode.decode (parameters i) : ℝ))
    (x :
      ℝ →
        Fin (ControllerPhaseProductPolynomialCode.dimension q) → ℝ)
    (hnormalized : ∀ t, OnClockCircles (x t))
    (hx :
      IsForwardTrajectory
        (PolynomialFieldCode.realize
          (ControllerPhaseProductPolynomialCode.fieldCode parameters))
        x (x 0))
    (hrec : ForwardRecurrentAt x 0)
    (i : Fin q) :
    Controller.IsControllerEquilibrium
      (RationalCode.decode (parameters i) : ℝ)
      (ControllerPhaseProductPolynomialCode.state (x 0) i).controller := by
  let p : Fin q → ℝ :=
    fun j ↦ (RationalCode.decode (parameters j) : ℝ)
  let y : ℝ → ClockProductSphere q :=
    sphereCurve x hnormalized
  let y₀ : ClockProductSphere q := y 0
  let canonical : ℝ → ClockProductSphere q :=
    fun t ↦ clockSphereFlow p hp t y₀
  have hyrec : ForwardRecurrentAt y 0 :=
    sphereCurve_forwardRecurrentAt x hnormalized hrec
  have hycanonical : ForwardRecurrentAt canonical 0 := by
    apply hyrec.congr_of_eqOn_Ici (by norm_num)
    intro t ht
    exact
      sphereCurve_eq_clockSphereFlow_on_Ici
        parameters hp x hnormalized hx t ht
  have hcontrollerRec :
      ForwardRecurrentAt
        (fun t ↦
          ControllerFlow.controllerFlow
            (p i) (hp i) t (controllerProjection i y₀)) 0 := by
    have hprojected :=
      hycanonical.map (continuous_controllerProjection i)
    apply hprojected.congr_of_eqOn_Ici (by norm_num)
    intro t _
    exact controllerProjection_clockSphereFlow p hp i t y₀
  have hlocked :=
    ControllerFlow.polynomialEquilibrium_of_forwardRecurrentAt
      (p i) (hp i) (controllerProjection i y₀) hcontrollerRec
  simpa [p, y₀, y,
    circleControllerState_controllerProjection] using hlocked

end HGAS.Clocks.RecurrentNormalizedControllerProduct
