import HGAS.Clocks.CircleRealCoordinates
import HGAS.Clocks.LockedControllerPhaseCharacterFormula
import Mathlib.Tactic

/-!
# Complete locked controller--phase curves

The explicit path in `LockedControllerPhaseTrajectory` starts from a family
of unit phases and rotates each phase with its locked angular velocity.
This file proves the corresponding uniqueness statement.

Suppose a complete real curve solves the compiled controller--phase
polynomial ODE.  If its initial controllers are equilibria and all of its
initial phases have radius one, then the entire curve is exactly the
explicit locked path through its initial point.  In particular every
integral phase character has a constant phase factor times one complex
exponential.

The result is deliberately independent of the fixed detector.  It can be
reused for any complete solution of the finite controller--phase compiler.
-/

namespace HGAS.Clocks.LockedControllerPhaseCompleteCurve

open HGAS
open Complex
open ControllerPhaseProductPolynomialCode
open ControllerPhaseProductCharacterCode
open LockedControllerPhaseTrajectory

noncomputable section

variable {q : ℕ}

/-- Controller data read from the initial point of a complete raw curve. -/
def initialController
    (x : ℝ → Fin (dimension q) → ℝ) :
    Fin q → Controller.ControllerState ℝ :=
  fun i ↦ (state (x 0) i).controller

/-- The initial real phase pair, packaged as a point of the unit circle. -/
def initialPhase
    (x : ℝ → Fin (dimension q) → ℝ)
    (hphase :
      ∀ i,
        Controller.phaseRadiusSq (state (x 0) i).phase = 1) :
    Fin q → Circle :=
  fun i ↦
    CircleRealCoordinates.circle
      ⟨![(state (x 0) i).phase.c, (state (x 0) i).phase.d], by
        simpa [Controller.phaseRadiusSq] using hphase i⟩

/-- At time zero the explicit locked path recovers the literal initial
structured state. -/
theorem stateFamily_initial_eq
    (parameters : Fin q → RationalCode)
    (x : ℝ → Fin (dimension q) → ℝ)
    (hphase :
      ∀ i,
        Controller.phaseRadiusSq (state (x 0) i).phase = 1) :
    stateFamily parameters
        (initialController x) (initialPhase x hphase) 0 =
      state (x 0) := by
  funext i
  apply ControllerPhaseState.ext
  · rfl
  · apply Controller.PhaseState.ext
    · simp [stateFamily, phasePath, initialPhase,
        PhaseClockFlow.phaseRotationFlow_apply,
        PhaseClockFlow.circlePhaseState,
        CircleRealCoordinates.circle]
    · simp [stateFamily, phasePath, initialPhase,
        PhaseClockFlow.phaseRotationFlow_apply,
        PhaseClockFlow.circlePhaseState,
        CircleRealCoordinates.circle]

/-- A complete solution with locked initial controllers is the explicit
phase-rotation path through its initial point. -/
theorem state_curve_eq_stateFamily
    (parameters : Fin q → RationalCode)
    (x : ℝ → Fin (dimension q) → ℝ)
    (hx :
      IsIntegralCurve x
        (fun _ y ↦
          PolynomialFieldCode.realize (fieldCode parameters) y))
    (hphase :
      ∀ i,
        Controller.phaseRadiusSq (state (x 0) i).phase = 1)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (initialController x i))
    (t : ℝ) :
    state (x t) =
      stateFamily parameters
        (initialController x) (initialPhase x hphase) t := by
  let F : (Fin (dimension q) → ℝ) → (Fin (dimension q) → ℝ) :=
    PolynomialFieldCode.realize (fieldCode parameters)
  let canonical : ℝ → Fin (dimension q) → ℝ :=
    fun s ↦
      point
        (stateFamily parameters
          (initialController x) (initialPhase x hphase) s)
  have hcanonical :
      IsIntegralCurve canonical (fun _ y ↦ F y) := by
    simpa only [canonical, F] using
      point_stateFamily_isIntegralCurve parameters
        (initialController x) (initialPhase x hphase) hlock
  have hzero : x 0 = canonical 0 := by
    unfold canonical
    rw [stateFamily_initial_eq parameters x hphase]
    exact (point_state (x 0)).symm
  have hF : ContDiff ℝ 1 F :=
    contDiff_polynomialFieldCode_realize (fieldCode parameters)
  have heq : x t = canonical t := by
    by_cases ht : 0 ≤ t
    · have h :=
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
      exact h ⟨ht, le_rfl⟩
    · have ht' : t ≤ 0 := le_of_not_ge ht
      have h :=
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
      exact h ⟨le_rfl, ht'⟩
  rw [heq]
  simp only [canonical, state_point]

end

end HGAS.Clocks.LockedControllerPhaseCompleteCurve
