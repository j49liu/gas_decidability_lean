import HGAS.Arithmetic.NormalizedCorrectedCanonicalOrbitClosureChart
import HGAS.Arithmetic.CanonicalFixedDetectorFundamentalPhase
import HGAS.Clocks.ControllerPhaseProductTorusObservation
import HGAS.Clocks.LockedControllerPhaseCompleteCurve
import Mathlib.Tactic

/-!
# Fundamental torus phase on the canonical orbit closure

The finite central chart recovers an ordinary fixed-detector state at
every point of the canonical orbit closure.  Projecting that state to its
literal controller--phase block gives real pairs `(cᵢ,dᵢ)`.

On the dense canonical orbit these are the explicit locked phase circles.
Continuity therefore extends two facts to the whole component:

* every controller is the originally selected locked controller; and
* every phase pair has squared radius one.

The second fact lets us convert the real pairs continuously to
`UnitAddTorus`.  The resulting observation is not an abstract extension:
its Fourier characters are exactly the signed-power polynomial
characters used by the detector compiler.
-/

noncomputable section

open Function

namespace HGAS.NormalizedCorrectedCanonicalOrbitClosurePhase

open HGAS
open HGAS.Analysis
open HGAS.Clocks
open HGAS.Clocks.ControllerPhaseProductPolynomialCode
open HGAS.Modular
open HGAS.NormalizedCorrectedCanonicalOrbitClosureChart

variable {eqs vars : ℕ}

/-- Reassemble the full semantic detector state from a component point. -/
def rawState
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i))
    (b : (component parameters I controller).Space) :
    FixedDetectorPolynomialCode.State eqs vars :=
  FixedDetectorPolynomialCode.state
    (rawPoint parameters I controller hcontroller hlock b)

/-- Coordinate embedding of the literal clock product through all
subsequent detector-extension layers. -/
def clockEmbedding :
    Fin
        (ControllerPhaseProductPolynomialCode.dimension
          (CanonicalFixedDetectorTrajectory.clockCount eqs vars)) ↪
      Fin (FixedDetectorPolynomialCode.dimension eqs vars) :=
  (((ControllerProductLinkedJacobiFamilyPolynomialCode.controllersEmbedding).trans
      ComplexGaugeFamilyPolynomialCode.baseEmbedding).trans
    ComplexReciprocalFamilyPolynomialCode.baseEmbedding).trans
  PolynomialBlockCode.leftEmbedding

/-- The raw clock-coordinate projection of a component point. -/
def clockPoint
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i))
    (b : (component parameters I controller).Space) :
    Fin
        (ControllerPhaseProductPolynomialCode.dimension
          (CanonicalFixedDetectorTrajectory.clockCount eqs vars)) →
      ℝ :=
  rawPoint parameters I controller hcontroller hlock b ∘
    clockEmbedding

/-- The literal controller--phase product stored inside the recovered
detector state. -/
def clockState
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i))
    (b : (component parameters I controller).Space) :
    StateFamily
      (CanonicalFixedDetectorTrajectory.clockCount eqs vars) ℝ :=
  ControllerPhaseProductPolynomialCode.state
    (clockPoint parameters I controller hcontroller hlock b)

/-- Reassembling a detector point and then restricting along
`clockEmbedding` gives its literal clock-product point. -/
theorem clockProjection_eq_comp_clockEmbedding
    (x : Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ) :
    ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint
        (FixedDetectorPolynomialCode.state x).base.base.source =
      x ∘ (clockEmbedding (eqs := eqs) (vars := vars)) := by
  funext k
  simp [clockEmbedding,
    ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint,
    FixedDetectorPolynomialCode.state,
    DetectorPoissonReciprocalCode.state,
    ComplexReciprocalFamilyPolynomialCode.state,
    ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.state,
    ComplexGaugeFamilyPolynomialCode.baseEmbedding,
    ComplexGaugeFamilyPolynomialCode.state,
    ControllerProductLinkedJacobiFamilyPolynomialCode.state]

/-- The coordinate definition of `clockState` agrees with the semantic
clock block inside `rawState`. -/
theorem clockState_eq_recovered
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i))
    (b : (component parameters I controller).Space) :
    clockState parameters I controller hcontroller hlock b =
      (rawState
        parameters I controller hcontroller hlock b).base.base.source.controllers := by
  unfold clockState clockPoint rawState
  rw [← clockProjection_eq_comp_clockEmbedding]
  simp only [
    ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint,
    ControllerPhaseProductPolynomialCode.state_point]

theorem continuous_clockPoint
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i)) :
    Continuous
      (clockPoint parameters I controller hcontroller hlock) := by
  apply continuous_pi
  intro k
  exact
    (continuous_apply (clockEmbedding k)).comp
      (continuous_rawPoint parameters I controller hcontroller hlock)

/-- On the named dense orbit, affine recovery gives the fully aligned
canonical semantic detector state. -/
theorem rawState_orbitPoint
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i))
    (τ : ℝ) :
    rawState parameters I controller hcontroller hlock
        (orbitClosureBaseComponent.orbitPoint
          (layout := layout eqs vars)
          (E :=
            NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDegreeBound
              I)
          (M :=
            NormalizedCorrectedFixedDetectorCompactSourceCode.clearingExponent
              I)
          (P :=
            NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode
              parameters I)
          (seed parameters I controller) τ) =
      CanonicalFixedDetectorRawOrbitBound.canonicalRawState
        parameters I controller
        (NormalizedCorrectedCanonicalCompactTrajectory.physicalTime
          parameters I controller hlock τ) := by
  unfold rawState
  rw [rawPoint_orbitPoint]
  simp only [
    NormalizedCorrectedCanonicalCompactTrajectory.canonicalAffineCurve,
    NormalizedCorrectedCanonicalFixedDetectorCentralChart.canonicalAffinePoint,
    FixedDetectorPolynomialCode.state_point]

/-- The clock block on the dense orbit is exactly the explicit family of
constant controllers and rotating unit phases. -/
theorem clockState_orbitPoint
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i))
    (τ : ℝ) :
    clockState parameters I controller hcontroller hlock
        (orbitClosureBaseComponent.orbitPoint
          (layout := layout eqs vars)
          (E :=
            NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDegreeBound
              I)
          (M :=
            NormalizedCorrectedFixedDetectorCompactSourceCode.clearingExponent
              I)
          (P :=
            NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode
              parameters I)
          (seed parameters I controller) τ) =
      LockedControllerPhaseTrajectory.stateFamily
        parameters controller
        LockedControllerPhaseTrajectory.onePhase
        (NormalizedCorrectedCanonicalCompactTrajectory.physicalTime
          parameters I controller hlock τ) := by
  rw [clockState_eq_recovered]
  rw [rawState_orbitPoint]
  rfl

@[simp]
theorem clockState_controller_r
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i))
    (b : (component parameters I controller).Space)
    (i : Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars)) :
    (clockState parameters I controller hcontroller hlock b i).controller.r =
      clockPoint parameters I controller hcontroller hlock b
        (ControllerPhaseProductPolynomialCode.blockEmbedding
          i ControllerPolynomialCode.rIndex) := by
  have h :=
    congrFun
      (ControllerPhaseProductPolynomialCode.point_state
        (clockPoint parameters I controller hcontroller hlock b))
      (ControllerPhaseProductPolynomialCode.blockEmbedding
        i ControllerPolynomialCode.rIndex)
  simpa [ControllerPhaseProductPolynomialCode.point,
    ControllerPhaseProductPolynomialCode.blockEmbedding,
    ControllerPolynomialCode.point,
    ControllerPolynomialCode.rIndex] using h

@[simp]
theorem clockState_controller_s
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i))
    (b : (component parameters I controller).Space)
    (i : Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars)) :
    (clockState parameters I controller hcontroller hlock b i).controller.s =
      clockPoint parameters I controller hcontroller hlock b
        (ControllerPhaseProductPolynomialCode.blockEmbedding
          i ControllerPolynomialCode.sIndex) := by
  have h :=
    congrFun
      (ControllerPhaseProductPolynomialCode.point_state
        (clockPoint parameters I controller hcontroller hlock b))
      (ControllerPhaseProductPolynomialCode.blockEmbedding
        i ControllerPolynomialCode.sIndex)
  simpa [ControllerPhaseProductPolynomialCode.point,
    ControllerPhaseProductPolynomialCode.blockEmbedding,
    ControllerPolynomialCode.point,
    ControllerPolynomialCode.sIndex] using h

@[simp]
theorem clockState_phase_c
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i))
    (b : (component parameters I controller).Space)
    (i : Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars)) :
    (clockState parameters I controller hcontroller hlock b i).phase.c =
      clockPoint parameters I controller hcontroller hlock b
        (ControllerPhaseProductPolynomialCode.blockEmbedding
          i ControllerPolynomialCode.cIndex) := by
  have h :=
    congrFun
      (ControllerPhaseProductPolynomialCode.point_state
        (clockPoint parameters I controller hcontroller hlock b))
      (ControllerPhaseProductPolynomialCode.blockEmbedding
        i ControllerPolynomialCode.cIndex)
  simpa [ControllerPhaseProductPolynomialCode.point,
    ControllerPhaseProductPolynomialCode.blockEmbedding,
    ControllerPolynomialCode.point,
    ControllerPolynomialCode.cIndex] using h

@[simp]
theorem clockState_phase_d
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i))
    (b : (component parameters I controller).Space)
    (i : Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars)) :
    (clockState parameters I controller hcontroller hlock b i).phase.d =
      clockPoint parameters I controller hcontroller hlock b
        (ControllerPhaseProductPolynomialCode.blockEmbedding
          i ControllerPolynomialCode.dIndex) := by
  have h :=
    congrFun
      (ControllerPhaseProductPolynomialCode.point_state
        (clockPoint parameters I controller hcontroller hlock b))
      (ControllerPhaseProductPolynomialCode.blockEmbedding
        i ControllerPolynomialCode.dIndex)
  simpa [ControllerPhaseProductPolynomialCode.point,
    ControllerPhaseProductPolynomialCode.blockEmbedding,
    ControllerPolynomialCode.point,
    ControllerPolynomialCode.dIndex] using h

/-- Each real controller coordinate is continuous on the component. -/
theorem continuous_controller_r
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i))
    (i : Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars)) :
    Continuous fun b ↦
      ((clockState parameters I controller hcontroller hlock b i).controller.r) := by
  simp only [clockState_controller_r]
  exact
    (continuous_apply
      (ControllerPhaseProductPolynomialCode.blockEmbedding
        i ControllerPolynomialCode.rIndex)).comp
      (continuous_clockPoint
        parameters I controller hcontroller hlock)

theorem continuous_controller_s
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i))
    (i : Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars)) :
    Continuous fun b ↦
      ((clockState parameters I controller hcontroller hlock b i).controller.s) := by
  simp only [clockState_controller_s]
  exact
    (continuous_apply
      (ControllerPhaseProductPolynomialCode.blockEmbedding
        i ControllerPolynomialCode.sIndex)).comp
      (continuous_clockPoint
        parameters I controller hcontroller hlock)

theorem continuous_phase_c
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i))
    (i : Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars)) :
    Continuous fun b ↦
      ((clockState parameters I controller hcontroller hlock b i).phase.c) := by
  simp only [clockState_phase_c]
  exact
    (continuous_apply
      (ControllerPhaseProductPolynomialCode.blockEmbedding
        i ControllerPolynomialCode.cIndex)).comp
      (continuous_clockPoint
        parameters I controller hcontroller hlock)

theorem continuous_phase_d
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i))
    (i : Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars)) :
    Continuous fun b ↦
      ((clockState parameters I controller hcontroller hlock b i).phase.d) := by
  simp only [clockState_phase_d]
  exact
    (continuous_apply
      (ControllerPhaseProductPolynomialCode.blockEmbedding
        i ControllerPolynomialCode.dIndex)).comp
      (continuous_clockPoint
        parameters I controller hcontroller hlock)

/-- Every recovered controller is the same locked controller used to
define the seed orbit. -/
theorem controller_eq
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i))
    (b : (component parameters I controller).Space)
    (i : Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars)) :
    (clockState parameters I controller hcontroller hlock b i).controller =
      controller i := by
  apply Controller.ControllerState.ext
  · have h :=
      orbitClosureBaseComponent.eq_of_continuous_on_orbit
        (layout := layout eqs vars)
        (E :=
          NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDegreeBound I)
        (M :=
          NormalizedCorrectedFixedDetectorCompactSourceCode.clearingExponent I)
        (P :=
          NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode
            parameters I)
        (seed parameters I controller)
        (fun b ↦
          (clockState parameters I controller hcontroller hlock b i).controller.r)
        (fun _ ↦ (controller i).r)
        (continuous_controller_r
          parameters I controller hcontroller hlock i)
        continuous_const
        (fun τ ↦ by
          dsimp only
          rw [clockState_orbitPoint]
          rfl)
    exact congrFun h b
  · have h :=
      orbitClosureBaseComponent.eq_of_continuous_on_orbit
        (layout := layout eqs vars)
        (E :=
          NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDegreeBound I)
        (M :=
          NormalizedCorrectedFixedDetectorCompactSourceCode.clearingExponent I)
        (P :=
          NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode
            parameters I)
        (seed parameters I controller)
        (fun b ↦
          (clockState parameters I controller hcontroller hlock b i).controller.s)
        (fun _ ↦ (controller i).s)
        (continuous_controller_s
          parameters I controller hcontroller hlock i)
        continuous_const
        (fun τ ↦ by
          dsimp only
          rw [clockState_orbitPoint]
          rfl)
    exact congrFun h b

/-- Every recovered phase pair lies on its unit circle. -/
theorem phaseRadiusSq_eq_one
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i))
    (b : (component parameters I controller).Space)
    (i : Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars)) :
    Controller.phaseRadiusSq
        (clockState parameters I controller hcontroller hlock b i).phase =
      1 := by
  have h :=
    orbitClosureBaseComponent.eq_of_continuous_on_orbit
      (layout := layout eqs vars)
      (E :=
        NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDegreeBound I)
      (M :=
        NormalizedCorrectedFixedDetectorCompactSourceCode.clearingExponent I)
      (P :=
        NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode
          parameters I)
      (seed parameters I controller)
      (fun b ↦
        Controller.phaseRadiusSq
          (clockState parameters I controller hcontroller hlock b i).phase)
      (fun _ ↦ (1 : ℝ))
      (by
        unfold Controller.phaseRadiusSq
        exact
          (continuous_phase_c
              parameters I controller hcontroller hlock i).pow 2 |>.add
            ((continuous_phase_d
              parameters I controller hcontroller hlock i).pow 2))
      continuous_const
      (fun τ ↦ by
        dsimp only
        rw [clockState_orbitPoint]
        exact
          NormalizedCorrectedCanonicalFixedDetectorGraph.phasePath_radiusSq
            _ _ _)
  exact congrFun h b

/-- The fundamental additive-torus observation on the component. -/
def phase
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i)) :
    (component parameters I controller).Space →
      UnitAddTorus
        (Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars)) :=
  ControllerPhaseProductTorusObservation.phase
    (clockState parameters I controller hcontroller hlock)
    (phaseRadiusSq_eq_one
      parameters I controller hcontroller hlock)

theorem continuous_phase
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i)) :
    Continuous (phase parameters I controller hcontroller hlock) := by
  apply ControllerPhaseProductTorusObservation.continuous_phase
  · exact continuous_phase_c
      parameters I controller hcontroller hlock
  · exact continuous_phase_d
      parameters I controller hcontroller hlock

/-- Every torus Fourier character is exactly the corresponding literal
signed-power character of the recovered polynomial clock block. -/
theorem mFourier_phase
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i))
    (b : (component parameters I controller).Space)
    (a : Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) → ℤ) :
    UnitAddTorus.mFourier a
        (phase parameters I controller hcontroller hlock b) =
      ControllerPhaseProductCharacterCode.characterValue a
        (clockState parameters I controller hcontroller hlock b) :=
  ControllerPhaseProductTorusObservation.mFourier_phase
    (clockState parameters I controller hcontroller hlock)
    (phaseRadiusSq_eq_one
      parameters I controller hcontroller hlock)
    b a

/-! ## Dynamics of the phase observation -/

/-- Literal flattened clock curve along the physical-time detector
trajectory based at a component point. -/
def physicalClockPoint
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i))
    (b : (component parameters I controller).Space)
    (τ : ℝ) :
    Fin
        (ControllerPhaseProductPolynomialCode.dimension
          (CanonicalFixedDetectorTrajectory.clockCount eqs vars)) →
      ℝ :=
  ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint
    (FixedDetectorReverseTrajectoryCrosswalk.recoveredState
      (physicalCurve parameters I controller hcontroller hlock b)
      τ).base.base.source

/-- Structured clock state along the physical-time curve. -/
def physicalClockState
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i))
    (b : (component parameters I controller).Space)
    (τ : ℝ) :
    StateFamily
      (CanonicalFixedDetectorTrajectory.clockCount eqs vars) ℝ :=
  ControllerPhaseProductPolynomialCode.state
    (physicalClockPoint
      parameters I controller hcontroller hlock b τ)

/-- The physical flattened clock curve solves the literal product clock
field. -/
theorem physicalClockPoint_isIntegralCurve
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i))
    (b : (component parameters I controller).Space) :
    IsIntegralCurve
      (physicalClockPoint
        parameters I controller hcontroller hlock b)
      (fun _ y ↦
        PolynomialFieldCode.realize
          (ControllerPhaseProductPolynomialCode.fieldCode parameters) y) :=
  (physicalCurve_isStructuredTrajectory
    parameters I controller hcontroller hlock b).controllers

/-- At physical time zero, the physical clock state is the state recovered
directly from the component point. -/
theorem physicalClockState_zero
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i))
    (b : (component parameters I controller).Space) :
    physicalClockState
        parameters I controller hcontroller hlock b 0 =
      clockState parameters I controller hcontroller hlock b := by
  rw [clockState_eq_recovered]
  unfold physicalClockState physicalClockPoint
    FixedDetectorReverseTrajectoryCrosswalk.recoveredState
  rw [physicalCurve_zero]
  unfold rawState
  simp only [
    ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint,
    ControllerPhaseProductPolynomialCode.state_point]

/-- The initial controller read by the complete clock uniqueness theorem
is the originally selected controller. -/
theorem physicalInitialController_eq
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i))
    (b : (component parameters I controller).Space) :
    LockedControllerPhaseCompleteCurve.initialController
        (physicalClockPoint
          parameters I controller hcontroller hlock b) =
      controller := by
  funext i
  unfold LockedControllerPhaseCompleteCurve.initialController
  change
    (physicalClockState
      parameters I controller hcontroller hlock b 0 i).controller =
      controller i
  rw [physicalClockState_zero]
  exact controller_eq
    parameters I controller hcontroller hlock b i

/-- Initial unit-phase hypothesis for the complete clock uniqueness
theorem. -/
theorem physicalInitialPhase_unit
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i))
    (b : (component parameters I controller).Space) :
    ∀ i,
      Controller.phaseRadiusSq
          (ControllerPhaseProductPolynomialCode.state
            (physicalClockPoint
              parameters I controller hcontroller hlock b 0) i).phase =
        1 := by
  intro i
  change
    Controller.phaseRadiusSq
        (physicalClockState
          parameters I controller hcontroller hlock b 0 i).phase =
      1
  rw [physicalClockState_zero]
  exact phaseRadiusSq_eq_one
    parameters I controller hcontroller hlock b i

/-- Initial multiplicative circle phase of the physical clock curve. -/
def physicalInitialPhase
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i))
    (b : (component parameters I controller).Space) :
    Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) → Circle :=
  LockedControllerPhaseCompleteCurve.initialPhase
    (physicalClockPoint
      parameters I controller hcontroller hlock b)
    (physicalInitialPhase_unit
      parameters I controller hcontroller hlock b)

/-- Complete ODE uniqueness identifies every physical clock curve with
the explicit locked phase rotation through its own initial phase. -/
theorem physicalClockState_eq_stateFamily
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i))
    (b : (component parameters I controller).Space)
    (τ : ℝ) :
    physicalClockState
        parameters I controller hcontroller hlock b τ =
      LockedControllerPhaseTrajectory.stateFamily
        parameters controller
        (physicalInitialPhase
          parameters I controller hcontroller hlock b)
        τ := by
  have h :=
    LockedControllerPhaseCompleteCurve.state_curve_eq_stateFamily
      parameters
      (physicalClockPoint
        parameters I controller hcontroller hlock b)
      (physicalClockPoint_isIntegralCurve
        parameters I controller hcontroller hlock b)
      (physicalInitialPhase_unit
        parameters I controller hcontroller hlock b)
      (fun i ↦ by
        rw [physicalInitialController_eq
          parameters I controller hcontroller hlock b]
        exact hlock i)
      τ
  simpa only [physicalClockState, physicalInitialPhase,
    physicalInitialController_eq
      parameters I controller hcontroller hlock b] using h

/-- Direct physical time accumulated over compact time. -/
def directPhysicalTime
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i))
    (b : (component parameters I controller).Space)
    (t : ℝ) : ℝ :=
  PositiveIntegralClock.orderIso
    (physicalClock parameters I controller hcontroller hlock b) t

/-- Evaluating the inverse-clock physical curve at direct physical time
recovers the original compact-time affine curve. -/
theorem physicalCurve_directPhysicalTime
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i))
    (b : (component parameters I controller).Space)
    (t : ℝ) :
    physicalCurve parameters I controller hcontroller hlock b
        (directPhysicalTime
          parameters I controller hcontroller hlock b t) =
      rawPoint parameters I controller hcontroller hlock
        ((component parameters I controller).flow t b) := by
  unfold physicalCurve directPhysicalTime
  rw [OrderIso.symm_apply_apply]

/-- Clock states in compact and physical time agree under the direct
clock. -/
theorem physicalClockState_directPhysicalTime
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i))
    (b : (component parameters I controller).Space)
    (t : ℝ) :
    physicalClockState parameters I controller hcontroller hlock b
        (directPhysicalTime
          parameters I controller hcontroller hlock b t) =
      clockState parameters I controller hcontroller hlock
        ((component parameters I controller).flow t b) := by
  unfold physicalClockState physicalClockPoint
    FixedDetectorReverseTrajectoryCrosswalk.recoveredState
  rw [clockState_eq_recovered]
  rw [physicalCurve_directPhysicalTime]
  unfold rawState
  simp only [
    ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint,
    ControllerPhaseProductPolynomialCode.state_point]

/-- Compact-time clock states are explicit locked rotations evaluated at
the accumulated physical time. -/
theorem clockState_flow_eq_stateFamily
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i))
    (b : (component parameters I controller).Space)
    (t : ℝ) :
    clockState parameters I controller hcontroller hlock
        ((component parameters I controller).flow t b) =
      LockedControllerPhaseTrajectory.stateFamily
        parameters controller
        (physicalInitialPhase
          parameters I controller hcontroller hlock b)
        (directPhysicalTime
          parameters I controller hcontroller hlock b t) := by
  rw [← physicalClockState_directPhysicalTime]
  exact physicalClockState_eq_stateFamily
    parameters I controller hcontroller hlock b _

/-- The direct physical clock has instantaneous speed equal to the
compactification speed. -/
theorem directPhysicalTime_hasDerivAt
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i))
    (b : (component parameters I controller).Space)
    (t : ℝ) :
    HasDerivAt
      (directPhysicalTime
        parameters I controller hcontroller hlock b)
      (speed parameters I controller hcontroller hlock
        ((component parameters I controller).flow t b)) t := by
  simpa only [directPhysicalTime,
    PositiveIntegralClock.orderIso_apply] using
      (integralClock_hasDerivAt
        (physicalClock
          parameters I controller hcontroller hlock b).continuous t)

/-- Angular-frequency normalization: radians in the compiler equal
`2π` times turns in the additive torus. -/
theorem torusAngularFrequency_turnsFrequency
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (a : Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) → ℤ) :
    Analysis.torusAngularFrequency a
        (CanonicalFixedDetectorFundamentalPhase.turnsFrequency
          parameters controller) =
      Complex.I *
        (LockedControllerPhaseTrajectory.characterFrequency
          parameters controller a : ℂ) := by
  unfold Analysis.torusAngularFrequency
    CanonicalFixedDetectorFundamentalPhase.turnsFrequency
    RadicalClock.frequencyPairing
    LockedControllerPhaseTrajectory.characterFrequency
  have hsum :
      (∑ i,
          (a i : ℝ) *
            (LockedControllerPhaseTrajectory.angularVelocity
                parameters controller i /
              (2 * Real.pi))) =
        (∑ i,
          (a i : ℝ) *
            LockedControllerPhaseTrajectory.angularVelocity
              parameters controller i) /
          (2 * Real.pi) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum]
  push_cast
  field_simp [Real.pi_ne_zero]

/-- Orbitwise derivative of every torus character under the compact
time-changed base flow. -/
theorem mFourier_phase_flow_hasDerivAt
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i))
    (b : (component parameters I controller).Space)
    (a : Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) → ℤ)
    (t : ℝ) :
    HasDerivAt
      (fun s ↦
        UnitAddTorus.mFourier a
          (phase parameters I controller hcontroller hlock
            ((component parameters I controller).flow s b)))
      (((speed parameters I controller hcontroller hlock
            ((component parameters I controller).flow t b) : ℝ) : ℂ) *
        Analysis.torusAngularFrequency a
          (CanonicalFixedDetectorFundamentalPhase.turnsFrequency
            parameters controller) *
        UnitAddTorus.mFourier a
          (phase parameters I controller hcontroller hlock
            ((component parameters I controller).flow t b))) t := by
  let phase₀ :=
    physicalInitialPhase
      parameters I controller hcontroller hlock b
  let T :=
    directPhysicalTime
      parameters I controller hcontroller hlock b
  have hcharacter :=
    LockedControllerPhaseTrajectory.characterValue_hasDerivAt
      parameters controller phase₀ a (T t)
  have hcomp :=
    hcharacter.scomp t
      (directPhysicalTime_hasDerivAt
        parameters I controller hcontroller hlock b t)
  have hstate :
      ∀ s,
        ControllerPhaseProductCharacterCode.characterValue a
            (clockState parameters I controller hcontroller hlock
              ((component parameters I controller).flow s b)) =
          ControllerPhaseProductCharacterCode.characterValue a
            (LockedControllerPhaseTrajectory.stateFamily
              parameters controller phase₀ (T s)) := by
    intro s
    rw [clockState_flow_eq_stateFamily]
  rw [torusAngularFrequency_turnsFrequency]
  simpa only [mFourier_phase, hstate, T, phase₀,
    Function.comp_def, Complex.real_smul, mul_assoc,
    mul_left_comm, mul_comm] using hcomp

end HGAS.NormalizedCorrectedCanonicalOrbitClosurePhase
