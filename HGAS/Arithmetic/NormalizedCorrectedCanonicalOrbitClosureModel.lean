import HGAS.Analysis.RadicalTimeChangedTorusComponentFiniteGraph
import HGAS.Analysis.ScaledRealTorusFourierFamily
import HGAS.Arithmetic.NormalizedCorrectedCanonicalDriftFourierCrosswalk
import HGAS.Arithmetic.NormalizedCorrectedCanonicalOrbitClosurePhase
import Mathlib.Tactic

/-!
# The canonical orbit closure as a time-changed Fourier component

The preceding chart and phase modules construct, on the closure of the
canonical compact orbit, an affine detector state and a fundamental torus
phase.  This file proves that the two observations carry the same Fourier
identity everywhere on that closure.

The proof has a useful separation of roles.

* On the named dense orbit, affine recovery gives the explicit canonical
  detector state.  The previously proved arithmetic Fourier crosswalk
  therefore identifies the detector drift with its Fourier series.
* Both sides are continuous on the orbit closure.  Equality on the dense
  orbit consequently implies equality everywhere.
* The finite-base-chart formula contributes exactly the compactification
  speed and the rational accumulator scale.

The final definition packages these facts as the reusable
`RadicalTimeChangedTorusFourierComponent.Model` consumed by the
finite-graph theorem.
-/

noncomputable section

open Function

namespace HGAS.NormalizedCorrectedCanonicalOrbitClosureModel

open HGAS
open HGAS.Analysis
open HGAS.Analysis.NormalizedCorrectedCanonicalDriftFourierFamily
open HGAS.Clocks
open HGAS.CompactAccumulatorPipelineCode
open HGAS.NormalizedCorrectedCanonicalOrbitClosureChart
open HGAS.NormalizedCorrectedCanonicalOrbitClosurePhase

variable {eqs vars : ℕ}

/-- The semantic normalized detector drift varies continuously with a
point of the canonical orbit closure. -/
theorem continuous_rawDriftValue
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
      (fun b ↦
        NormalizedCorrectedFixedDetectorDriftCode.driftValue I
          (rawState parameters I controller hcontroller hlock b)) := by
  apply continuous_pi
  intro q
  have hpoly :=
    MvPolynomial.continuous_eval
      (MvPolynomial.map (algebraMap ℚ ℝ)
        (PolynomialCode.decode
          (NormalizedCorrectedFixedDetectorDriftCode.driftCode I q)))
  have hcomp :=
    hpoly.comp
      (continuous_rawPoint
        parameters I controller hcontroller hlock)
  simpa only [MvPolynomial.eval_map, ←
    NormalizedCorrectedFixedDetectorDriftCode.eval_driftCode,
    rawState, FixedDetectorPolynomialCode.point_state] using hcomp

/-- The complete unscaled real Fourier vector is continuous after
pullback by the phase observation. -/
theorem continuous_fourierVector
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
    (hnot : ¬ I.Solvable) :
    Continuous
      (fun b ↦
        realTorusFourierVector
          (Index I hnot)
          (coefficient I hnot)
          (exponent I hnot)
          (phase parameters I controller hcontroller hlock b)) := by
  apply continuous_pi
  intro q
  exact
    Complex.continuous_re.comp
      ((continuous_torusFourierSeries
          (coefficient I hnot q)
          (exponent I hnot q)
          (coefficient_summable I hnot q)).comp
        (continuous_phase
          parameters I controller hcontroller hlock))

/-- On the named dense orbit, the extracted phase evaluates every
Fourier character exactly as the canonical fundamental phase. -/
theorem mFourier_phase_orbitPoint
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
    (a : Fin (vars + eqs) → ℤ)
    (τ : ℝ) :
    UnitAddTorus.mFourier a
        (phase parameters I controller hcontroller hlock
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
            (seed parameters I controller) τ)) =
      UnitAddTorus.mFourier a
        (CanonicalFixedDetectorFundamentalPhase.fundamentalPhasePath
          parameters controller
          (NormalizedCorrectedCanonicalCompactTrajectory.physicalTime
            parameters I controller hlock τ)) := by
  rw [mFourier_phase]
  rw [clockState_orbitPoint]
  exact
    CanonicalFixedDetectorFundamentalPhase.characterValue_onePhase_eq_mFourier_fundamental
      parameters controller a _

/-- On the dense canonical orbit, the recovered semantic detector drift
is the unscaled Fourier vector at the extracted phase. -/
theorem rawDriftValue_orbitPoint_eq_fourier
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
    (hnot : ¬ I.Solvable)
    (τ : ℝ) :
    NormalizedCorrectedFixedDetectorDriftCode.driftValue I
        (rawState parameters I controller hcontroller hlock
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
            (seed parameters I controller) τ)) =
      realTorusFourierVector
        (Index I hnot)
        (coefficient I hnot)
        (exponent I hnot)
        (phase parameters I controller hcontroller hlock
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
          (seed parameters I controller) τ)) := by
  rw [rawState_orbitPoint]
  change
    NormalizedCorrectedFixedDetectorDriftCode.driftValue I
        (CorrectedCanonicalFixedDetectorMomentFourierCrosswalk.canonicalState
          parameters I controller
          (NormalizedCorrectedCanonicalCompactTrajectory.physicalTime
            parameters I controller hlock τ)) =
      _
  rw [
    NormalizedCorrectedCanonicalDriftFourierCrosswalk.canonical_driftValue_eq_realTorusFourierVector
      parameters I controller hcontroller hnot]
  funext q
  unfold realTorusFourierVector torusFourierSeries torusSeriesTerm
  apply congrArg Complex.re
  apply tsum_congr
  intro i
  rw [mFourier_phase_orbitPoint]

/-- By density and continuity, the canonical drift--Fourier identity holds
at every point of the selected orbit-closure component. -/
theorem rawDriftValue_eq_fourier
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
    (hnot : ¬ I.Solvable) :
    (fun b ↦
      NormalizedCorrectedFixedDetectorDriftCode.driftValue I
        (rawState parameters I controller hcontroller hlock b)) =
      (fun b ↦
        realTorusFourierVector
          (Index I hnot)
          (coefficient I hnot)
          (exponent I hnot)
          (phase parameters I controller hcontroller hlock b)) := by
  apply orbitClosureBaseComponent.eq_of_continuous_on_orbit
  · exact continuous_rawDriftValue
      parameters I controller hcontroller hlock
  · exact continuous_fourierVector
      parameters I controller hcontroller hlock hnot
  · exact rawDriftValue_orbitPoint_eq_fourier
      parameters I controller hcontroller hlock hnot

/-- The literal compact drift is speed times the Fourier vector whose
coefficients already include the rational accumulator gain. -/
theorem baseDrift_eq_scaledFourier
    (κ : RationalCode)
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
    (hnot : ¬ I.Solvable)
    (b : (component parameters I controller).Space) :
    baseDriftBCF
        (layout eqs vars)
        (NormalizedCorrectedFixedDetectorCompactSourceCode.clearingExponent I)
        κ
        (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode I)
        b =
      speed parameters I controller hcontroller hlock b •
        realTorusFourierVector
          (Index I hnot)
          (scaledRealCoefficient
            (RationalCode.decode κ : ℝ)
            (coefficient I hnot))
          (exponent I hnot)
          (phase parameters I controller hcontroller hlock b) := by
  funext q
  have hbase :=
    AllAffineCompactBaseChartTrajectory.baseDriftBCF_eq
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDegreeBound I)
      κ
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode I)
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode_termsAffineBlockDegreeLE
        I)
      (finiteBasePoint
        parameters I controller hcontroller hlock b)
      q
  change
    (baseDriftBCF
      (AllAffineCompactSourceChart.layout
        (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDimension
          eqs vars))
      (2 *
        NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDegreeBound I)
      κ
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode I))
        (finiteBasePoint
          parameters I controller hcontroller hlock b) q =
      _
  rw [hbase]
  change
    (RationalCode.decode κ : ℝ) *
          speed parameters I controller hcontroller hlock b *
        MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
          (rawPoint parameters I controller hcontroller hlock b)
          (PolynomialCode.decode
            (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode
              I q)) =
      _
  rw [← FixedDetectorPolynomialCode.point_state
    (rawPoint parameters I controller hcontroller hlock b)]
  change
    (RationalCode.decode κ : ℝ) *
          speed parameters I controller hcontroller hlock b *
        MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
          (FixedDetectorPolynomialCode.point
            (rawState parameters I controller hcontroller hlock b))
          (PolynomialCode.decode
            (NormalizedCorrectedFixedDetectorDriftCode.driftCode I q)) =
      _
  rw [NormalizedCorrectedFixedDetectorDriftCode.eval_driftCode]
  rw [congrFun
    (rawDriftValue_eq_fourier
      parameters I controller hcontroller hlock hnot) b]
  rw [realTorusFourierVector_scaledRealCoefficient]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The canonical orbit closure, with its extracted phase and compact
speed, is a time-changed radical-torus Fourier component whenever the
chosen controller frequencies have the displayed signed-radical form. -/
def model
    (κ : RationalCode)
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
    (hnot : ¬ I.Solvable)
    (scale : ℝ)
    (p : Fin (vars + eqs) → ℕ)
    (sign : Fin (vars + eqs) → ℤ)
    (hfrequency :
      CanonicalFixedDetectorFundamentalPhase.turnsFrequency
          parameters controller =
        ScaledRadicalClock.scaledSignedPrimeSqrtFrequency
          scale p sign) :
    RadicalTimeChangedTorusFourierComponent.Model
      (layout eqs vars)
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDegreeBound I)
      (NormalizedCorrectedFixedDetectorCompactSourceCode.clearingExponent I)
      κ
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode
        parameters I)
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode I)
      (Index I hnot)
      scale p sign
      (scaledRealCoefficient
        (RationalCode.decode κ : ℝ)
        (coefficient I hnot))
      (exponent I hnot) where
  component := component parameters I controller
  phase := phase parameters I controller hcontroller hlock
  phase_continuous :=
    continuous_phase parameters I controller hcontroller hlock
  speed := speed parameters I controller hcontroller hlock
  speedBound := 1
  speedBound_nonneg := zero_le_one
  speed_le := by
    intro b
    rw [abs_of_pos
      (speed_pos parameters I controller hcontroller hlock b)]
    exact speed_le_one parameters I controller hcontroller hlock b
  character_derivative := by
    intro b a t
    rw [← hfrequency]
    exact
      mFourier_phase_flow_hasDerivAt
        parameters I controller hcontroller hlock b a t
  drift_eq_fourier :=
    baseDrift_eq_scaledFourier
      κ parameters I controller hcontroller hlock hnot
  probability :=
    orbitClosureBaseComponent.probability
      (layout := layout eqs vars)
      (E :=
        NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDegreeBound I)
      (M :=
        NormalizedCorrectedFixedDetectorCompactSourceCode.clearingExponent I)
      (P :=
        NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode
          parameters I)
      (seed parameters I controller)

end HGAS.NormalizedCorrectedCanonicalOrbitClosureModel
