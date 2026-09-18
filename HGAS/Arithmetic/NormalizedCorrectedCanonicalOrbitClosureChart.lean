import HGAS.Analysis.OrbitClosureDenseOrbit
import HGAS.Arithmetic.FixedDetectorReverseTrajectoryCrosswalk
import HGAS.Arithmetic.NormalizedCorrectedCanonicalCompactTrajectory
import HGAS.Compiler.AllAffineCompactBaseChartTrajectory
import HGAS.Dynamics.IntegralCurveStateTimeChange
import HGAS.Dynamics.PositiveIntegralClockUniformLower
import Mathlib.Tactic

/-!
# The finite affine chart on the canonical orbit-closure component

The explicit canonical detector orbit stays uniformly away from the
central equator.  Since the squared central coordinate is continuous, the
same lower bound holds on the closure of that orbit.  Consequently every
point of the orbit closure has a canonical affine representative.

This file packages that observation and the associated two-sided change
of time.  For every point `b` of the component:

* `rawPoint b` is its recovered ordinary detector state;
* the compact orbit through `b` satisfies
  `z' = affineSpeed z • P z`;
* the affine speed is uniformly bounded below by a positive constant;
* its integral is therefore a global increasing clock; and
* inverse-clock reparametrization is a complete solution of the literal
  unscaled fixed-detector polynomial field.

The construction is independent of the no-instance Fourier family and is
therefore reusable in other analyses of the same compact compiler.
-/

noncomputable section

open Function Set

namespace HGAS.NormalizedCorrectedCanonicalOrbitClosureChart

open HGAS
open HGAS.Analysis
open HGAS.Clocks
open HGAS.CompactAccumulatorPipelineCode
open HGAS.NormalizedCorrectedCanonicalCompactTrajectory
open HGAS.NormalizedCorrectedCanonicalFixedDetectorCentralChart
open
  HGAS.CompactAccumulatorPipelineCode.AllAffineCompactBaseChartTrajectory
open
  HGAS.CompactAccumulatorPipelineCode.AllAffineCompactSourceChart

variable {eqs vars : ℕ}

/-- Short name for the normalized detector's affine source dimension. -/
abbrev sourceDimension (eqs vars : ℕ) : ℕ :=
  NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDimension
    eqs vars

/-- Short name for its one-block all-affine compact layout. -/
abbrev layout (eqs vars : ℕ) :
    Fin (sourceDimension eqs vars) → Fin 1 ⊕ Fin 0 :=
  AllAffineCompactSourceChart.layout (sourceDimension eqs vars)

/-- The positive compact seed at ordinary time zero. -/
def seed
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ) :
    BaseSpace (layout eqs vars) :=
  by
    simpa [layout,
      NormalizedCorrectedFixedDetectorCompactSourceCode.layout] using
      (NormalizedCorrectedCanonicalFixedDetectorCentralChart.canonicalCompactBasePoint
        parameters I controller 0)

/-- The closure of the complete canonical compact orbit. -/
def component
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ) :
    BaseInvariantComponent
      (layout eqs vars)
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDegreeBound I)
      (NormalizedCorrectedFixedDetectorCompactSourceCode.clearingExponent I)
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode
        parameters I) :=
  orbitClosureBaseComponent (seed parameters I controller)

/-- The canonical central lower bound transfers from the explicit orbit
to every point in its closure. -/
theorem centralLower_le
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
    NormalizedCorrectedCanonicalFixedDetectorCentralChart.canonicalCentralWeightSqLowerBound
        eqs vars ≤
      baseCentralWeightProduct (layout eqs vars) b := by
  apply
    lowerBound_on_orbitClosure_of_continuous
      (layout := layout eqs vars)
      (E :=
        NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDegreeBound I)
      (M :=
        NormalizedCorrectedFixedDetectorCompactSourceCode.clearingExponent I)
      (P :=
        NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode
          parameters I)
      (seed parameters I controller)
      (baseCentralWeightProduct (layout eqs vars))
      (by
        unfold baseCentralWeightProduct
        apply continuous_finsetProd
        intro c _
        exact
          ((continuous_apply
            (MixedCentralPolynomialCode.wIndex
              (n := sourceDimension eqs vars) c)).comp
            continuous_subtype_val).pow 2)
      (NormalizedCorrectedCanonicalFixedDetectorCentralChart.canonicalCentralWeightSqLowerBound
        eqs vars)
      (fun τ ↦ by
        have hflow :
            NormalizedCorrectedCanonicalCompactTrajectory.canonicalCompactCurve
                parameters I controller hlock τ =
              baseFlow
                (layout eqs vars)
                (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDegreeBound I)
                (NormalizedCorrectedFixedDetectorCompactSourceCode.clearingExponent I)
                (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode
                  parameters I)
                τ (seed parameters I controller) := by
          simpa [layout, seed,
            NormalizedCorrectedFixedDetectorCompactSourceCode.layout] using
            (NormalizedCorrectedCanonicalCompactTrajectory.canonicalCompactCurve_eq_baseFlow
              parameters I controller hlock τ)
        rw [← hflow]
        rw [canonicalCompactCurve_eq_canonicalCompactBasePoint]
        exact
          canonicalCentralWeightSqLowerBound_le_baseCentralWeightProduct
            parameters I controller hcontroller
            (physicalTime parameters I controller hlock τ))
      b

/-- The unique central coordinate is nonzero throughout the component. -/
theorem weight_ne_zero
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
    AllAffineCompactBaseChartTrajectory.weight
        (b : BaseSpace (layout eqs vars)) ≠ 0 := by
  intro hzero
  have hlower :=
    centralLower_le parameters I controller hcontroller hlock b
  have hpositive :=
    NormalizedCorrectedCanonicalFixedDetectorCentralChart.canonicalCentralWeightSqLowerBound_pos
      (eqs := eqs) (vars := vars)
  have hproduct :
      baseCentralWeightProduct (layout eqs vars)
          (b : BaseSpace (layout eqs vars)) = 0 := by
    have hsquare :=
      congrArg (fun x : ℝ ↦ x ^ 2) hzero
    simpa [baseCentralWeightProduct, layout,
      AllAffineCompactBaseChartTrajectory.weight] using hsquare
  rw [hproduct] at hlower
  linarith

/-- A component point, bundled with membership in the finite central
chart. -/
def finiteBasePoint
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
    FiniteBaseSpace (sourceDimension eqs vars) :=
  ⟨b, weight_ne_zero parameters I controller hcontroller hlock b⟩

/-- Recover the ordinary affine fixed-detector point from the compact
component. -/
def rawPoint
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
    Fin (sourceDimension eqs vars) → ℝ :=
  affinePoint
    (finiteBasePoint parameters I controller hcontroller hlock b)

theorem continuous_finiteBasePoint
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
      (finiteBasePoint parameters I controller hcontroller hlock) := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val

theorem continuous_rawPoint
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
      (rawPoint parameters I controller hcontroller hlock) :=
  continuous_affinePoint.comp
    (continuous_finiteBasePoint
      parameters I controller hcontroller hlock)

/-- On the named dense orbit, affine recovery gives exactly the canonical
raw detector curve at inverse-clock physical time. -/
theorem rawPoint_orbitPoint
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
    rawPoint parameters I controller hcontroller hlock
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
      NormalizedCorrectedCanonicalCompactTrajectory.canonicalAffineCurve
        parameters I controller
        (NormalizedCorrectedCanonicalCompactTrajectory.physicalTime
          parameters I controller hlock τ) := by
  let z :=
    NormalizedCorrectedCanonicalCompactTrajectory.canonicalAffineCurve
      parameters I controller
      (NormalizedCorrectedCanonicalCompactTrajectory.physicalTime
        parameters I controller hlock τ)
  have hbase :=
    (NormalizedCorrectedCanonicalCompactTrajectory.canonicalCompactCurve_eq_baseFlow
      parameters I controller hlock τ).symm
  have hbase' :
      baseFlow
          (layout eqs vars)
          (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDegreeBound
            I)
          (NormalizedCorrectedFixedDetectorCompactSourceCode.clearingExponent
            I)
          (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode
            parameters I)
          τ (seed parameters I controller) =
        NormalizedCorrectedCanonicalCompactTrajectory.canonicalCompactCurve
          parameters I controller hlock τ := by
    simpa [layout, seed,
      NormalizedCorrectedFixedDetectorCompactSourceCode.layout] using hbase
  have hfinite :
      finiteBasePoint parameters I controller hcontroller hlock
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
        finitePositiveBasePoint z := by
    apply Subtype.ext
    change
      baseFlow
          (layout eqs vars)
          (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDegreeBound I)
          (NormalizedCorrectedFixedDetectorCompactSourceCode.clearingExponent I)
          (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode
            parameters I)
          τ (seed parameters I controller) =
        AllAffinePositiveCentralTrajectory.positiveBasePoint z
    rw [hbase']
    rfl
  change
    affinePoint
        (finiteBasePoint parameters I controller hcontroller hlock
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
      z
  rw [hfinite]
  exact affinePoint_finitePositiveBasePoint z

/-- Compact-time affine speed on the orbit-closure component. -/
def speed
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
    (b : (component parameters I controller).Space) : ℝ :=
  affineSpeed
    (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDegreeBound I)
    (rawPoint parameters I controller hcontroller hlock b)

theorem continuous_speed
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
      (speed parameters I controller hcontroller hlock) :=
  (continuous_affineSpeed
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDegreeBound I)).comp
    (continuous_rawPoint parameters I controller hcontroller hlock)

theorem speed_pos
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
    0 < speed parameters I controller hcontroller hlock b :=
  affineSpeed_pos _ _

theorem speed_le_one
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
    speed parameters I controller hcontroller hlock b ≤ 1 :=
  affineSpeed_le_one _ _

/-- The affine point recovered along an arbitrary component orbit solves
the intrinsically time-scaled detector field. -/
theorem rawCurve_isIntegralCurve
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
      (fun t ↦
        rawPoint parameters I controller hcontroller hlock
          ((component parameters I controller).flow t b))
      (fun _ z ↦
        timeScaledField
          (affineSpeed
            (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDegreeBound
              I))
          (PolynomialFieldCode.realize
            (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode
              parameters I)) z) := by
  let η : ℝ → BaseSpace (layout eqs vars) :=
    fun t ↦ ((component parameters I controller).flow t b : _)
  have hη :
      IsIntegralCurve
        (fun t ↦ (η t).1)
        (fun _ y ↦
          PolynomialFieldCode.realize
            (baseFieldCode
              (layout eqs vars)
              (NormalizedCorrectedFixedDetectorCompactSourceCode.clearingExponent
                I)
              (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode
                parameters I)) y) := by
    simpa only [η, BaseInvariantComponent.coe_flow_apply] using
      (baseFlow_integralCurve
        (layout eqs vars)
        (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDegreeBound I)
        (NormalizedCorrectedFixedDetectorCompactSourceCode.clearingExponent I)
        (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode
          parameters I)
        (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode_termsDegreeLE
          parameters I)
        (NormalizedCorrectedFixedDetectorCompactSourceCode.baseCompactTangency
          parameters I)
        b.1)
  simpa only [
    rawPoint, finiteBasePoint, η,
    NormalizedCorrectedFixedDetectorCompactSourceCode.clearingExponent] using
    (affinePoint_isIntegralCurve
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDegreeBound I)
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode
        parameters I)
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode_termsAffineBlockDegreeLE
        parameters I)
      η hη
      (fun t ↦
        weight_ne_zero parameters I controller hcontroller hlock
          ((component parameters I controller).flow t b)))

/-- The central lower bound gives a positive uniform lower bound for the
affine speed. -/
theorem centralLower_pow_le_speed
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
    NormalizedCorrectedCanonicalFixedDetectorCentralChart.canonicalCentralWeightSqLowerBound
          eqs vars ^
        NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDegreeBound I ≤
      speed parameters I controller hcontroller hlock b := by
  let fb :=
    finiteBasePoint parameters I controller hcontroller hlock b
  have hlower :=
    centralLower_le parameters I controller hcontroller hlock b
  have hproduct :
      baseCentralWeightProduct (layout eqs vars)
          (b : BaseSpace (layout eqs vars)) =
        AllAffineCompactBaseChartTrajectory.weight
          (b : BaseSpace (layout eqs vars)) ^ 2 := by
    simp [baseCentralWeightProduct, layout,
      AllAffineCompactBaseChartTrajectory.weight]
  rw [hproduct] at hlower
  have hpow :=
    pow_le_pow_left₀
      (NormalizedCorrectedCanonicalFixedDetectorCentralChart.canonicalCentralWeightSqLowerBound_pos
        (eqs := eqs) (vars := vars)).le
      hlower
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDegreeBound I)
  change
    _ ≤
      affineSpeed
        (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDegreeBound I)
        (affinePoint fb)
  rw [← weight_evenPow_eq_affineSpeed
    (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDegreeBound I)
    fb]
  rw [pow_mul]
  exact hpow

/-- The direct compact-to-physical clock along an arbitrary component
orbit is globally defined. -/
def physicalClock
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
    PositiveIntegralClock
      (fun t ↦
        speed parameters I controller hcontroller hlock
          ((component parameters I controller).flow t b)) := by
  apply positiveIntegralClock_of_uniformLowerBound
  · exact
      (continuous_speed parameters I controller hcontroller hlock).comp
        ((component parameters I controller).flow.continuous
          continuous_id continuous_const)
  · exact pow_pos
      (NormalizedCorrectedCanonicalFixedDetectorCentralChart.canonicalCentralWeightSqLowerBound_pos
        (eqs := eqs) (vars := vars))
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDegreeBound I)
  · intro t
    exact
      centralLower_pow_le_speed
        parameters I controller hcontroller hlock
        ((component parameters I controller).flow t b)

/-- The ordinary physical-time detector curve based at a component
point. -/
def physicalCurve
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
    Fin (sourceDimension eqs vars) → ℝ :=
  rawPoint parameters I controller hcontroller hlock
    ((component parameters I controller).flow
      ((PositiveIntegralClock.orderIso
        (physicalClock parameters I controller hcontroller hlock b)).symm τ)
      b)

@[simp]
theorem physicalCurve_zero
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
    physicalCurve parameters I controller hcontroller hlock b 0 =
      rawPoint parameters I controller hcontroller hlock b := by
  simp [physicalCurve]

/-- In physical time the recovered curve is a complete trajectory of the
literal unscaled detector polynomial field. -/
theorem physicalCurve_isIntegralCurve
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
      (physicalCurve parameters I controller hcontroller hlock b)
      (fun _ z ↦
        PolynomialFieldCode.realize
          (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode
            parameters I) z) := by
  simpa only [physicalCurve, speed] using
    (rawCurve_isIntegralCurve
      parameters I controller hcontroller hlock b).reparametrize_from_timeScaledField
        (physicalClock parameters I controller hcontroller hlock b)

/-- Every physical component curve has the complete nested
fixed-detector semantics. -/
theorem physicalCurve_isStructuredTrajectory
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
    FixedDetectorReverseTrajectoryCrosswalk.IsStructuredTrajectory
      parameters I
      (physicalCurve parameters I controller hcontroller hlock b) := by
  apply
    FixedDetectorReverseTrajectoryCrosswalk.isStructuredTrajectory_of_isIntegralCurve
  simpa only [
    NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode] using
    physicalCurve_isIntegralCurve
      parameters I controller hcontroller hlock b

end HGAS.NormalizedCorrectedCanonicalOrbitClosureChart
