import HGAS.Arithmetic.CorrectedFixedDetectorCompactSourceCode
import HGAS.Compiler.AllAffineConditionalGenericZeroOrbit
import HGAS.Compiler.AllAffinePhysicalDriftAverages
import Mathlib.Tactic

/-!
# Pointwise validity on the corrected detector's generic orbit

The first coordinate of the corrected detector drift is the unchanged
sum-of-squares validity energy.  This file specializes the reusable
zero-orbit selection theorem to that coordinate.
-/

namespace HGAS.CorrectedFixedDetectorValidityOrbit

open HGAS
open Filter Function MeasureTheory Set Topology
open scoped BoundedContinuousFunction

noncomputable section

open CompactAccumulatorPipelineCode
open CompactAccumulatorPipelineCode.AllAffineCompactSourceChart
open CompactAccumulatorPipelineCode.AllAffineCompactSourceClock
open CompactAccumulatorPipelineCode.AllAffineCompactSourceDrift
open CompactAccumulatorPipelineCode.AllAffineConditionalGenericOrbit
open CompactAccumulatorPipelineCode.AllAffineConditionalGenericZeroOrbit
open CompactAccumulatorPipelineCode.AllAffinePhysicalDriftAverages

variable {eqs vars : ℕ}

/-- The intrinsic compactification exponent used by the corrected
all-affine source. -/
abbrev speedExponent (I : DQLSystem eqs vars) : ℕ :=
  CorrectedFixedDetectorCompactSourceCode.sourceDegreeBound I

/-- The corrected compact flow, expressed through the reusable all-affine
one-block interface. -/
def compactFlow
    (u : CorrectedFixedDetectorCompactSourceCode.CompilerInput eqs vars) :
    Flow ℝ
      (AllAffineCompactSourceChart.SourceSpace
        (CorrectedFixedDetectorCompactSourceCode.sourceDimension eqs vars)
        (CorrectedFixedDetectorCompactSourceCode.driftDimension vars)) :=
  AllAffineConditionalGenericOrbit.compactFlow
    (speedExponent (CorrectedFixedDetectorCompactSourceCode.system u))
    (speedExponent (CorrectedFixedDetectorCompactSourceCode.system u))
    (CorrectedFixedDetectorCompactSourceCode.accumulatorScale u)
    (CorrectedFixedDetectorCompactSourceCode.sourceFieldCode
      (CorrectedFixedDetectorCompactSourceCode.parameters u)
      (CorrectedFixedDetectorCompactSourceCode.system u))
    (CorrectedFixedDetectorCompactSourceCode.sourceDriftCode
      (CorrectedFixedDetectorCompactSourceCode.system u))
    (CorrectedFixedDetectorCompactSourceCode.rewardMargin u)

/-- Invariant finite chart of the corrected compact source. -/
def finiteInvariant
    (u : CorrectedFixedDetectorCompactSourceCode.CompilerInput eqs vars) :
    IsInvariant (compactFlow u)
      (sourceFiniteInteriorSet
        (m :=
          CorrectedFixedDetectorCompactSourceCode.driftDimension vars)
        (layout
          (CorrectedFixedDetectorCompactSourceCode.sourceDimension
            eqs vars))) :=
  AllAffineConditionalGenericOrbit.finiteInvariant
    (speedExponent (CorrectedFixedDetectorCompactSourceCode.system u))
    (speedExponent (CorrectedFixedDetectorCompactSourceCode.system u))
    (CorrectedFixedDetectorCompactSourceCode.accumulatorScale u)
    (CorrectedFixedDetectorCompactSourceCode.sourceFieldCode
      (CorrectedFixedDetectorCompactSourceCode.parameters u)
      (CorrectedFixedDetectorCompactSourceCode.system u))
    (CorrectedFixedDetectorCompactSourceCode.sourceFieldCode_termsDegreeLE
      (CorrectedFixedDetectorCompactSourceCode.parameters u)
      (CorrectedFixedDetectorCompactSourceCode.system u))
    (CorrectedFixedDetectorCompactSourceCode.sourceDriftCode
      (CorrectedFixedDetectorCompactSourceCode.system u))
    (CorrectedFixedDetectorCompactSourceCode.sourceDriftCode_termsDegreeLE
      (CorrectedFixedDetectorCompactSourceCode.system u))
    (CorrectedFixedDetectorCompactSourceCode.rewardMargin u)

/-- Every orbit of the corrected compact source solves its literal
compiled polynomial field. -/
theorem compactFlow_integralCurve
    (u : CorrectedFixedDetectorCompactSourceCode.CompilerInput eqs vars)
    (v :
      AllAffineCompactSourceChart.SourceSpace
        (CorrectedFixedDetectorCompactSourceCode.sourceDimension eqs vars)
        (CorrectedFixedDetectorCompactSourceCode.driftDimension vars)) :
    IsIntegralCurve
      (fun t ↦ (compactFlow u t v).1)
      (fun _ x ↦
        PolynomialFieldCode.realize
          (fieldCode
            (layout
              (CorrectedFixedDetectorCompactSourceCode.sourceDimension
                eqs vars))
            (2 *
              speedExponent
                (CorrectedFixedDetectorCompactSourceCode.system u))
            (CorrectedFixedDetectorCompactSourceCode.accumulatorScale u)
            (CorrectedFixedDetectorCompactSourceCode.sourceFieldCode
              (CorrectedFixedDetectorCompactSourceCode.parameters u)
              (CorrectedFixedDetectorCompactSourceCode.system u))
            (CorrectedFixedDetectorCompactSourceCode.sourceDriftCode
              (CorrectedFixedDetectorCompactSourceCode.system u))) x) := by
  exact
    sourceFlow_integralCurve
      (layout
        (CorrectedFixedDetectorCompactSourceCode.sourceDimension eqs vars))
      (speedExponent
        (CorrectedFixedDetectorCompactSourceCode.system u))
      (2 *
        speedExponent
          (CorrectedFixedDetectorCompactSourceCode.system u))
      (CorrectedFixedDetectorCompactSourceCode.accumulatorScale u)
      (CorrectedFixedDetectorCompactSourceCode.sourceFieldCode
        (CorrectedFixedDetectorCompactSourceCode.parameters u)
        (CorrectedFixedDetectorCompactSourceCode.system u))
      (CorrectedFixedDetectorCompactSourceCode.sourceFieldCode_termsDegreeLE
        (CorrectedFixedDetectorCompactSourceCode.parameters u)
        (CorrectedFixedDetectorCompactSourceCode.system u))
      (CorrectedFixedDetectorCompactSourceCode.sourceDriftCode
        (CorrectedFixedDetectorCompactSourceCode.system u))
      (CorrectedFixedDetectorCompactSourceCode.sourceDriftCode_termsDegreeLE
        (CorrectedFixedDetectorCompactSourceCode.system u))
      (CorrectedFixedDetectorCompactSourceCode.rewardMargin u)
      (fullCompactTangencyHypothesis_of_base
        (layout
          (CorrectedFixedDetectorCompactSourceCode.sourceDimension
            eqs vars))
        (2 *
          speedExponent
            (CorrectedFixedDetectorCompactSourceCode.system u))
        (CorrectedFixedDetectorCompactSourceCode.sourceFieldCode
          (CorrectedFixedDetectorCompactSourceCode.parameters u)
          (CorrectedFixedDetectorCompactSourceCode.system u))
        (CorrectedFixedDetectorCompactSourceCode.baseCompactTangency
          (CorrectedFixedDetectorCompactSourceCode.parameters u)
          (CorrectedFixedDetectorCompactSourceCode.system u)))
      v

/-- The affine detector curve recovered from a corrected finite-chart
orbit. -/
def affineCurve
    (u : CorrectedFixedDetectorCompactSourceCode.CompilerInput eqs vars)
    (v :
      AllAffineCompactSourceChart.FiniteSourceSpace
        (CorrectedFixedDetectorCompactSourceCode.sourceDimension eqs vars)
        (CorrectedFixedDetectorCompactSourceCode.driftDimension vars))
    (t : ℝ) :
    Fin (CorrectedFixedDetectorCompactSourceCode.sourceDimension
      eqs vars) → ℝ :=
  AllAffineCompactSourceClock.affineCurve
    (compactFlow u) (finiteInvariant u) v t

/-- The data selected from an ergodic conditional with zero drift. -/
structure SelectedValidityOrbit
    (u : CorrectedFixedDetectorCompactSourceCode.CompilerInput eqs vars)
    where
  point :
    AllAffineCompactSourceChart.FiniteSourceSpace
      (CorrectedFixedDetectorCompactSourceCode.sourceDimension eqs vars)
      (CorrectedFixedDetectorCompactSourceCode.driftDimension vars)
  speedMean : ℝ
  clock :
    PositiveIntegralClock
      (stateClockWeight
        (affineSpeed
          (speedExponent
            (CorrectedFixedDetectorCompactSourceCode.system u)))
        (affineCurve u point))
  speedMean_pos : 0 < speedMean
  recurrent :
    ForwardRecurrentAt
      (fun t : ℝ ↦
        ((compactFlow u).restrict (finiteInvariant u)) t point) 0
  validityDrift_zero :
    ∀ t : ℝ,
      finiteDriftCoordinateBCF
        (speedExponent (CorrectedFixedDetectorCompactSourceCode.system u))
        (CorrectedFixedDetectorCompactSourceCode.accumulatorScale u)
        (CorrectedFixedDetectorCompactSourceCode.sourceDriftCode
          (CorrectedFixedDetectorCompactSourceCode.system u))
        (CorrectedFixedDetectorDriftCode.validityIndex vars)
        (((compactFlow u).restrict (finiteInvariant u)) t point) = 0
  speed_generic :
    Tendsto
      (fun q : ℕ ↦
        Dynamics.integerOrbitAverageObservable
          ((compactFlow u).restrict (finiteInvariant u))
          (affineSpeedBCF
            (speedExponent
              (CorrectedFixedDetectorCompactSourceCode.system u)))
          (q + 1) point)
      atTop (𝓝 speedMean)
  drift_generic :
    ∀ i :
        Fin (CorrectedFixedDetectorCompactSourceCode.driftDimension vars),
      Tendsto
        (fun q : ℕ ↦
          Dynamics.integerOrbitAverageObservable
            ((compactFlow u).restrict (finiteInvariant u))
            (finiteDriftCoordinateBCF
              (speedExponent
                (CorrectedFixedDetectorCompactSourceCode.system u))
              (CorrectedFixedDetectorCompactSourceCode.accumulatorScale u)
              (CorrectedFixedDetectorCompactSourceCode.sourceDriftCode
                (CorrectedFixedDetectorCompactSourceCode.system u))
              i)
            (q + 1) point)
        atTop (𝓝 0)

/-- The compact corrected validity drift is nonnegative whenever the
accumulator scale is nonnegative. -/
theorem finiteValidityDrift_nonneg
    (u : CorrectedFixedDetectorCompactSourceCode.CompilerInput eqs vars)
    (hscale :
      0 ≤
        ((CorrectedFixedDetectorCompactSourceCode.accumulatorScale u).decode :
          ℝ))
    (v :
      AllAffineCompactSourceChart.FiniteSourceSpace
        (CorrectedFixedDetectorCompactSourceCode.sourceDimension eqs vars)
        (CorrectedFixedDetectorCompactSourceCode.driftDimension vars)) :
    0 ≤
      finiteDriftCoordinateBCF
        (speedExponent (CorrectedFixedDetectorCompactSourceCode.system u))
        (CorrectedFixedDetectorCompactSourceCode.accumulatorScale u)
        (CorrectedFixedDetectorCompactSourceCode.sourceDriftCode
          (CorrectedFixedDetectorCompactSourceCode.system u))
        (CorrectedFixedDetectorDriftCode.validityIndex vars) v := by
  let I := CorrectedFixedDetectorCompactSourceCode.system u
  let z : FixedDetectorPolynomialCode.State eqs vars :=
    FixedDetectorPolynomialCode.state (affinePoint v)
  have heval :=
    CorrectedFixedDetectorDriftCode.eval_driftCode_validityIndex I z
  have heval' :
      _root_.MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
          (affinePoint v)
          (PolynomialCode.decode
            (CorrectedFixedDetectorCompactSourceCode.sourceDriftCode I
              (CorrectedFixedDetectorDriftCode.validityIndex vars))) =
        CorrectedFixedDetectorDriftCode.validityEnergyValue I z := by
    simpa [z, CorrectedFixedDetectorCompactSourceCode.sourceDriftCode] using
      heval
  rw [finiteDriftCoordinateBCF_eq
    (speedExponent I)
    (CorrectedFixedDetectorCompactSourceCode.accumulatorScale u)
    (CorrectedFixedDetectorCompactSourceCode.sourceDriftCode I)
    (by
      intro i
      simpa only [speedExponent,
        CorrectedFixedDetectorCompactSourceCode.clearingExponent] using
        CorrectedFixedDetectorCompactSourceCode.sourceDriftCode_termsAffineBlockDegreeLE
          I i)
    (CorrectedFixedDetectorDriftCode.validityIndex vars) v]
  rw [heval']
  exact mul_nonneg
    (mul_nonneg hscale
      (affineSpeed_nonneg (speedExponent I) (affinePoint v)))
    (CorrectedFixedDetectorDriftCode.validityEnergyValue_nonneg I z)

/-- Zero conditional base means select a recurrent, speed-generic orbit
whose validity sum of squares vanishes at every compact time. -/
theorem exists_selectedValidityOrbit_of_conditionalBase_zero
    (u : CorrectedFixedDetectorCompactSourceCode.CompilerInput eqs vars)
    (μ : Dynamics.InvariantProbabilityMeasure (compactFlow u))
    (hμ :
      Dynamics.IsErgodicInvariantProbability
        (compactFlow u) μ.measure)
    (hpos :
      (μ.measure :
        Measure
          (AllAffineCompactSourceChart.SourceSpace
            (CorrectedFixedDetectorCompactSourceCode.sourceDimension
              eqs vars)
            (CorrectedFixedDetectorCompactSourceCode.driftDimension vars)))
        (sourceFiniteInteriorSet
          (m :=
            CorrectedFixedDetectorCompactSourceCode.driftDimension vars)
          (layout
            (CorrectedFixedDetectorCompactSourceCode.sourceDimension
              eqs vars))) ≠ 0)
    (hzero :
      ∀ i :
          Fin (CorrectedFixedDetectorCompactSourceCode.driftDimension vars),
        (∫ b,
          baseDriftBCF
            (layout
              (CorrectedFixedDetectorCompactSourceCode.sourceDimension
                eqs vars))
            (2 *
              speedExponent
                (CorrectedFixedDetectorCompactSourceCode.system u))
            (CorrectedFixedDetectorCompactSourceCode.accumulatorScale u)
            (CorrectedFixedDetectorCompactSourceCode.sourceDriftCode
              (CorrectedFixedDetectorCompactSourceCode.system u))
            b i
          ∂((conditionalBaseProbability
              (layout
                (CorrectedFixedDetectorCompactSourceCode.sourceDimension
                  eqs vars))
              (speedExponent
                (CorrectedFixedDetectorCompactSourceCode.system u))
              (2 *
                speedExponent
                  (CorrectedFixedDetectorCompactSourceCode.system u))
              (CorrectedFixedDetectorCompactSourceCode.accumulatorScale u)
              (CorrectedFixedDetectorCompactSourceCode.sourceFieldCode
                (CorrectedFixedDetectorCompactSourceCode.parameters u)
                (CorrectedFixedDetectorCompactSourceCode.system u))
              (CorrectedFixedDetectorCompactSourceCode.sourceFieldCode_termsDegreeLE
                (CorrectedFixedDetectorCompactSourceCode.parameters u)
                (CorrectedFixedDetectorCompactSourceCode.system u))
              (CorrectedFixedDetectorCompactSourceCode.sourceDriftCode
                (CorrectedFixedDetectorCompactSourceCode.system u))
              (CorrectedFixedDetectorCompactSourceCode.sourceDriftCode_termsDegreeLE
                (CorrectedFixedDetectorCompactSourceCode.system u))
              (CorrectedFixedDetectorCompactSourceCode.rewardMargin u)
              (CorrectedFixedDetectorCompactSourceCode.baseCompactTangency
                (CorrectedFixedDetectorCompactSourceCode.parameters u)
                (CorrectedFixedDetectorCompactSourceCode.system u))
              μ hpos).measure :
            Measure
              (BaseSpace
                (layout
                  (CorrectedFixedDetectorCompactSourceCode.sourceDimension
                    eqs vars))))) = 0)
    (hscale :
      0 ≤
        ((CorrectedFixedDetectorCompactSourceCode.accumulatorScale u).decode :
          ℝ)) :
    Nonempty (SelectedValidityOrbit u) := by
  obtain ⟨v, c, hclock, hc, hrec, hvalid, hspeed, hdrift⟩ :=
    exists_recurrent_genericPhysicalPoint_zeroCoordinate_of_conditionalBase_zero
      (speedExponent
        (CorrectedFixedDetectorCompactSourceCode.system u))
      (speedExponent
        (CorrectedFixedDetectorCompactSourceCode.system u))
      (CorrectedFixedDetectorCompactSourceCode.accumulatorScale u)
      (CorrectedFixedDetectorCompactSourceCode.sourceFieldCode
        (CorrectedFixedDetectorCompactSourceCode.parameters u)
        (CorrectedFixedDetectorCompactSourceCode.system u))
      (CorrectedFixedDetectorCompactSourceCode.sourceFieldCode_termsDegreeLE
        (CorrectedFixedDetectorCompactSourceCode.parameters u)
        (CorrectedFixedDetectorCompactSourceCode.system u))
      (CorrectedFixedDetectorCompactSourceCode.sourceDriftCode
        (CorrectedFixedDetectorCompactSourceCode.system u))
      (CorrectedFixedDetectorCompactSourceCode.sourceDriftCode_termsDegreeLE
        (CorrectedFixedDetectorCompactSourceCode.system u))
      (CorrectedFixedDetectorCompactSourceCode.rewardMargin u)
      μ hμ hpos hzero
      (CorrectedFixedDetectorDriftCode.validityIndex vars)
      (finiteValidityDrift_nonneg u hscale)
  exact
    ⟨{
      point := v
      speedMean := c
      clock := hclock
      speedMean_pos := hc
      recurrent := hrec
      validityDrift_zero := hvalid
      speed_generic := hspeed
      drift_generic := hdrift
    }⟩

namespace SelectedValidityOrbit

variable
  {u : CorrectedFixedDetectorCompactSourceCode.CompilerInput eqs vars}
  (O : SelectedValidityOrbit u)

/-- Structured detector state on the selected compact-time affine orbit. -/
def compactTimeState (t : ℝ) :
    FixedDetectorPolynomialCode.State eqs vars :=
  FixedDetectorPolynomialCode.state (affineCurve u O.point t)

@[simp]
theorem point_compactTimeState (t : ℝ) :
    FixedDetectorPolynomialCode.point (O.compactTimeState t) =
      affineCurve u O.point t :=
  FixedDetectorPolynomialCode.point_state _

/-- With strictly positive accumulator scale, pointwise vanishing of the
compact validity drift is equivalent to vanishing of the literal detector
sum of squares along the affine orbit. -/
theorem validityEnergy_zero_compactTime
    (hscale :
      0 <
        ((CorrectedFixedDetectorCompactSourceCode.accumulatorScale u).decode :
          ℝ))
    (t : ℝ) :
    CorrectedFixedDetectorDriftCode.validityEnergyValue
        (CorrectedFixedDetectorCompactSourceCode.system u)
        (O.compactTimeState t) = 0 := by
  let I := CorrectedFixedDetectorCompactSourceCode.system u
  let vt :=
    ((compactFlow u).restrict (finiteInvariant u)) t O.point
  have hzero := O.validityDrift_zero t
  have hsem :
      _root_.MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
          (affinePoint vt)
          (PolynomialCode.decode
            (CorrectedFixedDetectorCompactSourceCode.sourceDriftCode I
              (CorrectedFixedDetectorDriftCode.validityIndex vars))) =
        CorrectedFixedDetectorDriftCode.validityEnergyValue I
          (FixedDetectorPolynomialCode.state (affinePoint vt)) := by
    simpa [CorrectedFixedDetectorCompactSourceCode.sourceDriftCode] using
      (CorrectedFixedDetectorDriftCode.eval_driftCode_validityIndex
        I (FixedDetectorPolynomialCode.state (affinePoint vt)))
  rw [finiteDriftCoordinateBCF_eq
    (speedExponent I)
    (CorrectedFixedDetectorCompactSourceCode.accumulatorScale u)
    (CorrectedFixedDetectorCompactSourceCode.sourceDriftCode I)
    (by
      intro i
      simpa only [speedExponent,
        CorrectedFixedDetectorCompactSourceCode.clearingExponent] using
        CorrectedFixedDetectorCompactSourceCode.sourceDriftCode_termsAffineBlockDegreeLE
          I i)
    (CorrectedFixedDetectorDriftCode.validityIndex vars) vt,
    hsem] at hzero
  have hfactor :
      ((CorrectedFixedDetectorCompactSourceCode.accumulatorScale u).decode :
          ℝ) *
        affineSpeed (speedExponent I) (affinePoint vt) ≠ 0 :=
    mul_ne_zero hscale.ne'
      (affineSpeed_pos (speedExponent I) (affinePoint vt)).ne'
  have henergy :
      CorrectedFixedDetectorDriftCode.validityEnergyValue I
          (FixedDetectorPolynomialCode.state (affinePoint vt)) = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hfactor
  simpa only [compactTimeState, affineCurve,
    AllAffineCompactSourceClock.affineCurve, vt, I] using henergy

/-- Ordinary physical-time detector point obtained from the selected
positive integral clock. -/
def physicalPoint (τ : ℝ) :
    Fin (CorrectedFixedDetectorCompactSourceCode.sourceDimension
      eqs vars) → ℝ :=
  affineCurve u O.point
    ((PositiveIntegralClock.orderIso O.clock).symm τ)

theorem continuous_physicalPoint :
    Continuous O.physicalPoint :=
  (AllAffineCompactSourceClock.continuous_affineCurve
    (compactFlow u) (finiteInvariant u) O.point).comp
      (PositiveIntegralClock.orderIso O.clock).symm.continuous

/-- Structured detector state in ordinary physical time. -/
def physicalState (τ : ℝ) :
    FixedDetectorPolynomialCode.State eqs vars :=
  FixedDetectorPolynomialCode.state (O.physicalPoint τ)

@[simp]
theorem point_physicalState (τ : ℝ) :
    FixedDetectorPolynomialCode.point (O.physicalState τ) =
      O.physicalPoint τ :=
  FixedDetectorPolynomialCode.point_state _

/-- The physical point is exactly the reusable inverse-clock curve. -/
theorem physicalPoint_eq_physicalCurve (τ : ℝ) :
    O.physicalPoint τ =
      AllAffineCompactSourceClock.physicalCurve
        (speedExponent
          (CorrectedFixedDetectorCompactSourceCode.system u))
        (compactFlow u) (finiteInvariant u) O.point O.clock τ :=
  rfl

/-- In physical time the selected point is a forward trajectory of the
literal fixed-detector polynomial field. -/
theorem physicalPoint_isForwardTrajectory :
    IsForwardTrajectory
      (PolynomialFieldCode.realize
        (CorrectedFixedDetectorCompactSourceCode.sourceFieldCode
          (CorrectedFixedDetectorCompactSourceCode.parameters u)
          (CorrectedFixedDetectorCompactSourceCode.system u)))
      O.physicalPoint
      (affinePoint O.point) := by
  have hAffine :
      ∀ j,
        MixedCentralPolynomialCode.TermsAffineBlockDegreeLE
          (layout
            (CorrectedFixedDetectorCompactSourceCode.sourceDimension
              eqs vars))
          (2 *
            speedExponent
              (CorrectedFixedDetectorCompactSourceCode.system u))
          (CorrectedFixedDetectorCompactSourceCode.sourceFieldCode
            (CorrectedFixedDetectorCompactSourceCode.parameters u)
            (CorrectedFixedDetectorCompactSourceCode.system u) j) := by
    intro j
    simpa only [speedExponent,
      CorrectedFixedDetectorCompactSourceCode.clearingExponent] using
      (CorrectedFixedDetectorCompactSourceCode.sourceFieldCode_termsAffineBlockDegreeLE
        (CorrectedFixedDetectorCompactSourceCode.parameters u)
        (CorrectedFixedDetectorCompactSourceCode.system u) j)
  simpa only [physicalPoint_eq_physicalCurve] using
    (AllAffineCompactSourceClock.physicalCurve_isForwardTrajectory
      (speedExponent
        (CorrectedFixedDetectorCompactSourceCode.system u))
      (CorrectedFixedDetectorCompactSourceCode.accumulatorScale u)
      (CorrectedFixedDetectorCompactSourceCode.sourceFieldCode
        (CorrectedFixedDetectorCompactSourceCode.parameters u)
        (CorrectedFixedDetectorCompactSourceCode.system u))
      (CorrectedFixedDetectorCompactSourceCode.sourceDriftCode
        (CorrectedFixedDetectorCompactSourceCode.system u))
      hAffine (compactFlow u) (compactFlow_integralCurve u)
      (finiteInvariant u) O.point O.clock)

/-- Compact recurrence survives the physical inverse-clock
reparametrization. -/
theorem physicalPoint_forwardRecurrentAt :
    ForwardRecurrentAt O.physicalPoint 0 := by
  simpa only [physicalPoint_eq_physicalCurve] using
    (AllAffineCompactSourceClock.physicalCurve_forwardRecurrentAt
      (speedExponent
        (CorrectedFixedDetectorCompactSourceCode.system u))
      (compactFlow u) (finiteInvariant u) O.point O.clock O.recurrent)

/-- The validity sum of squares vanishes for every ordinary physical
time. -/
theorem validityEnergy_zero_physicalTime
    (hscale :
      0 <
        ((CorrectedFixedDetectorCompactSourceCode.accumulatorScale u).decode :
          ℝ))
    (τ : ℝ) :
    CorrectedFixedDetectorDriftCode.validityEnergyValue
        (CorrectedFixedDetectorCompactSourceCode.system u)
        (O.physicalState τ) = 0 := by
  exact O.validityEnergy_zero_compactTime hscale
    ((PositiveIntegralClock.orderIso O.clock).symm τ)

/-- Physical clock horizons tend to `+∞`. -/
theorem physicalHorizon_tendsto_atTop :
    Tendsto
      (fun q : ℕ ↦
        integralClock
          (stateClockWeight
            (affineSpeed
              (speedExponent
                (CorrectedFixedDetectorCompactSourceCode.system u)))
            (affineCurve u O.point))
          (positiveIntegerHorizon q))
      atTop atTop :=
  O.clock.tendsto_atTop.comp positiveIntegerHorizon_tendsto_atTop

/-- Every corrected drift coordinate has zero ordinary-time Cesàro
average along the same unbounded physical clock horizons. -/
theorem physicalDriftAverage_tendsto_zero
    (hscale :
      ((CorrectedFixedDetectorCompactSourceCode.accumulatorScale u).decode :
          ℝ) ≠ 0)
    (i :
      Fin (CorrectedFixedDetectorCompactSourceCode.driftDimension vars)) :
    Tendsto
      (fun q : ℕ ↦
        (integralClock
          (stateClockWeight
            (affineSpeed
              (speedExponent
                (CorrectedFixedDetectorCompactSourceCode.system u)))
            (affineCurve u O.point))
          (positiveIntegerHorizon q))⁻¹ *
          ∫ τ in (0 : ℝ)..
              integralClock
                (stateClockWeight
                  (affineSpeed
                    (speedExponent
                      (CorrectedFixedDetectorCompactSourceCode.system u)))
                  (affineCurve u O.point))
                (positiveIntegerHorizon q),
            _root_.MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
              (O.physicalPoint τ)
              (PolynomialCode.decode
                (CorrectedFixedDetectorCompactSourceCode.sourceDriftCode
                  (CorrectedFixedDetectorCompactSourceCode.system u) i)))
      atTop (𝓝 0) := by
  have hh :
      ∀ r,
        MixedCentralPolynomialCode.TermsAffineBlockDegreeLE
          (layout
            (CorrectedFixedDetectorCompactSourceCode.sourceDimension
              eqs vars))
          (2 *
            speedExponent
              (CorrectedFixedDetectorCompactSourceCode.system u))
          (CorrectedFixedDetectorCompactSourceCode.sourceDriftCode
            (CorrectedFixedDetectorCompactSourceCode.system u) r) := by
    intro r
    simpa only [speedExponent,
      CorrectedFixedDetectorCompactSourceCode.clearingExponent] using
      (CorrectedFixedDetectorCompactSourceCode.sourceDriftCode_termsAffineBlockDegreeLE
        (CorrectedFixedDetectorCompactSourceCode.system u) r)
  simpa only [physicalPoint_eq_physicalCurve] using
    (AllAffinePhysicalDriftAverages.physicalDriftAverage_tendsto_zero
      (speedExponent
        (CorrectedFixedDetectorCompactSourceCode.system u))
      (CorrectedFixedDetectorCompactSourceCode.accumulatorScale u)
      (CorrectedFixedDetectorCompactSourceCode.sourceDriftCode
        (CorrectedFixedDetectorCompactSourceCode.system u))
      hh (compactFlow u) (finiteInvariant u) O.point i hscale
      O.speedMean_pos.ne' O.speed_generic (O.drift_generic i) O.clock)

end SelectedValidityOrbit

end

end HGAS.CorrectedFixedDetectorValidityOrbit
