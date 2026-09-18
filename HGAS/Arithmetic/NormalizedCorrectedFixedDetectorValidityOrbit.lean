import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorCompactSourceCode
import HGAS.Compiler.AllAffineConditionalGenericZeroOrbit
import HGAS.Compiler.AllAffinePhysicalDriftAverages
import Mathlib.Tactic

/-!
# Pointwise validity on the normalized corrected detector's generic orbit

The first coordinate of the normalized corrected detector drift is the unchanged
sum-of-squares validity energy.  This file specializes the reusable
zero-orbit selection theorem to that coordinate.
-/

namespace HGAS.NormalizedCorrectedFixedDetectorValidityOrbit

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
  NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDegreeBound I

/-- The normalized corrected compact flow, expressed through the reusable all-affine
one-block interface. -/
def compactFlow
    (u : NormalizedCorrectedFixedDetectorCompactSourceCode.CompilerInput eqs vars) :
    Flow ℝ
      (AllAffineCompactSourceChart.SourceSpace
        (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDimension eqs vars)
        (NormalizedCorrectedFixedDetectorCompactSourceCode.driftDimension vars)) :=
  AllAffineConditionalGenericOrbit.compactFlow
    (speedExponent (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
    (speedExponent (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
    (NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale u)
    (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode
      (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
      (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
    (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode
      (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
    (NormalizedCorrectedFixedDetectorCompactSourceCode.rewardMargin u)

/-- Invariant finite chart of the normalized corrected compact source. -/
def finiteInvariant
    (u : NormalizedCorrectedFixedDetectorCompactSourceCode.CompilerInput eqs vars) :
    IsInvariant (compactFlow u)
      (sourceFiniteInteriorSet
        (m :=
          NormalizedCorrectedFixedDetectorCompactSourceCode.driftDimension vars)
        (layout
          (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDimension
            eqs vars))) :=
  AllAffineConditionalGenericOrbit.finiteInvariant
    (speedExponent (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
    (speedExponent (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
    (NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale u)
    (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode
      (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
      (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
    (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode_termsDegreeLE
      (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
      (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
    (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode
      (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
    (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode_termsDegreeLE
      (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
    (NormalizedCorrectedFixedDetectorCompactSourceCode.rewardMargin u)

/-- Every orbit of the normalized corrected compact source solves its literal
compiled polynomial field. -/
theorem compactFlow_integralCurve
    (u : NormalizedCorrectedFixedDetectorCompactSourceCode.CompilerInput eqs vars)
    (v :
      AllAffineCompactSourceChart.SourceSpace
        (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDimension eqs vars)
        (NormalizedCorrectedFixedDetectorCompactSourceCode.driftDimension vars)) :
    IsIntegralCurve
      (fun t ↦ (compactFlow u t v).1)
      (fun _ x ↦
        PolynomialFieldCode.realize
          (fieldCode
            (layout
              (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDimension
                eqs vars))
            (2 *
              speedExponent
                (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
            (NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale u)
            (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode
              (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
              (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
            (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode
              (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))) x) := by
  exact
    sourceFlow_integralCurve
      (layout
        (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDimension eqs vars))
      (speedExponent
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
      (2 *
        speedExponent
          (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
      (NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale u)
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode
        (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode_termsDegreeLE
        (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode_termsDegreeLE
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
      (NormalizedCorrectedFixedDetectorCompactSourceCode.rewardMargin u)
      (fullCompactTangencyHypothesis_of_base
        (layout
          (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDimension
            eqs vars))
        (2 *
          speedExponent
            (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
        (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode
          (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
          (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
        (NormalizedCorrectedFixedDetectorCompactSourceCode.baseCompactTangency
          (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
          (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)))
      v

/-- The affine detector curve recovered from a corrected finite-chart
orbit. -/
def affineCurve
    (u : NormalizedCorrectedFixedDetectorCompactSourceCode.CompilerInput eqs vars)
    (v :
      AllAffineCompactSourceChart.FiniteSourceSpace
        (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDimension eqs vars)
        (NormalizedCorrectedFixedDetectorCompactSourceCode.driftDimension vars))
    (t : ℝ) :
    Fin (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDimension
      eqs vars) → ℝ :=
  AllAffineCompactSourceClock.affineCurve
    (compactFlow u) (finiteInvariant u) v t

/-- The data selected from an ergodic conditional with zero drift. -/
structure SelectedValidityOrbit
    (u : NormalizedCorrectedFixedDetectorCompactSourceCode.CompilerInput eqs vars)
    where
  point :
    AllAffineCompactSourceChart.FiniteSourceSpace
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDimension eqs vars)
      (NormalizedCorrectedFixedDetectorCompactSourceCode.driftDimension vars)
  speedMean : ℝ
  clock :
    PositiveIntegralClock
      (stateClockWeight
        (affineSpeed
          (speedExponent
            (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)))
        (affineCurve u point))
  speedMean_pos : 0 < speedMean
  recurrent :
    ForwardRecurrentAt
      (fun t : ℝ ↦
        ((compactFlow u).restrict (finiteInvariant u)) t point) 0
  validityDrift_zero :
    ∀ t : ℝ,
      finiteDriftCoordinateBCF
        (speedExponent (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
        (NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale u)
        (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode
          (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
        (NormalizedCorrectedFixedDetectorDriftCode.validityIndex vars)
        (((compactFlow u).restrict (finiteInvariant u)) t point) = 0
  speed_generic :
    Tendsto
      (fun q : ℕ ↦
        Dynamics.integerOrbitAverageObservable
          ((compactFlow u).restrict (finiteInvariant u))
          (affineSpeedBCF
            (speedExponent
              (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)))
          (q + 1) point)
      atTop (𝓝 speedMean)
  drift_generic :
    ∀ i :
        Fin (NormalizedCorrectedFixedDetectorCompactSourceCode.driftDimension vars),
      Tendsto
        (fun q : ℕ ↦
          Dynamics.integerOrbitAverageObservable
            ((compactFlow u).restrict (finiteInvariant u))
            (finiteDriftCoordinateBCF
              (speedExponent
                (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
              (NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale u)
              (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode
                (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
              i)
            (q + 1) point)
        atTop (𝓝 0)

/-- The compact normalized corrected validity drift is nonnegative whenever the
accumulator scale is nonnegative. -/
theorem finiteValidityDrift_nonneg
    (u : NormalizedCorrectedFixedDetectorCompactSourceCode.CompilerInput eqs vars)
    (hscale :
      0 ≤
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale u).decode :
          ℝ))
    (v :
      AllAffineCompactSourceChart.FiniteSourceSpace
        (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDimension eqs vars)
        (NormalizedCorrectedFixedDetectorCompactSourceCode.driftDimension vars)) :
    0 ≤
      finiteDriftCoordinateBCF
        (speedExponent (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
        (NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale u)
        (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode
          (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
        (NormalizedCorrectedFixedDetectorDriftCode.validityIndex vars) v := by
  let I := NormalizedCorrectedFixedDetectorCompactSourceCode.system u
  let z : FixedDetectorPolynomialCode.State eqs vars :=
    FixedDetectorPolynomialCode.state (affinePoint v)
  have heval :=
    NormalizedCorrectedFixedDetectorDriftCode.eval_driftCode_validityIndex I z
  have heval' :
      _root_.MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
          (affinePoint v)
          (PolynomialCode.decode
            (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode I
              (NormalizedCorrectedFixedDetectorDriftCode.validityIndex vars))) =
        NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue I z := by
    simpa [z, NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode] using
      heval
  rw [finiteDriftCoordinateBCF_eq
    (speedExponent I)
    (NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale u)
    (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode I)
    (by
      intro i
      simpa only [speedExponent,
        NormalizedCorrectedFixedDetectorCompactSourceCode.clearingExponent] using
        NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode_termsAffineBlockDegreeLE
          I i)
    (NormalizedCorrectedFixedDetectorDriftCode.validityIndex vars) v]
  rw [heval']
  exact mul_nonneg
    (mul_nonneg hscale
      (affineSpeed_nonneg (speedExponent I) (affinePoint v)))
    (NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue_nonneg I z)

/-- Zero conditional base means select a recurrent, speed-generic orbit
whose validity sum of squares vanishes at every compact time. -/
theorem exists_selectedValidityOrbit_of_conditionalBase_zero
    (u : NormalizedCorrectedFixedDetectorCompactSourceCode.CompilerInput eqs vars)
    (μ : Dynamics.InvariantProbabilityMeasure (compactFlow u))
    (hμ :
      Dynamics.IsErgodicInvariantProbability
        (compactFlow u) μ.measure)
    (hpos :
      (μ.measure :
        Measure
          (AllAffineCompactSourceChart.SourceSpace
            (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDimension
              eqs vars)
            (NormalizedCorrectedFixedDetectorCompactSourceCode.driftDimension vars)))
        (sourceFiniteInteriorSet
          (m :=
            NormalizedCorrectedFixedDetectorCompactSourceCode.driftDimension vars)
          (layout
            (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDimension
              eqs vars))) ≠ 0)
    (hzero :
      ∀ i :
          Fin (NormalizedCorrectedFixedDetectorCompactSourceCode.driftDimension vars),
        (∫ b,
          baseDriftBCF
            (layout
              (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDimension
                eqs vars))
            (2 *
              speedExponent
                (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
            (NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale u)
            (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode
              (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
            b i
          ∂((conditionalBaseProbability
              (layout
                (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDimension
                  eqs vars))
              (speedExponent
                (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
              (2 *
                speedExponent
                  (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
              (NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale u)
              (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode
                (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
                (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
              (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode_termsDegreeLE
                (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
                (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
              (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode
                (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
              (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode_termsDegreeLE
                (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
              (NormalizedCorrectedFixedDetectorCompactSourceCode.rewardMargin u)
              (NormalizedCorrectedFixedDetectorCompactSourceCode.baseCompactTangency
                (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
                (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
              μ hpos).measure :
            Measure
              (BaseSpace
                (layout
                  (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDimension
                    eqs vars))))) = 0)
    (hscale :
      0 ≤
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale u).decode :
          ℝ)) :
    Nonempty (SelectedValidityOrbit u) := by
  obtain ⟨v, c, hclock, hc, hrec, hvalid, hspeed, hdrift⟩ :=
    exists_recurrent_genericPhysicalPoint_zeroCoordinate_of_conditionalBase_zero
      (speedExponent
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
      (speedExponent
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
      (NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale u)
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode
        (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode_termsDegreeLE
        (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode_termsDegreeLE
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
      (NormalizedCorrectedFixedDetectorCompactSourceCode.rewardMargin u)
      μ hμ hpos hzero
      (NormalizedCorrectedFixedDetectorDriftCode.validityIndex vars)
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
  {u : NormalizedCorrectedFixedDetectorCompactSourceCode.CompilerInput eqs vars}
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
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale u).decode :
          ℝ))
    (t : ℝ) :
    NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
        (O.compactTimeState t) = 0 := by
  let I := NormalizedCorrectedFixedDetectorCompactSourceCode.system u
  let vt :=
    ((compactFlow u).restrict (finiteInvariant u)) t O.point
  have hzero := O.validityDrift_zero t
  have hsem :
      _root_.MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
          (affinePoint vt)
          (PolynomialCode.decode
            (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode I
              (NormalizedCorrectedFixedDetectorDriftCode.validityIndex vars))) =
        NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue I
          (FixedDetectorPolynomialCode.state (affinePoint vt)) := by
    simpa [NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode] using
      (NormalizedCorrectedFixedDetectorDriftCode.eval_driftCode_validityIndex
        I (FixedDetectorPolynomialCode.state (affinePoint vt)))
  rw [finiteDriftCoordinateBCF_eq
    (speedExponent I)
    (NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale u)
    (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode I)
    (by
      intro i
      simpa only [speedExponent,
        NormalizedCorrectedFixedDetectorCompactSourceCode.clearingExponent] using
        NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode_termsAffineBlockDegreeLE
          I i)
    (NormalizedCorrectedFixedDetectorDriftCode.validityIndex vars) vt,
    hsem] at hzero
  have hfactor :
      ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale u).decode :
          ℝ) *
        affineSpeed (speedExponent I) (affinePoint vt) ≠ 0 :=
    mul_ne_zero hscale.ne'
      (affineSpeed_pos (speedExponent I) (affinePoint vt)).ne'
  have henergy :
      NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue I
          (FixedDetectorPolynomialCode.state (affinePoint vt)) = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hfactor
  simpa only [compactTimeState, affineCurve,
    AllAffineCompactSourceClock.affineCurve, vt, I] using henergy

/-- Ordinary physical-time detector point obtained from the selected
positive integral clock. -/
def physicalPoint (τ : ℝ) :
    Fin (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDimension
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
          (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
        (compactFlow u) (finiteInvariant u) O.point O.clock τ :=
  rfl

/-- In physical time the selected point is a forward trajectory of the
literal fixed-detector polynomial field. -/
theorem physicalPoint_isForwardTrajectory :
    IsForwardTrajectory
      (PolynomialFieldCode.realize
        (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode
          (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
          (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)))
      O.physicalPoint
      (affinePoint O.point) := by
  have hAffine :
      ∀ j,
        MixedCentralPolynomialCode.TermsAffineBlockDegreeLE
          (layout
            (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDimension
              eqs vars))
          (2 *
            speedExponent
              (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
          (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
            (NormalizedCorrectedFixedDetectorCompactSourceCode.system u) j) := by
    intro j
    simpa only [speedExponent,
      NormalizedCorrectedFixedDetectorCompactSourceCode.clearingExponent] using
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode_termsAffineBlockDegreeLE
        (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u) j)
  simpa only [physicalPoint_eq_physicalCurve] using
    (AllAffineCompactSourceClock.physicalCurve_isForwardTrajectory
      (speedExponent
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
      (NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale u)
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode
        (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
      hAffine (compactFlow u) (compactFlow_integralCurve u)
      (finiteInvariant u) O.point O.clock)

/-- Compact recurrence survives the physical inverse-clock
reparametrization. -/
theorem physicalPoint_forwardRecurrentAt :
    ForwardRecurrentAt O.physicalPoint 0 := by
  simpa only [physicalPoint_eq_physicalCurve] using
    (AllAffineCompactSourceClock.physicalCurve_forwardRecurrentAt
      (speedExponent
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
      (compactFlow u) (finiteInvariant u) O.point O.clock O.recurrent)

/-- The validity sum of squares vanishes for every ordinary physical
time. -/
theorem validityEnergy_zero_physicalTime
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale u).decode :
          ℝ))
    (τ : ℝ) :
    NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
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
                (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)))
            (affineCurve u O.point))
          (positiveIntegerHorizon q))
      atTop atTop :=
  O.clock.tendsto_atTop.comp positiveIntegerHorizon_tendsto_atTop

/-- Every normalized corrected drift coordinate has zero ordinary-time Cesàro
average along the same unbounded physical clock horizons. -/
theorem physicalDriftAverage_tendsto_zero
    (hscale :
      ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale u).decode :
          ℝ) ≠ 0)
    (i :
      Fin (NormalizedCorrectedFixedDetectorCompactSourceCode.driftDimension vars)) :
    Tendsto
      (fun q : ℕ ↦
        (integralClock
          (stateClockWeight
            (affineSpeed
              (speedExponent
                (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)))
            (affineCurve u O.point))
          (positiveIntegerHorizon q))⁻¹ *
          ∫ τ in (0 : ℝ)..
              integralClock
                (stateClockWeight
                  (affineSpeed
                    (speedExponent
                      (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)))
                  (affineCurve u O.point))
                (positiveIntegerHorizon q),
            _root_.MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
              (O.physicalPoint τ)
              (PolynomialCode.decode
                (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode
                  (NormalizedCorrectedFixedDetectorCompactSourceCode.system u) i)))
      atTop (𝓝 0) := by
  have hh :
      ∀ r,
        MixedCentralPolynomialCode.TermsAffineBlockDegreeLE
          (layout
            (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDimension
              eqs vars))
          (2 *
            speedExponent
              (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
          (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode
            (NormalizedCorrectedFixedDetectorCompactSourceCode.system u) r) := by
    intro r
    simpa only [speedExponent,
      NormalizedCorrectedFixedDetectorCompactSourceCode.clearingExponent] using
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode_termsAffineBlockDegreeLE
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u) r)
  simpa only [physicalPoint_eq_physicalCurve] using
    (AllAffinePhysicalDriftAverages.physicalDriftAverage_tendsto_zero
      (speedExponent
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
      (NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale u)
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
      hh (compactFlow u) (finiteInvariant u) O.point i hscale
      O.speedMean_pos.ne' O.speed_generic (O.drift_generic i) O.clock)

end SelectedValidityOrbit

end

end HGAS.NormalizedCorrectedFixedDetectorValidityOrbit
