import HGAS.Arithmetic.FixedDetectorCompactSourceCode
import HGAS.Compiler.AllAffineCompactSourceClock
import Mathlib.Tactic

/-!
# Recovering the fixed detector from its compact source

This file specializes the reusable one-block chart and physical-clock
theorems to the literal fixed detector compiler.  For a compiler input
`u`, a point in the invariant finite interior of the canonical compact
source determines:

* an affine curve in the exact detector coordinate space;
* a positive compactification speed
  `(1 + ‖z‖²)⁻sourceDegreeBound`; and
* whenever that speed has positive generic mean, a recurrent ordinary-time
  trajectory of the uncompactified detector polynomial ODE.

The structured detector state is recovered by
`FixedDetectorPolynomialCode.state`; the proved identity
`point_state` guarantees that no coordinate information is lost.
-/

namespace HGAS

open Filter Set Topology
open scoped BoundedContinuousFunction

noncomputable section

namespace FixedDetectorCompactSourceTrajectory

open CompactAccumulatorPipelineCode
open CompactAccumulatorPipelineCode.AllAffineCompactSourceChart
open CompactAccumulatorPipelineCode.AllAffineCompactSourceClock

variable {eqs vars : ℕ}

abbrev sourceDimension (eqs vars : ℕ) : ℕ :=
  FixedDetectorCompactSourceCode.sourceDimension eqs vars

abbrev driftDimension (vars : ℕ) : ℕ :=
  FixedDetectorCompactSourceCode.driftDimension vars

abbrev SourceSpace (eqs vars : ℕ) :=
  AllAffineCompactSourceChart.SourceSpace
    (sourceDimension eqs vars) (driftDimension vars)

abbrev FiniteSourceSpace (eqs vars : ℕ) :=
  AllAffineCompactSourceChart.FiniteSourceSpace
    (sourceDimension eqs vars) (driftDimension vars)

/-- Canonical complete compact source flow emitted for one fixed detector
compiler input. -/
def compactFlow
    (u : FixedDetectorCompactSourceCode.CompilerInput eqs vars) :
    Flow ℝ (SourceSpace eqs vars) :=
  sourceFlow
    FixedDetectorCompactSourceCode.layout
    (FixedDetectorCompactSourceCode.sourceDegreeBound
      (FixedDetectorCompactSourceCode.system u))
    (FixedDetectorCompactSourceCode.clearingExponent
      (FixedDetectorCompactSourceCode.system u))
    (FixedDetectorCompactSourceCode.accumulatorScale u)
    (FixedDetectorCompactSourceCode.sourceFieldCode
      (FixedDetectorCompactSourceCode.parameters u)
      (FixedDetectorCompactSourceCode.system u))
    (FixedDetectorCompactSourceCode.sourceDriftCode
      (FixedDetectorCompactSourceCode.system u))
    (FixedDetectorCompactSourceCode.rewardMargin u)

/-- The finite affine-and-accumulator chart is invariant under the
canonical compact source flow. -/
def finiteInvariant
    (u : FixedDetectorCompactSourceCode.CompilerInput eqs vars) :
    IsInvariant (compactFlow u)
      (sourceFiniteInteriorSet
        (m := driftDimension vars)
        FixedDetectorCompactSourceCode.layout) :=
  canonicalFiniteInteriorInvariant
    FixedDetectorCompactSourceCode.layout
    (FixedDetectorCompactSourceCode.sourceDegreeBound
      (FixedDetectorCompactSourceCode.system u))
    (FixedDetectorCompactSourceCode.clearingExponent
      (FixedDetectorCompactSourceCode.system u))
    (FixedDetectorCompactSourceCode.accumulatorScale u)
    (FixedDetectorCompactSourceCode.sourceFieldCode
      (FixedDetectorCompactSourceCode.parameters u)
      (FixedDetectorCompactSourceCode.system u))
    (FixedDetectorCompactSourceCode.sourceFieldCode_termsDegreeLE
      (FixedDetectorCompactSourceCode.parameters u)
      (FixedDetectorCompactSourceCode.system u))
    (FixedDetectorCompactSourceCode.sourceDriftCode
      (FixedDetectorCompactSourceCode.system u))
    (FixedDetectorCompactSourceCode.sourceDriftCode_termsDegreeLE
      (FixedDetectorCompactSourceCode.system u))
    (FixedDetectorCompactSourceCode.rewardMargin u)
    (FixedDetectorCompactSourceCode.baseCompactTangency
      (FixedDetectorCompactSourceCode.parameters u)
      (FixedDetectorCompactSourceCode.system u))

/-- Every compact source orbit solves the exact emitted polynomial field. -/
theorem compactFlow_integralCurve
    (u : FixedDetectorCompactSourceCode.CompilerInput eqs vars)
    (v : SourceSpace eqs vars) :
    IsIntegralCurve
      (fun t ↦ (compactFlow u t v).1)
      (fun _ x ↦
        PolynomialFieldCode.realize
          (fieldCode
            FixedDetectorCompactSourceCode.layout
            (FixedDetectorCompactSourceCode.clearingExponent
              (FixedDetectorCompactSourceCode.system u))
            (FixedDetectorCompactSourceCode.accumulatorScale u)
            (FixedDetectorCompactSourceCode.sourceFieldCode
              (FixedDetectorCompactSourceCode.parameters u)
              (FixedDetectorCompactSourceCode.system u))
            (FixedDetectorCompactSourceCode.sourceDriftCode
              (FixedDetectorCompactSourceCode.system u))) x) := by
  exact
    sourceFlow_integralCurve
      FixedDetectorCompactSourceCode.layout
      (FixedDetectorCompactSourceCode.sourceDegreeBound
        (FixedDetectorCompactSourceCode.system u))
      (FixedDetectorCompactSourceCode.clearingExponent
        (FixedDetectorCompactSourceCode.system u))
      (FixedDetectorCompactSourceCode.accumulatorScale u)
      (FixedDetectorCompactSourceCode.sourceFieldCode
        (FixedDetectorCompactSourceCode.parameters u)
        (FixedDetectorCompactSourceCode.system u))
      (FixedDetectorCompactSourceCode.sourceFieldCode_termsDegreeLE
        (FixedDetectorCompactSourceCode.parameters u)
        (FixedDetectorCompactSourceCode.system u))
      (FixedDetectorCompactSourceCode.sourceDriftCode
        (FixedDetectorCompactSourceCode.system u))
      (FixedDetectorCompactSourceCode.sourceDriftCode_termsDegreeLE
        (FixedDetectorCompactSourceCode.system u))
      (FixedDetectorCompactSourceCode.rewardMargin u)
      (fullCompactTangencyHypothesis_of_base
        FixedDetectorCompactSourceCode.layout
        (FixedDetectorCompactSourceCode.clearingExponent
          (FixedDetectorCompactSourceCode.system u))
        (FixedDetectorCompactSourceCode.sourceFieldCode
          (FixedDetectorCompactSourceCode.parameters u)
          (FixedDetectorCompactSourceCode.system u))
        (FixedDetectorCompactSourceCode.baseCompactTangency
          (FixedDetectorCompactSourceCode.parameters u)
          (FixedDetectorCompactSourceCode.system u)))
      v

/-- The recovered affine detector point along a finite compact-source
orbit. -/
def affineCurve
    (u : FixedDetectorCompactSourceCode.CompilerInput eqs vars)
    (v : FiniteSourceSpace eqs vars) (t : ℝ) :
    Fin (sourceDimension eqs vars) → ℝ :=
  AllAffineCompactSourceClock.affineCurve
    (compactFlow u) (finiteInvariant u) v t

/-- The fixed detector's intrinsic speed observable on its finite compact
chart. -/
def speedBCF
    (u : FixedDetectorCompactSourceCode.CompilerInput eqs vars) :
    FiniteSourceSpace eqs vars →ᵇ ℝ :=
  affineSpeedBCF
    (FixedDetectorCompactSourceCode.sourceDegreeBound
      (FixedDetectorCompactSourceCode.system u))

/-- A positive generic speed mean gives the global physical clock for the
fixed detector orbit. -/
theorem positiveClock_of_genericSpeed
    (u : FixedDetectorCompactSourceCode.CompilerInput eqs vars)
    (v : FiniteSourceSpace eqs vars)
    {c : ℝ} (hc : 0 < c)
    (hgeneric :
      Tendsto
        (fun q : ℕ ↦
          Dynamics.integerOrbitAverageObservable
            ((compactFlow u).restrict (finiteInvariant u))
            (speedBCF u) (q + 1) v)
        atTop (𝓝 c)) :
    PositiveIntegralClock
      (stateClockWeight
        (affineSpeed
          (FixedDetectorCompactSourceCode.sourceDegreeBound
            (FixedDetectorCompactSourceCode.system u)))
        (affineCurve u v)) := by
  apply
    AllAffineCompactSourceClock.positiveClock_of_genericSpeed
      (FixedDetectorCompactSourceCode.sourceDegreeBound
        (FixedDetectorCompactSourceCode.system u))
      (compactFlow u) (finiteInvariant u) v hc
  simpa only [speedBCF] using hgeneric

/-- The ordinary-time affine detector curve obtained by inverting the
physical clock. -/
def physicalPoint
    (u : FixedDetectorCompactSourceCode.CompilerInput eqs vars)
    (v : FiniteSourceSpace eqs vars)
    (hclock :
      PositiveIntegralClock
        (stateClockWeight
          (affineSpeed
            (FixedDetectorCompactSourceCode.sourceDegreeBound
              (FixedDetectorCompactSourceCode.system u)))
          (affineCurve u v)))
    (τ : ℝ) :
    Fin (sourceDimension eqs vars) → ℝ :=
  affineCurve u v
    ((PositiveIntegralClock.orderIso hclock).symm τ)

/-- In physical time, the recovered affine point solves the literal fixed
detector polynomial source field. -/
theorem physicalPoint_isForwardTrajectory
    (u : FixedDetectorCompactSourceCode.CompilerInput eqs vars)
    (v : FiniteSourceSpace eqs vars)
    (hclock :
      PositiveIntegralClock
        (stateClockWeight
          (affineSpeed
            (FixedDetectorCompactSourceCode.sourceDegreeBound
              (FixedDetectorCompactSourceCode.system u)))
          (affineCurve u v))) :
    IsForwardTrajectory
      (PolynomialFieldCode.realize
        (FixedDetectorCompactSourceCode.sourceFieldCode
          (FixedDetectorCompactSourceCode.parameters u)
          (FixedDetectorCompactSourceCode.system u)))
      (physicalPoint u v hclock)
      (affinePoint v) := by
  have hAffine :
      ∀ j,
        MixedCentralPolynomialCode.TermsAffineBlockDegreeLE
          (AllAffineCompactSourceChart.layout
            (sourceDimension eqs vars))
          (2 *
            FixedDetectorCompactSourceCode.sourceDegreeBound
              (FixedDetectorCompactSourceCode.system u))
          (FixedDetectorCompactSourceCode.sourceFieldCode
            (FixedDetectorCompactSourceCode.parameters u)
            (FixedDetectorCompactSourceCode.system u) j) := by
    intro j
    simpa only [FixedDetectorCompactSourceCode.clearingExponent,
      FixedDetectorCompactSourceCode.layout] using
      (FixedDetectorCompactSourceCode.sourceFieldCode_termsAffineBlockDegreeLE
        (FixedDetectorCompactSourceCode.parameters u)
        (FixedDetectorCompactSourceCode.system u) j)
  exact
    AllAffineCompactSourceClock.physicalCurve_isForwardTrajectory
      (FixedDetectorCompactSourceCode.sourceDegreeBound
        (FixedDetectorCompactSourceCode.system u))
      (FixedDetectorCompactSourceCode.accumulatorScale u)
      (FixedDetectorCompactSourceCode.sourceFieldCode
        (FixedDetectorCompactSourceCode.parameters u)
        (FixedDetectorCompactSourceCode.system u))
      (FixedDetectorCompactSourceCode.sourceDriftCode
        (FixedDetectorCompactSourceCode.system u))
      hAffine
      (compactFlow u)
      (compactFlow_integralCurve u)
      (finiteInvariant u) v hclock

/-- Structured detector state recovered from the ordinary affine point. -/
def physicalState
    (u : FixedDetectorCompactSourceCode.CompilerInput eqs vars)
    (v : FiniteSourceSpace eqs vars)
    (hclock :
      PositiveIntegralClock
        (stateClockWeight
          (affineSpeed
            (FixedDetectorCompactSourceCode.sourceDegreeBound
              (FixedDetectorCompactSourceCode.system u)))
          (affineCurve u v)))
    (τ : ℝ) :
    FixedDetectorPolynomialCode.State eqs vars :=
  FixedDetectorPolynomialCode.state (physicalPoint u v hclock τ)

@[simp]
theorem point_physicalState
    (u : FixedDetectorCompactSourceCode.CompilerInput eqs vars)
    (v : FiniteSourceSpace eqs vars)
    (hclock :
      PositiveIntegralClock
        (stateClockWeight
          (affineSpeed
            (FixedDetectorCompactSourceCode.sourceDegreeBound
              (FixedDetectorCompactSourceCode.system u)))
          (affineCurve u v)))
    (τ : ℝ) :
    FixedDetectorPolynomialCode.point
        (physicalState u v hclock τ) =
      physicalPoint u v hclock τ :=
  FixedDetectorPolynomialCode.point_state _

/-- Compact recurrence transports to the ordinary affine detector curve. -/
theorem physicalPoint_forwardRecurrentAt
    (u : FixedDetectorCompactSourceCode.CompilerInput eqs vars)
    (v : FiniteSourceSpace eqs vars)
    (hclock :
      PositiveIntegralClock
        (stateClockWeight
          (affineSpeed
            (FixedDetectorCompactSourceCode.sourceDegreeBound
              (FixedDetectorCompactSourceCode.system u)))
          (affineCurve u v)))
    (hrec :
      ForwardRecurrentAt
        (fun t : ℝ ↦
          ((compactFlow u).restrict (finiteInvariant u)) t v) 0) :
    ForwardRecurrentAt (physicalPoint u v hclock) 0 := by
  exact
    AllAffineCompactSourceClock.physicalCurve_forwardRecurrentAt
      (FixedDetectorCompactSourceCode.sourceDegreeBound
        (FixedDetectorCompactSourceCode.system u))
      (compactFlow u) (finiteInvariant u) v hclock hrec

end FixedDetectorCompactSourceTrajectory

end

end HGAS
