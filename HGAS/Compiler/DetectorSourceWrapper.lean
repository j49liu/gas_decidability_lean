import HGAS.Arithmetic.DetectorInvariantAverage
import HGAS.Wrapper.UnitSphereWrapperConcreteReduction
import Mathlib.Tactic

/-!
# The exact source-compiler interface

The arithmetic detector and the homogeneous polynomial wrapper are both
fully formalized.  This file records the precise interface that the
remaining polynomial source construction must implement in order to join
those two pieces.

For a DQL system `I`, a source certificate consists of:

* a rational polynomial vector field `P` tangent to a compact product of
  spheres;
* a rational polynomial reward `a`;
* a flow `ψ` whose ambient trajectories solve `y' = P(y)`;
* a continuous equivariant factor from `ψ` to the detector phase torus;
* uniqueness of Haar measure as the detector-phase marginal of every
  invariant source probability;
* literal equality between the polynomial source reward and the negative
  half-detector pulled back along that factor.

The theorem at the end then has no hidden dynamical step: the concrete
wrapper theorem converts GAS to negativity of the source maximal invariant
average, and the detector theorem converts that negativity to solvability
of `I`.

This certificate is deliberately a *proof interface*, not an existence
claim.  Constructing it effectively from the modular/Jacobi blocks is the
remaining source-compilation theorem.
-/

namespace HGAS

open Function
open scoped BoundedContinuousFunction

noncomputable section

namespace Compiler

variable {n k eqs vars : ℕ}

/-- Complete semantic certificate expected from the polynomial source
compiler for one DQL instance.

The dimensions `n` and `k`, block assignment, degree bound, and DQL arities
remain parameters, so the same object can be used both for the
variable-resource construction and for a later fixed-resource compiler. -/
structure DetectorSourceCertificate
    (sourceBlock : Fin n → Fin k)
    [Nonempty (UnitSpherePolynomialWrapper.SourceProductSphere sourceBlock)]
    (I : DQLSystem eqs vars) where
  /-- Odd degree used by the exact homogeneous wrapper. -/
  degree : ℕ
  degree_ge_three : 3 ≤ degree
  degree_odd : degree % 2 = 1
  /-- Rational polynomial source vector field and reward. -/
  fieldCode : PolynomialFieldCode n
  field_degree :
    ∀ j, PolynomialCode.TermsDegreeLE degree (fieldCode j)
  rewardCode : PolynomialCode n
  reward_degree :
    PolynomialCode.TermsDegreeLE (degree - 1) rewardCode
  /-- A block used by the wrapper's proper-face witness. -/
  properFaceBlock : Fin k
  /-- The source field is tangent to every sphere factor. -/
  tangent :
    ∀ y :
        UnitSpherePolynomialWrapper.SourceProductSphere sourceBlock,
      UnitSpherePolynomialWrapper.SourceTangentAt sourceBlock y.1
        (PolynomialFieldCode.realize fieldCode y.1)
  /-- The intended compact source flow. -/
  sourceFlow :
    Flow ℝ
      (UnitSpherePolynomialWrapper.SourceProductSphere sourceBlock)
  sourceFlow_integralCurve :
    ∀ y,
      IsIntegralCurve
        (fun t ↦ (sourceFlow t y).1)
        (fun _ x ↦ PolynomialFieldCode.realize fieldCode x)
  /-- Frequencies and phase factor seen by the Fourier detector. -/
  detectorFrequency : DetectorPhase eqs vars → ℝ
  detectorPhase :
    UnitSpherePolynomialWrapper.SourceProductSphere sourceBlock →
      UnitAddTorus (DetectorPhase eqs vars)
  detectorPhase_continuous : Continuous detectorPhase
  detectorPhase_equivariant :
    ∀ t : ℝ,
      Semiconj detectorPhase (sourceFlow t)
        (Clocks.RadicalClock.torusTranslationFlow detectorFrequency t)
  /-- Every invariant source probability has Haar detector-phase marginal. -/
  detectorPhase_uniqueHaar :
    ∀ μ : Dynamics.InvariantProbabilityMeasure sourceFlow,
      (μ.mapEquivariant detectorPhase detectorPhase_continuous
          detectorPhase_equivariant).measure =
        Clocks.RadicalClock.torusHaarProbability
  /-- Exact readout identity required by the source compiler. -/
  reward_eq_detector :
    UnitSpherePolynomialWrapper.sourceRewardBCF
        sourceBlock rewardCode =
      (-halfExpandedDetectorRealBCF I).compContinuous
        ⟨detectorPhase, detectorPhase_continuous⟩

namespace DetectorSourceCertificate

/-- The executable homogeneous rational polynomial field emitted by the
already-verified wrapper from a source certificate. -/
def finalFieldCode
    {sourceBlock : Fin n → Fin k}
    [Nonempty (UnitSpherePolynomialWrapper.SourceProductSphere sourceBlock)]
    {I : DQLSystem eqs vars}
    (C : DetectorSourceCertificate sourceBlock I) :
    PolynomialFieldCode (n + 1) :=
  UnitSpherePolynomialWrapper.finalFieldCode
    sourceBlock C.degree C.fieldCode C.rewardCode

/-- **End-to-end semantic composition theorem.**

Once the source compiler supplies a `DetectorSourceCertificate`, GAS of the
concrete homogeneous rational polynomial output is equivalent to solvability
of the original DQL system. -/
theorem finalField_gas_iff_solvable
    {sourceBlock : Fin n → Fin k}
    [Nonempty (UnitSpherePolynomialWrapper.SourceProductSphere sourceBlock)]
    {I : DQLSystem eqs vars}
    (C : DetectorSourceCertificate sourceBlock I) :
    GloballyAsymptoticallyStable
        (PolynomialFieldCode.realize C.finalFieldCode) 0 ↔
      I.Solvable := by
  change
    GloballyAsymptoticallyStable
        (PolynomialFieldCode.realize
          (UnitSpherePolynomialWrapper.finalFieldCode
            sourceBlock C.degree C.fieldCode C.rewardCode)) 0 ↔
      I.Solvable
  rw [UnitSpherePolynomialWrapper.realize_finalFieldCode_gas_iff_externalSourceMaximum_neg
      sourceBlock C.degree C.degree_ge_three C.degree_odd
      C.fieldCode C.field_degree C.rewardCode C.reward_degree
      C.properFaceBlock C.tangent C.sourceFlow
      C.sourceFlow_integralCurve]
  rw [C.reward_eq_detector]
  exact maximalInvariantAverage_neg_halfDetector_iff_solvable
    C.sourceFlow C.detectorFrequency C.detectorPhase
    C.detectorPhase_continuous C.detectorPhase_equivariant
    C.detectorPhase_uniqueHaar I

end DetectorSourceCertificate

end Compiler

end

end HGAS
