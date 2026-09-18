import HGAS.Arithmetic.FixedDetectorOrdinaryTimeMomentSeries
import HGAS.Modular.JacobiBlochRecurrentReality
import Mathlib.Tactic

/-!
# Explicit arbitrary-phase recurrent-series endpoint

This file records the exact hypotheses under which the current formal
chain yields one global arbitrary-phase classified series for a selected
fixed-detector block.

The reverse polynomial crosswalk and zero validity do **not** by
themselves identify an arbitrary linked-Jacobi trajectory with one affine
Bloch path.  The current unconditional linked theory provides a coherent
moving theta representation; its own documentation explicitly stops
short of the constant-parameter simultaneous Bloch integral.  Therefore
the two global continuation facts are exposed below as hypotheses:

* the selected Jacobi path equals one affine Bloch path; and
* the compiled gauge output uses one constant fourth-root branch along
  that path.

Once these are supplied, forward recurrence forces the Bloch parameter
`a0` to be real, and the three corrected `Real.pi` moment theorems give
the required rows for every ordinary time.  The controller phase origin
is arbitrary throughout.
-/

namespace HGAS

open Modular
open Clocks
open Clocks.ControllerPhaseProductCharacterCode

noncomputable section

namespace FixedDetectorArbitraryPhaseClassifiedSeries

open FixedDetectorOrdinaryTimeBlochCrosswalk
open FixedDetectorOrdinaryTimeMomentSeries

variable {eqs vars : ℕ}

/-- Exact hypotheses for a single globally classified recurrent detector
block with arbitrary initial controller phase. -/
structure Hypotheses
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (x :
      ℝ →
        Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (controller :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → Circle)
    (j : Fin vars)
    (p : AffineBlochParameters)
    (d : ℂ)
    (t₀ : ℝ) : Prop where
  integralCurve :
    IsIntegralCurve
      x
      (fun _ y =>
        PolynomialFieldCode.realize
          (FixedDetectorPolynomialCode.fieldCode parameters I) y)
  validity_at :
    FixedDetectorDriftCode.validityEnergyValue I
        (FixedDetectorReverseTrajectoryCrosswalk.recoveredState
          x t₀) =
      0
  controllers_eq :
    ∀ t,
      (FixedDetectorReverseTrajectoryCrosswalk.recoveredState
          x t).base.base.source.controllers =
        CanonicalFixedDetectorTrajectory.clockPath
          parameters controller phase₀ t
  jacobi_eq :
    (fun t =>
      ((FixedDetectorReverseTrajectoryCrosswalk.recoveredState
        x t).base.base.source.linked j).jacobi) =
      p.jacobiBlochPath
  output_eq :
    ∀ t,
      (FixedDetectorReverseTrajectoryCrosswalk.recoveredState
          x t).base.base.gauge j *
          ((FixedDetectorReverseTrajectoryCrosswalk.recoveredState
            x t).base.base.source.linked j).jacobi.T1 =
        p.fourthRootGauge d t *
          (p.jacobiBlochPath t).T1
  recurrent :
    ForwardRecurrentAt
      (fun t =>
        JacobiPolynomialCode.point
          ((FixedDetectorReverseTrajectoryCrosswalk.recoveredState
            x t).base.base.source.linked j).jacobi)
      t₀
  omega_ne_zero :
    CanonicalFixedDetectorTrajectory.omegaFrequency
      parameters controller j ≠ 0
  c0_ne_zero : p.c0 ≠ 0
  kappa_eq :
    p.kappa =
      CanonicalFixedDetectorTrajectory.omegaFrequency
        parameters controller j / Real.pi
  nu_eq :
    p.nu =
      (CanonicalFixedDetectorTrajectory.omegaFrequency
          parameters controller j +
        CanonicalFixedDetectorTrajectory.numberFrequency
          parameters I controller j) /
        (2 * Real.pi)

/-- The reusable conclusion: structured ODE semantics, the selected
zero-validity residuals, reality of `a0`, and all three literal moment
rows at every ordinary time. -/
structure Conclusion
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (x :
      ℝ →
        Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (controller :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → Circle)
    (j : Fin vars)
    (p : AffineBlochParameters)
    (d : ℂ)
    (t₀ : ℝ) : Prop where
  structured :
    FixedDetectorReverseTrajectoryCrosswalk.IsStructuredTrajectory
      parameters I x
  linkedResiduals :
    ∀ r : LinkedJacobiResidualIndex,
      linkedJacobiResidual r
        ((FixedDetectorReverseTrajectoryCrosswalk.recoveredState
          x t₀).base.base.source.linked j) =
        0
  a0_real : p.a0.im = 0
  mean :
    ∀ t,
      evalPair (FixedDetectorMomentCode.jacobiMeanCode j)
          (x t) =
        quadraticMomentSeries
            (p.gaugedBlochCoefficient d)
            (CanonicalFixedDetectorTrajectory.omegaFrequency
              parameters controller j)
            (CanonicalFixedDetectorTrajectory.numberFrequency
                parameters I controller j /
              CanonicalFixedDetectorTrajectory.omegaFrequency
                parameters controller j)
            p.a0.re 0 t -
          1
  plus :
    ∀ t,
      let c :=
        characterValue
          (FixedDetectorMomentCode.jacobiPlusExponent I j)
          (CanonicalFixedDetectorTrajectory.clockPath
            parameters controller phase₀ 0)
      evalPair (FixedDetectorMomentCode.jacobiPlusMeanCode I j)
          (x t) =
        quadraticMomentSeries
            (fun k => c * p.gaugedBlochCoefficient d k)
            (CanonicalFixedDetectorTrajectory.omegaFrequency
              parameters controller j)
            (CanonicalFixedDetectorTrajectory.numberFrequency
                parameters I controller j /
              CanonicalFixedDetectorTrajectory.omegaFrequency
                parameters controller j)
            p.a0.re 1 t -
          (1 / 256 : ℚ)
  minus :
    ∀ t,
      let c :=
        characterValue
          (FixedDetectorMomentCode.jacobiMinusExponent I j)
          (CanonicalFixedDetectorTrajectory.clockPath
            parameters controller phase₀ 0)
      evalPair (FixedDetectorMomentCode.jacobiMinusMeanCode I j)
          (x t) =
        quadraticMomentSeries
            (fun k => c * p.gaugedBlochCoefficient d k)
            (CanonicalFixedDetectorTrajectory.omegaFrequency
              parameters controller j)
            (CanonicalFixedDetectorTrajectory.numberFrequency
                parameters I controller j /
              CanonicalFixedDetectorTrajectory.omegaFrequency
                parameters controller j)
            p.a0.re (-1) t -
          (1 / 256 : ℚ)

/-- The hypotheses above imply the complete arbitrary-phase classified
series conclusion. -/
theorem conclusion_of_hypotheses
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (x :
      ℝ →
        Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (controller :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → Circle)
    (j : Fin vars)
    (p : AffineBlochParameters)
    (d : ℂ)
    (t₀ : ℝ)
    (h :
      Hypotheses parameters I x controller phase₀ j p d t₀) :
    Conclusion parameters I x controller phase₀ j p d t₀ := by
  have hstructured :=
    FixedDetectorReverseTrajectoryCrosswalk.isStructuredTrajectory_of_isIntegralCurve
      parameters I x h.integralCurve
  have hresiduals :
      ∀ r : LinkedJacobiResidualIndex,
        linkedJacobiResidual r
          ((FixedDetectorReverseTrajectoryCrosswalk.recoveredState
            x t₀).base.base.source.linked j) =
          0 := by
    have hv :=
      (FixedDetectorReverseTrajectoryCrosswalk.validityEnergy_eq_zero_iff
        I x t₀).mp h.validity_at
    exact hv.1 j
  have hkappa : p.kappa ≠ 0 := by
    rw [h.kappa_eq]
    exact div_ne_zero h.omega_ne_zero Real.pi_ne_zero
  have ha :
      p.a0.im = 0 :=
    p.a0_im_eq_zero_of_forwardRecurrent_point
      h.recurrent h.jacobi_eq hkappa h.c0_ne_zero
  have hclocks :
      MatchesDetectorClocksRealPi p
        (CanonicalFixedDetectorTrajectory.omegaFrequency
          parameters controller j)
        (CanonicalFixedDetectorTrajectory.numberFrequency
          parameters I controller j) :=
    ⟨h.kappa_eq, h.nu_eq⟩
  have hmatch :
      ∀ t,
        MatchesCompiledGaugedBlochPhaseAt
          parameters controller phase₀ j p d t
          (FixedDetectorReverseTrajectoryCrosswalk.recoveredState
            x t) :=
    fun t => ⟨h.controllers_eq t, h.output_eq t⟩
  refine {
    structured := hstructured
    linkedResiduals := hresiduals
    a0_real := ha
    mean := ?_
    plus := ?_
    minus := ?_
  }
  · intro t
    simpa only [
      FixedDetectorReverseTrajectoryCrosswalk.point_recoveredState] using
      evalPair_jacobiMeanCode_eq_quadraticMomentSeries
        parameters I controller phase₀ j p d hclocks ha
        h.omega_ne_zero t
        (FixedDetectorReverseTrajectoryCrosswalk.recoveredState x t)
        (hmatch t)
  · intro t
    simpa only [
      FixedDetectorReverseTrajectoryCrosswalk.point_recoveredState] using
      evalPair_jacobiPlusMeanCode_eq_quadraticMomentSeries_phase
        parameters I controller phase₀ j p d hclocks ha
        h.omega_ne_zero t
        (FixedDetectorReverseTrajectoryCrosswalk.recoveredState x t)
        (hmatch t)
  · intro t
    simpa only [
      FixedDetectorReverseTrajectoryCrosswalk.point_recoveredState] using
      evalPair_jacobiMinusMeanCode_eq_quadraticMomentSeries_phase
        parameters I controller phase₀ j p d hclocks ha
        h.omega_ne_zero t
        (FixedDetectorReverseTrajectoryCrosswalk.recoveredState x t)
        (hmatch t)

end FixedDetectorArbitraryPhaseClassifiedSeries

end

end HGAS
