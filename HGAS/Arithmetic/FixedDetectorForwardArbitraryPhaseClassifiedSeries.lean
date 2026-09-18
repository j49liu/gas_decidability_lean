import HGAS.Arithmetic.FixedDetectorArbitraryPhaseClassifiedSeries
import HGAS.Arithmetic.FixedDetectorForwardTrajectoryReverseCrosswalk
import HGAS.Dynamics.ForwardRecurrenceEventualEquality
import Mathlib.Tactic

/-!
# Forward-time arbitrary-phase recurrent-series endpoint

This is the physical-time version of
`FixedDetectorArbitraryPhaseClassifiedSeries`.  It makes no ODE or Bloch
claim at negative times.

The flattened detector curve is assumed only to be an
`IsForwardTrajectory`.  The global continuation assumptions are imposed
only on the nonnegative time ray.  This is enough:

* the forward reverse crosswalk recovers all compiler equations at every
  `t > 0`, while retaining the right derivative at `t = 0`;
* equality with the Bloch path on `Set.Ici 0` transports forward
  recurrence to the Bloch path, because the recurrence times escape to
  `+∞`; and
* the three moment identities are pointwise algebraic statements, so
  they hold at every `t ≥ 0`.
-/

namespace HGAS

open Modular
open Clocks
open Clocks.ControllerPhaseProductCharacterCode

noncomputable section

namespace FixedDetectorForwardArbitraryPhaseClassifiedSeries

open FixedDetectorOrdinaryTimeBlochCrosswalk
open FixedDetectorOrdinaryTimeMomentSeries
open FixedDetectorReverseTrajectoryCrosswalk
open FixedDetectorForwardTrajectoryReverseCrosswalk

variable {eqs vars : ℕ}

/-- Exact forward-time hypotheses for one classified recurrent detector
block with arbitrary initial controller phase. -/
structure Hypotheses
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (x :
      ℝ →
        Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (x₀ :
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
  forwardTrajectory :
    IsForwardTrajectory
      (PolynomialFieldCode.realize
        (FixedDetectorPolynomialCode.fieldCode parameters I))
      x x₀
  recurrenceTime_nonnegative : 0 ≤ t₀
  validity_at :
    FixedDetectorDriftCode.validityEnergyValue I
        (recoveredState x t₀) =
      0
  controllers_eq :
    ∀ t, 0 ≤ t →
      (recoveredState x t).base.base.source.controllers =
        CanonicalFixedDetectorTrajectory.clockPath
          parameters controller phase₀ t
  jacobi_eq :
    ∀ t, 0 ≤ t →
      ((recoveredState x t).base.base.source.linked j).jacobi =
        p.jacobiBlochPath t
  output_eq :
    ∀ t, 0 ≤ t →
      (recoveredState x t).base.base.gauge j *
          ((recoveredState x t).base.base.source.linked j).jacobi.T1 =
        p.fourthRootGauge d t *
          (p.jacobiBlochPath t).T1
  recurrent :
    ForwardRecurrentAt
      (fun t =>
        JacobiPolynomialCode.point
          ((recoveredState x t).base.base.source.linked j).jacobi)
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

/-- Forward-time conclusion: structured positive-time ODE semantics,
the selected validity residuals, reality of `a0`, and the three moment
rows on the physical time ray. -/
structure Conclusion
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (x :
      ℝ →
        Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (x₀ :
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
    FixedDetectorForwardTrajectoryReverseCrosswalk.IsForwardStructuredTrajectory
      parameters I x x₀
  linkedResiduals :
    ∀ r : LinkedJacobiResidualIndex,
      linkedJacobiResidual r
        ((recoveredState x t₀).base.base.source.linked j) =
        0
  a0_real : p.a0.im = 0
  mean :
    ∀ t, 0 ≤ t →
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
    ∀ t, 0 ≤ t →
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
    ∀ t, 0 ≤ t →
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

/-- The forward hypotheses imply the complete forward classified-series
conclusion. -/
theorem conclusion_of_hypotheses
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (x :
      ℝ →
        Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (x₀ :
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
      Hypotheses
        parameters I x x₀ controller phase₀ j p d t₀) :
    Conclusion
      parameters I x x₀ controller phase₀ j p d t₀ := by
  have hstructured :=
    isForwardStructuredTrajectory_of_isForwardTrajectory
      parameters I x x₀ h.forwardTrajectory
  have hresiduals :
      ∀ r : LinkedJacobiResidualIndex,
        linkedJacobiResidual r
          ((recoveredState x t₀).base.base.source.linked j) =
          0 := by
    have hv :=
      (FixedDetectorReverseTrajectoryCrosswalk.validityEnergy_eq_zero_iff
        I x t₀).mp h.validity_at
    exact hv.1 j
  have hrecBloch :
      ForwardRecurrentAt
        (fun t =>
          JacobiPolynomialCode.point (p.jacobiBlochPath t))
        t₀ := by
    apply h.recurrent.congr_of_eqOn_Ici h.recurrenceTime_nonnegative
    intro t ht
    exact congrArg JacobiPolynomialCode.point (h.jacobi_eq t ht)
  have hkappa : p.kappa ≠ 0 := by
    rw [h.kappa_eq]
    exact div_ne_zero h.omega_ne_zero Real.pi_ne_zero
  have ha :
      p.a0.im = 0 :=
    p.a0_im_eq_zero_of_forwardRecurrent_point
      hrecBloch rfl hkappa h.c0_ne_zero
  have hclocks :
      MatchesDetectorClocksRealPi p
        (CanonicalFixedDetectorTrajectory.omegaFrequency
          parameters controller j)
        (CanonicalFixedDetectorTrajectory.numberFrequency
          parameters I controller j) :=
    ⟨h.kappa_eq, h.nu_eq⟩
  have hmatch :
      ∀ t, 0 ≤ t →
        MatchesCompiledGaugedBlochPhaseAt
          parameters controller phase₀ j p d t
          (recoveredState x t) :=
    fun t ht => ⟨h.controllers_eq t ht, h.output_eq t ht⟩
  refine {
    structured := hstructured
    linkedResiduals := hresiduals
    a0_real := ha
    mean := ?_
    plus := ?_
    minus := ?_
  }
  · intro t ht
    simpa only [point_recoveredState] using
      evalPair_jacobiMeanCode_eq_quadraticMomentSeries
        parameters I controller phase₀ j p d hclocks ha
        h.omega_ne_zero t (recoveredState x t) (hmatch t ht)
  · intro t ht
    simpa only [point_recoveredState] using
      evalPair_jacobiPlusMeanCode_eq_quadraticMomentSeries_phase
        parameters I controller phase₀ j p d hclocks ha
        h.omega_ne_zero t (recoveredState x t) (hmatch t ht)
  · intro t ht
    simpa only [point_recoveredState] using
      evalPair_jacobiMinusMeanCode_eq_quadraticMomentSeries_phase
        parameters I controller phase₀ j p d hclocks ha
        h.omega_ne_zero t (recoveredState x t) (hmatch t ht)

end FixedDetectorForwardArbitraryPhaseClassifiedSeries

end

end HGAS
