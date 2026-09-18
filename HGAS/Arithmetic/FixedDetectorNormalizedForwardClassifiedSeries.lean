import HGAS.Arithmetic.FixedDetectorNormalizedForwardBlochColumn
import HGAS.Modular.JacobiBlochRecurrentReality
import Mathlib.Tactic

/-!
# Corrected classified series from a normalized forward Bloch column

`FixedDetectorNormalizedForwardBlochColumn` derives the controller,
Jacobi, gauge, and output identities from one normalized seed and the
positive-time detector ODE.  This file applies those derived identities
to the three compiled Jacobi moment rows.

The two selector rows use the corrected conditional center

```text
  selectorCenter I j =
    1/128  if the full linear character of column j is zero,
    1/256  otherwise.
```

The zero-linear `1/128` specialization is stated explicitly below.
-/

namespace HGAS

open Modular
open Clocks
open Clocks.ControllerPhaseProductCharacterCode

noncomputable section

namespace FixedDetectorNormalizedForwardClassifiedSeries

open FixedDetectorNormalizedForwardBlochColumn
open FixedDetectorOrdinaryTimeBlochCrosswalk
open FixedDetectorReverseTrajectoryCrosswalk
open CorrectedFixedDetectorOrdinaryTimeMomentSeries

variable {eqs vars : ℕ}

/-- Recurrence and nonzero modular speed added to a normalized forward
column.  These are exactly the extra hypotheses needed to prove that the
Bloch parameter `a₀` is real and hence to invoke the quadratic series
identities. -/
structure ClassifiedSeed
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
  normalized :
    NormalizedSeed
      parameters I x x₀ controller phase₀ j p d
  recurrenceTime_nonnegative : 0 ≤ t₀
  recurrent :
    ForwardRecurrentAt
      (fun t =>
        JacobiPolynomialCode.point
          ((recoveredState x t).base.base.source.linked j).jacobi)
      t₀
  omega_ne_zero :
    CanonicalFixedDetectorTrajectory.omegaFrequency
      parameters controller j ≠ 0

/-- Recurrence transports across the derived forward Jacobi equality,
forcing the Bloch parameter to be real. -/
theorem a0_im_eq_zero
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
      ClassifiedSeed
        parameters I x x₀ controller phase₀ j p d t₀) :
    p.a0.im = 0 := by
  have hrecBloch :
      ForwardRecurrentAt
        (fun t =>
          JacobiPolynomialCode.point (p.jacobiBlochPath t))
        t₀ := by
    apply h.recurrent.congr_of_eqOn_Ici
      h.recurrenceTime_nonnegative
    intro t ht
    exact congrArg JacobiPolynomialCode.point
      ((jacobi_regular_and_eqOn_Ici
        parameters I x x₀ controller phase₀ j p d
        h.normalized).2 t ht)
  exact
    p.a0_im_eq_zero_of_forwardRecurrent_point
      hrecBloch rfl
      (h.normalized.clocks.kappa_ne_zero h.omega_ne_zero)
      h.normalized.c0_ne_zero

open FixedDetectorOrdinaryTimeMomentSeries in
/-- The untwisted corrected Jacobi mean row on physical time.  This row
is unchanged by selector recentering. -/
theorem mean_eq_quadraticMomentSeries
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
      ClassifiedSeed
        parameters I x x₀ controller phase₀ j p d t₀) :
    ∀ t, 0 ≤ t →
      evalPair (FixedDetectorMomentCode.jacobiMeanCode j) (x t) =
        quadraticMomentSeries
            (p.gaugedBlochCoefficient d)
            (CanonicalFixedDetectorTrajectory.omegaFrequency
              parameters controller j)
            (CanonicalFixedDetectorTrajectory.numberFrequency
                parameters I controller j /
              CanonicalFixedDetectorTrajectory.omegaFrequency
                parameters controller j)
            p.a0.re 0 t -
          1 := by
  intro t ht
  simpa only [point_recoveredState] using
    evalPair_jacobiMeanCode_eq_quadraticMomentSeries
      parameters I controller phase₀ j p d
      h.normalized.clocks
      (a0_im_eq_zero
        parameters I x x₀ controller phase₀ j p d t₀ h)
      h.omega_ne_zero t (recoveredState x t)
      (matchesCompiledGaugedBlochPhaseAt
        parameters I x x₀ controller phase₀ j p d
        h.normalized t ht)

/-- The corrected `(1,1)` row, with its conditional selector center
visible in the statement. -/
theorem plus_eq_quadraticMomentSeries
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
      ClassifiedSeed
        parameters I x x₀ controller phase₀ j p d t₀) :
    ∀ t, 0 ≤ t →
      let c :=
        characterValue
          (FixedDetectorMomentCode.jacobiPlusExponent I j)
          (CanonicalFixedDetectorTrajectory.clockPath
            parameters controller phase₀ 0)
      evalPair (CorrectedFixedDetectorMomentCode.jacobiPlusMeanCode I j)
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
          CorrectedJacobiSelectorCentering.selectorCenter I j := by
  intro t ht
  simpa only [point_recoveredState] using
    evalPair_jacobiPlusMeanCode_eq_quadraticMomentSeries_phase
      parameters I controller phase₀ j p d
      h.normalized.clocks
      (a0_im_eq_zero
        parameters I x x₀ controller phase₀ j p d t₀ h)
      h.omega_ne_zero t (recoveredState x t)
      (matchesCompiledGaugedBlochPhaseAt
        parameters I x x₀ controller phase₀ j p d
        h.normalized t ht)

/-- The corrected `(1,-1)` row, with its conditional selector center
visible in the statement. -/
theorem minus_eq_quadraticMomentSeries
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
      ClassifiedSeed
        parameters I x x₀ controller phase₀ j p d t₀) :
    ∀ t, 0 ≤ t →
      let c :=
        characterValue
          (FixedDetectorMomentCode.jacobiMinusExponent I j)
          (CanonicalFixedDetectorTrajectory.clockPath
            parameters controller phase₀ 0)
      evalPair (CorrectedFixedDetectorMomentCode.jacobiMinusMeanCode I j)
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
          CorrectedJacobiSelectorCentering.selectorCenter I j := by
  intro t ht
  simpa only [point_recoveredState] using
    evalPair_jacobiMinusMeanCode_eq_quadraticMomentSeries_phase
      parameters I controller phase₀ j p d
      h.normalized.clocks
      (a0_im_eq_zero
        parameters I x x₀ controller phase₀ j p d t₀ h)
      h.omega_ne_zero t (recoveredState x t)
      (matchesCompiledGaugedBlochPhaseAt
        parameters I x x₀ controller phase₀ j p d
        h.normalized t ht)

/-- In a zero-linear column the positive selector subtracts `1/128`,
not `1/256`. -/
theorem plus_eq_quadraticMomentSeries_zeroLinear
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
      ClassifiedSeed
        parameters I x x₀ controller phase₀ j p d t₀)
    (hlinear :
      DetectorCharacterCode.linearCharacter I j = 0) :
    ∀ t, 0 ≤ t →
      let c :=
        characterValue
          (FixedDetectorMomentCode.jacobiPlusExponent I j)
          (CanonicalFixedDetectorTrajectory.clockPath
            parameters controller phase₀ 0)
      evalPair (CorrectedFixedDetectorMomentCode.jacobiPlusMeanCode I j)
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
          (1 / 128 : ℚ) := by
  intro t ht
  rw [← CorrectedJacobiSelectorCentering.selectorCenter_eq_of_linearCharacter_eq_zero
    I j hlinear]
  exact
    plus_eq_quadraticMomentSeries
      parameters I x x₀ controller phase₀ j p d t₀ h t ht

/-- In a zero-linear column the negative selector also subtracts
`1/128`, accounting for the second resonant theta mode. -/
theorem minus_eq_quadraticMomentSeries_zeroLinear
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
      ClassifiedSeed
        parameters I x x₀ controller phase₀ j p d t₀)
    (hlinear :
      DetectorCharacterCode.linearCharacter I j = 0) :
    ∀ t, 0 ≤ t →
      let c :=
        characterValue
          (FixedDetectorMomentCode.jacobiMinusExponent I j)
          (CanonicalFixedDetectorTrajectory.clockPath
            parameters controller phase₀ 0)
      evalPair (CorrectedFixedDetectorMomentCode.jacobiMinusMeanCode I j)
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
          (1 / 128 : ℚ) := by
  intro t ht
  rw [← CorrectedJacobiSelectorCentering.selectorCenter_eq_of_linearCharacter_eq_zero
    I j hlinear]
  exact
    minus_eq_quadraticMomentSeries
      parameters I x x₀ controller phase₀ j p d t₀ h t ht

end FixedDetectorNormalizedForwardClassifiedSeries

end

end HGAS
