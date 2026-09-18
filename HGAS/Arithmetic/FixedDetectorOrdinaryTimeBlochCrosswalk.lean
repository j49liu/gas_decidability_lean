import HGAS.Arithmetic.FixedDetectorReverseTrajectoryCrosswalk
import HGAS.Modular.JacobiBlochSelectedContinuation
import HGAS.Modular.LinkedJacobiPointwiseBlochSeed
import Mathlib.Tactic

/-!
# Ordinary-time Bloch data on the fixed-detector validity locus

The reverse trajectory theorem recovers the semantic ODEs from an
ordinary-time Euclidean detector curve.  This file supplies the
pointwise bridge to the affine Bloch series interface.

There are two logically independent ingredients.

1. The affine speeds

```text
             κ = ω/π,       ν = (ω+N)/(2π)
```

give a `MatchesDetectorClocks` certificate by definition.

2. On the linked-Jacobi zero-residual locus, a generic unary point with a
chosen canonical-lambda lift has a finite twisted Bloch seed.  Selecting
affine parameters through that seed matches the twisted `T₁` coordinate.
The first twist is absorbed into the freely selected fourth-root gauge
constant.  Consequently the actual polynomial output `G*T₁` is exactly
the selected gauged Bloch output at that ordinary time.

The existing `MatchesCompiledGaugedBlochAt` structure uses the all-one
phase origin.  We introduce the phase-parametrized version needed for a
selected ergodic point.  Aggregate validity does not imply any particular
phase origin (nor controller equilibrium or unit phase circles).
-/

namespace HGAS

open Modular
open Clocks

noncomputable section

namespace FixedDetectorOrdinaryTimeBlochCrosswalk

variable {eqs vars : ℕ}

/-- Correct clock-matching interface.  The suffix records that the
denominator is the mathematical constant `Real.pi`, not an implicit
variable named `π`. -/
structure MatchesDetectorClocksRealPi
    (p : AffineBlochParameters) (ω N : ℝ) : Prop where
  kappa_eq : p.kappa = ω / Real.pi
  nu_eq : p.nu = (ω + N) / (2 * Real.pi)

namespace MatchesDetectorClocksRealPi

variable {p : AffineBlochParameters} {ω N : ℝ}

theorem quadraticOmega_eq
    (h : MatchesDetectorClocksRealPi p ω N) :
    p.quadraticOmega = ω := by
  rw [AffineBlochParameters.quadraticOmega, h.kappa_eq]
  field_simp [Real.pi_ne_zero]

theorem quadraticLinearFrequency_eq
    (h : MatchesDetectorClocksRealPi p ω N) :
    p.quadraticLinearFrequency = N := by
  calc
    p.quadraticLinearFrequency =
        2 * Real.pi *
          ((ω + N) / (2 * Real.pi)) - ω := by
      rw [AffineBlochParameters.quadraticLinearFrequency,
        h.quadraticOmega_eq, h.nu_eq]
    _ = N := by
      field_simp [Real.pi_ne_zero]
      ring

theorem kappa_ne_zero
    (h : MatchesDetectorClocksRealPi p ω N)
    (hω : ω ≠ 0) :
    p.kappa ≠ 0 := by
  rw [h.kappa_eq]
  exact div_ne_zero hω Real.pi_ne_zero

theorem quadraticClockRatio_eq
    (h : MatchesDetectorClocksRealPi p ω N) :
    p.quadraticClockRatio = N / ω := by
  rw [AffineBlochParameters.quadraticClockRatio,
    h.quadraticLinearFrequency_eq, h.quadraticOmega_eq]

end MatchesDetectorClocksRealPi

/-- The ordinary-time speed normalization used by the Jacobi moment
series is exactly the `MatchesDetectorClocks` interface. -/
theorem matchesDetectorClocks_of_speed_eq
    (p : AffineBlochParameters)
    (ω N : ℝ)
    (hkappa : p.kappa = ω / Real.pi)
    (hnu : p.nu = (ω + N) / (2 * Real.pi)) :
    MatchesDetectorClocksRealPi p ω N :=
  ⟨hkappa, hnu⟩

/-- Affine parameters selected with the detector's ordinary-time speeds
automatically match those detector clocks. -/
theorem selectedAffineBlochParameters_matchesDetectorClocks
    (τ : UpperHalfPlane) (w : ℂ)
    (ω N : ℝ) (S ξ L : ℂ) (t : ℝ) :
    MatchesDetectorClocksRealPi
      (selectedAffineBlochParameters
      τ w
      ((ω + N) / (2 * Real.pi))
      (ω / Real.pi)
      S ξ L t) ω N :=
  ⟨rfl, rfl⟩

/-- At the selected time, the `T₁` coordinate of the affine Bloch path
is the first coefficient-twisted coordinate stored in a pointwise seed. -/
theorem selectedAffineBlochParameters_T1_eq_twisted
    (τ : UpperHalfPlane)
    (z : LinkedJacobiState ℂ)
    (w : ℂ) (ν κ : ℝ)
    (seed : TwistedJacobiBlochSeed τ z w)
    (t : ℝ) :
    ((selectedAffineBlochParameters
        τ w ν κ seed.S seed.ξ seed.L t).jacobiBlochPath t).T1 =
      seed.d₁ * z.jacobi.T1 := by
  let p :=
    selectedAffineBlochParameters
      τ w ν κ seed.S seed.ξ seed.L t
  have hcore :=
    selectedAffineBlochParameters.corePoint_at
      τ w ν κ seed.S seed.ξ seed.L t
  have hT1core :=
    congrFun hcore (4 : Fin JacobiCoreDimension)
  have hseed := congrFun seed.value (0 : Fin 4)
  rw [jacobiBlochThetaVector_selected] at hseed
  have hT1seed :
      seed.S *
          jacobiTheta1 seed.ξ (τ : ℂ) =
        seed.d₁ * z.jacobi.T1 := by
    simpa only [Pi.smul_apply, smul_eq_mul,
      jacobiThetaVector, Matrix.cons_val_zero,
      jacobiCoefficientTwist_zero,
      jacobiResidualProjectiveCoordinates] using hseed
  change (p.jacobiBlochPath t).T1 =
    seed.d₁ * z.jacobi.T1
  calc
    (p.jacobiBlochPath t).T1 =
        seed.S *
          jacobiTheta1 seed.ξ (τ : ℂ) := by
      simpa only [p, jacobiCorePoint,
        JacobiState.blochGauge,
        canonicalJacobiThetaState,
        Matrix.cons_val_one, Matrix.cons_val_zero] using
        hT1core
    _ = seed.d₁ * z.jacobi.T1 := hT1seed

/-- Every desired point value of a fourth-root gauge is obtained by a
unique explicit choice of its free multiplicative constant. -/
def gaugeConstantForValue
    (p : AffineBlochParameters)
    (value : ℂ) (t : ℝ) : ℂ :=
  value /
    Complex.exp
      (Real.pi * Complex.I *
        (p.centeredW t + p.tauComplex t / 4))

@[simp]
theorem fourthRootGauge_gaugeConstantForValue
    (p : AffineBlochParameters)
    (value : ℂ) (t : ℝ) :
    p.fourthRootGauge
        (gaugeConstantForValue p value t) t =
      value := by
  rw [AffineBlochParameters.fourthRootGauge,
    gaugeConstantForValue]
  exact div_mul_cancel₀ value (Complex.exp_ne_zero _)

/-- Compiler/Bloch matching with an arbitrary initial controller phase.
This is the natural interface for a selected ergodic point. -/
structure MatchesCompiledGaugedBlochPhaseAt
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → Circle)
    (j : Fin vars)
    (p : AffineBlochParameters) (d : ℂ) (t : ℝ)
    (z : FixedDetectorPolynomialCode.State eqs vars) : Prop where
  controllers_eq :
    z.base.base.source.controllers =
      CanonicalFixedDetectorTrajectory.clockPath
        parameters controller phase₀ t
  output_eq :
    z.base.base.gauge j *
        (z.base.base.source.linked j).jacobi.T1 =
      p.fourthRootGauge d t * (p.jacobiBlochPath t).T1

/-- The old all-one matching structure is the specialization of the
arbitrary-phase interface to `onePhase`. -/
theorem matchesCompiledGaugedBlochAt_of_phase_one
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (j : Fin vars)
    (p : AffineBlochParameters) (d : ℂ) (t : ℝ)
    (z : FixedDetectorPolynomialCode.State eqs vars)
    (h :
      MatchesCompiledGaugedBlochPhaseAt
        parameters controller
        LockedControllerPhaseTrajectory.onePhase
        j p d t z) :
    FixedDetectorMomentCode.MatchesCompiledGaugedBlochAt
      parameters controller j p d t z :=
  ⟨h.controllers_eq, h.output_eq⟩

/-- Pointwise data sufficient to identify a recovered detector state
with one ordinary-time gauged Bloch output.

The validity field is included explicitly to record that this is an
identification on the compiler's zero-validity locus.  The all-one
controller equation is separate because it is not a consequence of that
locus. -/
structure GenericAlignedValidityPoint
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
    (τ : UpperHalfPlane)
    (t : ℝ) : Prop where
  validity :
    FixedDetectorDriftCode.validityEnergyValue I
        (FixedDetectorReverseTrajectoryCrosswalk.recoveredState x t) =
      0
  controllers_eq :
    (FixedDetectorReverseTrajectoryCrosswalk.recoveredState
        x t).base.base.source.controllers =
      CanonicalFixedDetectorTrajectory.clockPath
        parameters controller
        phase₀ t
  unary_B_ne_zero :
    UnaryModularState.B
        ((FixedDetectorReverseTrajectoryCrosswalk.recoveredState
          x t).base.base.source.linked j).unary ≠
      0
  lambda_eq :
    UnaryModularState.lambdaCoordinate
        ((FixedDetectorReverseTrajectoryCrosswalk.recoveredState
          x t).base.base.source.linked j).unary =
      canonicalLambda τ

/-- **Pointwise ordinary-time Bloch crosswalk on the zero-validity
locus.**

At every generic, phase-aligned validity point there exist affine
Bloch parameters and a fourth-root gauge constant which:

* match the literal detector frequencies in ordinary time; and
* satisfy `MatchesCompiledGaugedBlochAt` for the actual recovered state.

The finite coefficient branch returned by pointwise theta saturation is
absorbed into the gauge constant, so no canonical coefficient-sign
assumption is needed. -/
theorem exists_matchesCompiledGaugedBlochAt
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
    (τ : UpperHalfPlane)
    (t : ℝ)
    (h : GenericAlignedValidityPoint
      parameters I x controller phase₀ j τ t)
    (w : ℂ) :
    ∃ p : AffineBlochParameters, ∃ d : ℂ,
      MatchesDetectorClocksRealPi p
          (CanonicalFixedDetectorTrajectory.omegaFrequency
            parameters controller j)
          (CanonicalFixedDetectorTrajectory.numberFrequency
            parameters I controller j) ∧
        MatchesCompiledGaugedBlochPhaseAt
          parameters controller phase₀ j p d t
          (FixedDetectorReverseTrajectoryCrosswalk.recoveredState
            x t) := by
  let z :=
    FixedDetectorReverseTrajectoryCrosswalk.recoveredState x t
  have hresidual :
      ∀ r : LinkedJacobiResidualIndex,
        linkedJacobiResidual r (z.base.base.source.linked j) = 0 := by
    have hv :=
      (FixedDetectorReverseTrajectoryCrosswalk.validityEnergy_eq_zero_iff
        I x t).mp h.validity
    exact hv.1 j
  let seed : TwistedJacobiBlochSeed
      τ (z.base.base.source.linked j) w :=
    Classical.choice
      (linkedResidualPoint_exists_twistedJacobiBlochSeed
        τ (z.base.base.source.linked j) w
        h.unary_B_ne_zero h.lambda_eq hresidual)
  let ω :=
    CanonicalFixedDetectorTrajectory.omegaFrequency
      parameters controller j
  let N :=
    CanonicalFixedDetectorTrajectory.numberFrequency
      parameters I controller j
  let p :=
    selectedAffineBlochParameters
      τ w ((ω + N) / (2 * Real.pi))
      (ω / Real.pi)
      seed.S seed.ξ seed.L t
  let targetGauge : ℂ := z.base.base.gauge j / seed.d₁
  let d : ℂ := gaugeConstantForValue p targetGauge t
  refine ⟨p, d, ?_, ?_⟩
  · exact
      selectedAffineBlochParameters_matchesDetectorClocks
        τ w ω N seed.S seed.ξ seed.L t
  · refine {
      controllers_eq := ?_
      output_eq := ?_
    }
    · simpa only [z] using h.controllers_eq
    · have hT1 :
          (p.jacobiBlochPath t).T1 =
            seed.d₁ *
              (z.base.base.source.linked j).jacobi.T1 := by
        simpa only [p] using
          selectedAffineBlochParameters_T1_eq_twisted
            τ (z.base.base.source.linked j) w
            ((ω + N) / (2 * Real.pi))
            (ω / Real.pi) seed t
      have hgauge :
          p.fourthRootGauge d t = targetGauge := by
        exact fourthRootGauge_gaugeConstantForValue
          p targetGauge t
      change
        z.base.base.gauge j *
            (z.base.base.source.linked j).jacobi.T1 =
          p.fourthRootGauge d t *
            (p.jacobiBlochPath t).T1
      rw [hgauge, hT1]
      dsimp only [targetGauge]
      field_simp [seed.d₁_ne_zero]

end FixedDetectorOrdinaryTimeBlochCrosswalk

end

end HGAS
