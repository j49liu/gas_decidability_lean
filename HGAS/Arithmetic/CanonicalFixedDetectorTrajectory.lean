import HGAS.Arithmetic.FixedDetectorTrajectoryCrosswalk
import HGAS.Clocks.ControllerPhaseProductCharacterPowers
import HGAS.Clocks.LockedControllerPhaseTrajectory
import HGAS.Compiler.ReciprocalGraphDynamics
import Mathlib.Tactic

/-!
# An explicit canonical trajectory of the fixed detector

This file discharges the scalar ODE hypotheses exposed by
`FixedDetectorTrajectoryCrosswalk`.  We work over a fixed family of
locked controller states.  Their phase circles rotate explicitly, so all
frequency readouts are constant.  From those clocks we construct:

* affine elliptic and upper-half-plane parameters for the canonical
  linked Jacobi theta states;
* the literal fourth-root gauge character;
* the two literal Poisson reciprocals; and
* the final right-hand-side phase oscillator.

The endpoint is a concrete integral curve of the exact polynomial field
emitted by `FixedDetectorPolynomialCode`.
-/

namespace HGAS.CanonicalFixedDetectorTrajectory

open HGAS
open Complex
open Modular
open Clocks
open Clocks.ControllerPhaseProductCharacterCode

noncomputable section

variable {eqs vars : ℕ}

abbrev clockCount (eqs vars : ℕ) : ℕ :=
  DetectorCharacterCode.clockCount eqs vars

/-! ## Locked clocks and constant detector readouts -/

/-- Explicit locked controller--phase path used by every later layer. -/
def clockPath
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ : Fin (clockCount eqs vars) → Circle)
    (t : ℝ) :
    Clocks.ControllerPhaseProductPolynomialCode.StateFamily
      (clockCount eqs vars) ℝ :=
  Clocks.LockedControllerPhaseTrajectory.stateFamily
    parameters controller phase₀ t

/-- Constant private-character readout driving the modular parameter of
Jacobi block `j`. -/
def omegaFrequency
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (j : Fin vars) : ℝ :=
  ∑ i : Fin (clockCount eqs vars),
    (RationalCode.decode
        (DetectorCharacterCode.omegaWeights
          (eqs := eqs) j i) : ℝ) *
      (RationalCode.decode (parameters i) : ℝ) *
      (controller i).r

/-- Constant linear-character readout entering the elliptic parameter of
Jacobi block `j`. -/
def numberFrequency
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (j : Fin vars) : ℝ :=
  ∑ i : Fin (clockCount eqs vars),
    (RationalCode.decode
        (DetectorCharacterCode.numberWeights I j i) : ℝ) *
      (RationalCode.decode (parameters i) : ℝ) *
      (controller i).r

/-! ## Affine Jacobi parameters -/

/-- A horizontal upper-half-plane path with prescribed complex derivative
`ω/π`.  Its imaginary part is exactly that of `τ₀`. -/
def modularPath
    (τ₀ : UpperHalfPlane) (ω : ℝ) (t : ℝ) :
    UpperHalfPlane :=
  ⟨(τ₀ : ℂ) +
      ((((ω / Real.pi) * t : ℝ)) : ℂ),
    by simpa using τ₀.im_pos⟩

/-- The elliptic parameter whose derivative gives
`κZ = (ω+N)/2`. -/
def ellipticPath
    (ξ₀ : ℂ) (ω N : ℝ) (t : ℝ) : ℂ :=
  ξ₀ +
    ((((ω + N) / (2 * Real.pi) * t : ℝ)) : ℂ)

theorem modularPath_hasDerivAt
    (τ₀ : UpperHalfPlane) (ω : ℝ) (t : ℝ) :
    HasDerivAt
      (fun u : ℝ => (modularPath τ₀ ω u : ℂ))
      (((ω / Real.pi : ℝ) : ℂ)) t := by
  have hlinear :
      HasDerivAt
        (fun u : ℝ =>
          ((((ω / Real.pi) * u : ℝ)) : ℂ))
        (((ω / Real.pi : ℝ) : ℂ)) t :=
    by
      simpa only [id_eq, mul_one] using
        ((hasDerivAt_id t).const_mul
          (ω / Real.pi)).ofReal_comp
  convert
      (hasDerivAt_const t (τ₀ : ℂ)).add hlinear
      using 1
  all_goals simp

theorem ellipticPath_hasDerivAt
    (ξ₀ : ℂ) (ω N : ℝ) (t : ℝ) :
    HasDerivAt
      (ellipticPath ξ₀ ω N)
      ((((ω + N) / (2 * Real.pi) : ℝ) : ℂ)) t := by
  have hlinear :
      HasDerivAt
        (fun u : ℝ =>
          ((((ω + N) / (2 * Real.pi) * u : ℝ)) : ℂ))
        ((((ω + N) / (2 * Real.pi) : ℝ) : ℂ)) t :=
    by
      simpa only [id_eq, mul_one] using
        ((hasDerivAt_id t).const_mul
          ((ω + N) / (2 * Real.pi))).ofReal_comp
  convert
      (hasDerivAt_const t ξ₀).add hlinear
      using 1
  all_goals simp

/-! ## The canonical controller--linked Jacobi source -/

/-- Canonical linked theta family driven by the constant readouts of the
locked controller path. -/
def linkedSourcePath
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ : Fin (clockCount eqs vars) → Circle)
    (ξ₀ : Fin vars → ℂ)
    (τ₀ : Fin vars → UpperHalfPlane)
    (t : ℝ) :
    ControllerProductLinkedJacobiFamilyState
      (clockCount eqs vars) vars :=
  canonicalControllerLinkedJacobiFamilyPath
    (clockPath parameters controller phase₀)
    (fun j =>
      ellipticPath (ξ₀ j)
        (omegaFrequency parameters controller j)
        (numberFrequency parameters I controller j))
    (fun j =>
      modularPath (τ₀ j)
        (omegaFrequency parameters controller j))
    t

@[simp]
theorem linkedSourcePath_controllers
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ : Fin (clockCount eqs vars) → Circle)
    (ξ₀ : Fin vars → ℂ)
    (τ₀ : Fin vars → UpperHalfPlane)
    (t : ℝ) :
    (linkedSourcePath parameters I controller phase₀ ξ₀ τ₀ t).controllers =
      clockPath parameters controller phase₀ t :=
  rfl

theorem linkedSourcePath_kappaZ
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ : Fin (clockCount eqs vars) → Circle)
    (ξ₀ : Fin vars → ℂ)
    (τ₀ : Fin vars → UpperHalfPlane)
    (t : ℝ) (j : Fin vars) :
    ControllerProductLinkedJacobiFamilyPolynomialCode.kappaZ
        (fun a i =>
          (RationalCode.decode
            (DetectorCharacterCode.omegaWeights
              (eqs := eqs) a i) : ℝ))
        (fun a i =>
          (RationalCode.decode
            (DetectorCharacterCode.numberWeights I a i) : ℝ))
        (fun i =>
          (RationalCode.decode (parameters i) : ℝ))
        (linkedSourcePath parameters I controller phase₀ ξ₀ τ₀ t)
        j =
      (((omegaFrequency parameters controller j +
          numberFrequency parameters I controller j) / 2 : ℝ) : ℂ) := by
  simp [ControllerProductLinkedJacobiFamilyPolynomialCode.kappaZ,
    ControllerProductLinkedJacobiFamilyPolynomialCode.omega,
    ControllerProductLinkedJacobiFamilyPolynomialCode.number,
    Clocks.ControllerPhaseProductLinearFrequencyCode.value,
    linkedSourcePath, clockPath, omegaFrequency, numberFrequency,
    Clocks.LockedControllerPhaseTrajectory.stateFamily]

theorem linkedSourcePath_kappaPhi
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ : Fin (clockCount eqs vars) → Circle)
    (ξ₀ : Fin vars → ℂ)
    (τ₀ : Fin vars → UpperHalfPlane)
    (t : ℝ) (j : Fin vars) :
    ControllerProductLinkedJacobiFamilyPolynomialCode.kappaPhi
        (fun a i =>
          (RationalCode.decode
            (DetectorCharacterCode.omegaWeights
              (eqs := eqs) a i) : ℝ))
        (fun i =>
          (RationalCode.decode (parameters i) : ℝ))
        (linkedSourcePath parameters I controller phase₀ ξ₀ τ₀ t)
        j =
      Complex.I * omegaFrequency parameters controller j := by
  simp [ControllerProductLinkedJacobiFamilyPolynomialCode.kappaPhi,
    ControllerProductLinkedJacobiFamilyPolynomialCode.omega,
    Clocks.ControllerPhaseProductLinearFrequencyCode.value,
    linkedSourcePath, clockPath, omegaFrequency,
    Clocks.LockedControllerPhaseTrajectory.stateFamily]

/-- The complete explicit locked controller and canonical linked theta
path solves the literal detector source field.  The displayed
nonvanishing condition is precisely the chart condition for the stored
reciprocal `1/θ₁`. -/
theorem linkedSourcePath_point_isIntegralCurve
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ : Fin (clockCount eqs vars) → Circle)
    (ξ₀ : Fin vars → ℂ)
    (τ₀ : Fin vars → UpperHalfPlane)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i))
    (hθ₁ :
      ∀ j t,
        jacobiTheta1
          (ellipticPath (ξ₀ j)
            (omegaFrequency parameters controller j)
            (numberFrequency parameters I controller j) t)
          (modularPath (τ₀ j)
            (omegaFrequency parameters controller j) t : ℂ) ≠ 0) :
    IsIntegralCurve
      (fun t =>
        ControllerProductLinkedJacobiFamilyPolynomialCode.point
          (linkedSourcePath parameters I controller phase₀ ξ₀ τ₀ t))
      (fun _ x =>
        PolynomialFieldCode.realize
          (ControllerProductLinkedJacobiFamilyPolynomialCode.fieldCode
            parameters
            (DetectorCharacterCode.omegaWeights (eqs := eqs))
            (DetectorCharacterCode.numberWeights I)) x) := by
  apply
    canonicalControllerLinkedJacobiFamilyPath_point_isIntegralCurve
      parameters
      (DetectorCharacterCode.omegaWeights (eqs := eqs))
      (DetectorCharacterCode.numberWeights I)
      (clockPath parameters controller phase₀)
      (fun j =>
        ellipticPath (ξ₀ j)
          (omegaFrequency parameters controller j)
          (numberFrequency parameters I controller j))
      (fun j =>
        modularPath (τ₀ j)
          (omegaFrequency parameters controller j))
      (fun j =>
        (((omegaFrequency parameters controller j +
          numberFrequency parameters I controller j) /
            (2 * Real.pi) : ℝ) : ℂ))
      (fun j =>
        (((omegaFrequency parameters controller j /
          Real.pi : ℝ) : ℂ)))
  · exact
      Clocks.LockedControllerPhaseTrajectory.point_stateFamily_isIntegralCurve
        parameters controller phase₀ hlock
  · intro j t
    exact ellipticPath_hasDerivAt
      (ξ₀ j)
      (omegaFrequency parameters controller j)
      (numberFrequency parameters I controller j) t
  · intro j t
    exact modularPath_hasDerivAt
      (τ₀ j)
      (omegaFrequency parameters controller j) t
  · exact hθ₁
  · intro t j
    change
      ControllerProductLinkedJacobiFamilyPolynomialCode.kappaZ
          (fun a i =>
            (RationalCode.decode
              (DetectorCharacterCode.omegaWeights
                (eqs := eqs) a i) : ℝ))
          (fun a i =>
            (RationalCode.decode
              (DetectorCharacterCode.numberWeights I a i) : ℝ))
          (fun i =>
            (RationalCode.decode (parameters i) : ℝ))
          (linkedSourcePath
            parameters I controller phase₀ ξ₀ τ₀ t) j =
        _
    rw [linkedSourcePath_kappaZ]
    push_cast
    field_simp [Real.pi_ne_zero]
  · intro t j
    change
      ControllerProductLinkedJacobiFamilyPolynomialCode.kappaPhi
          (fun a i =>
            (RationalCode.decode
              (DetectorCharacterCode.omegaWeights
                (eqs := eqs) a i) : ℝ))
          (fun i =>
            (RationalCode.decode (parameters i) : ℝ))
          (linkedSourcePath
            parameters I controller phase₀ ξ₀ τ₀ t) j =
        _
    rw [linkedSourcePath_kappaPhi]
    push_cast
    field_simp [Real.pi_ne_zero]

/-! ## Explicit fourth-root gauges -/

/-- The exponent of the canonical fourth root of
`Qⱼ Vⱼ²`.  The public detector exponent contains a common factor four,
so this is again an integral Laurent character. -/
def gaugeRootExponent
    (I : DQLSystem eqs vars)
    (j : Fin vars) :
    Fin (clockCount eqs vars) → ℤ :=
  fun i =>
    DetectorJacobiGaugeData.gaugeCharacter I j
      (finSumFinEquiv.symm i)

theorem gaugeExponents_eq_four_mul_root
    (I : DQLSystem eqs vars)
    (j : Fin vars) :
    DetectorJacobiGaugeData.gaugeExponents I j =
      fun i => 4 * gaugeRootExponent I j i := by
  funext i
  rfl

/-- Constant logarithmic frequency of the canonical gauge root. -/
def gaugeRootFrequency
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (j : Fin vars) : ℝ :=
  Clocks.LockedControllerPhaseTrajectory.characterFrequency
    parameters controller (gaugeRootExponent I j)

/-- The canonical gauge is the Laurent character obtained after dividing
the detector's common exponent factor four, scaled by the intended
fourth-root radius `r₀ = 1/4`. -/
def gaugePath
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ : Fin (clockCount eqs vars) → Circle)
    (t : ℝ) (j : Fin vars) : ℂ :=
  (((1 / 4 : ℝ) : ℂ)) *
    characterValue (gaugeRootExponent I j)
      (clockPath parameters controller phase₀ t)

/-- The canonical gauge has the intended constant radius `r₀ = 1/4`. -/
theorem norm_gaugePath
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ : Fin (clockCount eqs vars) → Circle)
    (t : ℝ) (j : Fin vars) :
    ‖gaugePath parameters I controller phase₀ t j‖ = 1 / 4 := by
  rw [gaugePath, norm_mul]
  have hcharacter :
      ‖characterValue (gaugeRootExponent I j)
          (clockPath parameters controller phase₀ t)‖ = 1 := by
    unfold clockPath
    exact
      norm_characterValue_eq_one
        (gaugeRootExponent I j)
        (Clocks.LockedControllerPhaseTrajectory.stateFamily
          parameters controller phase₀ t)
        (Clocks.LockedControllerPhaseTrajectory.stateFamily_onPhaseCircles
          parameters controller phase₀ t)
  rw [hcharacter, mul_one]
  norm_num

/-- **Exact fourth-root graph identity.**

The common factor four in the detector exponent and the radius
`r₀ = 1/4` give

`G_j^4 = (1/256) χ_j`

at every time, exactly matching the gauge residual compiler. -/
theorem gaugePath_pow_four
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ : Fin (clockCount eqs vars) → Circle)
    (t : ℝ) (j : Fin vars) :
    gaugePath parameters I controller phase₀ t j ^ 4 =
      (((1 / 256 : ℝ) : ℂ)) *
        characterValue
          (DetectorJacobiGaugeData.gaugeExponents I j)
          (clockPath parameters controller phase₀ t) := by
  unfold gaugePath
  rw [mul_pow]
  rw [←
    Clocks.ControllerPhaseProductCharacterCode.characterValue_four_mul]
  rw [← gaugeExponents_eq_four_mul_root I j]
  norm_num

/-- Residual form of `gaugePath_pow_four`. -/
theorem gaugePath_graphResidual_eq_zero
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ : Fin (clockCount eqs vars) → Circle)
    (t : ℝ) (j : Fin vars) :
    gaugePath parameters I controller phase₀ t j ^ 4 -
        (((1 / 256 : ℝ) : ℂ)) *
          characterValue
            (DetectorJacobiGaugeData.gaugeExponents I j)
            (clockPath parameters controller phase₀ t) =
      0 := by
  rw [gaugePath_pow_four]
  ring

theorem gaugeFrequency_div_four
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ : Fin (clockCount eqs vars) → Circle)
    (t : ℝ) (j : Fin vars) :
    frequencyValue parameters
        (DetectorJacobiGaugeData.gaugeExponents I j)
        (clockPath parameters controller phase₀ t) / 4 =
      gaugeRootFrequency parameters I controller j := by
  change
    frequencyValue parameters
        (DetectorJacobiGaugeData.gaugeExponents I j)
        (Clocks.LockedControllerPhaseTrajectory.stateFamily
          parameters controller phase₀ t) / 4 =
      gaugeRootFrequency parameters I controller j
  rw [
    Clocks.LockedControllerPhaseTrajectory.frequencyValue_stateFamily]
  have hscale :
      Clocks.LockedControllerPhaseTrajectory.characterFrequency
          parameters controller
          (DetectorJacobiGaugeData.gaugeExponents I j) =
        4 * gaugeRootFrequency parameters I controller j := by
    unfold gaugeRootFrequency
    unfold Clocks.LockedControllerPhaseTrajectory.characterFrequency
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [gaugeExponents_eq_four_mul_root]
    push_cast
    ring
  rw [hscale]
  ring

/-- The explicit gauge character follows exactly the scalar ODE emitted
by the gauge-family compiler. -/
theorem gaugePath_hasDerivAt
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ : Fin (clockCount eqs vars) → Circle)
    (j : Fin vars) (t : ℝ) :
    HasDerivAt
      (fun u =>
        gaugePath parameters I controller phase₀ u j)
      (Complex.I *
        ((frequencyValue parameters
            (DetectorJacobiGaugeData.gaugeExponents I j)
            (clockPath parameters controller phase₀ t) / 4 : ℝ) : ℂ) *
        gaugePath parameters I controller phase₀ t j) t := by
  have h :=
    Clocks.LockedControllerPhaseTrajectory.characterValue_hasDerivAt
      parameters controller phase₀
      (gaugeRootExponent I j) t
  rw [gaugeFrequency_div_four]
  have hscaled :=
    h.const_mul (((1 / 4 : ℝ) : ℂ))
  convert hscaled using 1
  unfold gaugePath gaugeRootFrequency clockPath
  ring

/-- Gauge-completed canonical linked source. -/
def gaugeSourcePath
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ : Fin (clockCount eqs vars) → Circle)
    (ξ₀ : Fin vars → ℂ)
    (τ₀ : Fin vars → UpperHalfPlane)
    (t : ℝ) :
    ControllerProductLinkedJacobiGaugeFamilyState
      (clockCount eqs vars) vars where
  source :=
    linkedSourcePath parameters I controller phase₀ ξ₀ τ₀ t
  gauge :=
    gaugePath parameters I controller phase₀ t

@[simp]
theorem gaugeSourcePath_source
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ : Fin (clockCount eqs vars) → Circle)
    (ξ₀ : Fin vars → ℂ)
    (τ₀ : Fin vars → UpperHalfPlane)
    (t : ℝ) :
    (gaugeSourcePath
      parameters I controller phase₀ ξ₀ τ₀ t).source =
        linkedSourcePath
          parameters I controller phase₀ ξ₀ τ₀ t :=
  rfl

/-- The explicit gauge-completed source is an integral curve of the
literal DQL gauge compiler. -/
theorem gaugeSourcePath_point_isIntegralCurve
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ : Fin (clockCount eqs vars) → Circle)
    (ξ₀ : Fin vars → ℂ)
    (τ₀ : Fin vars → UpperHalfPlane)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i))
    (hθ₁ :
      ∀ j t,
        jacobiTheta1
          (ellipticPath (ξ₀ j)
            (omegaFrequency parameters controller j)
            (numberFrequency parameters I controller j) t)
          (modularPath (τ₀ j)
            (omegaFrequency parameters controller j) t : ℂ) ≠ 0) :
    IsIntegralCurve
      (fun t =>
        ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.point
          (gaugeSourcePath
            parameters I controller phase₀ ξ₀ τ₀ t))
      (fun _ x =>
        PolynomialFieldCode.realize
          (DetectorJacobiGaugeData.fieldCode parameters I) x) := by
  apply
    ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.point_isIntegralCurve
      parameters
      (DetectorCharacterCode.omegaWeights (eqs := eqs))
      (DetectorCharacterCode.numberWeights I)
      (DetectorJacobiGaugeData.gaugeExponents I)
      (gaugeSourcePath
        parameters I controller phase₀ ξ₀ τ₀)
  · exact
      linkedSourcePath_point_isIntegralCurve
        parameters I controller phase₀ ξ₀ τ₀ hlock hθ₁
  · intro j t
    have h :=
      gaugePath_hasDerivAt
        parameters I controller phase₀ j t
    simpa only [gaugeSourcePath,
      ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.vectorField,
      ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.rawState,
      ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.eval₂Hom_gaugeFrequencyBaseCode,
      linkedSourcePath_controllers,
      clockPath] using h

/-! ## Explicit Poisson reciprocals -/

/-- The signed Laurent character in one Poisson denominator.  The index
`k` ranges over the positive and negative character attached to each
arithmetic variable. -/
def poissonCharacterPath
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ : Fin (clockCount eqs vars) → Circle)
    (t : ℝ)
    (k : Fin (DetectorPoissonReciprocalCode.reciprocalCount vars)) :
    ℂ :=
  characterValue
    (DetectorPoissonReciprocalCode.reciprocalExponent I k)
    (clockPath parameters controller phase₀ t)

/-- The literal reciprocal selected by the Poisson denominator at
`η = 1/2`. -/
def poissonReciprocalPath
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ : Fin (clockCount eqs vars) → Circle)
    (t : ℝ)
    (k : Fin (DetectorPoissonReciprocalCode.reciprocalCount vars)) :
    ℂ :=
  (1 - (((1 / 2 : ℝ) : ℂ) *
    poissonCharacterPath parameters I controller phase₀ t k))⁻¹

/-- Every Poisson source character stays exactly on the unit circle. -/
theorem norm_poissonCharacterPath_eq_one
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ : Fin (clockCount eqs vars) → Circle)
    (t : ℝ)
    (k : Fin (DetectorPoissonReciprocalCode.reciprocalCount vars)) :
    ‖poissonCharacterPath
        parameters I controller phase₀ t k‖ = 1 := by
  unfold poissonCharacterPath clockPath
  exact
    norm_characterValue_eq_one
      (DetectorPoissonReciprocalCode.reciprocalExponent I k)
      (Clocks.LockedControllerPhaseTrajectory.stateFamily
        parameters controller phase₀ t)
      (Clocks.LockedControllerPhaseTrajectory.stateFamily_onPhaseCircles
        parameters controller phase₀ t)

/-- Since `η = 1/2 < 1`, a Poisson denominator along the canonical
trajectory never vanishes. -/
theorem poissonDenominator_ne_zero
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ : Fin (clockCount eqs vars) → Circle)
    (t : ℝ)
    (k : Fin (DetectorPoissonReciprocalCode.reciprocalCount vars)) :
    1 - (((1 / 2 : ℝ) : ℂ) *
      poissonCharacterPath parameters I controller phase₀ t k) ≠ 0 := by
  apply one_sub_real_mul_ne_zero_of_norm_eq_one
    (η := (1 / 2 : ℝ))
  · norm_num
  · norm_num
  · exact norm_poissonCharacterPath_eq_one
      parameters I controller phase₀ t k

/-- The source character has exactly the derivative supplied to the
reciprocal compiler. -/
theorem poissonCharacterPath_hasDerivAt
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ : Fin (clockCount eqs vars) → Circle)
    (k : Fin (DetectorPoissonReciprocalCode.reciprocalCount vars))
    (t : ℝ) :
    HasDerivAt
      (fun u =>
        poissonCharacterPath parameters I controller phase₀ u k)
      (Complex.I *
        (frequencyValue parameters
          (DetectorPoissonReciprocalCode.reciprocalExponent I k)
          (clockPath parameters controller phase₀ t) : ℂ) *
        poissonCharacterPath parameters I controller phase₀ t k) t := by
  have h :=
    Clocks.LockedControllerPhaseTrajectory.characterValue_hasDerivAt
      parameters controller phase₀
      (DetectorPoissonReciprocalCode.reciprocalExponent I k) t
  simpa only [poissonCharacterPath, clockPath,
    Clocks.LockedControllerPhaseTrajectory.frequencyValue_stateFamily]
    using h

/-- Differentiating the literal inverse gives precisely the polynomial
Riccati equation `g' = η w' g²` used by the reciprocal compiler. -/
theorem poissonReciprocalPath_hasDerivAt
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ : Fin (clockCount eqs vars) → Circle)
    (k : Fin (DetectorPoissonReciprocalCode.reciprocalCount vars))
    (t : ℝ) :
    HasDerivAt
      (fun u =>
        poissonReciprocalPath parameters I controller phase₀ u k)
      (reciprocalVelocity
        (((1 / 2 : ℝ) : ℂ))
        (Complex.I *
          (frequencyValue parameters
            (DetectorPoissonReciprocalCode.reciprocalExponent I k)
            (clockPath parameters controller phase₀ t) : ℂ) *
          poissonCharacterPath parameters I controller phase₀ t k)
        (poissonReciprocalPath
          parameters I controller phase₀ t k)) t := by
  let w : ℝ → ℂ :=
    fun u =>
      poissonCharacterPath parameters I controller phase₀ u k
  let wdot : ℂ :=
    Complex.I *
      (frequencyValue parameters
        (DetectorPoissonReciprocalCode.reciprocalExponent I k)
        (clockPath parameters controller phase₀ t) : ℂ) *
      w t
  have hw : HasDerivAt w wdot t := by
    exact poissonCharacterPath_hasDerivAt
      parameters I controller phase₀ k t
  have hden :
      1 - (((1 / 2 : ℝ) : ℂ) * w t) ≠ 0 := by
    exact poissonDenominator_ne_zero
      parameters I controller phase₀ t k
  have hdenDeriv :
      HasDerivAt
        (fun u => 1 - (((1 / 2 : ℝ) : ℂ) * w u))
        (-(((1 / 2 : ℝ) : ℂ) * wdot)) t := by
    convert
      (hasDerivAt_const t (1 : ℂ)).sub
        (hw.const_mul (((1 / 2 : ℝ) : ℂ)))
      using 1
    ring
  have hinv :=
    (hasFDerivAt_inv' (𝕜 := ℝ) hden).comp_hasDerivAt
      t hdenDeriv
  convert hinv using 1
  unfold reciprocalVelocity poissonReciprocalPath
  dsimp only [w, wdot]
  simp only [ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply]
  ring

/-- Gauge source together with all literal Poisson reciprocals. -/
def poissonSourcePath
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ : Fin (clockCount eqs vars) → Circle)
    (ξ₀ : Fin vars → ℂ)
    (τ₀ : Fin vars → UpperHalfPlane)
    (t : ℝ) :
    DetectorPoissonReciprocalCode.State eqs vars where
  base :=
    gaugeSourcePath parameters I controller phase₀ ξ₀ τ₀ t
  reciprocal :=
    poissonReciprocalPath parameters I controller phase₀ t

/-- The canonical gauge source and the canonical Poisson inverses form an
integral curve of the complete reciprocal extension. -/
theorem poissonSourcePath_point_isIntegralCurve
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ : Fin (clockCount eqs vars) → Circle)
    (ξ₀ : Fin vars → ℂ)
    (τ₀ : Fin vars → UpperHalfPlane)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i))
    (hθ₁ :
      ∀ j t,
        jacobiTheta1
          (ellipticPath (ξ₀ j)
            (omegaFrequency parameters controller j)
            (numberFrequency parameters I controller j) t)
          (modularPath (τ₀ j)
            (omegaFrequency parameters controller j) t : ℂ) ≠ 0) :
    IsIntegralCurve
      (fun t =>
        DetectorPoissonReciprocalCode.point
          (poissonSourcePath
            parameters I controller phase₀ ξ₀ τ₀ t))
      (fun _ x =>
        PolynomialFieldCode.realize
          (DetectorPoissonReciprocalCode.fieldCode
            parameters I) x) := by
  apply
    DetectorPoissonReciprocalCode.point_isIntegralCurve
      parameters I
      (poissonSourcePath
        parameters I controller phase₀ ξ₀ τ₀)
  · exact
      gaugeSourcePath_point_isIntegralCurve
        parameters I controller phase₀ ξ₀ τ₀ hlock hθ₁
  · intro k t
    have h :=
      poissonReciprocalPath_hasDerivAt
        parameters I controller phase₀ k t
    simpa only [poissonSourcePath,
      DetectorPoissonReciprocalCode.vectorField,
      DetectorPoissonReciprocalCode.evalPair_derivativeBaseCode,
      gaugeSourcePath, linkedSourcePath_controllers] using h

/-! ## The explicit right-hand-side oscillator -/

/-- Constant frequency represented by the weighted fundamental equation
clocks.  The oscillator compiler inserts the remaining factor `-4`. -/
def rhsFrequency
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ) : ℝ :=
  ∑ row : Fin eqs,
    (I.rhs row : ℝ) *
      Clocks.LockedControllerPhaseTrajectory.characterFrequency
        parameters controller
        (FixedDetectorPolynomialCode.equationBasisExponent row)

/-- Along the whole canonical source trajectory, the semantic frequency
read by the RHS compiler is the constant `rhsFrequency`. -/
theorem weightedFrequency_poissonSourcePath
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ : Fin (clockCount eqs vars) → Circle)
    (ξ₀ : Fin vars → ℂ)
    (τ₀ : Fin vars → UpperHalfPlane)
    (t : ℝ) :
    Clocks.RHSOscillatorPolynomialCode.weightedFrequency
        (FixedDetectorPolynomialCode.rhsWeightCode I)
        (FixedDetectorPolynomialCode.equationFrequencyCode parameters)
        (DetectorPoissonReciprocalCode.point
          (poissonSourcePath
            parameters I controller phase₀ ξ₀ τ₀ t)) =
      rhsFrequency parameters I controller := by
  rw [FixedDetectorPolynomialCode.weightedFrequency_eq]
  unfold rhsFrequency
  apply Finset.sum_congr rfl
  intro row _
  congr 1
  change
    frequencyValue parameters
        (FixedDetectorPolynomialCode.equationBasisExponent row)
        (Clocks.LockedControllerPhaseTrajectory.stateFamily
          parameters controller phase₀ t) =
      Clocks.LockedControllerPhaseTrajectory.characterFrequency
        parameters controller
        (FixedDetectorPolynomialCode.equationBasisExponent row)
  exact
    Clocks.LockedControllerPhaseTrajectory.frequencyValue_stateFamily
      parameters controller phase₀
      (FixedDetectorPolynomialCode.equationBasisExponent row) t

/-- Explicit solution of the final two-dimensional oscillator. -/
def rhsPath
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (rhs₀ : Circle)
    (t : ℝ) :
    Controller.PhaseState ℝ :=
  Clocks.LockedControllerPhaseTrajectory.phasePath
    (-4 * rhsFrequency parameters I controller) rhs₀ t

/-- The explicit RHS rotation solves the exact oscillator emitted by the
final compiler layer. -/
theorem rhsPath_isOscillatorTrajectory
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ : Fin (clockCount eqs vars) → Circle)
    (ξ₀ : Fin vars → ℂ)
    (τ₀ : Fin vars → UpperHalfPlane)
    (rhs₀ : Circle) :
    Clocks.RHSOscillatorPolynomialCode.IsOscillatorTrajectory
      (FixedDetectorPolynomialCode.rhsWeightCode I)
      (FixedDetectorPolynomialCode.equationFrequencyCode parameters)
      (fun t =>
        DetectorPoissonReciprocalCode.point
          (poissonSourcePath
            parameters I controller phase₀ ξ₀ τ₀ t))
      (rhsPath parameters I controller rhs₀) where
  c t := by
    rw [Clocks.RHSOscillatorPolynomialCode.oscillatorField,
      weightedFrequency_poissonSourcePath]
    exact
      Clocks.LockedControllerPhaseTrajectory.phasePath_c_hasDerivAt
        (-4 * rhsFrequency parameters I controller) rhs₀ t
  d t := by
    rw [Clocks.RHSOscillatorPolynomialCode.oscillatorField,
      weightedFrequency_poissonSourcePath]
    exact
      Clocks.LockedControllerPhaseTrajectory.phasePath_d_hasDerivAt
        (-4 * rhsFrequency parameters I controller) rhs₀ t

/-! ## The complete canonical detector trajectory -/

/-- The fully assembled canonical state: linked theta source, fourth-root
gauges, Poisson inverses, and RHS oscillator. -/
def fixedDetectorPath
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ : Fin (clockCount eqs vars) → Circle)
    (ξ₀ : Fin vars → ℂ)
    (τ₀ : Fin vars → UpperHalfPlane)
    (rhs₀ : Circle)
    (t : ℝ) :
    FixedDetectorPolynomialCode.State eqs vars where
  base :=
    poissonSourcePath parameters I controller phase₀ ξ₀ τ₀ t
  rhs :=
    rhsPath parameters I controller rhs₀ t

/-- **Concrete integral curve of the complete fixed detector.**

All auxiliary scalar ODEs are discharged by explicit formulas.  The only
hypotheses are the intended source-chart conditions: every controller is
locked at an equilibrium, and every canonical Jacobi trajectory stays in
the chart where the stored reciprocal `1/θ₁` is defined. -/
theorem fixedDetectorPath_point_isIntegralCurve
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ : Fin (clockCount eqs vars) → Circle)
    (ξ₀ : Fin vars → ℂ)
    (τ₀ : Fin vars → UpperHalfPlane)
    (rhs₀ : Circle)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i))
    (hθ₁ :
      ∀ j t,
        jacobiTheta1
          (ellipticPath (ξ₀ j)
            (omegaFrequency parameters controller j)
            (numberFrequency parameters I controller j) t)
          (modularPath (τ₀ j)
            (omegaFrequency parameters controller j) t : ℂ) ≠ 0) :
    IsIntegralCurve
      (fun t =>
        FixedDetectorPolynomialCode.point
          (fixedDetectorPath
            parameters I controller phase₀ ξ₀ τ₀ rhs₀ t))
      (fun _ x =>
        PolynomialFieldCode.realize
          (FixedDetectorPolynomialCode.fieldCode
            parameters I) x) := by
  apply
    FixedDetectorPolynomialCode.point_isIntegralCurve
      parameters I
      (fixedDetectorPath
        parameters I controller phase₀ ξ₀ τ₀ rhs₀)
  · exact
      poissonSourcePath_point_isIntegralCurve
        parameters I controller phase₀ ξ₀ τ₀ hlock hθ₁
  · exact
      rhsPath_isOscillatorTrajectory
        parameters I controller phase₀ ξ₀ τ₀ rhs₀

end

end HGAS.CanonicalFixedDetectorTrajectory
