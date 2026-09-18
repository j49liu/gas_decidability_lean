import HGAS.Analysis.ComplexRealTimeDerivative
import HGAS.Clocks.ControllerPhaseProductCharacterDynamics
import HGAS.Clocks.ControllerPhaseProductCharacterUnit
import Mathlib.Tactic

/-!
# Explicit trajectories with locked controllers

The detector uses the controller field only on its equilibrium locus.
There each controller is constant, while its companion phase rotates with
the fixed angular velocity

```text
                         ωᵢ = pᵢ rᵢ.
```

This file constructs that trajectory directly.  It is useful independently
of the detector: the resulting path solves the literal product polynomial
field, stays on all phase circles, and every compiled integral character
has its expected logarithmic derivative.
-/

namespace HGAS.Clocks.LockedControllerPhaseTrajectory

open HGAS
open Complex
open ControllerPhaseProductPolynomialCode
open ControllerPhaseProductCharacterCode

noncomputable section

variable {q : ℕ}

/-- The constant angular velocity selected by one locked controller. -/
def angularVelocity
    (parameters : Fin q → RationalCode)
    (controller : Fin q → Controller.ControllerState ℝ)
    (i : Fin q) : ℝ :=
  (RationalCode.decode (parameters i) : ℝ) *
    (controller i).r

/-- The explicit rotating real phase state. -/
def phasePath
    (ω : ℝ) (phase₀ : Circle) (t : ℝ) :
    Controller.PhaseState ℝ :=
  PhaseClockFlow.circlePhaseState
    (PhaseClockFlow.phaseRotationFlow ω t phase₀)

/-- A finite family of constant controllers and explicitly rotating
unit-circle phases. -/
def stateFamily
    (parameters : Fin q → RationalCode)
    (controller : Fin q → Controller.ControllerState ℝ)
    (phase₀ : Fin q → Circle)
    (t : ℝ) :
    StateFamily q ℝ :=
  fun i =>
    {
      controller := controller i
      phase :=
        phasePath
          (angularVelocity parameters controller i)
          (phase₀ i) t
    }

@[simp]
theorem stateFamily_controller
    (parameters : Fin q → RationalCode)
    (controller : Fin q → Controller.ControllerState ℝ)
    (phase₀ : Fin q → Circle)
    (t : ℝ) (i : Fin q) :
    (stateFamily parameters controller phase₀ t i).controller =
      controller i :=
  rfl

@[simp]
theorem phaseValue_stateFamily
    (parameters : Fin q → RationalCode)
    (controller : Fin q → Controller.ControllerState ℝ)
    (phase₀ : Fin q → Circle)
    (t : ℝ) (i : Fin q) :
    phaseValue
        (stateFamily parameters controller phase₀ t) i =
      (PhaseClockFlow.phaseRotationFlow
        (angularVelocity parameters controller i)
        t (phase₀ i) : ℂ) := by
  apply Complex.ext <;>
    simp [phaseValue, stateFamily, phasePath,
      PhaseClockFlow.circlePhaseState]

/-- The explicit phase family lies on every intended unit circle. -/
theorem stateFamily_onPhaseCircles
    (parameters : Fin q → RationalCode)
    (controller : Fin q → Controller.ControllerState ℝ)
    (phase₀ : Fin q → Circle)
    (t : ℝ) :
    OnPhaseCircles
      (stateFamily parameters controller phase₀ t) := by
  intro i
  rw [phaseValue_stateFamily]
  exact Circle.norm_coe _

/-- Real-part equation for one explicit rotating phase. -/
theorem phasePath_c_hasDerivAt
    (ω : ℝ) (phase₀ : Circle) (t : ℝ) :
    HasDerivAt
      (fun u => (phasePath ω phase₀ u).c)
      (Controller.phaseField ω (phasePath ω phase₀ t)).c t := by
  have h :=
    HGAS.HasDerivAt.complex_re
      (PhaseClockFlow.phaseRotationFlow_solves_phaseField
        ω t phase₀)
  simpa only [phasePath, PhaseClockFlow.circlePhaseState,
    PhaseClockFlow.phaseStateComplex,
    Controller.phaseField,
    Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, mul_one, sub_zero, add_zero] using h

/-- Imaginary-part equation for one explicit rotating phase. -/
theorem phasePath_d_hasDerivAt
    (ω : ℝ) (phase₀ : Circle) (t : ℝ) :
    HasDerivAt
      (fun u => (phasePath ω phase₀ u).d)
      (Controller.phaseField ω (phasePath ω phase₀ t)).d t := by
  have h :=
    HGAS.HasDerivAt.complex_im
      (PhaseClockFlow.phaseRotationFlow_solves_phaseField
        ω t phase₀)
  simpa only [phasePath, PhaseClockFlow.circlePhaseState,
    PhaseClockFlow.phaseStateComplex,
    Controller.phaseField,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, mul_one, zero_add, add_zero] using h

/-- The flattened explicit locked path is an integral curve of the
literal product controller polynomial code. -/
theorem point_stateFamily_isIntegralCurve
    (parameters : Fin q → RationalCode)
    (controller : Fin q → Controller.ControllerState ℝ)
    (phase₀ : Fin q → Circle)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i)) :
    IsIntegralCurve
      (fun t =>
        point (stateFamily parameters controller phase₀ t))
      (fun _ x =>
        PolynomialFieldCode.realize
          (fieldCode parameters) x) := by
  intro t
  rw [hasDerivAt_pi]
  intro k
  change
    HasDerivAt
      (fun u =>
        point
          (stateFamily parameters controller phase₀ u) k)
      (PolynomialFieldCode.realize
        (fieldCode parameters)
        (point
          (stateFamily parameters controller phase₀ t)) k) t
  rw [realize_fieldCode]
  obtain ⟨⟨i, j⟩, rfl⟩ :=
    finProdFinEquiv.surjective k
  rw [show
    finProdFinEquiv (i, j) =
      blockEmbedding i j by rfl]
  have hfield := hlock i
  have hr :
      (Controller.controllerField
        (RationalCode.decode (parameters i) : ℝ)
        (controller i)).r = 0 := by
    exact congrArg Controller.ControllerState.r hfield
  have hs :
      (Controller.controllerField
        (RationalCode.decode (parameters i) : ℝ)
        (controller i)).s = 0 := by
    exact congrArg Controller.ControllerState.s hfield
  have hr' :
      -(controller i).s *
          Controller.mismatch
            (RationalCode.decode (parameters i) : ℝ)
            (controller i) = 0 := by
    simpa only [Controller.controllerField_r] using hr
  have hr'' :
      -((controller i).s *
          Controller.mismatch
            (RationalCode.decode (parameters i) : ℝ)
            (controller i)) = 0 := by
    calc
      -((controller i).s *
          Controller.mismatch
            (RationalCode.decode (parameters i) : ℝ)
            (controller i)) =
          -(controller i).s *
            Controller.mismatch
              (RationalCode.decode (parameters i) : ℝ)
              (controller i) := by ring
      _ = 0 := hr'
  have hs' :
      (controller i).r *
          Controller.mismatch
            (RationalCode.decode (parameters i) : ℝ)
            (controller i) = 0 := by
    simpa only [Controller.controllerField_s] using hs
  fin_cases j
  · simpa [point, stateFamily, vectorField,
      blockEmbedding,
      ControllerPolynomialCode.point,
      ControllerPolynomialCode.vectorField,
      Controller.controllerOrigin, hr''] using
      (hasDerivAt_const t (controller i).r)
  · simpa [point, stateFamily, vectorField,
      blockEmbedding,
      ControllerPolynomialCode.point,
      ControllerPolynomialCode.vectorField,
      Controller.controllerOrigin, hs'] using
      (hasDerivAt_const t (controller i).s)
  · simpa [point, stateFamily, vectorField,
      blockEmbedding,
      ControllerPolynomialCode.point,
      ControllerPolynomialCode.vectorField,
      Controller.lockedPhaseField, angularVelocity] using
      phasePath_c_hasDerivAt
        (angularVelocity parameters controller i)
        (phase₀ i) t
  · simpa [point, stateFamily, vectorField,
      blockEmbedding,
      ControllerPolynomialCode.point,
      ControllerPolynomialCode.vectorField,
      Controller.lockedPhaseField, angularVelocity] using
      phasePath_d_hasDerivAt
        (angularVelocity parameters controller i)
        (phase₀ i) t

/-! ## Integral characters along the locked path -/

/-- Constant frequency of an integral phase character. -/
def characterFrequency
    (parameters : Fin q → RationalCode)
    (controller : Fin q → Controller.ControllerState ℝ)
    (exponents : Fin q → ℤ) : ℝ :=
  ∑ i : Fin q,
    (exponents i : ℝ) *
      angularVelocity parameters controller i

@[simp]
theorem frequencyValue_stateFamily
    (parameters : Fin q → RationalCode)
    (controller : Fin q → Controller.ControllerState ℝ)
    (phase₀ : Fin q → Circle)
    (exponents : Fin q → ℤ)
    (t : ℝ) :
    frequencyValue parameters exponents
        (stateFamily parameters controller phase₀ t) =
      characterFrequency parameters controller exponents := by
  simp only [frequencyValue, characterFrequency, stateFamily,
    angularVelocity]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Every signed-power character of the explicit locked path has the
constant logarithmic derivative `i` times its compiled frequency. -/
theorem characterValue_hasDerivAt
    (parameters : Fin q → RationalCode)
    (controller : Fin q → Controller.ControllerState ℝ)
    (phase₀ : Fin q → Circle)
    (exponents : Fin q → ℤ)
    (t : ℝ) :
    HasDerivAt
      (fun u =>
        characterValue exponents
          (stateFamily parameters controller phase₀ u))
      (Complex.I *
          (characterFrequency parameters controller
            exponents : ℂ) *
        characterValue exponents
          (stateFamily parameters controller phase₀ t)) t := by
  let ζ : Fin q → ℝ → ℂ :=
    fun i u =>
      (PhaseClockFlow.phaseRotationFlow
        (angularVelocity parameters controller i)
        u (phase₀ i) : ℂ)
  have hζ :
      ∀ i,
        HasDerivAt (ζ i)
          (Complex.I *
            (angularVelocity parameters controller i : ℂ) *
            ζ i t) t := by
    intro i
    have h :=
      PhaseClockFlow.hasDerivAt_phaseRotationFlow_coe
        (angularVelocity parameters controller i)
        t (phase₀ i)
    convert h using 1
    ring
  let f : Fin q → ℝ → ℂ :=
    fun i u =>
      signedPowerValue
        (stateFamily parameters controller phase₀ u)
        i (exponents i)
  let f' : Fin q → ℂ :=
    fun i =>
      Complex.I *
        (((exponents i : ℝ) *
          angularVelocity parameters controller i : ℝ) : ℂ) *
        f i t
  have hfactor :
      ∀ i, HasDerivAt (f i) (f' i) t := by
    intro i
    have hsigned :=
      ControllerPhaseProductCharacterDynamics.hasDerivAt_signedPower
        (ζ i)
        (angularVelocity parameters controller i)
        (exponents i) t (hζ i)
    simpa only [f, f', signedPowerValue,
      phaseValue_stateFamily, ζ] using hsigned
  have hproduct :=
    HasDerivAt.fun_finsetProd
      (u := Finset.univ)
      (fun i _ => hfactor i)
  have hvelocity :
      ∑ i : Fin q,
          (∏ j ∈ Finset.univ.erase i, f j t) • f' i =
        Complex.I *
          (characterFrequency parameters controller exponents : ℂ) *
          ∏ j : Fin q, f j t := by
    simp only [f']
    calc
      ∑ i : Fin q,
          (∏ j ∈ Finset.univ.erase i, f j t) •
            (Complex.I *
              (((exponents i : ℝ) *
                angularVelocity parameters controller i : ℝ) : ℂ) *
              f i t) =
          ∑ i : Fin q,
            Complex.I *
              (((exponents i : ℝ) *
                angularVelocity parameters controller i : ℝ) : ℂ) *
              ∏ j : Fin q, f j t := by
        apply Finset.sum_congr rfl
        intro i _
        rw [smul_eq_mul]
        calc
          (∏ j ∈ Finset.univ.erase i, f j t) *
                (Complex.I *
                  (((exponents i : ℝ) *
                    angularVelocity parameters controller i : ℝ) : ℂ) *
                  f i t) =
              Complex.I *
                (((exponents i : ℝ) *
                  angularVelocity parameters controller i : ℝ) : ℂ) *
                ((∏ j ∈ Finset.univ.erase i, f j t) *
                  f i t) := by
            ring
          _ =
              Complex.I *
                (((exponents i : ℝ) *
                  angularVelocity parameters controller i : ℝ) : ℂ) *
                ∏ j : Fin q, f j t := by
            rw [Finset.prod_erase_mul
              Finset.univ (fun j => f j t)
              (Finset.mem_univ i)]
      _ =
          Complex.I *
            (characterFrequency parameters controller exponents : ℂ) *
            ∏ j : Fin q, f j t := by
        unfold characterFrequency
        push_cast
        rw [Finset.mul_sum, Finset.sum_mul]
  rw [hvelocity] at hproduct
  simpa only [characterValue, List.prod_ofFn, f] using hproduct

/-- Code-facing form of `characterValue_hasDerivAt`. -/
theorem characterValue_hasDerivAt_derivativeCode
    (parameters : Fin q → RationalCode)
    (controller : Fin q → Controller.ControllerState ℝ)
    (phase₀ : Fin q → Circle)
    (exponents : Fin q → ℤ)
    (t : ℝ) :
    HasDerivAt
      (fun u =>
        characterValue exponents
          (stateFamily parameters controller phase₀ u))
      (evalPair
        (derivativeCode parameters exponents)
        (point
          (stateFamily parameters controller phase₀ t))) t := by
  simpa only [evalPair_derivativeCode,
    frequencyValue_stateFamily] using
    characterValue_hasDerivAt
      parameters controller phase₀ exponents t

end

end HGAS.Clocks.LockedControllerPhaseTrajectory
