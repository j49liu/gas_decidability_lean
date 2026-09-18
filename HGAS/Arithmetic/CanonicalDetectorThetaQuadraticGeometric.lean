import HGAS.Analysis.TorusFourierCesaroArbitraryHorizon
import HGAS.Analysis.PoissonKernelFourier
import HGAS.Arithmetic.DetectorFactorizedFourier
import HGAS.Arithmetic.FixedDetectorMomentCode
import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorSelectedFactorization
import HGAS.Modular.JacobiThreeMomentTargetRigidity
import Mathlib.Tactic

/-!
# Canonical detector theta coefficients are quadratic--geometric

Fix a point of the arithmetic detector torus.  The `n`th term of one
Gaussian theta factor is

```text
  λ^(|n|²) · χ_private(phase)^(n²) · χ_linear(phase)^n.
```

Thus it is the quadratic--geometric sequence

```text
  R^(n²) S^n,
  R = λ χ_private(phase),   S = χ_linear(phase).
```

This module records that elementary identity at the exact interface used
by `JacobiThreeMomentTargetRigidity`.  It also proves the corresponding
time-dependent identity along an arbitrary torus translation: the
quadratic moment series whose coefficients are frozen at the initial
phase is exactly the evolving canonical theta sum.
-/

noncomputable section

open scoped BigOperators

namespace HGAS.CanonicalDetectorThetaQuadraticGeometric

open HGAS
open HGAS.Analysis
open HGAS.Clocks
open HGAS.Modular
open HGAS.NormalizedCorrectedFixedDetectorBidirectionalValidityOrbit
open HGAS.NormalizedCorrectedFixedDetectorSelectedPhysicalPhase
open
  HGAS.NormalizedCorrectedFixedDetectorSelectedPhysicalPhase.SelectedBidirectionalValidityOrbit

variable {eqs vars : ℕ}

/-- The coefficient family of one detector theta factor, frozen at a
specified torus phase. -/
def fixedPhaseThetaCoefficient
    (lambda : ℝ) (I : DQLSystem eqs vars) (j : Fin vars)
    (phase : UnitAddTorus (DetectorPhase eqs vars)) (n : ℤ) : ℂ :=
  DetectorFactorizedFourier.thetaTerm lambda I j n phase

/-- The real angular frequency paired with the private character. -/
def privateAngularFrequency
    (j : Fin vars)
    (turnsFrequency : DetectorPhase eqs vars → ℝ) : ℝ :=
  Analysis.torusRealFrequency
    (fun _ : Unit ↦ DetectorCharacterCode.privateCharacter j)
    turnsFrequency ()

/-- The real angular frequency paired with the linear column character. -/
def linearAngularFrequency
    (I : DQLSystem eqs vars) (j : Fin vars)
    (turnsFrequency : DetectorPhase eqs vars → ℝ) : ℝ :=
  Analysis.torusRealFrequency
    (fun _ : Unit ↦ DetectorCharacterCode.linearCharacter I j)
    turnsFrequency ()

/-- Turns-per-time frequency of the fourth-power arithmetic detector
obtained from a family of locked physical controllers. -/
def controllerDetectorTurnsFrequency
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (coordinate : DetectorPhase eqs vars) : ℝ :=
  4 *
    (Clocks.LockedControllerPhaseTrajectory.angularVelocity
        parameters controller (finSumFinEquiv coordinate) /
      (2 * Real.pi))

/-- Pairing the fourth-power detector frequency with the private
character recovers the literal modular angular frequency. -/
theorem privateAngularFrequency_controllerDetectorTurnsFrequency
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (j : Fin vars) :
    privateAngularFrequency j
        (controllerDetectorTurnsFrequency parameters controller) =
      CanonicalFixedDetectorTrajectory.omegaFrequency
        parameters controller j := by
  rw [
    HGAS.CanonicalFixedDetectorFourierCrosswalk.omegaFrequency_eq_characterFrequency,
    HGAS.CanonicalFixedDetectorFourierCrosswalk.flattenedCharacterFrequency_eq]
  unfold privateAngularFrequency controllerDetectorTurnsFrequency
    Analysis.torusRealFrequency RadicalClock.frequencyPairing
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  field_simp [Real.pi_ne_zero]

/-- Pairing the fourth-power detector frequency with the DQL linear
character recovers the literal linear-column angular frequency. -/
theorem linearAngularFrequency_controllerDetectorTurnsFrequency
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (I : DQLSystem eqs vars) (j : Fin vars) :
    linearAngularFrequency I j
        (controllerDetectorTurnsFrequency parameters controller) =
      CanonicalFixedDetectorTrajectory.numberFrequency
        parameters I controller j := by
  rw [
    HGAS.CanonicalFixedDetectorFourierCrosswalk.numberFrequency_eq_characterFrequency,
    HGAS.CanonicalFixedDetectorFourierCrosswalk.flattenedCharacterFrequency_eq]
  unfold linearAngularFrequency controllerDetectorTurnsFrequency
    Analysis.torusRealFrequency RadicalClock.frequencyPairing
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  field_simp [Real.pi_ne_zero]

private theorem int_sq_eq_natAbs_sq (n : ℤ) :
    n ^ 2 = (n.natAbs ^ 2 : ℕ) := by
  rw [Nat.cast_pow, Int.natAbs_sq]

/-- Pointwise algebraic form of a detector theta coefficient. -/
theorem fixedPhaseThetaCoefficient_eq_quadraticGeometricSequence
    (lambda : ℝ) (I : DQLSystem eqs vars) (j : Fin vars)
    (phase : UnitAddTorus (DetectorPhase eqs vars)) (n : ℤ) :
    fixedPhaseThetaCoefficient lambda I j phase n =
      quadraticGeometricSequence
        (((lambda : ℂ) *
          UnitAddTorus.mFourier
            (DetectorCharacterCode.privateCharacter j) phase))
        (UnitAddTorus.mFourier
          (DetectorCharacterCode.linearCharacter I j) phase)
        n := by
  have hsquare := int_sq_eq_natAbs_sq n
  unfold fixedPhaseThetaCoefficient
    DetectorFactorizedFourier.thetaTerm
    DetectorFactorizedFourier.thetaCoordinateExponent
    quadraticGeometricSequence
  rw [show
      (fun coordinate : DetectorPhase eqs vars ↦
          n ^ 2 *
              DetectorCharacterCode.privateCharacter j coordinate +
            n *
              DetectorCharacterCode.linearCharacter I j coordinate) =
        (fun coordinate ↦
            n ^ 2 *
              DetectorCharacterCode.privateCharacter j coordinate) +
          (fun coordinate ↦
            n *
              DetectorCharacterCode.linearCharacter I j coordinate) by
      rfl]
  rw [UnitAddTorus.mFourier_add,
    HGAS.Analysis.mFourier_int_mul,
    HGAS.Analysis.mFourier_int_mul]
  rw [hsquare, zpow_natCast, zpow_natCast, mul_pow]
  push_cast
  ring

/-- At any fixed phase, a nonzero Gaussian detector theta coefficient
family is a normalized nondegenerate quadratic--geometric sequence. -/
theorem fixedPhaseThetaCoefficient_isQuadraticGeometric
    {lambda : ℝ} (hlambda : lambda ≠ 0)
    (I : DQLSystem eqs vars) (j : Fin vars)
    (phase : UnitAddTorus (DetectorPhase eqs vars)) :
    IsQuadraticGeometric
      (fixedPhaseThetaCoefficient lambda I j phase) := by
  refine
    ⟨((lambda : ℂ) *
        UnitAddTorus.mFourier
          (DetectorCharacterCode.privateCharacter j) phase),
      UnitAddTorus.mFourier
        (DetectorCharacterCode.linearCharacter I j) phase,
      ?_, ?_, ?_⟩
  · apply mul_ne_zero
    · exact_mod_cast hlambda
    · intro hzero
      have hnorm :=
        HGAS.Analysis.norm_mFourier_apply
          (DetectorCharacterCode.privateCharacter j) phase
      rw [hzero, norm_zero] at hnorm
      norm_num at hnorm
  · intro hzero
    have hnorm :=
      HGAS.Analysis.norm_mFourier_apply
        (DetectorCharacterCode.linearCharacter I j) phase
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm
  · funext n
    exact
      fixedPhaseThetaCoefficient_eq_quadraticGeometricSequence
        lambda I j phase n

/-- The canonical detector choice `λ = 1/256` is
quadratic--geometric at every initial phase. -/
theorem canonicalFixedPhaseThetaCoefficient_isQuadraticGeometric
    (I : DQLSystem eqs vars) (j : Fin vars)
    (phase : UnitAddTorus (DetectorPhase eqs vars)) :
    IsQuadraticGeometric
      (fixedPhaseThetaCoefficient (1 / 256 : ℝ) I j phase) := by
  exact
    fixedPhaseThetaCoefficient_isQuadraticGeometric
      (by norm_num) I j phase

/-! ## The two neighbouring coefficients and selector twists -/

/-- Detector-torus exponent of the positive Jacobi selector twist. -/
def jacobiPlusTorusExponent
    (I : DQLSystem eqs vars) (j : Fin vars) :
    DetectorPhase eqs vars → ℤ :=
  fun coordinate ↦
    -DetectorCharacterCode.privateCharacter j coordinate -
      DetectorCharacterCode.linearCharacter I j coordinate

/-- Detector-torus exponent of the negative Jacobi selector twist. -/
def jacobiMinusTorusExponent
    (I : DQLSystem eqs vars) (j : Fin vars) :
    DetectorPhase eqs vars → ℤ :=
  fun coordinate ↦
    -DetectorCharacterCode.privateCharacter j coordinate +
      DetectorCharacterCode.linearCharacter I j coordinate

/-- The compiled positive-selector character is exactly the flattened
torus exponent above. -/
theorem jacobiPlusExponent_eq_flattenCharacter
    (I : DQLSystem eqs vars) (j : Fin vars) :
    FixedDetectorMomentCode.jacobiPlusExponent I j =
      DetectorCharacterCode.flattenCharacter
        (jacobiPlusTorusExponent I j) := by
  funext i
  simp [FixedDetectorMomentCode.jacobiPlusExponent,
    FixedDetectorMomentCode.privateExponent,
    FixedDetectorMomentCode.linearExponent,
    DetectorCharacterCode.flattenCharacter,
    jacobiPlusTorusExponent]
  ring

/-- The compiled negative-selector character is exactly the flattened
torus exponent above. -/
theorem jacobiMinusExponent_eq_flattenCharacter
    (I : DQLSystem eqs vars) (j : Fin vars) :
    FixedDetectorMomentCode.jacobiMinusExponent I j =
      DetectorCharacterCode.flattenCharacter
        (jacobiMinusTorusExponent I j) := by
  funext i
  simp [FixedDetectorMomentCode.jacobiMinusExponent,
    FixedDetectorMomentCode.privateExponent,
    FixedDetectorMomentCode.linearExponent,
    DetectorCharacterCode.flattenCharacter,
    jacobiMinusTorusExponent]
  ring

/-- Initial phase factor of the positive Jacobi selector. -/
def jacobiPlusTorusTwist
    (I : DQLSystem eqs vars) (j : Fin vars)
    (phase : UnitAddTorus (DetectorPhase eqs vars)) : ℂ :=
  UnitAddTorus.mFourier (jacobiPlusTorusExponent I j) phase

/-- Initial phase factor of the negative Jacobi selector. -/
def jacobiMinusTorusTwist
    (I : DQLSystem eqs vars) (j : Fin vars)
    (phase : UnitAddTorus (DetectorPhase eqs vars)) : ℂ :=
  UnitAddTorus.mFourier (jacobiMinusTorusExponent I j) phase

theorem jacobiPlusTorusTwist_ne_zero
    (I : DQLSystem eqs vars) (j : Fin vars)
    (phase : UnitAddTorus (DetectorPhase eqs vars)) :
    jacobiPlusTorusTwist I j phase ≠ 0 := by
  intro hzero
  have hnorm :=
    HGAS.Analysis.norm_mFourier_apply
      (jacobiPlusTorusExponent I j) phase
  rw [show
      UnitAddTorus.mFourier
          (jacobiPlusTorusExponent I j) phase =
        jacobiPlusTorusTwist I j phase by rfl,
    hzero, norm_zero] at hnorm
  norm_num at hnorm

theorem jacobiMinusTorusTwist_ne_zero
    (I : DQLSystem eqs vars) (j : Fin vars)
    (phase : UnitAddTorus (DetectorPhase eqs vars)) :
    jacobiMinusTorusTwist I j phase ≠ 0 := by
  intro hzero
  have hnorm :=
    HGAS.Analysis.norm_mFourier_apply
      (jacobiMinusTorusExponent I j) phase
  rw [show
      UnitAddTorus.mFourier
          (jacobiMinusTorusExponent I j) phase =
        jacobiMinusTorusTwist I j phase by rfl,
    hzero, norm_zero] at hnorm
  norm_num at hnorm

/-- The positive selector twist cancels the phase of the coefficient at
`n = 1`, leaving only the Gaussian weight. -/
theorem jacobiPlusTorusTwist_mul_fixedPhaseThetaCoefficient_one
    (lambda : ℝ) (I : DQLSystem eqs vars) (j : Fin vars)
    (phase : UnitAddTorus (DetectorPhase eqs vars)) :
    jacobiPlusTorusTwist I j phase *
        fixedPhaseThetaCoefficient lambda I j phase 1 =
      (lambda : ℂ) := by
  have hcancel :
      jacobiPlusTorusExponent I j +
          DetectorFactorizedFourier.thetaCoordinateExponent I j 1 =
        0 := by
    funext coordinate
    simp [jacobiPlusTorusExponent,
      DetectorFactorizedFourier.thetaCoordinateExponent]
  unfold jacobiPlusTorusTwist fixedPhaseThetaCoefficient
    DetectorFactorizedFourier.thetaTerm
  simp only [Int.natAbs_one, one_pow, pow_one]
  calc
    UnitAddTorus.mFourier (jacobiPlusTorusExponent I j) phase *
          ((lambda : ℂ) *
            UnitAddTorus.mFourier
              (DetectorFactorizedFourier.thetaCoordinateExponent I j 1)
              phase) =
        (lambda : ℂ) *
          (UnitAddTorus.mFourier
              (jacobiPlusTorusExponent I j) phase *
            UnitAddTorus.mFourier
              (DetectorFactorizedFourier.thetaCoordinateExponent I j 1)
              phase) := by ring
    _ =
        (lambda : ℂ) *
          UnitAddTorus.mFourier
            (jacobiPlusTorusExponent I j +
              DetectorFactorizedFourier.thetaCoordinateExponent I j 1)
            phase := by rw [UnitAddTorus.mFourier_add]
    _ = (lambda : ℂ) := by
      simp [hcancel, UnitAddTorus.mFourier_zero]

/-- The negative selector twist cancels the phase of the coefficient at
`n = -1`, leaving only the Gaussian weight. -/
theorem jacobiMinusTorusTwist_mul_fixedPhaseThetaCoefficient_neg_one
    (lambda : ℝ) (I : DQLSystem eqs vars) (j : Fin vars)
    (phase : UnitAddTorus (DetectorPhase eqs vars)) :
    jacobiMinusTorusTwist I j phase *
        fixedPhaseThetaCoefficient lambda I j phase (-1) =
      (lambda : ℂ) := by
  have hcancel :
      jacobiMinusTorusExponent I j +
          DetectorFactorizedFourier.thetaCoordinateExponent I j (-1) =
        0 := by
    funext coordinate
    simp [jacobiMinusTorusExponent,
      DetectorFactorizedFourier.thetaCoordinateExponent]
    ring
  unfold jacobiMinusTorusTwist fixedPhaseThetaCoefficient
    DetectorFactorizedFourier.thetaTerm
  norm_num only [Int.natAbs_neg, Int.natAbs_one, one_pow, pow_one]
  calc
    UnitAddTorus.mFourier (jacobiMinusTorusExponent I j) phase *
          ((lambda : ℂ) *
            UnitAddTorus.mFourier
              (DetectorFactorizedFourier.thetaCoordinateExponent I j (-1))
              phase) =
        (lambda : ℂ) *
          (UnitAddTorus.mFourier
              (jacobiMinusTorusExponent I j) phase *
            UnitAddTorus.mFourier
              (DetectorFactorizedFourier.thetaCoordinateExponent I j (-1))
              phase) := by ring
    _ =
        (lambda : ℂ) *
          UnitAddTorus.mFourier
            (jacobiMinusTorusExponent I j +
              DetectorFactorizedFourier.thetaCoordinateExponent I j (-1))
            phase := by rw [UnitAddTorus.mFourier_add]
    _ = (lambda : ℂ) := by
      simp [hcancel, UnitAddTorus.mFourier_zero]

theorem jacobiPlusTorusTwist_mul_canonicalThetaCoefficient_one
    (I : DQLSystem eqs vars) (j : Fin vars)
    (phase : UnitAddTorus (DetectorPhase eqs vars)) :
    jacobiPlusTorusTwist I j phase *
        fixedPhaseThetaCoefficient (1 / 256 : ℝ) I j phase 1 =
      ((1 / 256 : ℝ) : ℂ) :=
  jacobiPlusTorusTwist_mul_fixedPhaseThetaCoefficient_one
    (1 / 256 : ℝ) I j phase

theorem jacobiMinusTorusTwist_mul_canonicalThetaCoefficient_neg_one
    (I : DQLSystem eqs vars) (j : Fin vars)
    (phase : UnitAddTorus (DetectorPhase eqs vars)) :
    jacobiMinusTorusTwist I j phase *
        fixedPhaseThetaCoefficient (1 / 256 : ℝ) I j phase (-1) =
      ((1 / 256 : ℝ) : ℂ) :=
  jacobiMinusTorusTwist_mul_fixedPhaseThetaCoefficient_neg_one
    (1 / 256 : ℝ) I j phase

/-! The next two statements are the literal selected-orbit form used by
the three-moment argument.  The actual controller character at time zero
is converted to its detector-torus Fourier character by the already
proved physical-phase crosswalk. -/

theorem characterValue_jacobiPlusExponent_mul_physicalThetaCoefficient_one
    {u :
      NormalizedCorrectedFixedDetectorCompactSourceCode.CompilerInput
        eqs vars}
    (O : SelectedBidirectionalValidityOrbit u)
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (lambda : ℝ) (I : DQLSystem eqs vars) (j : Fin vars) :
    Clocks.ControllerPhaseProductCharacterCode.characterValue
          (FixedDetectorMomentCode.jacobiPlusExponent I j)
          (physicalControllers O 0) *
        fixedPhaseThetaCoefficient lambda I j
          (physicalDetectorPhase O hscale 0) 1 =
      (lambda : ℂ) := by
  rw [jacobiPlusExponent_eq_flattenCharacter]
  rw [← mFourier_physicalDetectorPhase O hscale]
  exact
    jacobiPlusTorusTwist_mul_fixedPhaseThetaCoefficient_one
      lambda I j
        (physicalDetectorPhase O hscale 0)

theorem characterValue_jacobiMinusExponent_mul_physicalThetaCoefficient_neg_one
    {u :
      NormalizedCorrectedFixedDetectorCompactSourceCode.CompilerInput
        eqs vars}
    (O : SelectedBidirectionalValidityOrbit u)
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (lambda : ℝ) (I : DQLSystem eqs vars) (j : Fin vars) :
    Clocks.ControllerPhaseProductCharacterCode.characterValue
          (FixedDetectorMomentCode.jacobiMinusExponent I j)
          (physicalControllers O 0) *
        fixedPhaseThetaCoefficient lambda I j
          (physicalDetectorPhase O hscale 0) (-1) =
      (lambda : ℂ) := by
  rw [jacobiMinusExponent_eq_flattenCharacter]
  rw [← mFourier_physicalDetectorPhase O hscale]
  exact
    jacobiMinusTorusTwist_mul_fixedPhaseThetaCoefficient_neg_one
      lambda I j
        (physicalDetectorPhase O hscale 0)

/-! ## Evolution along a torus translation -/

/-- The angular frequency of a theta monomial is the expected quadratic
combination of the private and linear angular frequencies. -/
theorem thetaCoordinate_torusRealFrequency
    (I : DQLSystem eqs vars) (j : Fin vars)
    (turnsFrequency : DetectorPhase eqs vars → ℝ) (n : ℤ) :
    Analysis.torusRealFrequency
        (DetectorFactorizedFourier.thetaCoordinateExponent I j)
        turnsFrequency n =
      (n : ℝ) ^ 2 *
          privateAngularFrequency j turnsFrequency +
        (n : ℝ) *
          linearAngularFrequency I j turnsFrequency := by
  unfold Analysis.torusRealFrequency
    privateAngularFrequency linearAngularFrequency
    Clocks.RadicalClock.frequencyPairing
    DetectorFactorizedFourier.thetaCoordinateExponent
  simp only [Analysis.torusRealFrequency,
    Clocks.RadicalClock.frequencyPairing]
  push_cast
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  have hprivate :
      (∑ x : DetectorPhase eqs vars,
          (n : ℝ) ^ 2 *
              (DetectorCharacterCode.privateCharacter j x : ℝ) *
            turnsFrequency x) =
        (n : ℝ) ^ 2 *
          ∑ x : DetectorPhase eqs vars,
            (DetectorCharacterCode.privateCharacter j x : ℝ) *
              turnsFrequency x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hlinear :
      (∑ x : DetectorPhase eqs vars,
          (n : ℝ) *
              (DetectorCharacterCode.linearCharacter I j x : ℝ) *
            turnsFrequency x) =
        (n : ℝ) *
          ∑ x : DetectorPhase eqs vars,
            (DetectorCharacterCode.linearCharacter I j x : ℝ) *
              turnsFrequency x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hprivate, hlinear]
  ring

/-- The torus angular frequency of a theta monomial, rewritten as the
quadratic dispersion used by the Jacobi moment series. -/
theorem thetaCoordinate_torusRealFrequency_eq_quadraticMomentFrequency
    (I : DQLSystem eqs vars) (j : Fin vars)
    (turnsFrequency : DetectorPhase eqs vars → ℝ)
    (hprivate :
      privateAngularFrequency j turnsFrequency ≠ 0)
    (n : ℤ) :
    Analysis.torusRealFrequency
        (DetectorFactorizedFourier.thetaCoordinateExponent I j)
        turnsFrequency n =
      quadraticMomentFrequency
        (privateAngularFrequency j turnsFrequency)
        (linearAngularFrequency I j turnsFrequency /
          privateAngularFrequency j turnsFrequency)
        0 0 n := by
  rw [thetaCoordinate_torusRealFrequency]
  unfold quadraticMomentFrequency quadraticDispersion
  push_cast
  field_simp [hprivate]
  ring

/-- Freezing the theta coefficients at the initial torus point and
evolving them by their quadratic frequencies gives exactly the theta sum
evaluated on the translated torus point. -/
theorem quadraticMomentSeries_fixedPhaseThetaCoefficient_eq_thetaSum
    (lambda : ℝ) (I : DQLSystem eqs vars) (j : Fin vars)
    (turnsFrequency : DetectorPhase eqs vars → ℝ)
    (phase₀ : UnitAddTorus (DetectorPhase eqs vars))
    (hprivate :
      privateAngularFrequency j turnsFrequency ≠ 0)
    (t : ℝ) :
    quadraticMomentSeries
        (fixedPhaseThetaCoefficient lambda I j phase₀)
        (privateAngularFrequency j turnsFrequency)
        (linearAngularFrequency I j turnsFrequency /
          privateAngularFrequency j turnsFrequency)
        0 0 t =
      ∑' n : ℤ,
        DetectorFactorizedFourier.thetaTerm lambda I j n
          (RadicalClock.torusTranslationFlow
            turnsFrequency t phase₀) := by
  change
    quadraticMomentSeries
        (fixedPhaseThetaCoefficient lambda I j phase₀)
        (privateAngularFrequency j turnsFrequency)
        (linearAngularFrequency I j turnsFrequency /
          privateAngularFrequency j turnsFrequency)
        0 0 t =
      torusFourierSeries
        (fun n : ℤ ↦ ((lambda ^ (n.natAbs ^ 2) : ℝ) : ℂ))
        (DetectorFactorizedFourier.thetaCoordinateExponent I j)
        (RadicalClock.torusTranslationFlow
          turnsFrequency t phase₀)
  rw [Analysis.torusFourierSeries_translation_eq_exponentialSeries]
  unfold quadraticMomentSeries Analysis.exponentialSeries
  apply tsum_congr
  intro n
  unfold Analysis.exponentialSeriesTerm
    Analysis.translatedTorusCoefficient
    fixedPhaseThetaCoefficient
    DetectorFactorizedFourier.thetaTerm
  rw [
    thetaCoordinate_torusRealFrequency_eq_quadraticMomentFrequency
      I j turnsFrequency hprivate n]

end HGAS.CanonicalDetectorThetaQuadraticGeometric
