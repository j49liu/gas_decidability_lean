import HGAS.Arithmetic.CanonicalFixedDetectorAlignment
import HGAS.Arithmetic.DetectorFactorizedFourier
import HGAS.Arithmetic.FixedDetectorNormalizedInvariantAverage
import HGAS.Analysis.PoissonKernelFourier
import Mathlib.Tactic

/-!
# The canonical polynomial detector is the normalized Fourier detector

This module closes the literal normalization diagram between:

* the fourth-power physical controller clocks;
* the canonical Jacobi theta trajectory at height `log 256 / π`;
* the rational Poisson reciprocal states;
* the right-hand-side oscillator; and
* the factorized/expanded Fourier detector with parameters
  `λ = 1/256`, `η = 1/2`.

The intermediate lemmas are stated separately so that the conversion from
physical radians to additive-torus turns can be reused.
-/

noncomputable section

open scoped BigOperators

namespace HGAS.CanonicalFixedDetectorFourierCrosswalk

open HGAS
open Modular
open Clocks
open Complex

variable {eqs vars : ℕ}

/-- The arithmetic detector phase read from the all-one fundamental clock
trajectory.  Arithmetic characters use fourth powers, hence the angular
velocity is multiplied by four before converting radians to turns. -/
def detectorPhasePath
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ) :
    UnitAddTorus (DetectorPhase eqs vars) :=
  fun phase ↦
    ((4 *
        Clocks.LockedControllerPhaseTrajectory.angularVelocity
          parameters controller (finSumFinEquiv phase) *
        t / (2 * Real.pi) : ℝ) : UnitAddCircle)

/-- Exact frequency pairing after flattening a detector character by the
common fourth-power convention. -/
theorem flattenedCharacterFrequency_eq
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (a : DetectorPhase eqs vars → ℤ) :
    Clocks.LockedControllerPhaseTrajectory.characterFrequency
        parameters controller
        (DetectorCharacterCode.flattenCharacter a) =
      ∑ phase : DetectorPhase eqs vars,
        (a phase : ℝ) *
          (4 *
            Clocks.LockedControllerPhaseTrajectory.angularVelocity
              parameters controller (finSumFinEquiv phase)) := by
  unfold Clocks.LockedControllerPhaseTrajectory.characterFrequency
    DetectorCharacterCode.flattenCharacter
  rw [← finSumFinEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro phase _
  push_cast
  rw [finSumFinEquiv.symm_apply_apply]
  ring

/-- Every detector-torus Fourier character along `detectorPhasePath` is
the same exponential as the corresponding flattened physical-clock
character. -/
theorem mFourier_detectorPhasePath
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (a : DetectorPhase eqs vars → ℤ)
    (t : ℝ) :
    UnitAddTorus.mFourier a
        (detectorPhasePath parameters controller t) =
      Complex.exp
        (((Clocks.LockedControllerPhaseTrajectory.characterFrequency
              parameters controller
              (DetectorCharacterCode.flattenCharacter a) *
            t : ℝ) : ℂ) *
          Complex.I) := by
  unfold UnitAddTorus.mFourier detectorPhasePath
  simp only [ContinuousMap.coe_mk, fourier_coe_apply]
  rw [← Complex.exp_sum]
  congr 1
  rw [flattenedCharacterFrequency_eq]
  push_cast
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro phase _
  field_simp [Real.pi_ne_zero]

/-- Physical compiled characters and additive-torus Fourier characters
agree pointwise on the canonical all-one clock orbit. -/
theorem characterValue_onePhase_eq_mFourier
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (a : DetectorPhase eqs vars → ℤ)
    (t : ℝ) :
    Clocks.ControllerPhaseProductCharacterCode.characterValue
        (DetectorCharacterCode.flattenCharacter a)
        (CanonicalFixedDetectorTrajectory.clockPath
          parameters controller
          Clocks.LockedControllerPhaseTrajectory.onePhase t) =
      UnitAddTorus.mFourier a
        (detectorPhasePath parameters controller t) := by
  unfold CanonicalFixedDetectorTrajectory.clockPath
  rw [
    Clocks.LockedControllerPhaseTrajectory.characterValue_onePhase,
    mFourier_detectorPhasePath]

/-! ## The right-hand-side character -/

/-- A fundamental equation-coordinate exponent reads exactly the angular
velocity of that equation clock. -/
theorem characterFrequency_equationBasisExponent
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (row : Fin eqs) :
    Clocks.LockedControllerPhaseTrajectory.characterFrequency
        parameters controller
        (FixedDetectorPolynomialCode.equationBasisExponent row) =
      Clocks.LockedControllerPhaseTrajectory.angularVelocity
        parameters controller (finSumFinEquiv (Sum.inr row)) := by
  unfold Clocks.LockedControllerPhaseTrajectory.characterFrequency
    FixedDetectorPolynomialCode.equationBasisExponent
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp

/-- The `-4` inserted by the terminal real oscillator is precisely the
fourth-power flattening of the Fourier right-hand-side character. -/
theorem rhsCharacterFrequency_eq
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ) :
    Clocks.LockedControllerPhaseTrajectory.characterFrequency
        parameters controller
        (DetectorCharacterCode.flattenCharacter
          (DetectorCharacterCode.rhsCharacter I)) =
      -4 *
        CanonicalFixedDetectorTrajectory.rhsFrequency
          parameters I controller := by
  rw [flattenedCharacterFrequency_eq]
  unfold CanonicalFixedDetectorTrajectory.rhsFrequency
  simp_rw [characterFrequency_equationBasisExponent]
  rw [Fintype.sum_sum_type]
  simp only [DetectorCharacterCode.rhsCharacter, Int.cast_zero,
    zero_mul, Finset.sum_const_zero, zero_add, Int.cast_neg,
    neg_mul]
  rw [Finset.sum_neg_distrib]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro row _
  ring

/-- With initial phase `1`, the terminal polynomial oscillator is
literally the Fourier right-hand-side character along the detector
phase orbit. -/
theorem rhsPath_one_eq_mFourier
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ) :
    let rhs :=
      CanonicalFixedDetectorTrajectory.rhsPath
        parameters I controller (1 : Circle) t
    (⟨rhs.c, rhs.d⟩ : ℂ) =
      UnitAddTorus.mFourier
        (DetectorCharacterCode.rhsCharacter I)
        (detectorPhasePath parameters controller t) := by
  rw [mFourier_detectorPhasePath, rhsCharacterFrequency_eq]
  dsimp only
  calc
    (⟨(CanonicalFixedDetectorTrajectory.rhsPath
          parameters I controller (1 : Circle) t).c,
        (CanonicalFixedDetectorTrajectory.rhsPath
          parameters I controller (1 : Circle) t).d⟩ : ℂ) =
        Clocks.PhaseClockFlow.phaseStateComplex
          (CanonicalFixedDetectorTrajectory.rhsPath
            parameters I controller (1 : Circle) t) := by
      apply Complex.ext <;>
        simp [Clocks.PhaseClockFlow.phaseStateComplex]
    _ = Complex.exp
          (((-4 *
              CanonicalFixedDetectorTrajectory.rhsFrequency
                parameters I controller * t : ℝ) : ℂ) *
            Complex.I) := by
      unfold CanonicalFixedDetectorTrajectory.rhsPath
        Clocks.LockedControllerPhaseTrajectory.phasePath
      rw [Clocks.PhaseClockFlow.phaseStateComplex_circlePhaseState]
      simp only [neg_mul,
        Clocks.PhaseClockFlow.phaseRotationFlow_apply,
        Circle.exp_neg, mul_one, Circle.coe_inv, Circle.coe_exp,
        Complex.ofReal_mul, Complex.ofReal_ofNat,
        Complex.ofReal_neg]
      exact (Complex.exp_neg _).symm

/-! ## Poisson reciprocal factors -/

/-- The positive signed Poisson character on the physical clock orbit is
the corresponding detector-torus Fourier character. -/
theorem poissonCharacterPath_positiveIndex_onePhase_eq_mFourier
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ) (j : Fin vars) :
    CanonicalFixedDetectorTrajectory.poissonCharacterPath
        parameters I controller
        Clocks.LockedControllerPhaseTrajectory.onePhase t
        (DetectorPoissonReciprocalCode.positiveIndex j) =
      UnitAddTorus.mFourier
        (DetectorCharacterCode.poissonArgumentCharacter I j)
        (detectorPhasePath parameters controller t) := by
  unfold CanonicalFixedDetectorTrajectory.poissonCharacterPath
  rw [DetectorPoissonReciprocalCode.reciprocalExponent_positiveIndex]
  exact
    characterValue_onePhase_eq_mFourier parameters controller
      (DetectorCharacterCode.poissonArgumentCharacter I j) t

/-- The negative signed Poisson character is the inverse of the positive
character, hence the inverse torus character. -/
theorem poissonCharacterPath_negativeIndex_onePhase_eq_mFourier_inv
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ) (j : Fin vars) :
    CanonicalFixedDetectorTrajectory.poissonCharacterPath
        parameters I controller
        Clocks.LockedControllerPhaseTrajectory.onePhase t
        (DetectorPoissonReciprocalCode.negativeIndex j) =
      (UnitAddTorus.mFourier
        (DetectorCharacterCode.poissonArgumentCharacter I j)
        (detectorPhasePath parameters controller t))⁻¹ := by
  unfold CanonicalFixedDetectorTrajectory.poissonCharacterPath
  rw [DetectorPoissonReciprocalCode.reciprocalExponent_negativeIndex]
  rw [Clocks.ControllerPhaseProductCharacterCode.characterValue_neg_eq_inv]
  · congr 1
    exact
      characterValue_onePhase_eq_mFourier parameters controller
        (DetectorCharacterCode.poissonArgumentCharacter I j) t
  · exact
      Clocks.LockedControllerPhaseTrajectory.stateFamily_onPhaseCircles
        parameters controller
        Clocks.LockedControllerPhaseTrajectory.onePhase t

/-- A detector Poisson series is the generic torus Poisson-kernel series
with base exponent `poissonArgumentCharacter`. -/
theorem tsum_poissonTerm
    {eta : ℝ} (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    (I : DQLSystem eqs vars) (j : Fin vars)
    (phase : UnitAddTorus (DetectorPhase eqs vars)) :
    ∑' s : ℤ,
        DetectorFactorizedFourier.poissonTerm eta I j s phase =
      ((1 - eta ^ 2 : ℝ) : ℂ) /
        ((1 - (eta : ℂ) *
            UnitAddTorus.mFourier
              (DetectorCharacterCode.poissonArgumentCharacter I j)
              phase) *
          (1 - (eta : ℂ) *
            (UnitAddTorus.mFourier
              (DetectorCharacterCode.poissonArgumentCharacter I j)
              phase)⁻¹)) := by
  simpa only [
    DetectorFactorizedFourier.poissonTerm,
    DetectorFactorizedFourier.poissonCoordinateExponent,
    Analysis.torusPoissonFourierTerm] using
      (Analysis.tsum_torusPoissonFourierTerm
        heta0 heta1
        (DetectorCharacterCode.poissonArgumentCharacter I j)
        phase)

/-- The literal product of the two stored reciprocal coordinates and the
factor `3/4 = 1-(1/2)²` is exactly the Poisson Fourier series. -/
theorem canonical_poissonFactor_eq_poissonSeries
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (rhs₀ : Circle)
    (t : ℝ) (j : Fin vars) :
    let state :=
      CanonicalFixedDetectorTrajectory.fixedDetectorPath
        parameters I controller
        Clocks.LockedControllerPhaseTrajectory.onePhase
        (fun _ ↦
          CanonicalFixedDetectorChart.halfPeriodInitialElliptic
            0 thetaGaugeBasePoint)
        (fun _ ↦ thetaGaugeBasePoint) rhs₀ t
    (((3 / 4 : ℝ) : ℂ) *
        state.base.reciprocal
          (DetectorPoissonReciprocalCode.positiveIndex j) *
        state.base.reciprocal
          (DetectorPoissonReciprocalCode.negativeIndex j)) =
      ∑' s : ℤ,
        DetectorFactorizedFourier.poissonTerm
          (1 / 2 : ℝ) I j s
          (detectorPhasePath parameters controller t) := by
  rw [tsum_poissonTerm (by norm_num) (by norm_num)]
  dsimp only [
    CanonicalFixedDetectorTrajectory.fixedDetectorPath,
    CanonicalFixedDetectorTrajectory.poissonSourcePath,
    CanonicalFixedDetectorTrajectory.poissonReciprocalPath]
  rw [
    poissonCharacterPath_positiveIndex_onePhase_eq_mFourier,
    poissonCharacterPath_negativeIndex_onePhase_eq_mFourier_inv]
  rw [div_eq_mul_inv]
  norm_num
  rw [mul_assoc, ← mul_inv_rev]
  congr 2
  all_goals ring

/-! ## Gaussian theta terms -/

/-- The private modular readout is the flattened private-character
frequency. -/
theorem omegaFrequency_eq_characterFrequency
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (j : Fin vars) :
    CanonicalFixedDetectorTrajectory.omegaFrequency
        parameters controller j =
      Clocks.LockedControllerPhaseTrajectory.characterFrequency
        parameters controller
        (DetectorCharacterCode.flattenCharacter
          (DetectorCharacterCode.privateCharacter j)) := by
  unfold CanonicalFixedDetectorTrajectory.omegaFrequency
    DetectorCharacterCode.omegaWeights
    Clocks.ControllerPhaseProductCharacterCode.exponentWeightCode
    Clocks.LockedControllerPhaseTrajectory.characterFrequency
    Clocks.LockedControllerPhaseTrajectory.angularVelocity
  simp only [RationalCode.decode_encode, Rat.cast_intCast]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The linear DQL readout is the flattened linear-character
frequency. -/
theorem numberFrequency_eq_characterFrequency
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (j : Fin vars) :
    CanonicalFixedDetectorTrajectory.numberFrequency
        parameters I controller j =
      Clocks.LockedControllerPhaseTrajectory.characterFrequency
        parameters controller
        (DetectorCharacterCode.flattenCharacter
          (DetectorCharacterCode.linearCharacter I j)) := by
  unfold CanonicalFixedDetectorTrajectory.numberFrequency
    DetectorCharacterCode.numberWeights
    Clocks.ControllerPhaseProductCharacterCode.exponentWeightCode
    Clocks.LockedControllerPhaseTrajectory.characterFrequency
    Clocks.LockedControllerPhaseTrajectory.angularVelocity
  simp only [RationalCode.decode_encode, Rat.cast_intCast]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Frequency of one theta-series term. -/
theorem thetaCoordinateFrequency_eq
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (j : Fin vars) (n : ℤ) :
    Clocks.LockedControllerPhaseTrajectory.characterFrequency
        parameters controller
        (DetectorCharacterCode.flattenCharacter
          (DetectorFactorizedFourier.thetaCoordinateExponent I j n)) =
      (n : ℝ) ^ 2 *
          CanonicalFixedDetectorTrajectory.omegaFrequency
            parameters controller j +
        (n : ℝ) *
          CanonicalFixedDetectorTrajectory.numberFrequency
            parameters I controller j := by
  rw [omegaFrequency_eq_characterFrequency,
    numberFrequency_eq_characterFrequency]
  unfold Clocks.LockedControllerPhaseTrajectory.characterFrequency
    DetectorCharacterCode.flattenCharacter
    DetectorFactorizedFourier.thetaCoordinateExponent
  rw [Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring

/-- The height `log 256 / π` gives exactly the Gaussian coefficient used
by the rational gauge. -/
theorem gaussianWeight_thetaGaugeHeight (n : ℤ) :
    Real.exp
        (-Real.pi * thetaGaugeHeight * (n : ℝ) ^ 2) =
      (1 / 256 : ℝ) ^ (n.natAbs ^ 2) := by
  have hn :
      ((n.natAbs ^ 2 : ℕ) : ℝ) = (n : ℝ) ^ 2 := by
    have hnZ : n ^ 2 = (n.natAbs ^ 2 : ℕ) := by
      rw [Nat.cast_pow, Int.natAbs_sq]
    calc
      ((n.natAbs ^ 2 : ℕ) : ℝ) =
          ((n ^ 2 : ℤ) : ℝ) := by
            simpa only [Int.cast_natCast] using
              congrArg (fun z : ℤ ↦ (z : ℝ)) hnZ.symm
      _ = (n : ℝ) ^ 2 := by push_cast; rfl
  rw [← exp_neg_pi_mul_thetaGaugeHeight]
  rw [← Real.exp_nat_mul]
  congr 1
  rw [hn]
  ring

/-- Each literal Mathlib theta term on the canonical affine path is the
corresponding Gaussian Fourier term of the detector. -/
theorem jacobiTheta₂_term_canonical_eq_thetaTerm
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ) (j : Fin vars) (n : ℤ) :
    jacobiTheta₂_term n
        (CanonicalFixedDetectorChart.centeredEllipticPath 0
          (CanonicalFixedDetectorTrajectory.numberFrequency
            parameters I controller j) t)
        (CanonicalFixedDetectorTrajectory.modularPath
          thetaGaugeBasePoint
          (CanonicalFixedDetectorTrajectory.omegaFrequency
            parameters controller j) t : ℂ) =
      DetectorFactorizedFourier.thetaTerm
        (1 / 256 : ℝ) I j n
        (detectorPhasePath parameters controller t) := by
  let ω :=
    CanonicalFixedDetectorTrajectory.omegaFrequency
      parameters controller j
  let N :=
    CanonicalFixedDetectorTrajectory.numberFrequency
      parameters I controller j
  unfold jacobiTheta₂_term
  rw [show
      2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) *
            CanonicalFixedDetectorChart.centeredEllipticPath 0 N t +
          (Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 *
            (CanonicalFixedDetectorTrajectory.modularPath
              thetaGaugeBasePoint ω t : ℂ) =
        (((-Real.pi * thetaGaugeHeight * (n : ℝ) ^ 2 : ℝ) : ℂ)) +
          ((((((n : ℝ) ^ 2 * ω + (n : ℝ) * N) * t : ℝ) : ℂ)) *
            Complex.I) by
    unfold CanonicalFixedDetectorChart.centeredEllipticPath
      CanonicalFixedDetectorTrajectory.modularPath
      thetaGaugeBasePoint
    push_cast
    field_simp [Real.pi_ne_zero]
    ring_nf
    simp only [Complex.I_sq]
    ring]
  rw [Complex.exp_add, ← Complex.ofReal_exp,
    gaussianWeight_thetaGaugeHeight]
  unfold DetectorFactorizedFourier.thetaTerm
  rw [mFourier_detectorPhasePath,
    thetaCoordinateFrequency_eq]

/-- The complete canonical `θ₃` output is the detector's Gaussian theta
series on the physical arithmetic phase orbit. -/
theorem jacobiTheta3_canonical_eq_thetaSeries
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ) (j : Fin vars) :
    jacobiTheta3
        (CanonicalFixedDetectorChart.centeredEllipticPath 0
          (CanonicalFixedDetectorTrajectory.numberFrequency
            parameters I controller j) t)
        (CanonicalFixedDetectorTrajectory.modularPath
          thetaGaugeBasePoint
          (CanonicalFixedDetectorTrajectory.omegaFrequency
            parameters controller j) t : ℂ) =
      ∑' n : ℤ,
        DetectorFactorizedFourier.thetaTerm
          (1 / 256 : ℝ) I j n
          (detectorPhasePath parameters controller t) := by
  unfold jacobiTheta3 jacobiTheta₂
  apply tsum_congr
  intro n
  exact jacobiTheta₂_term_canonical_eq_thetaTerm
    parameters I controller t j n

/-- The literal polynomial coordinate `G_j T₁,j` equals the normalized
Gaussian theta factor in the detector product. -/
theorem canonical_thetaOutput_eq_thetaSeries
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (rhs₀ : Circle)
    (t : ℝ) (j : Fin vars) :
    let state :=
      CanonicalFixedDetectorTrajectory.fixedDetectorPath
        parameters I controller
        Clocks.LockedControllerPhaseTrajectory.onePhase
        (fun _ ↦
          CanonicalFixedDetectorChart.halfPeriodInitialElliptic
            0 thetaGaugeBasePoint)
        (fun _ ↦ thetaGaugeBasePoint) rhs₀ t
    state.base.base.gauge j *
        (state.base.base.source.linked j).jacobi.T1 =
      ∑' n : ℤ,
        DetectorFactorizedFourier.thetaTerm
          (1 / 256 : ℝ) I j n
          (detectorPhasePath parameters controller t) := by
  calc
    (let state :=
        CanonicalFixedDetectorTrajectory.fixedDetectorPath
          parameters I controller
          Clocks.LockedControllerPhaseTrajectory.onePhase
          (fun _ ↦
            CanonicalFixedDetectorChart.halfPeriodInitialElliptic
              0 thetaGaugeBasePoint)
          (fun _ ↦ thetaGaugeBasePoint) rhs₀ t;
      state.base.base.gauge j *
          (state.base.base.source.linked j).jacobi.T1) =
        jacobiTheta3
          (CanonicalFixedDetectorChart.centeredEllipticPath 0
            (CanonicalFixedDetectorTrajectory.numberFrequency
              parameters I controller j) t)
          (CanonicalFixedDetectorTrajectory.modularPath
            thetaGaugeBasePoint
            (CanonicalFixedDetectorTrajectory.omegaFrequency
              parameters controller j) t : ℂ) :=
      CanonicalFixedDetectorAlignment.canonical_thetaOutput_eq_jacobiTheta3
        parameters I controller rhs₀ t j
    _ = ∑' n : ℤ,
          DetectorFactorizedFourier.thetaTerm
            (1 / 256 : ℝ) I j n
            (detectorPhasePath parameters controller t) :=
      jacobiTheta3_canonical_eq_thetaSeries
        parameters I controller t j

/-! ## The complete detector crosswalk -/

/-- Multiplying the coordinatewise theta and Poisson identities gives the
whole detector product before the terminal right-hand-side oscillator. -/
theorem canonical_detectorProduct_eq_factorizedProduct
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (rhs₀ : Circle)
    (t : ℝ) :
    let state :=
      CanonicalFixedDetectorTrajectory.fixedDetectorPath
        parameters I controller
        Clocks.LockedControllerPhaseTrajectory.onePhase
        (fun _ ↦
          CanonicalFixedDetectorChart.halfPeriodInitialElliptic
            0 thetaGaugeBasePoint)
        (fun _ ↦ thetaGaugeBasePoint) rhs₀ t
    (∏ j : Fin vars,
        ((state.base.base.gauge j *
            (state.base.base.source.linked j).jacobi.T1) *
          (((3 / 4 : ℝ) : ℂ) *
            state.base.reciprocal
              (DetectorPoissonReciprocalCode.positiveIndex j) *
            state.base.reciprocal
              (DetectorPoissonReciprocalCode.negativeIndex j)))) =
      (∏ j : Fin vars,
        ∑' n : ℤ,
          DetectorFactorizedFourier.thetaTerm
            (1 / 256 : ℝ) I j n
            (detectorPhasePath parameters controller t)) *
      (∏ j : Fin vars,
        ∑' s : ℤ,
          DetectorFactorizedFourier.poissonTerm
            (1 / 2 : ℝ) I j s
            (detectorPhasePath parameters controller t)) := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [
    canonical_thetaOutput_eq_thetaSeries,
    canonical_poissonFactor_eq_poissonSeries]

/-- **Literal polynomial/Fourier detector identity.**

Along the canonical all-one physical orbit, evaluation of the compiled
polynomial pair is exactly the normalization-matched factorized Fourier
detector.  This theorem includes every otherwise delicate constant:
the fourth-power clock convention, `λ = 1/256`, `η = 1/2`, the Poisson
factor `3/4`, and the RHS oscillator's factor `-4`. -/
theorem evalPair_detectorCode_canonical_eq_factorizedDetector
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ) :
    let state :=
      CanonicalFixedDetectorTrajectory.fixedDetectorPath
        parameters I controller
        Clocks.LockedControllerPhaseTrajectory.onePhase
        (fun _ ↦
          CanonicalFixedDetectorChart.halfPeriodInitialElliptic
            0 thetaGaugeBasePoint)
        (fun _ ↦ thetaGaugeBasePoint) (1 : Circle) t
    Clocks.ControllerPhaseProductCharacterCode.evalPair
        (FixedDetectorPolynomialCode.detectorCode
          (eqs := eqs) (vars := vars))
        (FixedDetectorPolynomialCode.point state) =
      DetectorFactorizedFourier.factorizedDetector
        (1 / 256 : ℝ) (1 / 2 : ℝ) I
        (detectorPhasePath parameters controller t) := by
  dsimp only
  rw [FixedDetectorPolynomialCode.evalPair_detectorCode]
  change
    (⟨(CanonicalFixedDetectorTrajectory.rhsPath
          parameters I controller (1 : Circle) t).c,
        (CanonicalFixedDetectorTrajectory.rhsPath
          parameters I controller (1 : Circle) t).d⟩ : ℂ) *
        _ =
      _
  rw [rhsPath_one_eq_mFourier]
  unfold DetectorFactorizedFourier.factorizedDetector
  rw [mul_assoc]
  congr 1
  exact
    canonical_detectorProduct_eq_factorizedProduct
      parameters I controller (1 : Circle) t

/-- Final analytic form: the compiled polynomial detector is the absolutely
convergent expanded detector whose Haar constant term encodes DQL
solvability. -/
theorem evalPair_detectorCode_canonical_eq_expandedDetector
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ) :
    let state :=
      CanonicalFixedDetectorTrajectory.fixedDetectorPath
        parameters I controller
        Clocks.LockedControllerPhaseTrajectory.onePhase
        (fun _ ↦
          CanonicalFixedDetectorChart.halfPeriodInitialElliptic
            0 thetaGaugeBasePoint)
        (fun _ ↦ thetaGaugeBasePoint) (1 : Circle) t
    Clocks.ControllerPhaseProductCharacterCode.evalPair
        (FixedDetectorPolynomialCode.detectorCode
          (eqs := eqs) (vars := vars))
        (FixedDetectorPolynomialCode.point state) =
      expandedDetector
        (1 / 256 : ℝ) (1 / 2 : ℝ) I
        (detectorPhasePath parameters controller t) := by
  dsimp only
  rw [evalPair_detectorCode_canonical_eq_factorizedDetector]
  exact
    DetectorFactorizedFourier.factorizedDetector_eq_expandedDetector
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      I (detectorPhasePath parameters controller t)

end HGAS.CanonicalFixedDetectorFourierCrosswalk
