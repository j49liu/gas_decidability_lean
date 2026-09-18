import HGAS.Analysis.CanonicalSelectorMomentAggregatedFamilies
import HGAS.Analysis.CenteredTorusFourierOperations
import HGAS.Arithmetic.CanonicalFixedDetectorFundamentalPhase
import HGAS.Arithmetic.CorrectedFixedDetectorMomentCode
import Mathlib.Tactic

/-!
# Fourier crosswalk for all corrected canonical selector moments

This module identifies the seven complex selector coordinates of the
corrected compiler with the seven centered Fourier families developed in
`CanonicalSelectorMomentAggregatedFamilies`.

The path is the completely explicit chart-safe detector orbit:

* every controller phase starts at one;
* every elliptic parameter starts at the canonical half period;
* every modular parameter starts at height `log 256 / π`; and
* the terminal right-hand-side phase starts at one.

Fourier characters are evaluated on the *fundamental* compiler clocks,
not on an informally rescaled torus.  The preceding fundamental-phase
module proves the exact fourth-power conversion.
-/

noncomputable section

open scoped BigOperators

namespace HGAS.CorrectedCanonicalFixedDetectorMomentFourierCrosswalk

open HGAS
open HGAS.Analysis
open HGAS.Analysis.CanonicalSelectorMomentAggregatedFamilies
open HGAS.Clocks
open HGAS.Clocks.ControllerPhaseProductCharacterCode
open HGAS.Modular

variable {eqs vars : ℕ}

/-- The completely canonical detector state used in the no-instance
graph. -/
def canonicalState
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ) :
    FixedDetectorPolynomialCode.State eqs vars :=
  CanonicalFixedDetectorTrajectory.fixedDetectorPath
    parameters I controller
    LockedControllerPhaseTrajectory.onePhase
    (fun _ ↦
      CanonicalFixedDetectorChart.halfPeriodInitialElliptic
        0 thetaGaugeBasePoint)
    (fun _ ↦ thetaGaugeBasePoint)
    (1 : Circle) t

/-- Short name for the literal compiler-clock phase. -/
abbrev phase
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ) :
    UnitAddTorus (Fin (vars + eqs)) :=
  CanonicalFixedDetectorFundamentalPhase.fundamentalPhasePath
    parameters controller t

private def harmlessRadicand :
    Fin (vars + eqs) → ℕ :=
  fun _ ↦ 2

private theorem thetaCoefficient_summable
    (I : DQLSystem eqs vars) (j : Fin vars) :
    Summable fun n : ℤ ↦
      ‖CanonicalSelectorMomentZeroModes.thetaCoefficient n‖ := by
  simpa using
    (Analysis.CanonicalSelectorMomentRadicalSummability.summable_unaryExponent
      harmlessRadicand I j 0)

private theorem flatten_centeredFourierExponent
    {ι : Type*}
    (exponent : ι → DetectorPhase eqs vars → ℤ) :
    (fun i ↦ DetectorCharacterCode.flattenCharacter
      (centeredFourierExponent exponent i)) =
      centeredFourierExponent
        (fun i ↦ DetectorCharacterCode.flattenCharacter (exponent i)) := by
  funext i k
  cases i with
  | inl u =>
      simp [centeredFourierExponent,
        DetectorCharacterCode.flattenCharacter]
  | inr i =>
      rfl

private theorem unaryMean_flatExponent
    (I : DQLSystem eqs vars) (j : Fin vars) :
    (unaryMean I j).flatExponent =
      centeredFourierExponent
        (fun n ↦ DetectorCharacterCode.flattenCharacter
          (CanonicalSelectorMomentZeroModes.unaryExponent
            (eqs := eqs) j n)) := by
  exact flatten_centeredFourierExponent
    (CanonicalSelectorMomentZeroModes.unaryExponent
      (eqs := eqs) j)

private theorem unaryFirst_flatExponent
    (I : DQLSystem eqs vars) (j : Fin vars) :
    (unaryFirst I j).flatExponent =
      centeredFourierExponent
        (fun n ↦ DetectorCharacterCode.flattenCharacter
          (CanonicalSelectorMomentZeroModes.unaryFirstExponent
            (eqs := eqs) j n)) := by
  exact flatten_centeredFourierExponent
    (CanonicalSelectorMomentZeroModes.unaryFirstExponent
      (eqs := eqs) j)

private theorem jacobiMean_flatExponent
    (I : DQLSystem eqs vars) (j : Fin vars) :
    (jacobiMean I j).flatExponent =
      centeredFourierExponent
        (fun n ↦ DetectorCharacterCode.flattenCharacter
          (CanonicalSelectorMomentZeroModes.jacobiMeanExponent I j n)) := by
  exact flatten_centeredFourierExponent
    (CanonicalSelectorMomentZeroModes.jacobiMeanExponent I j)

private theorem rootP4_flatExponent
    (j : Fin vars) :
    (rootP4 (eqs := eqs) j).flatExponent =
      centeredFourierExponent
        (fun nm ↦ DetectorCharacterCode.flattenCharacter
          (CanonicalSelectorMomentZeroModes.rootP4Exponent
            (eqs := eqs) j nm)) := by
  exact flatten_centeredFourierExponent
    (CanonicalSelectorMomentZeroModes.rootP4Exponent
      (eqs := eqs) j)

private theorem rootP2_flatExponent
    (j : Fin vars) :
    (rootP2 (eqs := eqs) j).flatExponent =
      centeredFourierExponent
        (fun nm ↦ DetectorCharacterCode.flattenCharacter
          (CanonicalSelectorMomentZeroModes.rootP2Exponent
            (eqs := eqs) j nm)) := by
  exact flatten_centeredFourierExponent
    (CanonicalSelectorMomentZeroModes.rootP2Exponent
      (eqs := eqs) j)

private theorem jacobiPlus_coefficient
    (I : DQLSystem eqs vars) (j : Fin vars) :
    (jacobiPlus I j).coefficient =
      centeredFourierCoefficient
        (((CorrectedJacobiSelectorCentering.selectorCenter I j : ℚ) : ℂ))
        CanonicalSelectorMomentZeroModes.thetaCoefficient := by
  funext i
  cases i <;>
    rfl

private theorem jacobiPlus_flatExponent
    (I : DQLSystem eqs vars) (j : Fin vars) :
    (jacobiPlus I j).flatExponent =
      centeredFourierExponent
        (fun n ↦ DetectorCharacterCode.flattenCharacter
          (CorrectedJacobiSelectorCentering.plusExponent I j n)) := by
  funext i k
  cases i with
  | inl u =>
      simp [RawCenteredFamily.flatExponent, jacobiPlus,
        CorrectedJacobiSelectorCentering.centeredPlusExponent,
        centeredFourierExponent,
        DetectorCharacterCode.flattenCharacter]
  | inr n =>
      rfl

private theorem jacobiMinus_coefficient
    (I : DQLSystem eqs vars) (j : Fin vars) :
    (jacobiMinus I j).coefficient =
      centeredFourierCoefficient
        (((CorrectedJacobiSelectorCentering.selectorCenter I j : ℚ) : ℂ))
        CanonicalSelectorMomentZeroModes.thetaCoefficient := by
  funext i
  cases i <;>
    rfl

private theorem jacobiMinus_flatExponent
    (I : DQLSystem eqs vars) (j : Fin vars) :
    (jacobiMinus I j).flatExponent =
      centeredFourierExponent
        (fun n ↦ DetectorCharacterCode.flattenCharacter
          (CorrectedJacobiSelectorCentering.minusExponent I j n)) := by
  funext i k
  cases i with
  | inl u =>
      simp [RawCenteredFamily.flatExponent, jacobiMinus,
        CorrectedJacobiSelectorCentering.centeredMinusExponent,
        centeredFourierExponent,
        DetectorCharacterCode.flattenCharacter]
  | inr n =>
      rfl

/-! ## Unary `θ₃` moments -/

private theorem unaryFrequency_eq
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (j : Fin vars) (n : ℤ) :
    LockedControllerPhaseTrajectory.characterFrequency
        parameters controller
        (DetectorCharacterCode.flattenCharacter
          (CanonicalSelectorMomentZeroModes.unaryExponent
            (eqs := eqs) j n)) =
      (n : ℝ) ^ 2 *
        CanonicalFixedDetectorTrajectory.omegaFrequency
          parameters controller j := by
  rw [
    CanonicalFixedDetectorFourierCrosswalk.omegaFrequency_eq_characterFrequency]
  unfold LockedControllerPhaseTrajectory.characterFrequency
    DetectorCharacterCode.flattenCharacter
    CanonicalSelectorMomentZeroModes.unaryExponent
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring

/-- One `θ₃` summand is exactly the corresponding Gaussian Fourier
summand on the fundamental compiler clocks. -/
theorem theta3Term_canonical_eq_unaryTerm
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ) (j : Fin vars) (n : ℤ) :
    theta₃Term n
        (CanonicalFixedDetectorTrajectory.modularPath
          thetaGaugeBasePoint
          (CanonicalFixedDetectorTrajectory.omegaFrequency
            parameters controller j) t) =
      torusSeriesTerm
        CanonicalSelectorMomentZeroModes.thetaCoefficient
        (fun k ↦ DetectorCharacterCode.flattenCharacter
          (CanonicalSelectorMomentZeroModes.unaryExponent
            (eqs := eqs) j k))
        n (phase parameters controller t) := by
  let omega :=
    CanonicalFixedDetectorTrajectory.omegaFrequency
      parameters controller j
  unfold theta₃Term torusSeriesTerm
  rw [
    CanonicalFixedDetectorFundamentalPhase.mFourier_flattenCharacter_fundamentalPhasePath,
    CanonicalFixedDetectorFourierCrosswalk.mFourier_detectorPhasePath,
    unaryFrequency_eq]
  rw [show
      (Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 *
          (CanonicalFixedDetectorTrajectory.modularPath
            thetaGaugeBasePoint omega t : ℂ) =
        (((-Real.pi * thetaGaugeHeight * (n : ℝ) ^ 2 : ℝ) : ℂ)) +
          (((((n : ℝ) ^ 2 * omega * t : ℝ) : ℂ)) *
            Complex.I) by
    unfold CanonicalFixedDetectorTrajectory.modularPath
      thetaGaugeBasePoint
    push_cast
    field_simp [Real.pi_ne_zero]
    ring_nf
    simp only [Complex.I_sq]
    ring]
  rw [Complex.exp_add, ← Complex.ofReal_exp,
    CanonicalFixedDetectorFourierCrosswalk.gaussianWeight_thetaGaugeHeight]
  unfold CanonicalSelectorMomentZeroModes.thetaCoefficient
    CorrectedJacobiSelectorCentering.thetaCoefficient
  ring

/-- The unary coordinate `Y` is its Gaussian Fourier series. -/
theorem canonical_unaryY_eq_series
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ) (j : Fin vars) :
    ((canonicalState parameters I controller t).base.base.source.linked
        j).unary.Y =
      torusFourierSeries
        CanonicalSelectorMomentZeroModes.thetaCoefficient
        (fun n ↦ DetectorCharacterCode.flattenCharacter
          (CanonicalSelectorMomentZeroModes.unaryExponent
            (eqs := eqs) j n))
        (phase parameters controller t) := by
  change
    theta₃
        (CanonicalFixedDetectorTrajectory.modularPath
          thetaGaugeBasePoint
          (CanonicalFixedDetectorTrajectory.omegaFrequency
            parameters controller j) t) =
      _
  unfold theta₃ torusFourierSeries
  apply tsum_congr
  intro n
  exact theta3Term_canonical_eq_unaryTerm
    parameters controller t j n

/-- Corrected moment 0: `Y - 1`. -/
theorem localMomentValue_zero_eq_unaryMean_series
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ) (j : Fin vars) :
    CorrectedFixedDetectorMomentCode.localMomentValue
        I j (canonicalState parameters I controller t) 0 =
      torusFourierSeries
        (unaryMean I j).coefficient
        (unaryMean I j).flatExponent
        (phase parameters controller t) := by
  change
    ((canonicalState parameters I controller t).base.base.source.linked
        j).unary.Y - 1 = _
  rw [canonical_unaryY_eq_series]
  symm
  rw [unaryMean_flatExponent]
  simpa [unaryMean] using
    (torusFourierSeries_centered
      1 CanonicalSelectorMomentZeroModes.thetaCoefficient
      (fun n ↦ DetectorCharacterCode.flattenCharacter
        (CanonicalSelectorMomentZeroModes.unaryExponent
          (eqs := eqs) j n))
      (thetaCoefficient_summable I j)
      (phase parameters controller t))

private theorem unaryFirst_character_eq
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ) (j : Fin vars) :
    characterValue
        (FixedDetectorMomentCode.unaryFirstHarmonicExponent j)
        (canonicalState parameters I controller t).base.base.source.controllers =
      UnitAddTorus.mFourier
        (DetectorCharacterCode.flattenCharacter
          (fun phase ↦
            -DetectorCharacterCode.privateCharacter j phase))
        (phase parameters controller t) := by
  rw [show
      (canonicalState parameters I controller t).base.base.source.controllers =
        CanonicalFixedDetectorTrajectory.clockPath
          parameters controller
          LockedControllerPhaseTrajectory.onePhase t from rfl]
  rw [show
      FixedDetectorMomentCode.unaryFirstHarmonicExponent j =
        DetectorCharacterCode.flattenCharacter
          (fun phase ↦
            -DetectorCharacterCode.privateCharacter j phase) by
    funext i
    simp [FixedDetectorMomentCode.unaryFirstHarmonicExponent,
      FixedDetectorMomentCode.privateExponent,
      DetectorCharacterCode.flattenCharacter]]
  rw [
    CanonicalFixedDetectorFourierCrosswalk.characterValue_onePhase_eq_mFourier]
  exact
    (CanonicalFixedDetectorFundamentalPhase.mFourier_flattenCharacter_fundamentalPhasePath
      parameters controller _ t).symm

private theorem flatUnaryFirstExponent_eq_add
    (j : Fin vars) (n : ℤ) :
    DetectorCharacterCode.flattenCharacter
        (CanonicalSelectorMomentZeroModes.unaryFirstExponent
          (eqs := eqs) j n) =
      DetectorCharacterCode.flattenCharacter
          (CanonicalSelectorMomentZeroModes.unaryExponent
            (eqs := eqs) j n) +
        DetectorCharacterCode.flattenCharacter
          (fun phase ↦
            -DetectorCharacterCode.privateCharacter j phase) := by
  funext i
  simp [DetectorCharacterCode.flattenCharacter,
    CanonicalSelectorMomentZeroModes.unaryFirstExponent,
    CanonicalSelectorMomentZeroModes.unaryExponent]
  ring

/-- Corrected moment 1: `Y Q⁻¹ - 1/128`. -/
theorem localMomentValue_one_eq_unaryFirst_series
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ) (j : Fin vars) :
    CorrectedFixedDetectorMomentCode.localMomentValue
        I j (canonicalState parameters I controller t) 1 =
      torusFourierSeries
        (unaryFirst I j).coefficient
        (unaryFirst I j).flatExponent
        (phase parameters controller t) := by
  change
    ((canonicalState parameters I controller t).base.base.source.linked
        j).unary.Y *
          characterValue
            (FixedDetectorMomentCode.unaryFirstHarmonicExponent j)
            (canonicalState parameters I controller t).base.base.source.controllers -
        (1 / 128 : ℚ) = _
  rw [canonical_unaryY_eq_series, unaryFirst_character_eq]
  rw [torusFourierSeries_mul_mFourier]
  rw [show
      (fun n ↦
        DetectorCharacterCode.flattenCharacter
            (CanonicalSelectorMomentZeroModes.unaryExponent
              (eqs := eqs) j n) +
          DetectorCharacterCode.flattenCharacter
            (fun phase ↦
              -DetectorCharacterCode.privateCharacter j phase)) =
        fun n ↦ DetectorCharacterCode.flattenCharacter
          (CanonicalSelectorMomentZeroModes.unaryFirstExponent
            (eqs := eqs) j n) by
    funext n
    exact (flatUnaryFirstExponent_eq_add j n).symm]
  symm
  rw [unaryFirst_flatExponent]
  simpa [unaryFirst] using
    (torusFourierSeries_centered
      (((1 / 128 : ℝ) : ℂ))
      CanonicalSelectorMomentZeroModes.thetaCoefficient
      (fun n ↦ DetectorCharacterCode.flattenCharacter
        (CanonicalSelectorMomentZeroModes.unaryFirstExponent
          (eqs := eqs) j n))
      (thetaCoefficient_summable I j)
      (phase parameters controller t))

/-! ## The `θ₄²` root moment -/

private def theta4Coefficient (n : ℤ) : ℂ :=
  (-1 : ℂ) ^ n.natAbs *
    CanonicalSelectorMomentZeroModes.thetaCoefficient n

private theorem neg_one_zpow_eq_natAbs_pow (n : ℤ) :
    (-1 : ℂ) ^ n = (-1 : ℂ) ^ n.natAbs := by
  cases n with
  | ofNat n => rfl
  | negSucc n =>
      change ((-1 : ℂ) ^ (n + 1))⁻¹ = (-1 : ℂ) ^ (n + 1)
      rw [← inv_pow]
      norm_num

private theorem theta4Coefficient_summable
    (I : DQLSystem eqs vars) (j : Fin vars) :
    Summable fun n : ℤ ↦ ‖theta4Coefficient n‖ := by
  apply (thetaCoefficient_summable I j).congr
  intro n
  simp [theta4Coefficient]

/-- One `θ₄` term differs from the corresponding `θ₃` term only by its
parity sign. -/
theorem theta4Term_canonical_eq_term
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ) (j : Fin vars) (n : ℤ) :
    theta₄Term n
        (CanonicalFixedDetectorTrajectory.modularPath
          thetaGaugeBasePoint
          (CanonicalFixedDetectorTrajectory.omegaFrequency
            parameters controller j) t) =
      torusSeriesTerm theta4Coefficient
        (fun k ↦ DetectorCharacterCode.flattenCharacter
          (CanonicalSelectorMomentZeroModes.unaryExponent
            (eqs := eqs) j k))
        n (phase parameters controller t) := by
  have hthree :=
    theta3Term_canonical_eq_unaryTerm
      parameters controller t j n
  unfold theta₃Term torusSeriesTerm at hthree
  unfold theta₄Term torusSeriesTerm theta4Coefficient
  rw [neg_one_zpow_eq_natAbs_pow]
  rw [hthree]
  ring

private theorem canonical_theta4_eq_series
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ) (j : Fin vars) :
    theta₄
        (CanonicalFixedDetectorTrajectory.modularPath
          thetaGaugeBasePoint
          (CanonicalFixedDetectorTrajectory.omegaFrequency
            parameters controller j) t) =
      torusFourierSeries theta4Coefficient
        (fun n ↦ DetectorCharacterCode.flattenCharacter
          (CanonicalSelectorMomentZeroModes.unaryExponent
            (eqs := eqs) j n))
        (phase parameters controller t) := by
  unfold theta₄ torusFourierSeries
  apply tsum_congr
  intro n
  exact theta4Term_canonical_eq_term
    parameters controller t j n

private theorem theta4Coefficient_product
    (nm : ℤ × ℤ) :
    theta4Coefficient nm.1 * theta4Coefficient nm.2 =
      CanonicalSelectorMomentZeroModes.rootP4Coefficient nm := by
  unfold theta4Coefficient
    CanonicalSelectorMomentZeroModes.rootP4Coefficient
  rw [pow_add]
  ring

private theorem flatRootP4Exponent_eq_add
    (j : Fin vars) (nm : ℤ × ℤ) :
    DetectorCharacterCode.flattenCharacter
        (CanonicalSelectorMomentZeroModes.rootP4Exponent
          (eqs := eqs) j nm) =
      DetectorCharacterCode.flattenCharacter
          (CanonicalSelectorMomentZeroModes.unaryExponent
            (eqs := eqs) j nm.1) +
        DetectorCharacterCode.flattenCharacter
          (CanonicalSelectorMomentZeroModes.unaryExponent
            (eqs := eqs) j nm.2) := by
  funext i
  simp [DetectorCharacterCode.flattenCharacter,
    CanonicalSelectorMomentZeroModes.rootP4Exponent,
    CanonicalSelectorMomentZeroModes.unaryExponent]
  ring

/-- The stored root `p₄ = θ₄²` is the raw double Fourier series. -/
theorem canonical_rootP4_eq_raw_series
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ) (j : Fin vars) :
    ((canonicalState parameters I controller t).base.base.source.linked
        j).jacobi.p4 =
      torusFourierSeries
        CanonicalSelectorMomentZeroModes.rootP4Coefficient
        (fun nm ↦ DetectorCharacterCode.flattenCharacter
          (CanonicalSelectorMomentZeroModes.rootP4Exponent
            (eqs := eqs) j nm))
        (phase parameters controller t) := by
  change
    theta₄
          (CanonicalFixedDetectorTrajectory.modularPath
            thetaGaugeBasePoint
            (CanonicalFixedDetectorTrajectory.omegaFrequency
              parameters controller j) t) ^ 2 =
      _
  rw [canonical_theta4_eq_series parameters controller t j]
  rw [torusFourierSeries_sq
    theta4Coefficient
    (fun n ↦ DetectorCharacterCode.flattenCharacter
      (CanonicalSelectorMomentZeroModes.unaryExponent
        (eqs := eqs) j n))
    (theta4Coefficient_summable I j)
    (phase parameters controller t)]
  congr 1
  · funext nm
    exact theta4Coefficient_product nm
  · funext nm
    exact (flatRootP4Exponent_eq_add j nm).symm

/-- Corrected moment 2: `p₄ - 1`. -/
theorem localMomentValue_two_eq_rootP4_series
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ) (j : Fin vars) :
    CorrectedFixedDetectorMomentCode.localMomentValue
        I j (canonicalState parameters I controller t) 2 =
      torusFourierSeries
        (rootP4 (eqs := eqs) j).coefficient
        (rootP4 (eqs := eqs) j).flatExponent
        (phase parameters controller t) := by
  change
    ((canonicalState parameters I controller t).base.base.source.linked
        j).jacobi.p4 - 1 = _
  rw [canonical_rootP4_eq_raw_series]
  symm
  rw [rootP4_flatExponent]
  simpa [rootP4] using
    (torusFourierSeries_centered
      1 CanonicalSelectorMomentZeroModes.rootP4Coefficient
      (fun nm ↦ DetectorCharacterCode.flattenCharacter
        (CanonicalSelectorMomentZeroModes.rootP4Exponent
          (eqs := eqs) j nm))
      (by
        simpa using
          (Analysis.CanonicalSelectorMomentRadicalSummability.summable_rootP4Exponent
            (eqs := eqs) (vars := vars)
            (harmlessRadicand (eqs := eqs) (vars := vars)) j 0))
      (phase parameters controller t))

/-! ## The `θ₂² ζ⁻²` root moment -/

/-- Exponent of one `θ₂` term in the literal fundamental private clock.
It is the odd square `(2n+1)²`, before the later `ζ⁻²` twist. -/
private def theta2FundamentalExponent
    (j : Fin vars) (n : ℤ) :
    Fin (vars + eqs) → ℤ :=
  fun i ↦
    CanonicalSelectorMomentZeroModes.oddSquare n *
      match finSumFinEquiv.symm i with
      | Sum.inl k => if k = j then 1 else 0
      | Sum.inr _ => 0

private def theta2Coefficient (n : ℤ) : ℂ :=
  (((1 / 4 : ℝ) ^
    ((2 * n + 1).natAbs ^ 2) : ℝ) : ℂ)

private theorem natAbs_le_oddSquare (n : ℤ) :
    n.natAbs ≤ (2 * n + 1).natAbs ^ 2 := by
  cases n with
  | ofNat k =>
      change
        k ≤ (2 * (Int.ofNat k) + 1).natAbs ^ 2
      have heq :
          2 * (Int.ofNat k) + 1 =
            Int.ofNat (2 * k + 1) := by norm_num
      have habs :
          (2 * (Int.ofNat k) + 1).natAbs =
            2 * k + 1 := by
        rw [heq]
        rfl
      rw [habs]
      nlinarith
  | negSucc k =>
      have heq :
          2 * Int.negSucc k + 1 =
            Int.negSucc (2 * k) := by omega
      rw [heq]
      simp
      nlinarith

private theorem theta2Coefficient_summable :
    Summable fun n : ℤ ↦ ‖theta2Coefficient n‖ := by
  have h :=
    Analysis.summable_intDecay_mul_height_pow_of_polynomial_bound
      (q := (1 / 4 : ℝ)) (C := 1)
      (by norm_num) (by norm_num)
      (fun n : ℤ ↦ (2 * n + 1).natAbs ^ 2)
      natAbs_le_oddSquare 0 0
      (fun _ : ℤ ↦ (1 : ℝ))
      (fun _ ↦ by norm_num)
      (fun _ ↦ by norm_num)
  simpa [theta2Coefficient] using h

private theorem omegaFrequency_eq_four_mul_privateAngularVelocity
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (j : Fin vars) :
    CanonicalFixedDetectorTrajectory.omegaFrequency
        parameters controller j =
      4 *
        LockedControllerPhaseTrajectory.angularVelocity
          parameters controller (finSumFinEquiv (Sum.inl j)) := by
  rw [
    CanonicalFixedDetectorFourierCrosswalk.omegaFrequency_eq_characterFrequency]
  unfold LockedControllerPhaseTrajectory.characterFrequency
    DetectorCharacterCode.flattenCharacter
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp [DetectorCharacterCode.privateCharacter]

private theorem theta2FrequencyPairing
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (j : Fin vars) (n : ℤ) :
    RadicalClock.frequencyPairing
        (theta2FundamentalExponent (eqs := eqs) j n)
        (CanonicalFixedDetectorFundamentalPhase.turnsFrequency
          parameters controller) =
      (CanonicalSelectorMomentZeroModes.oddSquare n : ℝ) *
          LockedControllerPhaseTrajectory.angularVelocity
            parameters controller (finSumFinEquiv (Sum.inl j)) /
        (2 * Real.pi) := by
  unfold RadicalClock.frequencyPairing theta2FundamentalExponent
    CanonicalFixedDetectorFundamentalPhase.turnsFrequency
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp
  ring

private theorem theta2GaussianWeight (n : ℤ) :
    Real.exp
        ((-Real.pi * thetaGaugeHeight / 4) *
          ((2 * n + 1 : ℤ) : ℝ) ^ 2) =
      (1 / 4 : ℝ) ^ ((2 * n + 1).natAbs ^ 2) := by
  have hn :
      ((((2 * n + 1).natAbs ^ 2 : ℕ) : ℝ)) =
        ((2 * n + 1 : ℤ) : ℝ) ^ 2 := by
    have hnZ :
        (2 * n + 1 : ℤ) ^ 2 =
          ((2 * n + 1).natAbs ^ 2 : ℕ) := by
      rw [Nat.cast_pow, Int.natAbs_sq]
    calc
      ((((2 * n + 1).natAbs ^ 2 : ℕ) : ℝ)) =
          ((((2 * n + 1 : ℤ) ^ 2 : ℤ) : ℝ)) := by
            simpa only [Int.cast_natCast] using
              congrArg (fun z : ℤ ↦ (z : ℝ)) hnZ.symm
      _ = ((2 * n + 1 : ℤ) : ℝ) ^ 2 := by
        push_cast
        rfl
  rw [← exp_neg_pi_mul_thetaGaugeHeight_div_four]
  rw [← Real.exp_nat_mul]
  congr 1
  rw [hn]
  ring

/-- One `θ₂` term is a Fourier term in the odd fundamental private
harmonic. -/
theorem theta2Term_canonical_eq_term
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ) (j : Fin vars) (n : ℤ) :
    theta₂Term n
        (CanonicalFixedDetectorTrajectory.modularPath
          thetaGaugeBasePoint
          (CanonicalFixedDetectorTrajectory.omegaFrequency
            parameters controller j) t) =
      torusSeriesTerm theta2Coefficient
        (theta2FundamentalExponent (eqs := eqs) j)
        n (phase parameters controller t) := by
  let angular :=
    LockedControllerPhaseTrajectory.angularVelocity
      parameters controller (finSumFinEquiv (Sum.inl j))
  unfold theta₂Term torusSeriesTerm
  unfold phase
    CanonicalFixedDetectorFundamentalPhase.fundamentalPhasePath
  rw [RadicalClock.mFourier_torusDisplacement,
    theta2FrequencyPairing]
  rw [omegaFrequency_eq_four_mul_privateAngularVelocity]
  rw [show
      (Real.pi : ℂ) * Complex.I *
          ((n : ℂ) + 1 / 2) ^ 2 *
          (CanonicalFixedDetectorTrajectory.modularPath
            thetaGaugeBasePoint (4 * angular) t : ℂ) =
        ((((-Real.pi * thetaGaugeHeight / 4) *
          ((2 * n + 1 : ℤ) : ℝ) ^ 2 : ℝ) : ℂ)) +
          2 * (Real.pi : ℂ) * Complex.I *
            (((t *
              ((CanonicalSelectorMomentZeroModes.oddSquare n : ℝ) *
                angular / (2 * Real.pi)) : ℝ) : ℂ)) by
    unfold CanonicalFixedDetectorTrajectory.modularPath
      thetaGaugeBasePoint
      CanonicalSelectorMomentZeroModes.oddSquare
    push_cast
    field_simp [Real.pi_ne_zero]
    ring_nf
    simp only [Complex.I_sq]
    ring]
  rw [Complex.exp_add, ← Complex.ofReal_exp, theta2GaussianWeight]
  unfold theta2Coefficient
  congr 1
  push_cast
  ring

private theorem canonical_theta2_eq_series
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ) (j : Fin vars) :
    theta₂
        (CanonicalFixedDetectorTrajectory.modularPath
          thetaGaugeBasePoint
          (CanonicalFixedDetectorTrajectory.omegaFrequency
            parameters controller j) t) =
      torusFourierSeries theta2Coefficient
        (theta2FundamentalExponent (eqs := eqs) j)
        (phase parameters controller t) := by
  unfold theta₂ torusFourierSeries
  apply tsum_congr
  intro n
  exact theta2Term_canonical_eq_term
    parameters controller t j n

private theorem theta2Coefficient_product
    (nm : ℤ × ℤ) :
    theta2Coefficient nm.1 * theta2Coefficient nm.2 =
      CanonicalSelectorMomentZeroModes.rootP2Coefficient nm := by
  unfold theta2Coefficient
    CanonicalSelectorMomentZeroModes.rootP2Coefficient
  rw [← Complex.ofReal_mul]
  congr 1
  rw [← pow_add]

private theorem rootHalfExponent_eq_privateTwist
    (j : Fin vars) :
    FixedDetectorMomentCode.rootHalfExponent (eqs := eqs) j =
      fun i ↦
        -2 *
          match finSumFinEquiv.symm i with
          | Sum.inl k => if k = j then (1 : ℤ) else 0
          | Sum.inr _ => (0 : ℤ) := by
  funext i
  cases h : finSumFinEquiv.symm i with
  | inl k =>
      by_cases hkj : k = j
      · simp [FixedDetectorMomentCode.rootHalfExponent, h, hkj]
      · simp [FixedDetectorMomentCode.rootHalfExponent, h, hkj]
  | inr e =>
      simp [FixedDetectorMomentCode.rootHalfExponent, h]

private theorem flatRootP2Exponent_eq_sum_add_twist
    (j : Fin vars) (nm : ℤ × ℤ) :
    DetectorCharacterCode.flattenCharacter
        (CanonicalSelectorMomentZeroModes.rootP2Exponent
          (eqs := eqs) j nm) =
      theta2FundamentalExponent (eqs := eqs) j nm.1 +
        theta2FundamentalExponent (eqs := eqs) j nm.2 +
          FixedDetectorMomentCode.rootHalfExponent (eqs := eqs) j := by
  funext i
  rw [rootHalfExponent_eq_privateTwist]
  simp [DetectorCharacterCode.flattenCharacter,
    CanonicalSelectorMomentZeroModes.rootP2Exponent,
    CanonicalSelectorMomentZeroModes.consecutiveProduct,
    theta2FundamentalExponent,
    CanonicalSelectorMomentZeroModes.oddSquare,
    DetectorCharacterCode.privateCharacter]
  ring_nf
  rfl

private theorem rootHalf_character_eq
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ) (j : Fin vars) :
    characterValue
        (FixedDetectorMomentCode.rootHalfExponent (eqs := eqs) j)
        (canonicalState parameters I controller t).base.base.source.controllers =
      UnitAddTorus.mFourier
        (FixedDetectorMomentCode.rootHalfExponent (eqs := eqs) j)
        (phase parameters controller t) := by
  rw [show
      (canonicalState parameters I controller t).base.base.source.controllers =
        CanonicalFixedDetectorTrajectory.clockPath
          parameters controller
          LockedControllerPhaseTrajectory.onePhase t from rfl]
  exact
    CanonicalFixedDetectorFundamentalPhase.characterValue_onePhase_eq_mFourier_fundamental
      parameters controller _ t

/-- The twisted stored root `p₂ ζ⁻²` is its raw double Fourier series. -/
theorem canonical_rootP2_twisted_eq_raw_series
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ) (j : Fin vars) :
    ((canonicalState parameters I controller t).base.base.source.linked
        j).jacobi.p2 *
        characterValue
          (FixedDetectorMomentCode.rootHalfExponent (eqs := eqs) j)
          (canonicalState parameters I controller t).base.base.source.controllers =
      torusFourierSeries
        CanonicalSelectorMomentZeroModes.rootP2Coefficient
        (fun nm ↦ DetectorCharacterCode.flattenCharacter
          (CanonicalSelectorMomentZeroModes.rootP2Exponent
            (eqs := eqs) j nm))
        (phase parameters controller t) := by
  change
    theta₂
          (CanonicalFixedDetectorTrajectory.modularPath
            thetaGaugeBasePoint
            (CanonicalFixedDetectorTrajectory.omegaFrequency
              parameters controller j) t) ^ 2 *
        characterValue
          (FixedDetectorMomentCode.rootHalfExponent (eqs := eqs) j)
          (canonicalState parameters I controller t).base.base.source.controllers =
      _
  rw [canonical_theta2_eq_series, rootHalf_character_eq]
  rw [torusFourierSeries_sq
    theta2Coefficient
    (theta2FundamentalExponent (eqs := eqs) j)
    theta2Coefficient_summable
    (phase parameters controller t)]
  rw [torusFourierSeries_mul_mFourier]
  congr 1
  · funext nm
    exact theta2Coefficient_product nm
  · funext nm
    exact (flatRootP2Exponent_eq_sum_add_twist j nm).symm

/-- Corrected moment 3: `p₂ ζ⁻² - 1/4`. -/
theorem localMomentValue_three_eq_rootP2_series
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ) (j : Fin vars) :
    CorrectedFixedDetectorMomentCode.localMomentValue
        I j (canonicalState parameters I controller t) 3 =
      torusFourierSeries
        (rootP2 (eqs := eqs) j).coefficient
        (rootP2 (eqs := eqs) j).flatExponent
        (phase parameters controller t) := by
  change
    ((canonicalState parameters I controller t).base.base.source.linked
        j).jacobi.p2 *
          characterValue
            (FixedDetectorMomentCode.rootHalfExponent (eqs := eqs) j)
            (canonicalState parameters I controller t).base.base.source.controllers -
        (1 / 4 : ℚ) = _
  rw [canonical_rootP2_twisted_eq_raw_series]
  symm
  rw [rootP2_flatExponent]
  simpa [rootP2] using
    (torusFourierSeries_centered
      (((1 / 4 : ℝ) : ℂ))
      CanonicalSelectorMomentZeroModes.rootP2Coefficient
      (fun nm ↦ DetectorCharacterCode.flattenCharacter
        (CanonicalSelectorMomentZeroModes.rootP2Exponent
          (eqs := eqs) j nm))
      (by
        simpa using
          (Analysis.CanonicalSelectorMomentRadicalSummability.summable_rootP2Exponent
            (eqs := eqs) (vars := vars)
            (harmlessRadicand (eqs := eqs) (vars := vars)) j 0))
      (phase parameters controller t))

/-! ## The three gauge-corrected Jacobi moments -/

private theorem canonical_thetaOutput_eq_raw_series
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ) (j : Fin vars) :
    (canonicalState parameters I controller t).base.base.gauge j *
        ((canonicalState parameters I controller t).base.base.source.linked
          j).jacobi.T1 =
      torusFourierSeries
        CanonicalSelectorMomentZeroModes.thetaCoefficient
        (fun n ↦ DetectorCharacterCode.flattenCharacter
          (CanonicalSelectorMomentZeroModes.jacobiMeanExponent I j n))
        (phase parameters controller t) := by
  rw [
    CanonicalFixedDetectorFundamentalPhase.torusFourierSeries_flatten_fundamentalPhasePath]
  simpa [canonicalState, torusFourierSeries, torusSeriesTerm,
    DetectorFactorizedFourier.thetaTerm,
    CanonicalSelectorMomentZeroModes.thetaCoefficient,
    CorrectedJacobiSelectorCentering.thetaCoefficient] using
    (CanonicalFixedDetectorFourierCrosswalk.canonical_thetaOutput_eq_thetaSeries
      parameters I controller (1 : Circle) t j)

/-- Corrected moment 4: `F - 1`. -/
theorem localMomentValue_four_eq_jacobiMean_series
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ) (j : Fin vars) :
    CorrectedFixedDetectorMomentCode.localMomentValue
        I j (canonicalState parameters I controller t) 4 =
      torusFourierSeries
        (jacobiMean I j).coefficient
        (jacobiMean I j).flatExponent
        (phase parameters controller t) := by
  change
    (canonicalState parameters I controller t).base.base.gauge j *
          ((canonicalState parameters I controller t).base.base.source.linked
            j).jacobi.T1 -
        1 = _
  rw [canonical_thetaOutput_eq_raw_series]
  symm
  rw [jacobiMean_flatExponent]
  simpa [jacobiMean] using
    (torusFourierSeries_centered
      1 CanonicalSelectorMomentZeroModes.thetaCoefficient
      (fun n ↦ DetectorCharacterCode.flattenCharacter
        (CanonicalSelectorMomentZeroModes.jacobiMeanExponent I j n))
      (thetaCoefficient_summable I j)
      (phase parameters controller t))

private theorem flatPlusExponent_eq_add
    (I : DQLSystem eqs vars) (j : Fin vars) (n : ℤ) :
    DetectorCharacterCode.flattenCharacter
        (CorrectedJacobiSelectorCentering.plusExponent I j n) =
      DetectorCharacterCode.flattenCharacter
          (CanonicalSelectorMomentZeroModes.jacobiMeanExponent I j n) +
        DetectorCharacterCode.flattenCharacter
          (fun phase ↦
            -DetectorCharacterCode.privateCharacter j phase -
              DetectorCharacterCode.linearCharacter I j phase) := by
  funext i
  simp [DetectorCharacterCode.flattenCharacter,
    CorrectedJacobiSelectorCentering.plusExponent]
  ring

private theorem flatMinusExponent_eq_add
    (I : DQLSystem eqs vars) (j : Fin vars) (n : ℤ) :
    DetectorCharacterCode.flattenCharacter
        (CorrectedJacobiSelectorCentering.minusExponent I j n) =
      DetectorCharacterCode.flattenCharacter
          (CanonicalSelectorMomentZeroModes.jacobiMeanExponent I j n) +
        DetectorCharacterCode.flattenCharacter
          (fun phase ↦
            -DetectorCharacterCode.privateCharacter j phase +
              DetectorCharacterCode.linearCharacter I j phase) := by
  funext i
  simp [DetectorCharacterCode.flattenCharacter,
    CorrectedJacobiSelectorCentering.minusExponent]
  ring

private theorem jacobiPlus_character_eq
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ) (j : Fin vars) :
    characterValue
        (FixedDetectorMomentCode.jacobiPlusExponent I j)
        (canonicalState parameters I controller t).base.base.source.controllers =
      UnitAddTorus.mFourier
        (DetectorCharacterCode.flattenCharacter
          (fun phase ↦
            -DetectorCharacterCode.privateCharacter j phase -
              DetectorCharacterCode.linearCharacter I j phase))
        (phase parameters controller t) := by
  rw [show
      (canonicalState parameters I controller t).base.base.source.controllers =
        CanonicalFixedDetectorTrajectory.clockPath
          parameters controller
          LockedControllerPhaseTrajectory.onePhase t from rfl]
  rw [show
      FixedDetectorMomentCode.jacobiPlusExponent I j =
        DetectorCharacterCode.flattenCharacter
          (fun phase ↦
            -DetectorCharacterCode.privateCharacter j phase -
              DetectorCharacterCode.linearCharacter I j phase) by
    funext i
    simp [FixedDetectorMomentCode.jacobiPlusExponent,
      FixedDetectorMomentCode.privateExponent,
      FixedDetectorMomentCode.linearExponent,
      DetectorCharacterCode.flattenCharacter]
    ring]
  rw [
    CanonicalFixedDetectorFourierCrosswalk.characterValue_onePhase_eq_mFourier]
  exact
    (CanonicalFixedDetectorFundamentalPhase.mFourier_flattenCharacter_fundamentalPhasePath
      parameters controller _ t).symm

private theorem jacobiMinus_character_eq
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ) (j : Fin vars) :
    characterValue
        (FixedDetectorMomentCode.jacobiMinusExponent I j)
        (canonicalState parameters I controller t).base.base.source.controllers =
      UnitAddTorus.mFourier
        (DetectorCharacterCode.flattenCharacter
          (fun phase ↦
            -DetectorCharacterCode.privateCharacter j phase +
              DetectorCharacterCode.linearCharacter I j phase))
        (phase parameters controller t) := by
  rw [show
      (canonicalState parameters I controller t).base.base.source.controllers =
        CanonicalFixedDetectorTrajectory.clockPath
          parameters controller
          LockedControllerPhaseTrajectory.onePhase t from rfl]
  rw [show
      FixedDetectorMomentCode.jacobiMinusExponent I j =
        DetectorCharacterCode.flattenCharacter
          (fun phase ↦
            -DetectorCharacterCode.privateCharacter j phase +
              DetectorCharacterCode.linearCharacter I j phase) by
    funext i
    simp [FixedDetectorMomentCode.jacobiMinusExponent,
      FixedDetectorMomentCode.privateExponent,
      FixedDetectorMomentCode.linearExponent,
      DetectorCharacterCode.flattenCharacter]
    ring]
  rw [
    CanonicalFixedDetectorFourierCrosswalk.characterValue_onePhase_eq_mFourier]
  exact
    (CanonicalFixedDetectorFundamentalPhase.mFourier_flattenCharacter_fundamentalPhasePath
      parameters controller _ t).symm

/-- Corrected moment 5, including the conditional selector center. -/
theorem localMomentValue_five_eq_jacobiPlus_series
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ) (j : Fin vars) :
    CorrectedFixedDetectorMomentCode.localMomentValue
        I j (canonicalState parameters I controller t) 5 =
      torusFourierSeries
        (jacobiPlus I j).coefficient
        (jacobiPlus I j).flatExponent
        (phase parameters controller t) := by
  change
    ((canonicalState parameters I controller t).base.base.gauge j *
          ((canonicalState parameters I controller t).base.base.source.linked
            j).jacobi.T1) *
          characterValue
            (FixedDetectorMomentCode.jacobiPlusExponent I j)
            (canonicalState parameters I controller t).base.base.source.controllers -
        CorrectedJacobiSelectorCentering.selectorCenter I j = _
  rw [canonical_thetaOutput_eq_raw_series, jacobiPlus_character_eq]
  rw [torusFourierSeries_mul_mFourier]
  rw [show
      (fun n ↦
        DetectorCharacterCode.flattenCharacter
            (CanonicalSelectorMomentZeroModes.jacobiMeanExponent I j n) +
          DetectorCharacterCode.flattenCharacter
            (fun phase ↦
              -DetectorCharacterCode.privateCharacter j phase -
                DetectorCharacterCode.linearCharacter I j phase)) =
        fun n ↦ DetectorCharacterCode.flattenCharacter
          (CorrectedJacobiSelectorCentering.plusExponent I j n) by
    funext n
    exact (flatPlusExponent_eq_add I j n).symm]
  symm
  rw [jacobiPlus_coefficient, jacobiPlus_flatExponent]
  exact torusFourierSeries_centered
    (((CorrectedJacobiSelectorCentering.selectorCenter I j : ℚ) : ℂ))
    CanonicalSelectorMomentZeroModes.thetaCoefficient
    (fun n ↦ DetectorCharacterCode.flattenCharacter
      (CorrectedJacobiSelectorCentering.plusExponent I j n))
    (thetaCoefficient_summable I j)
    (phase parameters controller t)

/-- Corrected moment 6, including the conditional selector center. -/
theorem localMomentValue_six_eq_jacobiMinus_series
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ) (j : Fin vars) :
    CorrectedFixedDetectorMomentCode.localMomentValue
        I j (canonicalState parameters I controller t) 6 =
      torusFourierSeries
        (jacobiMinus I j).coefficient
        (jacobiMinus I j).flatExponent
        (phase parameters controller t) := by
  change
    ((canonicalState parameters I controller t).base.base.gauge j *
          ((canonicalState parameters I controller t).base.base.source.linked
            j).jacobi.T1) *
          characterValue
            (FixedDetectorMomentCode.jacobiMinusExponent I j)
            (canonicalState parameters I controller t).base.base.source.controllers -
        CorrectedJacobiSelectorCentering.selectorCenter I j = _
  rw [canonical_thetaOutput_eq_raw_series, jacobiMinus_character_eq]
  rw [torusFourierSeries_mul_mFourier]
  rw [show
      (fun n ↦
        DetectorCharacterCode.flattenCharacter
            (CanonicalSelectorMomentZeroModes.jacobiMeanExponent I j n) +
          DetectorCharacterCode.flattenCharacter
            (fun phase ↦
              -DetectorCharacterCode.privateCharacter j phase +
                DetectorCharacterCode.linearCharacter I j phase)) =
        fun n ↦ DetectorCharacterCode.flattenCharacter
          (CorrectedJacobiSelectorCentering.minusExponent I j n) by
    funext n
    exact (flatMinusExponent_eq_add I j n).symm]
  symm
  rw [jacobiMinus_coefficient, jacobiMinus_flatExponent]
  exact torusFourierSeries_centered
    (((CorrectedJacobiSelectorCentering.selectorCenter I j : ℚ) : ℂ))
    CanonicalSelectorMomentZeroModes.thetaCoefficient
    (fun n ↦ DetectorCharacterCode.flattenCharacter
      (CorrectedJacobiSelectorCentering.minusExponent I j n))
    (thetaCoefficient_summable I j)
    (phase parameters controller t)

end HGAS.CorrectedCanonicalFixedDetectorMomentFourierCrosswalk
