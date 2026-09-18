import HGAS.Analysis.GaussianPolynomialWeightedSummability
import HGAS.Analysis.DetectorRadicalWeightedSummability
import HGAS.Arithmetic.CanonicalSelectorMomentZeroModes
import Mathlib.Tactic

/-!
# Radical-height weighted summability of the corrected selector moments

The seven selector moments are built from one- and two-dimensional theta
series.  Their coefficients have Gaussian (or stronger odd-square)
decay, while every flattened clock exponent has at most quadratic growth
in the integer theta indices.  Hence the prime-radical small-divisor
height, to every fixed power, remains summable.

The final section adjoins each centering constant.  A constant is one
finite Fourier term of exponent zero, so it does not affect summability.
-/

noncomputable section

open scoped BigOperators

namespace HGAS.Analysis.CanonicalSelectorMomentRadicalSummability

open HGAS
open HGAS.Clocks

variable {eqs vars : ℕ}

/-- Radical height of a detector character after the required
fourth-root-clock flattening. -/
def characterHeight
    (radicand : Fin (vars + eqs) → ℕ)
    (a : DetectorPhase eqs vars → ℤ) : ℝ :=
  RadicalSmallDivisor.radicalConjugateHeight
    radicand (DetectorCharacterCode.flattenCharacter a)

theorem characterHeight_nonneg
    (radicand : Fin (vars + eqs) → ℕ)
    (a : DetectorPhase eqs vars → ℤ) :
    0 ≤ characterHeight radicand a :=
  RadicalSmallDivisor.radicalConjugateHeight_nonneg
    radicand (DetectorCharacterCode.flattenCharacter a)

/-- Radical height is controlled by the unsigned flattened character
energy. -/
theorem characterHeight_le_rootSum_mul_energy
    (radicand : Fin (vars + eqs) → ℕ)
    (a : DetectorPhase eqs vars → ℤ) :
    characterHeight radicand a ≤
      radicalRootSum radicand *
        (DetectorCharacterCode.detectorCharacterEnergy a : ℝ) := by
  exact
    radicalConjugateHeight_le_rootSum_mul_integerL1Energy
      radicand (DetectorCharacterCode.flattenCharacter a)

private theorem sum_natAbs_single
    (j : Fin vars) (z : ℤ) :
    (∑ k : Fin vars,
      (if k = j then z else 0).natAbs) =
        z.natAbs := by
  classical
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    simp [hkj]
  · simp

/-- Exact energy of a private/linear two-character combination. -/
theorem detectorCharacterEnergy_private_linear
    (I : DQLSystem eqs vars) (j : Fin vars)
    (a b : ℤ) :
    DetectorCharacterCode.detectorCharacterEnergy
        (fun phase ↦
          a * DetectorCharacterCode.privateCharacter j phase +
            b * DetectorCharacterCode.linearCharacter I j phase) =
      4 * (a.natAbs +
        b.natAbs *
          DetectorCharacterCode.linearColumnEnergy I j) := by
  rw [DetectorCharacterCode.detectorCharacterEnergy_eq]
  simp only [DetectorCharacterCode.privateCharacter,
    DetectorCharacterCode.linearCharacter, mul_ite, mul_one,
    mul_zero, add_zero, zero_add, Int.natAbs_mul]
  rw [sum_natAbs_single]
  unfold DetectorCharacterCode.linearColumnEnergy
  simp only [Finset.mul_sum]

/-- Exact energy of a scalar private character. -/
theorem detectorCharacterEnergy_private
    (j : Fin vars) (a : ℤ) :
    DetectorCharacterCode.detectorCharacterEnergy
        (fun phase : DetectorPhase eqs vars ↦
          a * DetectorCharacterCode.privateCharacter j phase) =
      4 * a.natAbs := by
  rw [DetectorCharacterCode.detectorCharacterEnergy_eq]
  simp only [DetectorCharacterCode.privateCharacter,
    mul_ite, mul_one, mul_zero, Int.natAbs_zero,
    Finset.sum_const_zero, add_zero]
  rw [sum_natAbs_single]

/-- Coarse common quadratic energy bound for all one-index selector
characters. -/
theorem private_linear_energy_le_quadratic
    (I : DQLSystem eqs vars) (j : Fin vars)
    (a b n : ℤ)
    (ha : a.natAbs ≤ n.natAbs ^ 2 + 1)
    (hb : b.natAbs ≤ n.natAbs + 1) :
    DetectorCharacterCode.detectorCharacterEnergy
        (fun phase ↦
          a * DetectorCharacterCode.privateCharacter j phase +
            b * DetectorCharacterCode.linearCharacter I j phase) ≤
      4 * (1 +
          DetectorCharacterCode.linearColumnEnergy I j) *
        (1 + n.natAbs) ^ 2 := by
  rw [detectorCharacterEnergy_private_linear]
  let L := DetectorCharacterCode.linearColumnEnergy I j
  have hn : n.natAbs ≤ (1 + n.natAbs) ^ 2 := by
    simp only [pow_two]
    nlinarith
  have hsq : n.natAbs ^ 2 + 1 ≤
      (1 + n.natAbs) ^ 2 := by
    simp only [pow_two]
    have hn0 : 0 ≤ n.natAbs := Nat.zero_le _
    nlinarith
  have hb' : b.natAbs ≤ (1 + n.natAbs) ^ 2 :=
    hb.trans (by
      simp only [pow_two]
      nlinarith)
  have ha' : a.natAbs ≤ (1 + n.natAbs) ^ 2 :=
    ha.trans hsq
  calc
    4 * (a.natAbs + b.natAbs * L) ≤
        4 * ((1 + n.natAbs) ^ 2 +
          (1 + n.natAbs) ^ 2 * L) :=
      Nat.mul_le_mul_left 4
        (Nat.add_le_add ha'
          (Nat.mul_le_mul_right L hb'))
    _ =
        4 * (1 + L) * (1 + n.natAbs) ^ 2 := by
      ring

private theorem natAbs_sq_sub_one_le (n : ℤ) :
    (n ^ 2 - 1).natAbs ≤ n.natAbs ^ 2 + 1 := by
  calc
    (n ^ 2 - 1).natAbs ≤
        (n ^ 2).natAbs + (1 : ℤ).natAbs :=
      Int.natAbs_sub_le _ _
    _ = n.natAbs ^ 2 + 1 := by norm_num

private theorem natAbs_sub_one_le (n : ℤ) :
    (n - 1).natAbs ≤ n.natAbs + 1 := by
  simpa using Int.natAbs_sub_le n 1

private theorem natAbs_add_one_le (n : ℤ) :
    (n + 1).natAbs ≤ n.natAbs + 1 := by
  simpa using Int.natAbs_add_le n 1

theorem unaryExponent_energy_le
    (j : Fin vars) (n : ℤ) :
    DetectorCharacterCode.detectorCharacterEnergy
        (CanonicalSelectorMomentZeroModes.unaryExponent
          (eqs := eqs) j n) ≤
      4 * (1 + n.natAbs) ^ 2 := by
  change
    DetectorCharacterCode.detectorCharacterEnergy
        (fun phase : DetectorPhase eqs vars ↦
          n ^ 2 *
            DetectorCharacterCode.privateCharacter j phase) ≤ _
  rw [detectorCharacterEnergy_private]
  simp only [Int.natAbs_pow]
  exact Nat.mul_le_mul_left 4
    (Nat.pow_le_pow_left (by omega) 2)

theorem unaryFirstExponent_energy_le
    (j : Fin vars) (n : ℤ) :
    DetectorCharacterCode.detectorCharacterEnergy
        (CanonicalSelectorMomentZeroModes.unaryFirstExponent
          (eqs := eqs) j n) ≤
      4 * (1 + n.natAbs) ^ 2 := by
  change
    DetectorCharacterCode.detectorCharacterEnergy
        (fun phase : DetectorPhase eqs vars ↦
          (n ^ 2 - 1) *
            DetectorCharacterCode.privateCharacter j phase) ≤ _
  rw [detectorCharacterEnergy_private]
  exact Nat.mul_le_mul_left 4
    ((natAbs_sq_sub_one_le n).trans (by
      simp only [pow_two]
      have hn0 : 0 ≤ n.natAbs := Nat.zero_le _
      nlinarith))

theorem jacobiMeanExponent_energy_le
    (I : DQLSystem eqs vars) (j : Fin vars) (n : ℤ) :
    DetectorCharacterCode.detectorCharacterEnergy
        (CanonicalSelectorMomentZeroModes.jacobiMeanExponent
          I j n) ≤
      4 * (1 +
          DetectorCharacterCode.linearColumnEnergy I j) *
        (1 + n.natAbs) ^ 2 := by
  apply private_linear_energy_le_quadratic I j
  · simp only [Int.natAbs_pow]
    omega
  · omega

theorem plusExponent_energy_le
    (I : DQLSystem eqs vars) (j : Fin vars) (n : ℤ) :
    DetectorCharacterCode.detectorCharacterEnergy
        (CorrectedJacobiSelectorCentering.plusExponent I j n) ≤
      4 * (1 +
          DetectorCharacterCode.linearColumnEnergy I j) *
        (1 + n.natAbs) ^ 2 := by
  have hrewrite :
      CorrectedJacobiSelectorCentering.plusExponent I j n =
        fun phase ↦
          (n ^ 2 - 1) *
              DetectorCharacterCode.privateCharacter j phase +
            (n - 1) *
              DetectorCharacterCode.linearCharacter I j phase := by
    funext phase
    simp [CorrectedJacobiSelectorCentering.plusExponent,
      DetectorFactorizedFourier.thetaCoordinateExponent]
    ring
  rw [hrewrite]
  exact
    private_linear_energy_le_quadratic I j
      (n ^ 2 - 1) (n - 1) n
      (natAbs_sq_sub_one_le n)
      (natAbs_sub_one_le n)

theorem minusExponent_energy_le
    (I : DQLSystem eqs vars) (j : Fin vars) (n : ℤ) :
    DetectorCharacterCode.detectorCharacterEnergy
        (CorrectedJacobiSelectorCentering.minusExponent I j n) ≤
      4 * (1 +
          DetectorCharacterCode.linearColumnEnergy I j) *
        (1 + n.natAbs) ^ 2 := by
  have hrewrite :
      CorrectedJacobiSelectorCentering.minusExponent I j n =
        fun phase ↦
          (n ^ 2 - 1) *
              DetectorCharacterCode.privateCharacter j phase +
            (n + 1) *
              DetectorCharacterCode.linearCharacter I j phase := by
    funext phase
    simp [CorrectedJacobiSelectorCentering.minusExponent,
      DetectorFactorizedFourier.thetaCoordinateExponent]
    ring
  rw [hrewrite]
  exact
    private_linear_energy_le_quadratic I j
      (n ^ 2 - 1) (n + 1) n
      (natAbs_sq_sub_one_le n)
      (natAbs_add_one_le n)

theorem rootP4Exponent_energy_le
    (j : Fin vars) (nm : ℤ × ℤ) :
    DetectorCharacterCode.detectorCharacterEnergy
        (CanonicalSelectorMomentZeroModes.rootP4Exponent
          (eqs := eqs) j nm) ≤
      4 * (1 + integerPairAbsEnergy nm) ^ 2 := by
  change
    DetectorCharacterCode.detectorCharacterEnergy
        (fun phase : DetectorPhase eqs vars ↦
          (nm.1 ^ 2 + nm.2 ^ 2) *
            DetectorCharacterCode.privateCharacter j phase) ≤ _
  rw [detectorCharacterEnergy_private]
  have hadd := Int.natAbs_add_le (nm.1 ^ 2) (nm.2 ^ 2)
  calc
    4 * (nm.1 ^ 2 + nm.2 ^ 2).natAbs ≤
        4 * ((nm.1 ^ 2).natAbs + (nm.2 ^ 2).natAbs) :=
      Nat.mul_le_mul_left 4 hadd
    _ = 4 * (nm.1.natAbs ^ 2 + nm.2.natAbs ^ 2) := by
      simp only [Int.natAbs_pow]
    _ ≤ 4 * (1 + integerPairAbsEnergy nm) ^ 2 := by
      apply Nat.mul_le_mul_left
      unfold integerPairAbsEnergy
      have h1 : 0 ≤ nm.1.natAbs := Nat.zero_le _
      have h2 : 0 ≤ nm.2.natAbs := Nat.zero_le _
      have h12 : 0 ≤ nm.1.natAbs * nm.2.natAbs :=
        Nat.zero_le _
      nlinarith

private theorem natAbs_consecutiveProduct_le
    (n : ℤ) :
    (HGAS.CanonicalSelectorMomentZeroModes.consecutiveProduct n).natAbs ≤
      n.natAbs * (n.natAbs + 1) := by
  unfold HGAS.CanonicalSelectorMomentZeroModes.consecutiveProduct
  rw [Int.natAbs_mul]
  exact Nat.mul_le_mul_left _
    (natAbs_add_one_le n)

theorem rootP2Exponent_energy_le
    (j : Fin vars) (nm : ℤ × ℤ) :
    DetectorCharacterCode.detectorCharacterEnergy
        (CanonicalSelectorMomentZeroModes.rootP2Exponent
          (eqs := eqs) j nm) ≤
      4 * (1 + integerPairAbsEnergy nm) ^ 2 := by
  change
    DetectorCharacterCode.detectorCharacterEnergy
        (fun phase : DetectorPhase eqs vars ↦
          (HGAS.CanonicalSelectorMomentZeroModes.consecutiveProduct nm.1 +
              HGAS.CanonicalSelectorMomentZeroModes.consecutiveProduct nm.2) *
            DetectorCharacterCode.privateCharacter j phase) ≤ _
  rw [detectorCharacterEnergy_private]
  have hadd :=
    Int.natAbs_add_le
      (HGAS.CanonicalSelectorMomentZeroModes.consecutiveProduct nm.1)
      (HGAS.CanonicalSelectorMomentZeroModes.consecutiveProduct nm.2)
  have h1 := natAbs_consecutiveProduct_le nm.1
  have h2 := natAbs_consecutiveProduct_le nm.2
  calc
    4 *
        (HGAS.CanonicalSelectorMomentZeroModes.consecutiveProduct nm.1 +
          HGAS.CanonicalSelectorMomentZeroModes.consecutiveProduct nm.2).natAbs ≤
      4 *
        ((HGAS.CanonicalSelectorMomentZeroModes.consecutiveProduct nm.1).natAbs +
          (HGAS.CanonicalSelectorMomentZeroModes.consecutiveProduct nm.2).natAbs) :=
      Nat.mul_le_mul_left 4 hadd
    _ ≤
      4 * (nm.1.natAbs * (nm.1.natAbs + 1) +
        nm.2.natAbs * (nm.2.natAbs + 1)) :=
      Nat.mul_le_mul_left 4 (Nat.add_le_add h1 h2)
    _ ≤ 4 * (1 + integerPairAbsEnergy nm) ^ 2 := by
      apply Nat.mul_le_mul_left
      unfold integerPairAbsEnergy
      have h1' : 0 ≤ nm.1.natAbs := Nat.zero_le _
      have h2' : 0 ≤ nm.2.natAbs := Nat.zero_le _
      have h12 : 0 ≤ nm.1.natAbs * nm.2.natAbs :=
        Nat.zero_le _
      nlinarith

/-! ## Radical-height bounds -/

def unaryHeightConstant
    (radicand : Fin (vars + eqs) → ℕ)
    (I : DQLSystem eqs vars) (j : Fin vars) : ℝ :=
  radicalRootSum radicand *
    (4 * (1 + DetectorCharacterCode.linearColumnEnergy I j) : ℕ)

def pairHeightConstant
    (radicand : Fin (vars + eqs) → ℕ) : ℝ :=
  radicalRootSum radicand * 4

theorem characterHeight_le_unaryQuadratic
    (radicand : Fin (vars + eqs) → ℕ)
    (I : DQLSystem eqs vars) (j : Fin vars)
    (a : ℤ → DetectorPhase eqs vars → ℤ)
    (ha :
      ∀ n,
        DetectorCharacterCode.detectorCharacterEnergy (a n) ≤
          4 * (1 +
            DetectorCharacterCode.linearColumnEnergy I j) *
              (1 + n.natAbs) ^ 2)
    (n : ℤ) :
    characterHeight radicand (a n) ≤
      unaryHeightConstant radicand I j *
        (1 + (n.natAbs : ℝ)) ^ 2 := by
  calc
    characterHeight radicand (a n) ≤
        radicalRootSum radicand *
          (DetectorCharacterCode.detectorCharacterEnergy
            (a n) : ℝ) :=
      characterHeight_le_rootSum_mul_energy radicand (a n)
    _ ≤
        radicalRootSum radicand *
          ((4 * (1 +
              DetectorCharacterCode.linearColumnEnergy I j) *
                (1 + n.natAbs) ^ 2 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left
        (Nat.cast_le.mpr (ha n))
        (radicalRootSum_nonneg radicand)
    _ =
        unaryHeightConstant radicand I j *
          (1 + (n.natAbs : ℝ)) ^ 2 := by
      simp only [unaryHeightConstant, Nat.cast_mul,
        Nat.cast_ofNat, Nat.cast_add, Nat.cast_pow]
      ring

theorem characterHeight_le_pairQuadratic
    (radicand : Fin (vars + eqs) → ℕ)
    (a : ℤ × ℤ → DetectorPhase eqs vars → ℤ)
    (ha :
      ∀ nm,
        DetectorCharacterCode.detectorCharacterEnergy (a nm) ≤
          4 * (1 + integerPairAbsEnergy nm) ^ 2)
    (nm : ℤ × ℤ) :
    characterHeight radicand (a nm) ≤
      pairHeightConstant radicand *
        (1 + (integerPairAbsEnergy nm : ℝ)) ^ 2 := by
  calc
    characterHeight radicand (a nm) ≤
        radicalRootSum radicand *
          (DetectorCharacterCode.detectorCharacterEnergy
            (a nm) : ℝ) :=
      characterHeight_le_rootSum_mul_energy radicand (a nm)
    _ ≤
        radicalRootSum radicand *
          ((4 * (1 + integerPairAbsEnergy nm) ^ 2 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left
        (Nat.cast_le.mpr (ha nm))
        (radicalRootSum_nonneg radicand)
    _ =
        pairHeightConstant radicand *
          (1 + (integerPairAbsEnergy nm : ℝ)) ^ 2 := by
      simp only [pairHeightConstant, Nat.cast_mul,
        Nat.cast_ofNat, Nat.cast_add, Nat.cast_pow]
      ring

/-! ## Gaussian coefficient identities -/

theorem norm_thetaCoefficient
    (n : ℤ) :
  ‖CanonicalSelectorMomentZeroModes.thetaCoefficient n‖ =
      (1 / 256 : ℝ) ^ (n.natAbs ^ 2) := by
  simp [CanonicalSelectorMomentZeroModes.thetaCoefficient,
    CorrectedJacobiSelectorCentering.thetaCoefficient]

theorem norm_rootP4Coefficient
    (nm : ℤ × ℤ) :
    ‖CanonicalSelectorMomentZeroModes.rootP4Coefficient nm‖ =
      (1 / 256 : ℝ) ^
        (nm.1.natAbs ^ 2 + nm.2.natAbs ^ 2) := by
  simp only [CanonicalSelectorMomentZeroModes.rootP4Coefficient,
    norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    norm_thetaCoefficient]
  rw [← pow_add]

theorem norm_rootP2Coefficient
    (nm : ℤ × ℤ) :
    ‖CanonicalSelectorMomentZeroModes.rootP2Coefficient nm‖ =
      (1 / 4 : ℝ) ^
        ((2 * nm.1 + 1).natAbs ^ 2 +
          (2 * nm.2 + 1).natAbs ^ 2) := by
  simp [CanonicalSelectorMomentZeroModes.rootP2Coefficient]

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

/-! ## Raw one- and two-index families -/

/-- Generic weighted summability theorem for a canonical theta
coefficient and any selector exponent satisfying the common quadratic
energy bound. -/
theorem summable_thetaCoefficient_mul_characterHeight_pow
    (radicand : Fin (vars + eqs) → ℕ)
    (I : DQLSystem eqs vars) (j : Fin vars)
    (a : ℤ → DetectorPhase eqs vars → ℤ)
    (ha :
      ∀ n,
        DetectorCharacterCode.detectorCharacterEnergy (a n) ≤
          4 * (1 +
            DetectorCharacterCode.linearColumnEnergy I j) *
              (1 + n.natAbs) ^ 2)
    (heightPower : ℕ) :
    Summable fun n : ℤ ↦
      ‖CanonicalSelectorMomentZeroModes.thetaCoefficient n‖ *
        characterHeight radicand (a n) ^ heightPower := by
  have h :=
    summable_gaussian_mul_height_pow_of_polynomial_bound
      (q := (1 / 256 : ℝ))
      (C := unaryHeightConstant radicand I j)
      (by norm_num) (by norm_num)
      heightPower 2
      (fun n ↦ characterHeight radicand (a n))
      (fun n ↦ characterHeight_nonneg radicand (a n))
      (characterHeight_le_unaryQuadratic
        radicand I j a ha)
  exact h.congr fun n ↦ by
    rw [norm_thetaCoefficient]

theorem summable_unaryExponent
    (radicand : Fin (vars + eqs) → ℕ)
    (I : DQLSystem eqs vars) (j : Fin vars)
    (heightPower : ℕ) :
    Summable fun n : ℤ ↦
      ‖CanonicalSelectorMomentZeroModes.thetaCoefficient n‖ *
        characterHeight radicand
          (CanonicalSelectorMomentZeroModes.unaryExponent
            (eqs := eqs) j n) ^ heightPower := by
  apply
    summable_thetaCoefficient_mul_characterHeight_pow
      radicand I j
      (CanonicalSelectorMomentZeroModes.unaryExponent
        (eqs := eqs) j)
  intro n
  exact (unaryExponent_energy_le j n).trans (by
    have hL :
        1 ≤ 1 +
          DetectorCharacterCode.linearColumnEnergy I j := by omega
    nlinarith)

theorem summable_unaryFirstExponent
    (radicand : Fin (vars + eqs) → ℕ)
    (I : DQLSystem eqs vars) (j : Fin vars)
    (heightPower : ℕ) :
    Summable fun n : ℤ ↦
      ‖CanonicalSelectorMomentZeroModes.thetaCoefficient n‖ *
        characterHeight radicand
          (CanonicalSelectorMomentZeroModes.unaryFirstExponent
            (eqs := eqs) j n) ^ heightPower := by
  apply
    summable_thetaCoefficient_mul_characterHeight_pow
      radicand I j
      (CanonicalSelectorMomentZeroModes.unaryFirstExponent
        (eqs := eqs) j)
  intro n
  exact (unaryFirstExponent_energy_le j n).trans (by
    have hL :
        1 ≤ 1 +
          DetectorCharacterCode.linearColumnEnergy I j := by omega
    nlinarith)

theorem summable_jacobiMeanExponent
    (radicand : Fin (vars + eqs) → ℕ)
    (I : DQLSystem eqs vars) (j : Fin vars)
    (heightPower : ℕ) :
    Summable fun n : ℤ ↦
      ‖CanonicalSelectorMomentZeroModes.thetaCoefficient n‖ *
        characterHeight radicand
          (CanonicalSelectorMomentZeroModes.jacobiMeanExponent
            I j n) ^ heightPower :=
  summable_thetaCoefficient_mul_characterHeight_pow
    radicand I j
    (CanonicalSelectorMomentZeroModes.jacobiMeanExponent I j)
    (jacobiMeanExponent_energy_le I j) heightPower

theorem summable_plusExponent
    (radicand : Fin (vars + eqs) → ℕ)
    (I : DQLSystem eqs vars) (j : Fin vars)
    (heightPower : ℕ) :
    Summable fun n : ℤ ↦
      ‖CanonicalSelectorMomentZeroModes.thetaCoefficient n‖ *
        characterHeight radicand
          (CorrectedJacobiSelectorCentering.plusExponent
            I j n) ^ heightPower :=
  summable_thetaCoefficient_mul_characterHeight_pow
    radicand I j
    (CorrectedJacobiSelectorCentering.plusExponent I j)
    (plusExponent_energy_le I j) heightPower

theorem summable_minusExponent
    (radicand : Fin (vars + eqs) → ℕ)
    (I : DQLSystem eqs vars) (j : Fin vars)
    (heightPower : ℕ) :
    Summable fun n : ℤ ↦
      ‖CanonicalSelectorMomentZeroModes.thetaCoefficient n‖ *
        characterHeight radicand
          (CorrectedJacobiSelectorCentering.minusExponent
            I j n) ^ heightPower :=
  summable_thetaCoefficient_mul_characterHeight_pow
    radicand I j
    (CorrectedJacobiSelectorCentering.minusExponent I j)
    (minusExponent_energy_le I j) heightPower

theorem summable_rootP4Exponent
    (radicand : Fin (vars + eqs) → ℕ)
    (j : Fin vars) (heightPower : ℕ) :
    Summable fun nm : ℤ × ℤ ↦
      ‖CanonicalSelectorMomentZeroModes.rootP4Coefficient nm‖ *
        characterHeight radicand
          (CanonicalSelectorMomentZeroModes.rootP4Exponent
            (eqs := eqs) j nm) ^ heightPower := by
  have h :=
    summable_pairGaussian_mul_height_pow_of_polynomial_bound
      (q := (1 / 256 : ℝ))
      (C := pairHeightConstant radicand)
      (by norm_num) (by norm_num)
      heightPower 2
      (fun nm ↦ characterHeight radicand
        (CanonicalSelectorMomentZeroModes.rootP4Exponent
          (eqs := eqs) j nm))
      (fun nm ↦ characterHeight_nonneg radicand
        (CanonicalSelectorMomentZeroModes.rootP4Exponent
          (eqs := eqs) j nm))
      (characterHeight_le_pairQuadratic
        radicand
        (CanonicalSelectorMomentZeroModes.rootP4Exponent
          (eqs := eqs) j)
        (rootP4Exponent_energy_le j))
  exact h.congr fun nm ↦ by
    rw [norm_rootP4Coefficient]

theorem summable_rootP2Exponent
    (radicand : Fin (vars + eqs) → ℕ)
    (j : Fin vars) (heightPower : ℕ) :
    Summable fun nm : ℤ × ℤ ↦
      ‖CanonicalSelectorMomentZeroModes.rootP2Coefficient nm‖ *
        characterHeight radicand
          (CanonicalSelectorMomentZeroModes.rootP2Exponent
            (eqs := eqs) j nm) ^ heightPower := by
  have hdecay :
      ∀ nm : ℤ × ℤ,
        integerPairAbsEnergy nm ≤
          (2 * nm.1 + 1).natAbs ^ 2 +
            (2 * nm.2 + 1).natAbs ^ 2 := by
    intro nm
    unfold integerPairAbsEnergy
    exact Nat.add_le_add
      (natAbs_le_oddSquare nm.1)
      (natAbs_le_oddSquare nm.2)
  have h :=
    summable_intPairDecay_mul_height_pow_of_polynomial_bound
      (q := (1 / 4 : ℝ))
      (C := pairHeightConstant radicand)
      (by norm_num) (by norm_num)
      (fun nm : ℤ × ℤ ↦
        (2 * nm.1 + 1).natAbs ^ 2 +
          (2 * nm.2 + 1).natAbs ^ 2)
      hdecay heightPower 2
      (fun nm ↦ characterHeight radicand
        (CanonicalSelectorMomentZeroModes.rootP2Exponent
          (eqs := eqs) j nm))
      (fun nm ↦ characterHeight_nonneg radicand
        (CanonicalSelectorMomentZeroModes.rootP2Exponent
          (eqs := eqs) j nm))
      (characterHeight_le_pairQuadratic
        radicand
        (CanonicalSelectorMomentZeroModes.rootP2Exponent
          (eqs := eqs) j)
        (rootP2Exponent_energy_le j))
  exact h.congr fun nm ↦ by
    rw [norm_rootP2Coefficient]

/-! ## Adjoining the exact centering constants -/

/-- A single zero-exponent centering term does not affect any weighted
summability estimate. -/
theorem summable_centeredFourier_mul_characterHeight_pow
    {ι : Type*}
    (radicand : Fin (vars + eqs) → ℕ)
    (center : ℂ) (coefficient : ι → ℂ)
    (exponent : ι → DetectorPhase eqs vars → ℤ)
    (heightPower : ℕ)
    (hraw :
      Summable fun i : ι ↦
        ‖coefficient i‖ *
          characterHeight radicand (exponent i) ^ heightPower) :
    Summable fun i : CenteredFourierIndex ι ↦
      ‖centeredFourierCoefficient center coefficient i‖ *
        characterHeight radicand
          (centeredFourierExponent exponent i) ^ heightPower := by
  apply Summable.sum
  · exact Summable.of_finite
  · simpa [Function.comp_def, centeredFourierCoefficient,
      centeredFourierExponent] using hraw

theorem summable_centeredUnaryMean
    (radicand : Fin (vars + eqs) → ℕ)
    (I : DQLSystem eqs vars) (j : Fin vars)
    (heightPower : ℕ) :
    Summable fun i : CenteredFourierIndex ℤ ↦
      ‖centeredFourierCoefficient
          1 CanonicalSelectorMomentZeroModes.thetaCoefficient i‖ *
        characterHeight radicand
          (centeredFourierExponent
            (CanonicalSelectorMomentZeroModes.unaryExponent
              (eqs := eqs) j) i) ^ heightPower :=
  summable_centeredFourier_mul_characterHeight_pow
    radicand 1
    CanonicalSelectorMomentZeroModes.thetaCoefficient
    (CanonicalSelectorMomentZeroModes.unaryExponent
      (eqs := eqs) j)
    heightPower
    (summable_unaryExponent radicand I j heightPower)

theorem summable_centeredUnaryFirst
    (radicand : Fin (vars + eqs) → ℕ)
    (I : DQLSystem eqs vars) (j : Fin vars)
    (heightPower : ℕ) :
    Summable fun i : CenteredFourierIndex ℤ ↦
      ‖centeredFourierCoefficient
          (((1 / 128 : ℝ) : ℂ))
          CanonicalSelectorMomentZeroModes.thetaCoefficient i‖ *
        characterHeight radicand
          (centeredFourierExponent
            (CanonicalSelectorMomentZeroModes.unaryFirstExponent
              (eqs := eqs) j) i) ^ heightPower :=
  summable_centeredFourier_mul_characterHeight_pow
    radicand (((1 / 128 : ℝ) : ℂ))
    CanonicalSelectorMomentZeroModes.thetaCoefficient
    (CanonicalSelectorMomentZeroModes.unaryFirstExponent
      (eqs := eqs) j)
    heightPower
    (summable_unaryFirstExponent radicand I j heightPower)

theorem summable_centeredRootP4
    (radicand : Fin (vars + eqs) → ℕ)
    (j : Fin vars) (heightPower : ℕ) :
    Summable fun i : CenteredFourierIndex (ℤ × ℤ) ↦
      ‖centeredFourierCoefficient
          1 CanonicalSelectorMomentZeroModes.rootP4Coefficient i‖ *
        characterHeight radicand
          (centeredFourierExponent
            (CanonicalSelectorMomentZeroModes.rootP4Exponent
              (eqs := eqs) j) i) ^ heightPower :=
  summable_centeredFourier_mul_characterHeight_pow
    radicand 1
    CanonicalSelectorMomentZeroModes.rootP4Coefficient
    (CanonicalSelectorMomentZeroModes.rootP4Exponent
      (eqs := eqs) j)
    heightPower
    (summable_rootP4Exponent radicand j heightPower)

theorem summable_centeredRootP2
    (radicand : Fin (vars + eqs) → ℕ)
    (j : Fin vars) (heightPower : ℕ) :
    Summable fun i : CenteredFourierIndex (ℤ × ℤ) ↦
      ‖centeredFourierCoefficient
          (((1 / 4 : ℝ) : ℂ))
          CanonicalSelectorMomentZeroModes.rootP2Coefficient i‖ *
        characterHeight radicand
          (centeredFourierExponent
            (CanonicalSelectorMomentZeroModes.rootP2Exponent
              (eqs := eqs) j) i) ^ heightPower :=
  summable_centeredFourier_mul_characterHeight_pow
    radicand (((1 / 4 : ℝ) : ℂ))
    CanonicalSelectorMomentZeroModes.rootP2Coefficient
    (CanonicalSelectorMomentZeroModes.rootP2Exponent
      (eqs := eqs) j)
    heightPower
    (summable_rootP2Exponent radicand j heightPower)

theorem summable_centeredJacobiMean
    (radicand : Fin (vars + eqs) → ℕ)
    (I : DQLSystem eqs vars) (j : Fin vars)
    (heightPower : ℕ) :
    Summable fun i : CenteredFourierIndex ℤ ↦
      ‖centeredFourierCoefficient
          1 CanonicalSelectorMomentZeroModes.thetaCoefficient i‖ *
        characterHeight radicand
          (centeredFourierExponent
            (CanonicalSelectorMomentZeroModes.jacobiMeanExponent
              I j) i) ^ heightPower :=
  summable_centeredFourier_mul_characterHeight_pow
    radicand 1
    CanonicalSelectorMomentZeroModes.thetaCoefficient
    (CanonicalSelectorMomentZeroModes.jacobiMeanExponent I j)
    heightPower
    (summable_jacobiMeanExponent radicand I j heightPower)

theorem summable_centeredJacobiPlus
    (radicand : Fin (vars + eqs) → ℕ)
    (I : DQLSystem eqs vars) (j : Fin vars)
    (heightPower : ℕ) :
    Summable fun i :
        CorrectedJacobiSelectorCentering.CenteredThetaIndex ↦
      ‖CorrectedJacobiSelectorCentering.centeredCoefficient I j i‖ *
        characterHeight radicand
          (CorrectedJacobiSelectorCentering.centeredPlusExponent
            I j i) ^ heightPower := by
  apply Summable.sum
  · exact Summable.of_finite
  · simpa [Function.comp_def,
      CorrectedJacobiSelectorCentering.centeredCoefficient,
      CorrectedJacobiSelectorCentering.centeredPlusExponent] using
      summable_plusExponent radicand I j heightPower

theorem summable_centeredJacobiMinus
    (radicand : Fin (vars + eqs) → ℕ)
    (I : DQLSystem eqs vars) (j : Fin vars)
    (heightPower : ℕ) :
    Summable fun i :
        CorrectedJacobiSelectorCentering.CenteredThetaIndex ↦
      ‖CorrectedJacobiSelectorCentering.centeredCoefficient I j i‖ *
        characterHeight radicand
          (CorrectedJacobiSelectorCentering.centeredMinusExponent
            I j i) ^ heightPower := by
  apply Summable.sum
  · exact Summable.of_finite
  · simpa [Function.comp_def,
      CorrectedJacobiSelectorCentering.centeredCoefficient,
      CorrectedJacobiSelectorCentering.centeredMinusExponent] using
      summable_minusExponent radicand I j heightPower

end HGAS.Analysis.CanonicalSelectorMomentRadicalSummability
