import HGAS.Analysis.CenteredFourierAggregation
import HGAS.Arithmetic.CorrectedJacobiSelectorCentering
import HGAS.Arithmetic.DetectorFactorizedFourier
import Mathlib.Tactic

/-!
# Aggregate zero modes of the canonical selector moments

This module performs the zero-frequency bookkeeping for the five
selector moments not covered by
`CorrectedJacobiSelectorCentering`.  Together the two files cover all
seven complex moments:

1. `Y - 1`;
2. `Y Q⁻¹ - 1/128`;
3. `p₄ - 1`;
4. `p₂ ζ⁻² - 1/4`;
5. `F - 1`;
6. `F (QV)⁻¹ - c_j`;
7. `F Q⁻¹V - c_j`.

The proofs deliberately aggregate repeated exponents.  The first unary
harmonic has two resonant terms `n = ±1`, while the `p₂` root moment has
four resonant pairs `n,m ∈ {0,-1}`.  None of those raw terms vanishes
individually; their finite sums equal the displayed centering constants.
-/

noncomputable section

open scoped BigOperators

namespace HGAS.CanonicalSelectorMomentZeroModes

variable {eqs vars : ℕ}

/-- Integer-square exponent of the unary `θ₃` coordinate. -/
def unaryExponent
    (j : Fin vars) (n : ℤ) :
    DetectorPhase eqs vars → ℤ :=
  fun phase ↦
    n ^ 2 * DetectorCharacterCode.privateCharacter j phase

/-- First private harmonic of the unary `θ₃` coordinate. -/
def unaryFirstExponent
    (j : Fin vars) (n : ℤ) :
    DetectorPhase eqs vars → ℤ :=
  fun phase ↦
    (n ^ 2 - 1) *
      DetectorCharacterCode.privateCharacter j phase

/-- Exponent of one term in `θ₄²`. -/
def rootP4Exponent
    (j : Fin vars) (nm : ℤ × ℤ) :
    DetectorPhase eqs vars → ℤ :=
  fun phase ↦
    (nm.1 ^ 2 + nm.2 ^ 2) *
      DetectorCharacterCode.privateCharacter j phase

/-- Odd square occurring in a `θ₂` term when measured in the fundamental
fourth-root clock. -/
def oddSquare (n : ℤ) : ℤ :=
  (2 * n + 1) ^ 2

/-- The exponent identity
`((2n+1)² - 1)/4 = n(n+1)`. -/
def consecutiveProduct (n : ℤ) : ℤ :=
  n * (n + 1)

/-- Exponent of one term in `θ₂² ζ⁻²`, measured in the private
`Q = ζ⁴` coordinate.  Indeed

```text
 ((2n+1)² + (2m+1)² - 2) / 4
   = n(n+1) + m(m+1).
``` -/
def rootP2Exponent
    (j : Fin vars) (nm : ℤ × ℤ) :
    DetectorPhase eqs vars → ℤ :=
  fun phase ↦
    (consecutiveProduct nm.1 +
      consecutiveProduct nm.2) *
      DetectorCharacterCode.privateCharacter j phase

/-- The Jacobi mean uses the same theta exponent as the arithmetic
detector factor. -/
abbrev jacobiMeanExponent
    (I : DQLSystem eqs vars) (j : Fin vars) (n : ℤ) :
    DetectorPhase eqs vars → ℤ :=
  DetectorFactorizedFourier.thetaCoordinateExponent I j n

/-- Canonical Gaussian coefficient `256^{-n²}`. -/
abbrev thetaCoefficient :=
  CorrectedJacobiSelectorCentering.thetaCoefficient

/-- Coefficient of one `θ₄²` term. -/
def rootP4Coefficient (nm : ℤ × ℤ) : ℂ :=
  (-1 : ℂ) ^ (nm.1.natAbs + nm.2.natAbs) *
    thetaCoefficient nm.1 * thetaCoefficient nm.2

/-- Coefficient of one `θ₂²` term at the canonical height. -/
def rootP2Coefficient (nm : ℤ × ℤ) : ℂ :=
  (((1 / 4 : ℝ) ^
      ((2 * nm.1 + 1).natAbs ^ 2 +
        (2 * nm.2 + 1).natAbs ^ 2) : ℝ) : ℂ)

theorem unaryExponent_eq_zero_iff
    (j : Fin vars) (n : ℤ) :
    unaryExponent (eqs := eqs) j n = 0 ↔
      n = 0 := by
  constructor
  · intro h
    have hj := congrFun h (Sum.inl j)
    change
      n ^ 2 * (if j = j then 1 else 0) = 0 at hj
    simp only [ite_true, mul_one,
      sq_eq_zero_iff] at hj
    exact hj
  · rintro rfl
    funext phase
    change (0 : ℤ) ^ 2 *
      DetectorCharacterCode.privateCharacter j phase = 0
    norm_num

theorem unaryFirstExponent_eq_zero_iff
    (j : Fin vars) (n : ℤ) :
    unaryFirstExponent (eqs := eqs) j n = 0 ↔
      n = 1 ∨ n = -1 := by
  constructor
  · intro h
    have hj := congrFun h (Sum.inl j)
    simp only [unaryFirstExponent,
      DetectorCharacterCode.privateCharacter,
      ite_true, mul_one, Pi.zero_apply] at hj
    exact sq_eq_one_iff.mp (sub_eq_zero.mp hj)
  · rintro (rfl | rfl) <;>
      funext phase <;>
      simp [unaryFirstExponent]

theorem rootP4Exponent_eq_zero_iff
    (j : Fin vars) (nm : ℤ × ℤ) :
    rootP4Exponent (eqs := eqs) j nm = 0 ↔
      nm = (0, 0) := by
  constructor
  · intro h
    have hj := congrFun h (Sum.inl j)
    simp only [rootP4Exponent,
      DetectorCharacterCode.privateCharacter,
      ite_true, mul_one, Pi.zero_apply] at hj
    have hn0 : nm.1 = 0 := by
      nlinarith [sq_nonneg nm.1, sq_nonneg nm.2]
    have hm0 : nm.2 = 0 := by
      nlinarith [sq_nonneg nm.1, sq_nonneg nm.2]
    exact Prod.ext hn0 hm0
  · rintro rfl
    funext phase
    change ((0 : ℤ) ^ 2 + (0 : ℤ) ^ 2) *
      DetectorCharacterCode.privateCharacter j phase = 0
    norm_num

private theorem consecutiveProduct_nonneg (n : ℤ) :
    0 ≤ consecutiveProduct n := by
  unfold consecutiveProduct
  by_cases hn : 0 ≤ n
  · exact mul_nonneg hn (by omega)
  · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)

private theorem consecutiveProduct_eq_zero_iff (n : ℤ) :
    consecutiveProduct n = 0 ↔
      n = 0 ∨ n = -1 := by
  unfold consecutiveProduct
  rw [mul_eq_zero]
  omega

theorem rootP2Exponent_eq_zero_iff
    (j : Fin vars) (nm : ℤ × ℤ) :
    rootP2Exponent (eqs := eqs) j nm = 0 ↔
      (nm.1 = 0 ∨ nm.1 = -1) ∧
        (nm.2 = 0 ∨ nm.2 = -1) := by
  constructor
  · intro h
    have hj := congrFun h (Sum.inl j)
    simp only [rootP2Exponent,
      DetectorCharacterCode.privateCharacter,
      ite_true, mul_one, Pi.zero_apply] at hj
    have hfirst : consecutiveProduct nm.1 = 0 := by
      have h1 := consecutiveProduct_nonneg nm.1
      have h2 := consecutiveProduct_nonneg nm.2
      omega
    have hsecond : consecutiveProduct nm.2 = 0 := by
      have h1 := consecutiveProduct_nonneg nm.1
      have h2 := consecutiveProduct_nonneg nm.2
      omega
    exact
      ⟨(consecutiveProduct_eq_zero_iff nm.1).mp hfirst,
        (consecutiveProduct_eq_zero_iff nm.2).mp hsecond⟩
  · rintro ⟨hn, hm⟩
    have hn0 : consecutiveProduct nm.1 = 0 :=
      (consecutiveProduct_eq_zero_iff nm.1).mpr hn
    have hm0 : consecutiveProduct nm.2 = 0 :=
      (consecutiveProduct_eq_zero_iff nm.2).mpr hm
    funext phase
    simp [rootP2Exponent, hn0, hm0]

theorem jacobiMeanExponent_eq_zero_iff
    (I : DQLSystem eqs vars) (j : Fin vars) (n : ℤ) :
    jacobiMeanExponent I j n = 0 ↔
      n = 0 := by
  constructor
  · intro h
    have hj := congrFun h (Sum.inl j)
    change
      n ^ 2 * (if j = j then 1 else 0) +
          n * 0 = 0 at hj
    simp only [ite_true, mul_one, mul_zero,
      add_zero, sq_eq_zero_iff] at hj
    exact hj
  · rintro rfl
    funext phase
    norm_num [jacobiMeanExponent,
      DetectorFactorizedFourier.thetaCoordinateExponent]

private theorem hasSum_unaryMean_resonant
    (j : Fin vars) :
    HasSum
      (fun n : ℤ ↦
        if unaryExponent (eqs := eqs) j n = 0 then
          thetaCoefficient n
        else 0)
      1 := by
  have hfun :
      (fun n : ℤ ↦
        if unaryExponent (eqs := eqs) j n = 0 then
          thetaCoefficient n
        else 0) =
      fun n : ℤ ↦
        if n = 0 then thetaCoefficient 0 else 0 := by
    funext n
    simp only [unaryExponent_eq_zero_iff]
    split_ifs with h
    · subst n
      rfl
    · rfl
  rw [hfun]
  convert hasSum_ite_eq (0 : ℤ) (thetaCoefficient 0) using 1

private theorem hasSum_unaryFirst_resonant
    (j : Fin vars) :
    HasSum
      (fun n : ℤ ↦
        if unaryFirstExponent (eqs := eqs) j n = 0 then
          thetaCoefficient n
        else 0)
      ((1 / 128 : ℝ) : ℂ) := by
  have hfun :
      (fun n : ℤ ↦
        if unaryFirstExponent (eqs := eqs) j n = 0 then
          thetaCoefficient n
        else 0) =
      fun n : ℤ ↦
        (if n = 1 then thetaCoefficient 1 else 0) +
          (if n = -1 then thetaCoefficient (-1) else 0) := by
    funext n
    simp only [unaryFirstExponent_eq_zero_iff]
    by_cases h1 : n = 1
    · subst n
      simp
    · by_cases hm1 : n = -1
      · subst n
        simp
      · simp [h1, hm1]
  rw [hfun]
  convert
    (hasSum_ite_eq (1 : ℤ) (thetaCoefficient 1)).add
      (hasSum_ite_eq (-1 : ℤ) (thetaCoefficient (-1))) using 1
  norm_num [CorrectedJacobiSelectorCentering.thetaCoefficient]

private theorem hasSum_rootP4_resonant
    (j : Fin vars) :
    HasSum
      (fun nm : ℤ × ℤ ↦
        if rootP4Exponent (eqs := eqs) j nm = 0 then
          rootP4Coefficient nm
        else 0)
      1 := by
  have hfun :
      (fun nm : ℤ × ℤ ↦
        if rootP4Exponent (eqs := eqs) j nm = 0 then
          rootP4Coefficient nm
        else 0) =
      fun nm : ℤ × ℤ ↦
        if nm = (0, 0) then rootP4Coefficient (0, 0) else 0 := by
    funext nm
    simp only [rootP4Exponent_eq_zero_iff]
    split_ifs with h
    · subst nm
      rfl
    · rfl
  rw [hfun]
  convert
    hasSum_ite_eq ((0, 0) : ℤ × ℤ)
      (rootP4Coefficient (0, 0)) using 1
  norm_num [rootP4Coefficient,
    CorrectedJacobiSelectorCentering.thetaCoefficient]

private theorem hasSum_rootP2_resonant
    (j : Fin vars) :
    HasSum
      (fun nm : ℤ × ℤ ↦
        if rootP2Exponent (eqs := eqs) j nm = 0 then
          rootP2Coefficient nm
        else 0)
      ((1 / 4 : ℝ) : ℂ) := by
  let p00 : ℤ × ℤ := (0, 0)
  let p0m : ℤ × ℤ := (0, -1)
  let pm0 : ℤ × ℤ := (-1, 0)
  let pmm : ℤ × ℤ := (-1, -1)
  have hfun :
      (fun nm : ℤ × ℤ ↦
        if rootP2Exponent (eqs := eqs) j nm = 0 then
          rootP2Coefficient nm
        else 0) =
      fun nm : ℤ × ℤ ↦
        (if nm = p00 then rootP2Coefficient p00 else 0) +
        (if nm = p0m then rootP2Coefficient p0m else 0) +
        (if nm = pm0 then rootP2Coefficient pm0 else 0) +
        (if nm = pmm then rootP2Coefficient pmm else 0) := by
    funext nm
    simp only [rootP2Exponent_eq_zero_iff]
    rcases nm with ⟨n, m⟩
    dsimp only at *
    by_cases hn0 : n = 0
    · subst n
      by_cases hm0 : m = 0
      · subst m
        simp [p00, p0m, pm0, pmm]
      · by_cases hmm : m = -1
        · subst m
          simp [p00, p0m, pm0, pmm]
        · simp [p00, p0m, pm0, pmm, hm0, hmm]
    · by_cases hnm : n = -1
      · subst n
        by_cases hm0 : m = 0
        · subst m
          simp [p00, p0m, pm0, pmm]
        · by_cases hmm : m = -1
          · subst m
            simp [p00, p0m, pm0, pmm]
          · simp [p00, p0m, pm0, pmm, hm0, hmm]
      · simp [p00, p0m, pm0, pmm, hn0, hnm]
  rw [hfun]
  have h00 :=
    hasSum_ite_eq p00 (rootP2Coefficient p00)
  have h0m :=
    hasSum_ite_eq p0m (rootP2Coefficient p0m)
  have hm0 :=
    hasSum_ite_eq pm0 (rootP2Coefficient pm0)
  have hmm :=
    hasSum_ite_eq pmm (rootP2Coefficient pmm)
  convert (((h00.add h0m).add hm0).add hmm) using 1
  norm_num [p00, p0m, pm0, pmm, rootP2Coefficient]

private theorem hasSum_jacobiMean_resonant
    (I : DQLSystem eqs vars) (j : Fin vars) :
    HasSum
      (fun n : ℤ ↦
        if jacobiMeanExponent I j n = 0 then
          thetaCoefficient n
        else 0)
      1 := by
  have hfun :
      (fun n : ℤ ↦
        if jacobiMeanExponent I j n = 0 then
          thetaCoefficient n
        else 0) =
      fun n : ℤ ↦
        if n = 0 then thetaCoefficient 0 else 0 := by
    funext n
    simp only [jacobiMeanExponent_eq_zero_iff]
    split_ifs with h
    · subst n
      rfl
    · rfl
  rw [hfun]
  convert hasSum_ite_eq (0 : ℤ) (thetaCoefficient 0) using 1

/-- Aggregate zero-mode cancellation for `Y - 1`. -/
theorem aggregate_unaryMean_zero
    (j : Fin vars) :
    Analysis.aggregateFourierCoefficient
        (Analysis.centeredFourierCoefficient
          1 thetaCoefficient)
        (Analysis.centeredFourierExponent
          (unaryExponent (eqs := eqs) j)) 0 = 0 :=
  Analysis.aggregate_centeredFourierCoefficient_zero
    1 thetaCoefficient
    (unaryExponent (eqs := eqs) j)
    (hasSum_unaryMean_resonant j)

/-- Aggregate zero-mode cancellation for `Y Q⁻¹ - 1/128`. -/
theorem aggregate_unaryFirst_zero
    (j : Fin vars) :
    Analysis.aggregateFourierCoefficient
        (Analysis.centeredFourierCoefficient
          (((1 / 128 : ℝ) : ℂ)) thetaCoefficient)
        (Analysis.centeredFourierExponent
          (unaryFirstExponent (eqs := eqs) j)) 0 = 0 :=
  Analysis.aggregate_centeredFourierCoefficient_zero
    (((1 / 128 : ℝ) : ℂ)) thetaCoefficient
    (unaryFirstExponent (eqs := eqs) j)
    (hasSum_unaryFirst_resonant j)

/-- Aggregate zero-mode cancellation for `p₄ - 1`. -/
theorem aggregate_rootP4Mean_zero
    (j : Fin vars) :
    Analysis.aggregateFourierCoefficient
        (Analysis.centeredFourierCoefficient
          1 rootP4Coefficient)
        (Analysis.centeredFourierExponent
          (rootP4Exponent (eqs := eqs) j)) 0 = 0 :=
  Analysis.aggregate_centeredFourierCoefficient_zero
    1 rootP4Coefficient
    (rootP4Exponent (eqs := eqs) j)
    (hasSum_rootP4_resonant j)

/-- Aggregate zero-mode cancellation for `p₂ ζ⁻² - 1/4`. -/
theorem aggregate_rootP2Mean_zero
    (j : Fin vars) :
    Analysis.aggregateFourierCoefficient
        (Analysis.centeredFourierCoefficient
          (((1 / 4 : ℝ) : ℂ)) rootP2Coefficient)
        (Analysis.centeredFourierExponent
          (rootP2Exponent (eqs := eqs) j)) 0 = 0 :=
  Analysis.aggregate_centeredFourierCoefficient_zero
    (((1 / 4 : ℝ) : ℂ)) rootP2Coefficient
    (rootP2Exponent (eqs := eqs) j)
    (hasSum_rootP2_resonant j)

/-- Aggregate zero-mode cancellation for `F - 1`. -/
theorem aggregate_jacobiMean_zero
    (I : DQLSystem eqs vars) (j : Fin vars) :
    Analysis.aggregateFourierCoefficient
        (Analysis.centeredFourierCoefficient
          1 thetaCoefficient)
        (Analysis.centeredFourierExponent
          (jacobiMeanExponent I j)) 0 = 0 :=
  Analysis.aggregate_centeredFourierCoefficient_zero
    1 thetaCoefficient
    (jacobiMeanExponent I j)
    (hasSum_jacobiMean_resonant I j)

end HGAS.CanonicalSelectorMomentZeroModes
