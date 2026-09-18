import HGAS.Analysis.FourierExponentAggregation
import HGAS.Arithmetic.DetectorFactorizedFourier
import HGAS.Arithmetic.FixedDetectorMomentCode
import Mathlib.Tactic

/-!
# Correct centering of the two Jacobi selector harmonics

## Status in the completed reduction

This coefficient-aggregation module remains live.  The completed endpoint,
however, first applies the nonzero-column augmentation, so every selected
column uses the `1/256` branch.  The `1/128` zero-column branch is retained
for the older unaugmented analysis and does not by itself repair the
general `ρ = 0` three-moment collision.

The original fixed-detector code subtracts `1/256` from each of

```text
                 F (Q V)⁻¹,       F Q⁻¹ V.
```

That is correct when the linear DQL character `V` is nontrivial.  It is
not correct when its whole column is zero.  Indeed the theta expansion

```text
             F = Σₙ 256^(-n²) Q^(n²) V^n
```

has the following zero-frequency terms after twisting:

* in `F (QV)⁻¹`, `n = 1` always resonates, and `n = -1` also resonates
  exactly when `V = 1`;
* in `F Q⁻¹V`, `n = -1` always resonates, and `n = 1` also resonates
  exactly when `V = 1`.

Thus the correct center is `1/256` for a nonzero linear column and
`2/256 = 1/128` for a zero column.  Zero linear columns genuinely occur
in the fixed DQL compiler: the auxiliary variables in the four-square
rows enter quadratically but not linearly.

This module records the correction without modifying the previously saved
compiler files.  It proves the exact resonance classifications and,
using canonical exponent aggregation, proves that both corrected centered
families have aggregate coefficient zero at exponent zero.
-/

noncomputable section

open scoped BigOperators

namespace HGAS

namespace CorrectedJacobiSelectorCentering

variable {eqs vars : ℕ}

/-- Exponent of the `n`th theta term after multiplication by
`(Q_j V_j)⁻¹`. -/
def plusExponent
    (I : DQLSystem eqs vars) (j : Fin vars) (n : ℤ) :
    DetectorPhase eqs vars → ℤ :=
  fun phase ↦
    DetectorFactorizedFourier.thetaCoordinateExponent I j n phase -
      DetectorCharacterCode.privateCharacter j phase -
      DetectorCharacterCode.linearCharacter I j phase

/-- Exponent of the `n`th theta term after multiplication by
`Q_j⁻¹ V_j`. -/
def minusExponent
    (I : DQLSystem eqs vars) (j : Fin vars) (n : ℤ) :
    DetectorPhase eqs vars → ℤ :=
  fun phase ↦
    DetectorFactorizedFourier.thetaCoordinateExponent I j n phase -
      DetectorCharacterCode.privateCharacter j phase +
      DetectorCharacterCode.linearCharacter I j phase

/-- Exact resonance classification for the positive selector harmonic. -/
theorem plusExponent_eq_zero_iff
    (I : DQLSystem eqs vars) (j : Fin vars) (n : ℤ) :
    plusExponent I j n = 0 ↔
      n = 1 ∨
        (n = -1 ∧
          DetectorCharacterCode.linearCharacter I j = 0) := by
  constructor
  · intro h
    have hj := congrFun h (Sum.inl j)
    simp only [plusExponent,
        DetectorFactorizedFourier.thetaCoordinateExponent,
        DetectorCharacterCode.privateCharacter,
        DetectorCharacterCode.linearCharacter,
        ite_true, mul_one, mul_zero, add_zero,
        sub_zero, Pi.zero_apply] at hj
    have hnSq : n ^ 2 = 1 :=
      sub_eq_zero.mp hj
    rcases (sq_eq_one_iff.mp hnSq) with hn | hn
    · exact Or.inl hn
    · right
      refine ⟨hn, ?_⟩
      funext phase
      change
        DetectorCharacterCode.linearCharacter I j phase = (0 : ℤ)
      have hphase := congrFun h phase
      change plusExponent I j n phase = (0 : ℤ) at hphase
      rw [hn] at hphase
      simp only [plusExponent,
        DetectorFactorizedFourier.thetaCoordinateExponent,
        neg_sq, one_mul, neg_mul] at hphase
      omega
  · rintro (rfl | ⟨rfl, hlinear⟩)
    · funext phase
      simp [plusExponent,
        DetectorFactorizedFourier.thetaCoordinateExponent]
    · funext phase
      have hphase := congrFun hlinear phase
      simp only [Pi.zero_apply] at hphase
      simp [plusExponent,
        DetectorFactorizedFourier.thetaCoordinateExponent,
        hphase]

/-- Exact resonance classification for the negative selector harmonic. -/
theorem minusExponent_eq_zero_iff
    (I : DQLSystem eqs vars) (j : Fin vars) (n : ℤ) :
    minusExponent I j n = 0 ↔
      n = -1 ∨
        (n = 1 ∧
          DetectorCharacterCode.linearCharacter I j = 0) := by
  constructor
  · intro h
    have hj := congrFun h (Sum.inl j)
    simp only [minusExponent,
        DetectorFactorizedFourier.thetaCoordinateExponent,
        DetectorCharacterCode.privateCharacter,
        DetectorCharacterCode.linearCharacter,
        ite_true, mul_one, mul_zero, add_zero,
        Pi.zero_apply] at hj
    have hnSq : n ^ 2 = 1 :=
      sub_eq_zero.mp hj
    rcases (sq_eq_one_iff.mp hnSq) with hn | hn
    · right
      refine ⟨hn, ?_⟩
      funext phase
      change
        DetectorCharacterCode.linearCharacter I j phase = (0 : ℤ)
      have hphase := congrFun h phase
      change minusExponent I j n phase = (0 : ℤ) at hphase
      rw [hn] at hphase
      simp only [minusExponent,
        DetectorFactorizedFourier.thetaCoordinateExponent,
        one_pow, one_mul] at hphase
      omega
    · exact Or.inl hn
  · rintro (rfl | ⟨rfl, hlinear⟩)
    · funext phase
      simp [minusExponent,
        DetectorFactorizedFourier.thetaCoordinateExponent]
    · funext phase
      have hphase := congrFun hlinear phase
      simp only [Pi.zero_apply] at hphase
      simp [minusExponent,
        DetectorFactorizedFourier.thetaCoordinateExponent,
        hphase]

/-- Correct rational center of either Jacobi selector harmonic. -/
def selectorCenter
    (I : DQLSystem eqs vars) (j : Fin vars) : ℚ :=
  if DetectorCharacterCode.linearCharacter I j = 0 then
    1 / 128
  else
    1 / 256

theorem selectorCenter_eq_of_linearCharacter_eq_zero
    (I : DQLSystem eqs vars) (j : Fin vars)
    (hlinear :
      DetectorCharacterCode.linearCharacter I j = 0) :
    selectorCenter I j = 1 / 128 := by
  simp [selectorCenter, hlinear]

theorem selectorCenter_eq_of_linearCharacter_ne_zero
    (I : DQLSystem eqs vars) (j : Fin vars)
    (hlinear :
      DetectorCharacterCode.linearCharacter I j ≠ 0) :
    selectorCenter I j = 1 / 256 := by
  simp [selectorCenter, hlinear]

/-- One constant centering term together with the integer theta series. -/
abbrev CenteredThetaIndex :=
  Unit ⊕ ℤ

/-- Gaussian theta coefficient at the canonical height. -/
def thetaCoefficient (n : ℤ) : ℂ :=
  (((1 / 256 : ℝ) ^ (n.natAbs ^ 2) : ℝ) : ℂ)

/-- Raw coefficients of either corrected centered selector harmonic. -/
def centeredCoefficient
    (I : DQLSystem eqs vars) (j : Fin vars) :
    CenteredThetaIndex → ℂ
  | Sum.inl _ => -((selectorCenter I j : ℚ) : ℂ)
  | Sum.inr n => thetaCoefficient n

/-- Raw exponents of the corrected positive selector harmonic. -/
def centeredPlusExponent
    (I : DQLSystem eqs vars) (j : Fin vars) :
    CenteredThetaIndex → DetectorPhase eqs vars → ℤ
  | Sum.inl _ => 0
  | Sum.inr n => plusExponent I j n

/-- Raw exponents of the corrected negative selector harmonic. -/
def centeredMinusExponent
    (I : DQLSystem eqs vars) (j : Fin vars) :
    CenteredThetaIndex → DetectorPhase eqs vars → ℤ
  | Sum.inl _ => 0
  | Sum.inr n => minusExponent I j n

private theorem hasSum_centered_left
    (I : DQLSystem eqs vars) (j : Fin vars)
    (exponent :
      CenteredThetaIndex → DetectorPhase eqs vars → ℤ)
    (hexponent : exponent (Sum.inl ()) = 0) :
    HasSum
      (fun u : Unit ↦
        if exponent (Sum.inl u) = 0 then
          centeredCoefficient I j (Sum.inl u)
        else 0)
      (-((selectorCenter I j : ℚ) : ℂ)) := by
  convert
    hasSum_fintype
      (fun u : Unit ↦
        if exponent (Sum.inl u) = 0 then
          centeredCoefficient I j (Sum.inl u)
        else 0) using 1
  simp [hexponent, centeredCoefficient]

private theorem hasSum_plus_right
    (I : DQLSystem eqs vars) (j : Fin vars) :
    HasSum
      (fun n : ℤ ↦
        if centeredPlusExponent I j (Sum.inr n) = 0 then
          centeredCoefficient I j (Sum.inr n)
        else 0)
      (((selectorCenter I j : ℚ) : ℂ)) := by
  by_cases hlinear :
      DetectorCharacterCode.linearCharacter I j = 0
  · rw [selectorCenter_eq_of_linearCharacter_eq_zero I j hlinear]
    have hresonant :
        (fun n : ℤ ↦
          if centeredPlusExponent I j (Sum.inr n) = 0 then
            centeredCoefficient I j (Sum.inr n)
          else 0) =
        fun n : ℤ ↦
          (if n = 1 then thetaCoefficient 1 else 0) +
            (if n = -1 then thetaCoefficient (-1) else 0) := by
      funext n
      simp only [centeredPlusExponent, centeredCoefficient,
        plusExponent_eq_zero_iff, hlinear, and_true]
      by_cases h1 : n = 1
      · subst n
        simp
      · by_cases hm1 : n = -1
        · subst n
          simp
        · simp [h1, hm1]
    rw [hresonant]
    convert
      (hasSum_ite_eq (1 : ℤ) (thetaCoefficient 1)).add
        (hasSum_ite_eq (-1 : ℤ) (thetaCoefficient (-1))) using 1
    norm_num [thetaCoefficient]
  · rw [selectorCenter_eq_of_linearCharacter_ne_zero I j hlinear]
    have hresonant :
        (fun n : ℤ ↦
          if centeredPlusExponent I j (Sum.inr n) = 0 then
            centeredCoefficient I j (Sum.inr n)
          else 0) =
        fun n : ℤ ↦
          if n = 1 then thetaCoefficient 1 else 0 := by
      funext n
      by_cases h1 : n = 1
      · subst n
        simp [centeredPlusExponent, centeredCoefficient,
          plusExponent_eq_zero_iff, hlinear]
      · simp [centeredPlusExponent,
          plusExponent_eq_zero_iff, hlinear, h1]
    rw [hresonant]
    convert
      hasSum_ite_eq (1 : ℤ) (thetaCoefficient 1) using 1
    norm_num [thetaCoefficient]

private theorem hasSum_minus_right
    (I : DQLSystem eqs vars) (j : Fin vars) :
    HasSum
      (fun n : ℤ ↦
        if centeredMinusExponent I j (Sum.inr n) = 0 then
          centeredCoefficient I j (Sum.inr n)
        else 0)
      (((selectorCenter I j : ℚ) : ℂ)) := by
  by_cases hlinear :
      DetectorCharacterCode.linearCharacter I j = 0
  · rw [selectorCenter_eq_of_linearCharacter_eq_zero I j hlinear]
    have hresonant :
        (fun n : ℤ ↦
          if centeredMinusExponent I j (Sum.inr n) = 0 then
            centeredCoefficient I j (Sum.inr n)
          else 0) =
        fun n : ℤ ↦
          (if n = -1 then thetaCoefficient (-1) else 0) +
            (if n = 1 then thetaCoefficient 1 else 0) := by
      funext n
      simp only [centeredMinusExponent, centeredCoefficient,
        minusExponent_eq_zero_iff, hlinear, and_true]
      by_cases hm1 : n = -1
      · subst n
        simp
      · by_cases h1 : n = 1
        · subst n
          simp
        · simp [h1, hm1]
    rw [hresonant]
    convert
      (hasSum_ite_eq (-1 : ℤ) (thetaCoefficient (-1))).add
        (hasSum_ite_eq (1 : ℤ) (thetaCoefficient 1)) using 1
    norm_num [thetaCoefficient]
  · rw [selectorCenter_eq_of_linearCharacter_ne_zero I j hlinear]
    have hresonant :
        (fun n : ℤ ↦
          if centeredMinusExponent I j (Sum.inr n) = 0 then
            centeredCoefficient I j (Sum.inr n)
          else 0) =
        fun n : ℤ ↦
          if n = -1 then thetaCoefficient (-1) else 0 := by
      funext n
      by_cases hm1 : n = -1
      · subst n
        simp [centeredMinusExponent, centeredCoefficient,
          minusExponent_eq_zero_iff, hlinear]
      · simp [centeredMinusExponent,
          minusExponent_eq_zero_iff, hlinear, hm1]
    rw [hresonant]
    convert
      hasSum_ite_eq (-1 : ℤ) (thetaCoefficient (-1)) using 1
    norm_num [thetaCoefficient]

/-- The corrected positive selector has zero collected coefficient at
exponent zero. -/
theorem aggregate_centeredPlusCoefficient_zero
    (I : DQLSystem eqs vars) (j : Fin vars) :
    Analysis.aggregateFourierCoefficient
        (centeredCoefficient I j)
        (centeredPlusExponent I j) 0 = 0 := by
  classical
  have hleft :=
    hasSum_centered_left I j (centeredPlusExponent I j) rfl
  have hright := hasSum_plus_right I j
  let zeroFiber : Set CenteredThetaIndex :=
    {i | centeredPlusExponent I j i = 0}
  have hleftIndicator :
      HasSum
        (fun u : Unit ↦
          zeroFiber.indicator (centeredCoefficient I j)
            (Sum.inl u))
        (-((selectorCenter I j : ℚ) : ℂ)) := by
    apply hleft.congr
    intro s
    apply Finset.sum_congr rfl
    intro u _
    simp only [zeroFiber, Set.indicator,
      Set.mem_setOf_eq]
    by_cases hu :
        centeredPlusExponent I j (Sum.inl u) = 0 <;>
      simp [hu]
  have hrightIndicator :
      HasSum
        (fun n : ℤ ↦
          zeroFiber.indicator (centeredCoefficient I j)
            (Sum.inr n))
        (((selectorCenter I j : ℚ) : ℂ)) := by
    apply hright.congr
    intro s
    apply Finset.sum_congr rfl
    intro n _
    simp only [zeroFiber, Set.indicator,
      Set.mem_setOf_eq]
    by_cases hn :
        centeredPlusExponent I j (Sum.inr n) = 0 <;>
      simp [hn]
  have htotal :
      HasSum
        (zeroFiber.indicator (centeredCoefficient I j))
        (-((selectorCenter I j : ℚ) : ℂ) +
          ((selectorCenter I j : ℚ) : ℂ)) :=
    HasSum.sum
      (f := zeroFiber.indicator (centeredCoefficient I j))
      hleftIndicator hrightIndicator
  calc
    Analysis.aggregateFourierCoefficient
        (centeredCoefficient I j)
        (centeredPlusExponent I j) 0 =
      ∑' i : CenteredThetaIndex,
        zeroFiber.indicator (centeredCoefficient I j) i :=
      tsum_subtype zeroFiber (centeredCoefficient I j)
    _ =
        -((selectorCenter I j : ℚ) : ℂ) +
          ((selectorCenter I j : ℚ) : ℂ) :=
      htotal.tsum_eq
    _ = 0 := by ring

/-- The corrected negative selector has zero collected coefficient at
exponent zero. -/
theorem aggregate_centeredMinusCoefficient_zero
    (I : DQLSystem eqs vars) (j : Fin vars) :
    Analysis.aggregateFourierCoefficient
        (centeredCoefficient I j)
        (centeredMinusExponent I j) 0 = 0 := by
  classical
  have hleft :=
    hasSum_centered_left I j (centeredMinusExponent I j) rfl
  have hright := hasSum_minus_right I j
  let zeroFiber : Set CenteredThetaIndex :=
    {i | centeredMinusExponent I j i = 0}
  have hleftIndicator :
      HasSum
        (fun u : Unit ↦
          zeroFiber.indicator (centeredCoefficient I j)
            (Sum.inl u))
        (-((selectorCenter I j : ℚ) : ℂ)) := by
    apply hleft.congr
    intro s
    apply Finset.sum_congr rfl
    intro u _
    simp only [zeroFiber, Set.indicator,
      Set.mem_setOf_eq]
    by_cases hu :
        centeredMinusExponent I j (Sum.inl u) = 0 <;>
      simp [hu]
  have hrightIndicator :
      HasSum
        (fun n : ℤ ↦
          zeroFiber.indicator (centeredCoefficient I j)
            (Sum.inr n))
        (((selectorCenter I j : ℚ) : ℂ)) := by
    apply hright.congr
    intro s
    apply Finset.sum_congr rfl
    intro n _
    simp only [zeroFiber, Set.indicator,
      Set.mem_setOf_eq]
    by_cases hn :
        centeredMinusExponent I j (Sum.inr n) = 0 <;>
      simp [hn]
  have htotal :
      HasSum
        (zeroFiber.indicator (centeredCoefficient I j))
        (-((selectorCenter I j : ℚ) : ℂ) +
          ((selectorCenter I j : ℚ) : ℂ)) :=
    HasSum.sum
      (f := zeroFiber.indicator (centeredCoefficient I j))
      hleftIndicator hrightIndicator
  calc
    Analysis.aggregateFourierCoefficient
        (centeredCoefficient I j)
        (centeredMinusExponent I j) 0 =
      ∑' i : CenteredThetaIndex,
        zeroFiber.indicator (centeredCoefficient I j) i :=
      tsum_subtype zeroFiber (centeredCoefficient I j)
    _ =
        -((selectorCenter I j : ℚ) : ℂ) +
          ((selectorCenter I j : ℚ) : ℂ) :=
      htotal.tsum_eq
    _ = 0 := by ring

end CorrectedJacobiSelectorCentering

end HGAS
