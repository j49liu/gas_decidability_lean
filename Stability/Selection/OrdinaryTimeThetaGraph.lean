import Stability.Selection.OrdinaryTimeWeightedFourier
import Stability.Analysis.ShiftedThetaBounds
import HGAS.Arithmetic.CanonicalFixedDetectorFundamentalPhase

/-!
# Weighted theta and character coordinates on the intended torus graph

Section 8, Lemma `graph`, uses the fundamental clock angles, not their
fourth powers. The exponent below therefore includes the gauge-root
shift. Section 9, Lemma `bounds`, weights its actual Haar coefficients.
-/

noncomputable section

open scoped BigOperators

namespace Stability.Selection

open HGAS HGAS.Analysis HGAS.Modular
open CanonicalFixedDetectorTrajectory CanonicalFixedDetectorFundamentalPhase

variable {eqs vars : ℕ}

/-- Fundamental-clock exponent of the half-period `T₁` theta term. -/
def halfPeriodThetaExponent (I : DQLSystem eqs vars) (j : Fin vars) (n : ℤ) :
    Fin (vars + eqs) → ℤ :=
  DetectorCharacterCode.flattenCharacter
      (DetectorFactorizedFourier.thetaCoordinateExponent I j n) - gaugeRootExponent I j

/-- The literal half-period theta coordinate as a periodic function of
the fundamental clock phases. Its coefficient at `n = 0` is `4`. -/
def halfPeriodThetaGraph (I : DQLSystem eqs vars) (j : Fin vars) :
    UnitAddTorus (Fin (vars + eqs)) → ℂ :=
  torusFourierSeries (fun n : ℤ ↦ (4 : ℂ) * ((1 / 256 : ℝ) ^ (n.natAbs ^ 2) : ℝ))
    (halfPeriodThetaExponent I j)

private theorem thetaCoefficient_summable :
    Summable fun n : ℤ ↦ ‖(4 : ℂ) * ((1 / 256 : ℝ) ^ (n.natAbs ^ 2) : ℝ)‖ := by
  have h := (summable_gaussianIntWeight (by norm_num : (0 : ℝ) ≤ 1 / 256)
    (by norm_num : (1 / 256 : ℝ) < 1)).mul_left 4
  simpa [gaussianIntWeight, norm_mul, Complex.norm_real, abs_of_nonneg (by positivity :
    ∀ n : ℤ, 0 ≤ (1 / 256 : ℝ) ^ (n.natAbs ^ 2))] using h

theorem continuous_halfPeriodThetaGraph (I : DQLSystem eqs vars) (j : Fin vars) :
    Continuous (halfPeriodThetaGraph I j) :=
  continuous_torusFourierSeries _ _ thetaCoefficient_summable

/-- Multiplication by the literal gauge root recovers the centered
Gaussian theta output at every phase. -/
theorem gauge_mul_halfPeriodThetaGraph (I : DQLSystem eqs vars) (j : Fin vars)
    (x : UnitAddTorus (Fin (vars + eqs))) :
    (1 / 4 : ℂ) * UnitAddTorus.mFourier (gaugeRootExponent I j) x *
        halfPeriodThetaGraph I j x =
      torusFourierSeries (fun n : ℤ ↦ (((1 / 256 : ℝ) ^ (n.natAbs ^ 2) : ℝ) : ℂ))
        (fun n ↦ DetectorCharacterCode.flattenCharacter
          (DetectorFactorizedFourier.thetaCoordinateExponent I j n)) x := by
  unfold halfPeriodThetaGraph torusFourierSeries
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  unfold torusSeriesTerm
  dsimp only
  have he : gaugeRootExponent I j + halfPeriodThetaExponent I j n =
      DetectorCharacterCode.flattenCharacter
        (DetectorFactorizedFourier.thetaCoordinateExponent I j n) := by
    unfold halfPeriodThetaExponent
    abel
  rw [← he, UnitAddTorus.mFourier_add]
  ring

private theorem mFourier_realPhase (a : Fin (vars + eqs) → ℤ)
    (x : Fin (vars + eqs) → ℝ) :
    UnitAddTorus.mFourier a (fun i ↦ (x i : UnitAddCircle)) =
      Complex.exp (2 * Real.pi * Complex.I * (∑ i, (a i : ℝ) * x i)) := by
  have h := Clocks.RadicalClock.mFourier_torusDisplacement a x 1
  have hphase : Clocks.RadicalClock.torusDisplacement x 1 =
      fun i ↦ (x i : UnitAddCircle) := by
    funext i
    change (((1 : ℝ) * x i : ℝ) : UnitAddCircle) = _
    rw [one_mul]
  rw [hphase] at h
  simpa only [Clocks.RadicalClock.frequencyPairing, Complex.ofReal_one, one_mul] using h

private theorem thetaPairing (I : DQLSystem eqs vars) (j : Fin vars) (n : ℤ)
    (x : Fin (vars + eqs) → ℝ) :
    (∑ i, (DetectorCharacterCode.flattenCharacter
      (DetectorFactorizedFourier.thetaCoordinateExponent I j n) i : ℝ) * x i) =
      4 * (n : ℝ) ^ 2 * x (finSumFinEquiv (Sum.inl j)) +
        4 * (n : ℝ) * ∑ row, (I.linear row j : ℝ) * x (finSumFinEquiv (Sum.inr row)) := by
  classical
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [DetectorCharacterCode.flattenCharacter, Equiv.symm_apply_apply,
    DetectorFactorizedFourier.thetaCoordinateExponent,
    DetectorCharacterCode.privateCharacter, DetectorCharacterCode.linearCharacter]
  push_cast
  simp only [mul_zero, add_zero, zero_add]
  rw [Finset.mul_sum]
  congr 1
  · simp
  · apply Finset.sum_congr rfl
    intro row _
    ring

private theorem gaugePairing (I : DQLSystem eqs vars) (j : Fin vars)
    (x : Fin (vars + eqs) → ℝ) :
    (∑ i, (gaugeRootExponent I j i : ℝ) * x i) =
      x (finSumFinEquiv (Sum.inl j)) +
        2 * ∑ row, (I.linear row j : ℝ) * x (finSumFinEquiv (Sum.inr row)) := by
  classical
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [gaugeRootExponent, Equiv.symm_apply_apply,
    DetectorJacobiGaugeData.gaugeCharacter, DetectorCharacterCode.privateCharacter,
    DetectorCharacterCode.linearCharacter]
  push_cast
  simp [Finset.mul_sum, mul_assoc]

/-- On every real lift of the torus, this is exactly the manuscript's
Jacobi theta value at `z + (1 + τ)/2`, with `τ = iY + 8xⱼ` and
`z = 4 Σ Bₗⱼ xₗ`. Thus the periodic series defines a literal coordinate
of the intended graph, not only an observable on one orbit. -/
theorem halfPeriodThetaGraph_eq_jacobiTheta1
    (I : DQLSystem eqs vars) (j : Fin vars) (x : Fin (vars + eqs) → ℝ) :
    let τ : ℂ := thetaGaugeBasePoint + 8 * (x (finSumFinEquiv (Sum.inl j)) : ℂ)
    let z : ℂ := 4 * ((∑ row, (I.linear row j : ℝ) *
      x (finSumFinEquiv (Sum.inr row)) : ℝ) : ℂ)
    halfPeriodThetaGraph I j (fun i ↦ (x i : UnitAddCircle)) =
      jacobiTheta1 (z + (1 + τ) / 2) τ := by
  dsimp only
  let u := x (finSumFinEquiv (Sum.inl j))
  let v := ∑ row, (I.linear row j : ℝ) * x (finSumFinEquiv (Sum.inr row))
  let τ : ℂ := thetaGaugeBasePoint + 8 * (u : ℂ)
  let z : ℂ := 4 * (v : ℂ)
  change halfPeriodThetaGraph I j (fun i ↦ (x i : UnitAddCircle)) =
    jacobiTheta1 (z + (1 + τ) / 2) τ
  have ht : torusFourierSeries
      (fun n : ℤ ↦ (((1 / 256 : ℝ) ^ (n.natAbs ^ 2) : ℝ) : ℂ))
      (fun n ↦ DetectorCharacterCode.flattenCharacter
        (DetectorFactorizedFourier.thetaCoordinateExponent I j n))
      (fun i ↦ (x i : UnitAddCircle)) = jacobiTheta3 z τ := by
    unfold torusFourierSeries jacobiTheta3 jacobiTheta₂
    apply tsum_congr
    intro n
    rw [torusSeriesTerm, mFourier_realPhase, thetaPairing]
    unfold jacobiTheta₂_term
    rw [show 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z +
        (Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * τ =
        (((-Real.pi * thetaGaugeHeight * (n : ℝ) ^ 2 : ℝ) : ℂ)) +
          2 * Real.pi * Complex.I * (4 * (n : ℝ) ^ 2 * u + 4 * (n : ℝ) * v) by
      dsimp [z, τ, thetaGaugeBasePoint]
      push_cast
      ring_nf
      simp only [Complex.I_sq]
      ring]
    rw [Complex.exp_add, ← Complex.ofReal_exp,
      CanonicalFixedDetectorFourierCrosswalk.gaussianWeight_thetaGaugeHeight]
    dsimp [u, v]
    push_cast
    rfl
  have hg : (1 / 4 : ℂ) * UnitAddTorus.mFourier (gaugeRootExponent I j)
      (fun i ↦ (x i : UnitAddCircle)) =
        Complex.exp (Real.pi * Complex.I * (z + τ / 4)) := by
    rw [mFourier_realPhase, gaugePairing]
    rw [show (Real.pi : ℂ) * Complex.I * (z + τ / 4) =
        (((-Real.pi * thetaGaugeHeight / 4 : ℝ) : ℂ)) +
          2 * Real.pi * Complex.I * ((u + 2 * v : ℝ) : ℂ) by
      dsimp [z, τ, thetaGaugeBasePoint]
      push_cast
      ring_nf
      simp only [Complex.I_sq]
      ring]
    rw [Complex.exp_add, ← Complex.ofReal_exp, exp_neg_pi_mul_thetaGaugeHeight_div_four]
    norm_num [u, v]
  apply mul_left_cancel₀ (Complex.exp_ne_zero (Real.pi * Complex.I * (z + τ / 4)))
  rw [← hg, gauge_mul_halfPeriodThetaGraph, ht, jacobiTheta3_eq_halfPeriod_jacobiTheta1, hg]

/-- The exact exponent length retains the possibly negative shifted
quadratic `4 n² - 1`. -/
theorem halfPeriodThetaExponent_length (I : DQLSystem eqs vars) (j : Fin vars)
    (n : ℤ) :
    (∑ i, |(halfPeriodThetaExponent I j n i : ℝ)|) =
      |4 * (n : ℝ) ^ 2 - 1| +
        |4 * (n : ℝ) - 2| * ∑ row, |(I.linear row j : ℝ)| := by
  classical
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [halfPeriodThetaExponent, Pi.sub_apply,
    DetectorCharacterCode.flattenCharacter, gaugeRootExponent,
    Equiv.symm_apply_apply, DetectorFactorizedFourier.thetaCoordinateExponent,
    DetectorJacobiGaugeData.gaugeCharacter, DetectorCharacterCode.privateCharacter,
    DetectorCharacterCode.linearCharacter]
  push_cast
  simp only [mul_zero, add_zero, zero_add]
  have hprivate : (∑ k : Fin vars,
      |4 * ((n : ℝ) ^ 2 * (if k = j then 1 else 0)) -
        (if k = j then 1 else 0)|) = |4 * (n : ℝ) ^ 2 - 1| := by
    calc
      _ = ∑ k : Fin vars, if k = j then |4 * (n : ℝ) ^ 2 - 1| else 0 := by
        apply Finset.sum_congr rfl
        intro k _
        split_ifs <;> simp_all
      _ = _ := by simp
  rw [hprivate, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro row _
  rw [← abs_mul]
  congr 1
  ring

/-- Gaussian decay controls the genuine weighted Fourier coefficients
of this coordinate. No nonnegativity of the shifted quadratic is used. -/
theorem summable_weighted_halfPeriodThetaGraph
    (I : DQLSystem eqs vars) (j : Fin vars) {ρ : ℝ}
    (hρ : 1 ≤ ρ) (hdecay : (1 / 256 : ℝ) * ρ ^ (4 : ℝ) < 1) :
    Summable fun a : Fin (vars + eqs) → ℤ ↦
      ‖UnitAddTorus.mFourierCoeff (halfPeriodThetaGraph I j) a‖ *
        ρ ^ (∑ i, |(a i : ℝ)|) := by
  apply summable_weighted_fourierCoeff_of_expansion _ _ _
    (fun _ ↦ Real.rpow_nonneg (zero_lt_one.trans_le hρ).le _) thetaCoefficient_summable
  let D : ℝ := ∑ row, |(I.linear row j : ℝ)|
  have hD : 0 ≤ D := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have h := Stability.Analysis.ShiftedThetaBounds.summable_weighted_quadratic
    (by norm_num : (0 : ℝ) < 1 / 256) hρ
    (a := 1) (A := 4) (by norm_num) (by norm_num) hdecay 0 0 (4 * D) (1 + 2 * D) 0
  apply (h.mul_left 2).of_nonneg_of_le
  · intro n
    positivity
  · intro n
    have hn : ((n.natAbs ^ 2 : ℕ) : ℝ) = (n : ℝ) ^ 2 := by
      have hnZ : n ^ 2 = (n.natAbs ^ 2 : ℕ) := by
        rw [Nat.cast_pow, Int.natAbs_sq]
      calc
        _ = ((n ^ 2 : ℤ) : ℝ) := by
          simpa only [Int.cast_natCast] using
            congrArg (fun z : ℤ ↦ (z : ℝ)) hnZ.symm
        _ = _ := by push_cast; rfl
    have hfreq : (∑ i, |(halfPeriodThetaExponent I j n i : ℝ)|) ≤
        4 * |(n : ℝ) ^ 2| + 4 * D * |(n : ℝ)| + (1 + 2 * D) := by
      rw [halfPeriodThetaExponent_length]
      have h₁ : |4 * (n : ℝ) ^ 2 - 1| ≤ 4 * (n : ℝ) ^ 2 + 1 := by
        calc
          _ ≤ |4 * (n : ℝ) ^ 2| + |(1 : ℝ)| := by
            have ht := abs_add_le (4 * (n : ℝ) ^ 2) (-1 : ℝ)
            norm_num only [abs_neg, abs_one] at ht
            simpa only [sub_eq_add_neg, abs_one] using ht
          _ = _ := by rw [abs_of_nonneg (by positivity)]; norm_num
      have h₂ : |4 * (n : ℝ) - 2| ≤ 4 * |(n : ℝ)| + 2 := by
        calc
          _ ≤ |4 * (n : ℝ)| + |(2 : ℝ)| := by
            simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (4 * (n : ℝ)) (-2)
          _ = _ := by rw [abs_mul]; norm_num
      rw [abs_of_nonneg (sq_nonneg (n : ℝ))]
      nlinarith [mul_le_mul_of_nonneg_right h₂ hD]
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤
        (1 / 256 : ℝ) ^ (n.natAbs ^ 2))]
    rw [← Real.rpow_natCast, hn]
    simp only [pow_zero, one_add_one_eq_two, one_mul, zero_mul, add_zero]
    have hp := Real.rpow_le_rpow_of_exponent_le hρ hfreq
    nlinarith [mul_le_mul_of_nonneg_left hp
      (by positivity : 0 ≤ (1 / 256 : ℝ) ^ ((n : ℝ) ^ 2))]

/-- The right-hand-side oscillator has exactly the Fourier norm used in
the instance-dependent bound: `ρ` to four times the RHS vector's `ℓ¹` norm. -/
theorem rhsCharacter_weightedFourierNorm (I : DQLSystem eqs vars) (ρ : ℝ) :
    (∑' a : Fin (vars + eqs) → ℤ,
      ‖UnitAddTorus.mFourierCoeff
        (UnitAddTorus.mFourier
          (DetectorCharacterCode.flattenCharacter (DetectorCharacterCode.rhsCharacter I))) a‖ *
        ρ ^ (∑ i, |(a i : ℝ)|)) =
      ρ ^ (4 * ∑ row, |(I.rhs row : ℝ)|) := by
  rw [tsum_weighted_fourierCoeff_character]
  congr 1
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [DetectorCharacterCode.flattenCharacter, Equiv.symm_apply_apply,
    DetectorCharacterCode.rhsCharacter]
  push_cast
  simp [abs_mul, Finset.mul_sum]

end Stability.Selection
