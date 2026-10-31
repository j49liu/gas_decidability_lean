import Stability.Selection.OrdinaryTimeFourierInverse
import Stability.Selection.OrdinaryTimeFourierCharacters
import Stability.Selection.OrdinaryTimeThetaGraph

/-!
# The centered theta reciprocal in the weighted Fourier norm

Section 9, Lemma `bounds`, controls the nonconstant theta tail by `2/7`
and its inverse by `7/5`. All coefficients below use the fundamental
clock phases and their literal fourth-power arithmetic characters.
-/

noncomputable section

open scoped BigOperators

namespace Stability.Selection

open HGAS HGAS.Analysis

variable {eqs vars : ℕ}

/-- The centered Gaussian theta output on the fundamental phase torus. -/
def centeredThetaGraph (I : DQLSystem eqs vars) (j : Fin vars) :
    UnitAddTorus (Fin (vars + eqs)) → ℂ :=
  torusFourierSeries (fun n : ℤ ↦ (((1 / 256 : ℝ) ^ (n.natAbs ^ 2) : ℝ) : ℂ))
    (fun n ↦ DetectorCharacterCode.flattenCharacter
      (DetectorFactorizedFourier.thetaCoordinateExponent I j n))

/-- Exact identification with the half-period coordinate and its literal
gauge root; this also identifies the centered series on every phase lift. -/
theorem centeredThetaGraph_eq_gauge_mul_halfPeriod
    (I : DQLSystem eqs vars) (j : Fin vars)
    (x : UnitAddTorus (Fin (vars + eqs))) :
    centeredThetaGraph I j x = (1 / 4 : ℂ) *
      UnitAddTorus.mFourier (CanonicalFixedDetectorTrajectory.gaugeRootExponent I j) x *
        halfPeriodThetaGraph I j x :=
  (gauge_mul_halfPeriodThetaGraph I j x).symm

private def thetaTailCoefficient (n : ℤ) : ℂ :=
  if n = 0 then 0 else -(((1 / 256 : ℝ) ^ (n.natAbs ^ 2) : ℝ) : ℂ)

private def geometricTail (n : ℤ) : ℝ :=
  if n = 0 then 0 else (1 / 8 : ℝ) ^ n.natAbs

private theorem geometricTail_hasSum : HasSum geometricTail (2 / 7 : ℝ) := by
  have hg : HasSum (fun n : ℕ ↦ (1 / 8 : ℝ) ^ (n + 1)) (1 / 7 : ℝ) := by
    convert (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 8)
      (by norm_num : (1 / 8 : ℝ) < 1)).mul_left (1 / 8) using 1
    · ext n
      rw [pow_succ]
      ring
    · norm_num
  have hp : HasSum (fun n : ℕ ↦ geometricTail (n + 1)) (1 / 7 : ℝ) := by
    simpa [geometricTail] using hg
  have hn : HasSum (fun n : ℕ ↦ geometricTail (-(n + 1))) (1 / 7 : ℝ) := by
    apply hg.congr_fun
    intro n
    dsimp only
    rw [geometricTail, if_neg (by omega : -((n : ℤ) + 1) ≠ 0), Int.natAbs_neg]
    norm_num
    change (Int.ofNat (n + 1)).natAbs = n + 1
    rfl
  convert hp.of_add_one_of_neg_add_one hn using 1
  norm_num [geometricTail]

private theorem centeredThetaExponent_length (I : DQLSystem eqs vars) (j : Fin vars)
    (n : ℤ) :
    (∑ i, |(DetectorCharacterCode.flattenCharacter
      (DetectorFactorizedFourier.thetaCoordinateExponent I j n) i : ℝ)|) =
      4 * (n : ℝ) ^ 2 + 4 * |(n : ℝ)| * ∑ row, |(I.linear row j : ℝ)| := by
  classical
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [DetectorCharacterCode.flattenCharacter, Equiv.symm_apply_apply,
    DetectorFactorizedFourier.thetaCoordinateExponent,
    DetectorCharacterCode.privateCharacter, DetectorCharacterCode.linearCharacter]
  push_cast
  simp [abs_mul, abs_of_nonneg (sq_nonneg (n : ℝ)), Finset.mul_sum, apply_ite abs, mul_assoc]

/-- The actual weighted raw tail is bounded by the two-sided geometric
series `Σ_{n≠0} (1/8)^|n| = 2/7`. -/
private theorem centeredThetaTail_weighted_bound (I : DQLSystem eqs vars) (j : Fin vars)
    {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hratio : (1 / 256 : ℝ) * ρ ^ (4 + 4 * ∑ row, |(I.linear row j : ℝ)|) ≤ 1 / 8) :
    Summable (fun n : ℤ ↦ ‖thetaTailCoefficient n‖ *
      ρ ^ (∑ i, |(DetectorCharacterCode.flattenCharacter
        (DetectorFactorizedFourier.thetaCoordinateExponent I j n) i : ℝ)|)) ∧
    (∑' n : ℤ, ‖thetaTailCoefficient n‖ *
      ρ ^ (∑ i, |(DetectorCharacterCode.flattenCharacter
        (DetectorFactorizedFourier.thetaCoordinateExponent I j n) i : ℝ)|)) ≤ 2 / 7 := by
  have hle (n : ℤ) : ‖thetaTailCoefficient n‖ *
      ρ ^ (∑ i, |(DetectorCharacterCode.flattenCharacter
        (DetectorFactorizedFourier.thetaCoordinateExponent I j n) i : ℝ)|) ≤ geometricTail n := by
    by_cases hn : n = 0
    · simp [thetaTailCoefficient, geometricTail, hn]
    · have hncast : ((n.natAbs ^ 2 : ℕ) : ℝ) = (n : ℝ) ^ 2 := by
        have hnZ : n ^ 2 = (n.natAbs ^ 2 : ℕ) := by
          rw [Nat.cast_pow, Int.natAbs_sq]
        calc
          _ = ((n ^ 2 : ℤ) : ℝ) := by
            simpa only [Int.cast_natCast] using
              congrArg (fun z : ℤ ↦ (z : ℝ)) hnZ.symm
          _ = _ := by push_cast; rfl
      have hnabs : |(n : ℝ)| ≤ (n : ℝ) ^ 2 := by
        have hz : (n.natAbs : ℝ) ≤ ((n.natAbs ^ 2 : ℕ) : ℝ) := by
          exact_mod_cast (show n.natAbs ≤ n.natAbs ^ 2 by
            simpa only [pow_two] using n.natAbs.le_mul_self)
        simpa only [Nat.cast_natAbs, Int.cast_abs, hncast] using hz
      have hD : 0 ≤ ∑ row, |(I.linear row j : ℝ)| :=
        Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
      have hfreq : (∑ i, |(DetectorCharacterCode.flattenCharacter
          (DetectorFactorizedFourier.thetaCoordinateExponent I j n) i : ℝ)|) ≤
          (4 + 4 * ∑ row, |(I.linear row j : ℝ)|) * ((n.natAbs ^ 2 : ℕ) : ℝ) := by
        rw [centeredThetaExponent_length, hncast]
        nlinarith [mul_le_mul_of_nonneg_right hnabs hD]
      simp only [thetaTailCoefficient, geometricTail, if_neg hn, norm_neg,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity :
          0 ≤ (1 / 256 : ℝ) ^ (n.natAbs ^ 2))]
      calc
        _ ≤ (1 / 256 : ℝ) ^ (n.natAbs ^ 2) *
            ρ ^ ((4 + 4 * ∑ row, |(I.linear row j : ℝ)|) *
              ((n.natAbs ^ 2 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hρ hfreq)
            (by positivity)
        _ = ((1 / 256 : ℝ) *
            ρ ^ (4 + 4 * ∑ row, |(I.linear row j : ℝ)|)) ^ (n.natAbs ^ 2) := by
          rw [Real.rpow_mul (zero_lt_one.trans_le hρ).le, Real.rpow_natCast, mul_pow]
        _ ≤ (1 / 8 : ℝ) ^ (n.natAbs ^ 2) := pow_le_pow_left₀ (by positivity) hratio _
        _ ≤ (1 / 8 : ℝ) ^ n.natAbs :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num)
            (by simpa only [pow_two] using n.natAbs.le_mul_self)
  have hs := geometricTail_hasSum.summable.of_nonneg_of_le (fun _ ↦ by positivity) hle
  exact ⟨hs, (hs.tsum_le_tsum hle geometricTail_hasSum.summable).trans_eq
    geometricTail_hasSum.tsum_eq⟩

private theorem thetaTail_series_eq (I : DQLSystem eqs vars) (j : Fin vars)
    (x : UnitAddTorus (Fin (vars + eqs))) :
    torusFourierSeries thetaTailCoefficient
      (fun n ↦ DetectorCharacterCode.flattenCharacter
        (DetectorFactorizedFourier.thetaCoordinateExponent I j n)) x =
      1 - centeredThetaGraph I j x := by
  let c : ℤ → ℂ := fun n ↦ (((1 / 256 : ℝ) ^ (n.natAbs ^ 2) : ℝ) : ℂ)
  let e : ℤ → Fin (vars + eqs) → ℤ := fun n ↦
    DetectorCharacterCode.flattenCharacter
      (DetectorFactorizedFourier.thetaCoordinateExponent I j n)
  have hc : Summable fun n ↦ ‖c n‖ := by
    apply (summable_gaussianIntWeight (by norm_num : (0 : ℝ) ≤ 1 / 256)
      (by norm_num : (1 / 256 : ℝ) < 1)).congr
    intro n
    change (1 / 256 : ℝ) ^ (n.natAbs ^ 2) =
      ‖(((1 / 256 : ℝ) ^ (n.natAbs ^ 2) : ℝ) : ℂ)‖
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have ht : Summable fun n ↦ torusSeriesTerm c e n x :=
    hc.of_norm_bounded fun n ↦ (norm_torusSeriesTerm _ _ _ _).le
  have hsplit := ht.tsum_eq_add_tsum_ite 0
  have hz : torusSeriesTerm c e 0 x = 1 := by
    have he : e 0 = 0 := by
      funext i
      simp [e, DetectorCharacterCode.flattenCharacter,
        DetectorFactorizedFourier.thetaCoordinateExponent]
    simp [torusSeriesTerm, he, c, UnitAddTorus.mFourier_zero]
  rw [hz] at hsplit
  have hterm (n : ℤ) : torusSeriesTerm thetaTailCoefficient e n x =
      -(if n = 0 then 0 else torusSeriesTerm c e n x) := by
    by_cases hn : n = 0 <;> simp [torusSeriesTerm, thetaTailCoefficient, c, hn]
  change (∑' n, torusSeriesTerm thetaTailCoefficient e n x) =
    1 - ∑' n, torusSeriesTerm c e n x
  rw [tsum_congr hterm, tsum_neg, hsplit]
  ring

/-- The literal centered theta reciprocal has actual weighted Fourier
norm at most `7/5`; the tail bound is proved from the Gaussian terms. -/
theorem centeredThetaGraph_inverse_weightedFourier_bound
    (I : DQLSystem eqs vars) (j : Fin vars) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hratio : (1 / 256 : ℝ) * ρ ^ (4 + 4 * ∑ row, |(I.linear row j : ℝ)|) ≤ 1 / 8) :
    Summable (fun a : Fin (vars + eqs) → ℤ ↦
      ‖UnitAddTorus.mFourierCoeff (fun x ↦ (centeredThetaGraph I j x)⁻¹) a‖ *
        ρ ^ (∑ i, |(a i : ℝ)|)) ∧
    (∑' a : Fin (vars + eqs) → ℤ,
      ‖UnitAddTorus.mFourierCoeff (fun x ↦ (centeredThetaGraph I j x)⁻¹) a‖ *
        ρ ^ (∑ i, |(a i : ℝ)|)) ≤ 7 / 5 := by
  obtain ⟨hs, hb⟩ := centeredThetaTail_weighted_bound I j hρ hratio
  have hi := exponential_fourierCoeff_inverse_one_sub thetaTailCoefficient
    (fun n ↦ DetectorCharacterCode.flattenCharacter
      (DetectorFactorizedFourier.thetaCoordinateExponent I j n)) hρ hs (by linarith)
  simp only [thetaTail_series_eq, sub_sub_cancel] at hi
  refine ⟨hi.1, hi.2.trans ?_⟩
  rw [← one_div]
  apply (div_le_iff₀ (by linarith)).2
  linarith

/-- The centered theta denominator never vanishes, at any torus phase. -/
theorem centeredThetaGraph_ne_zero (I : DQLSystem eqs vars) (j : Fin vars)
    (x : UnitAddTorus (Fin (vars + eqs))) : centeredThetaGraph I j x ≠ 0 := by
  obtain ⟨hs, hb⟩ := centeredThetaTail_weighted_bound I j (ρ := 1) le_rfl (by norm_num)
  simp only [Real.one_rpow, mul_one] at hs hb
  have ht : Summable fun n ↦ ‖torusSeriesTerm thetaTailCoefficient
      (fun n ↦ DetectorCharacterCode.flattenCharacter
        (DetectorFactorizedFourier.thetaCoordinateExponent I j n)) n x‖ := by
    simpa only [norm_torusSeriesTerm] using hs
  have hn := norm_tsum_le_tsum_norm ht
  change ‖torusFourierSeries thetaTailCoefficient
    (fun n ↦ DetectorCharacterCode.flattenCharacter
      (DetectorFactorizedFourier.thetaCoordinateExponent I j n)) x‖ ≤ _ at hn
  rw [thetaTail_series_eq] at hn
  simp only [norm_torusSeriesTerm] at hn
  intro hz
  rw [hz, sub_zero, norm_one] at hn
  linarith

theorem continuous_centeredThetaGraph (I : DQLSystem eqs vars) (j : Fin vars) :
    Continuous (centeredThetaGraph I j) := by
  have heq : centeredThetaGraph I j = fun x ↦ (1 / 4 : ℂ) *
      UnitAddTorus.mFourier (CanonicalFixedDetectorTrajectory.gaugeRootExponent I j) x *
        halfPeriodThetaGraph I j x :=
    funext (centeredThetaGraph_eq_gauge_mul_halfPeriod I j)
  rw [heq]
  exact (continuous_const.mul (UnitAddTorus.mFourier _).continuous).mul
    (continuous_halfPeriodThetaGraph I j)

/-- The literal reciprocal coordinate `U = G / Θ`, with the fundamental
gauge `G = χ_g / 4` and centered theta denominator `Θ`. -/
def thetaReciprocalGraph (I : DQLSystem eqs vars) (j : Fin vars)
    (x : UnitAddTorus (Fin (vars + eqs))) : ℂ :=
  (1 / 4 : ℂ) *
    UnitAddTorus.mFourier (CanonicalFixedDetectorTrajectory.gaugeRootExponent I j) x *
      (centeredThetaGraph I j x)⁻¹

theorem continuous_thetaReciprocalGraph (I : DQLSystem eqs vars) (j : Fin vars) :
    Continuous (thetaReciprocalGraph I j) :=
  (continuous_const.mul (UnitAddTorus.mFourier _).continuous).mul
    ((continuous_centeredThetaGraph I j).inv₀ (centeredThetaGraph_ne_zero I j))

/-- The reciprocal graph relation is exact at every phase, not only
along the intended dense orbit. -/
theorem thetaReciprocalGraph_identity (I : DQLSystem eqs vars) (j : Fin vars)
    (x : UnitAddTorus (Fin (vars + eqs))) :
    halfPeriodThetaGraph I j x * thetaReciprocalGraph I j x = 1 := by
  have hg := centeredThetaGraph_eq_gauge_mul_halfPeriod I j x
  calc
    _ = centeredThetaGraph I j x * (centeredThetaGraph I j x)⁻¹ := by
      dsimp only [thetaReciprocalGraph]
      rw [hg]
      ring
    _ = 1 := mul_inv_cancel₀ (centeredThetaGraph_ne_zero I j x)

/-- The constructed reciprocal is the field inverse of the literal
half-period theta coordinate. -/
theorem thetaReciprocalGraph_eq_inv (I : DQLSystem eqs vars) (j : Fin vars)
    (x : UnitAddTorus (Fin (vars + eqs))) :
    thetaReciprocalGraph I j x = (halfPeriodThetaGraph I j x)⁻¹ := by
  have hprod := thetaReciprocalGraph_identity I j x
  have hn : halfPeriodThetaGraph I j x ≠ 0 := by
    intro hz
    simp only [hz, zero_mul, zero_ne_one] at hprod
  apply mul_left_cancel₀ hn
  rw [mul_inv_cancel₀ hn]
  exact hprod

theorem gaugeRootExponent_length (I : DQLSystem eqs vars) (j : Fin vars) :
    (∑ i, |(CanonicalFixedDetectorTrajectory.gaugeRootExponent I j i : ℝ)|) =
      1 + 2 * ∑ row, |(I.linear row j : ℝ)| := by
  classical
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp [CanonicalFixedDetectorTrajectory.gaugeRootExponent,
    DetectorJacobiGaugeData.gaugeCharacter, DetectorCharacterCode.privateCharacter,
    DetectorCharacterCode.linearCharacter, abs_mul, Finset.mul_sum, apply_ite abs]

/-- The literal `U` coordinate has weighted Fourier norm at most
`(7/20) ρ^(1 + 2 |B_j|₁)`, including the fundamental gauge-root weight. -/
theorem thetaReciprocalGraph_weightedFourier_bound
    (I : DQLSystem eqs vars) (j : Fin vars) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hratio : (1 / 256 : ℝ) * ρ ^ (4 + 4 * ∑ row, |(I.linear row j : ℝ)|) ≤ 1 / 8) :
    Summable (fun a : Fin (vars + eqs) → ℤ ↦
      ‖UnitAddTorus.mFourierCoeff (thetaReciprocalGraph I j) a‖ *
        ρ ^ (∑ i, |(a i : ℝ)|)) ∧
    (∑' a : Fin (vars + eqs) → ℤ,
      ‖UnitAddTorus.mFourierCoeff (thetaReciprocalGraph I j) a‖ *
        ρ ^ (∑ i, |(a i : ℝ)|)) ≤
      (7 / 20 : ℝ) * ρ ^ (1 + 2 * ∑ row, |(I.linear row j : ℝ)|) := by
  obtain ⟨hs, hb⟩ := centeredThetaGraph_inverse_weightedFourier_bound I j hρ hratio
  have hc := exponential_fourierCoeff_scalar_character_mul
    (fun x ↦ (centeredThetaGraph I j x)⁻¹) (1 / 4 : ℂ)
    (CanonicalFixedDetectorTrajectory.gaugeRootExponent I j) hρ hs
  change Summable (fun a ↦ ‖UnitAddTorus.mFourierCoeff (thetaReciprocalGraph I j) a‖ *
    ρ ^ (∑ i, |(a i : ℝ)|)) ∧ _ at hc
  refine ⟨hc.1, hc.2.trans ?_⟩
  rw [gaugeRootExponent_length]
  norm_num only [norm_div, norm_one, Complex.norm_ofNat]
  have hm := mul_le_mul_of_nonneg_left hb
    (by positivity : 0 ≤ (1 / 4 : ℝ) *
      ρ ^ (1 + 2 * ∑ row, |(I.linear row j : ℝ)|))
  linarith

end Stability.Selection
