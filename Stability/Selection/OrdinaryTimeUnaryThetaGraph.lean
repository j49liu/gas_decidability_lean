import Stability.Selection.OrdinaryTimeJacobiGraph
import Stability.Selection.OrdinaryTimeFourierCharacters

/-!
# Unary theta constants on the fundamental phase torus

The canonical height is fixed and the modular parameter is `iY + 8x`.
The theta constants therefore have integral fundamental-clock frequencies,
including the odd squares in the half-integral characteristic.
-/

noncomputable section

open scoped BigOperators

namespace Stability.Selection

open HGAS HGAS.Analysis HGAS.Modular

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The canonical modular parameter on a real lift of the phase torus. -/
def fundamentalThetaParameter (j : d) (x : d → ℝ) : UpperHalfPlane :=
  ⟨thetaGaugeBasePoint + 8 * (x j : ℂ), by
    simpa [thetaGaugeBasePoint] using thetaGaugeHeight_pos⟩

/-- The static coefficient of a unary half-characteristic term. -/
def unaryThetaGraphCoefficient (q r n : ℤ) : ℂ :=
  Complex.exp (Real.pi * Complex.I *
    (((n : ℂ) + (q : ℂ) / 2) ^ 2 * thetaGaugeBasePoint +
      ((n : ℂ) + (q : ℂ) / 2) * (r : ℂ)))

/-- The fundamental-clock frequency is the integral square `(2n+q)²`. -/
def unaryThetaGraphExponent (j : d) (q n : ℤ) : d → ℤ :=
  fun i ↦ if i = j then (2 * n + q) ^ 2 else 0

/-- Unary theta constants, represented by their explicit phase series. -/
def unaryThetaGraph (j : d) (q r : ℤ) : UnitAddTorus d → ℂ :=
  torusFourierSeries (unaryThetaGraphCoefficient q r) (unaryThetaGraphExponent j q)

/-- The actual unary half-characteristic value on every real phase lift. -/
theorem unaryThetaGraph_eq_jacobiTheta (j : d) (q r : ℤ) (x : d → ℝ) :
    let τ : ℂ := fundamentalThetaParameter j x
    unaryThetaGraph j q r (fun i ↦ (x i : UnitAddCircle)) =
      Complex.exp (Real.pi * Complex.I *
        ((q : ℂ) ^ 2 * τ / 4 + (q : ℂ) * (r : ℂ) / 2)) *
          jacobiTheta₂ ((r : ℂ) / 2 + (q : ℂ) * τ / 2) τ := by
  dsimp only
  unfold unaryThetaGraph torusFourierSeries jacobiTheta₂
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [torusSeriesTerm, fourierCharacter_realLift]
  have hp : (∑ i, (unaryThetaGraphExponent j q n i : ℝ) * x i) =
      (2 * (n : ℝ) + (q : ℝ)) ^ 2 * x j := by
    simp [unaryThetaGraphExponent, apply_ite (fun z : ℤ ↦ (z : ℝ))]
  rw [hp]
  unfold unaryThetaGraphCoefficient jacobiTheta₂_term
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  dsimp only [fundamentalThetaParameter]
  push_cast
  ring

theorem norm_unaryThetaGraphCoefficient (q r n : ℤ) :
    ‖unaryThetaGraphCoefficient q r n‖ =
      (1 / 256 : ℝ) ^ (((n : ℝ) + (q : ℝ) / 2) ^ 2) := by
  rw [unaryThetaGraphCoefficient, Complex.norm_exp]
  have he : (Real.pi * Complex.I *
      (((n : ℂ) + (q : ℂ) / 2) ^ 2 * thetaGaugeBasePoint +
        ((n : ℂ) + (q : ℂ) / 2) * (r : ℂ))).re =
      -Real.pi * thetaGaugeHeight * ((n : ℝ) + (q : ℝ) / 2) ^ 2 := by
    simp [thetaGaugeBasePoint, pow_two, Complex.mul_re, Complex.mul_im]
    ring
  rw [he, ← exp_neg_pi_mul_thetaGaugeHeight, Real.exp_mul]

theorem unaryThetaGraphExponent_length (j : d) (q n : ℤ) :
    (∑ i, |(unaryThetaGraphExponent j q n i : ℝ)|) =
      4 * ((n : ℝ) + (q : ℝ) / 2) ^ 2 := by
  have hi (i : d) : |(unaryThetaGraphExponent j q n i : ℝ)| =
      if i = j then (2 * (n : ℝ) + (q : ℝ)) ^ 2 else 0 := by
    by_cases hij : i = j
    · simp [unaryThetaGraphExponent, hij, abs_of_nonneg (sq_nonneg (2 * (n : ℝ) + q))]
    · simp [unaryThetaGraphExponent, hij]
  simp only [hi, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

private theorem summable_weighted_unaryThetaGraphCoefficient
    (j : d) (q r : ℤ) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hdecay : (1 / 256 : ℝ) * ρ ^ (4 : ℝ) < 1) :
    Summable fun n : ℤ ↦ ‖unaryThetaGraphCoefficient q r n‖ *
      ρ ^ (∑ i, |(unaryThetaGraphExponent j q n i : ℝ)|) := by
  have hs := Analysis.ShiftedThetaBounds.summable_weighted_quadratic
    (lam := 1 / 256) (a := 1) (A := 4) (by norm_num) hρ
    (by norm_num) (by norm_num) hdecay (q : ℝ) ((q : ℝ) ^ 2 / 4) 0 0 0
  have hquad (n : ℤ) : 1 * (n : ℝ) ^ 2 + (q : ℝ) * (n : ℝ) + (q : ℝ) ^ 2 / 4 =
      ((n : ℝ) + (q : ℝ) / 2) ^ 2 := by ring
  have habs (n : ℤ) : |((n : ℝ) + (q : ℝ) / 2) ^ 2| =
      ((n : ℝ) + (q : ℝ) / 2) ^ 2 := abs_of_nonneg (sq_nonneg _)
  simp only [hquad, pow_zero, one_add_one_eq_two, zero_mul, add_zero, habs] at hs
  apply hs.of_nonneg_of_le (fun _ ↦ by positivity)
  intro n
  rw [norm_unaryThetaGraphCoefficient, unaryThetaGraphExponent_length]
  have hn : 0 ≤ (1 / 256 : ℝ) ^ (((n : ℝ) + (q : ℝ) / 2) ^ 2) *
      ρ ^ (4 * ((n : ℝ) + (q : ℝ) / 2) ^ 2) := by positivity
  linarith

private theorem summable_norm_unaryThetaGraphCoefficient (q r : ℤ) :
    Summable fun n : ℤ ↦ ‖unaryThetaGraphCoefficient q r n‖ := by
  simpa only [Real.one_rpow, mul_one] using
    summable_weighted_unaryThetaGraphCoefficient () q r (ρ := 1) le_rfl (by norm_num)

theorem continuous_unaryThetaGraph (j : d) (q r : ℤ) :
    Continuous (unaryThetaGraph j q r) :=
  continuous_torusFourierSeries _ _ (summable_norm_unaryThetaGraphCoefficient q r)

/-- The actual Haar coefficients, not merely the presentation terms,
are summable with the fundamental-clock exponential weight. -/
theorem summable_weighted_unaryThetaGraph
    (j : d) (q r : ℤ) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hdecay : (1 / 256 : ℝ) * ρ ^ (4 : ℝ) < 1) :
    Summable fun a : d → ℤ ↦ ‖UnitAddTorus.mFourierCoeff (unaryThetaGraph j q r) a‖ *
      ρ ^ (∑ i, |(a i : ℝ)|) :=
  summable_weighted_fourierCoeff_of_expansion _ _
    (fun a ↦ ρ ^ (∑ i, |(a i : ℝ)|)) (fun _ ↦ by positivity)
    (summable_norm_unaryThetaGraphCoefficient q r)
    (summable_weighted_unaryThetaGraphCoefficient j q r hρ hdecay)

/-- Identification with the three literal even theta constants. -/
theorem unaryThetaGraph_eq_thetaConstants (j : d) (x : d → ℝ) :
    unaryThetaGraph j 1 0 (fun i ↦ (x i : UnitAddCircle)) =
        theta₂ (fundamentalThetaParameter j x) ∧
    unaryThetaGraph j 0 0 (fun i ↦ (x i : UnitAddCircle)) =
        theta₃ (fundamentalThetaParameter j x) ∧
    unaryThetaGraph j 0 1 (fun i ↦ (x i : UnitAddCircle)) =
        theta₄ (fundamentalThetaParameter j x) := by
  constructor
  · simpa [theta₂_eq_jacobiTheta₂, mul_div_assoc] using
      unaryThetaGraph_eq_jacobiTheta j 1 0 x
  constructor
  · simpa [theta₃_eq_jacobiTheta₂] using unaryThetaGraph_eq_jacobiTheta j 0 0 x
  · simpa [theta₄_eq_jacobiTheta₂] using unaryThetaGraph_eq_jacobiTheta j 0 1 x

end Stability.Selection
