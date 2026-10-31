import Stability.Selection.OrdinaryTimeUnaryThetaGraph

/-!
# The weight-two Eisenstein coordinate on the phase torus

The divisor-sum expansion has frequencies `8n` in the fundamental modular
phase. Its weighted terms are dominated by a polynomial times a geometric
sequence, as in Section 9, Lemma `bounds`.
-/

noncomputable section

open scoped BigOperators ArithmeticFunction.sigma

namespace Stability.Selection

open HGAS HGAS.Analysis HGAS.Modular

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Constant and positive-frequency coefficients of the literal `E₂`. -/
def eisensteinGraphCoefficient : Unit ⊕ ℕ+ → ℂ
  | .inl _ => 1
  | .inr n => -(24 : ℂ) * (σ 1 (n : ℕ) : ℕ) * (1 / 65536 : ℂ) ^ (n : ℕ)

/-- The frequency `8n` comes from `exp(2πi τ)` with `τ = iY + 8x`. -/
def eisensteinGraphExponent (j : d) : Unit ⊕ ℕ+ → d → ℤ
  | .inl _ => 0
  | .inr n => fun i ↦ if i = j then 8 * (n : ℕ) else 0

/-- The actual Eisenstein series as a periodic function of the phases. -/
def eisensteinGraph (j : d) : UnitAddTorus d → ℂ :=
  torusFourierSeries eisensteinGraphCoefficient (eisensteinGraphExponent j)

private theorem eisensteinGraphExponent_length (j : d) (n : ℕ+) :
    (∑ i, |(eisensteinGraphExponent j (.inr n) i : ℝ)|) = 8 * (n : ℝ) := by
  simp [eisensteinGraphExponent, apply_ite abs]

theorem eisenstein_weighted_term (j : d) (n : ℕ+) {ρ : ℝ} (hρ : 1 ≤ ρ) :
    ‖eisensteinGraphCoefficient (.inr n)‖ *
      ρ ^ (∑ i, |(eisensteinGraphExponent j (.inr n) i : ℝ)|) =
        24 * (σ 1 (n : ℕ) : ℕ) * ((1 / 65536 : ℝ) * ρ ^ (8 : ℝ)) ^ (n : ℕ) := by
  rw [eisensteinGraphExponent_length, eisensteinGraphCoefficient]
  norm_num only [norm_mul, norm_neg, Complex.norm_ofNat, Complex.norm_natCast,
    norm_pow, norm_div, norm_one]
  rw [Real.rpow_mul (zero_lt_one.trans_le hρ).le, Real.rpow_natCast, mul_pow]
  ring

private theorem summable_weighted_eisensteinGraphCoefficient
    (j : d) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hdecay : (1 / 65536 : ℝ) * ρ ^ (8 : ℝ) < 1) :
    Summable fun n : Unit ⊕ ℕ+ ↦ ‖eisensteinGraphCoefficient n‖ *
      ρ ^ (∑ i, |(eisensteinGraphExponent j n i : ℝ)|) := by
  apply Summable.sum _ (Summable.of_finite)
  have hb : 0 ≤ (1 / 65536 : ℝ) * ρ ^ (8 : ℝ) := by positivity
  have hr : ‖(1 / 65536 : ℝ) * ρ ^ (8 : ℝ)‖ < 1 := by
    rwa [Real.norm_of_nonneg hb]
  have hs := ((summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 hr).subtype
    (fun n : ℕ ↦ 0 < n)).mul_left 24
  apply hs.of_nonneg_of_le (fun _ ↦ by dsimp only [Function.comp_apply]; positivity)
  intro n
  dsimp only [Function.comp_apply]
  rw [eisenstein_weighted_term j n hρ]
  have hn : ((σ 1 (n : ℕ) : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
    exact_mod_cast (ArithmeticFunction.sigma_le_pow_succ 1 (n : ℕ)).trans_eq (by norm_num)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hn (pow_nonneg hb (n : ℕ))) (by norm_num : (0 : ℝ) ≤ 24)

private theorem summable_norm_eisensteinGraphCoefficient :
    Summable fun n : Unit ⊕ ℕ+ ↦ ‖eisensteinGraphCoefficient n‖ := by
  simpa only [Real.one_rpow, mul_one] using
    summable_weighted_eisensteinGraphCoefficient () (ρ := 1) le_rfl (by norm_num)

theorem continuous_eisensteinGraph (j : d) : Continuous (eisensteinGraph j) :=
  continuous_torusFourierSeries _ _ summable_norm_eisensteinGraphCoefficient

/-- The actual weighted Haar Fourier coefficients of the literal
Eisenstein coordinate are absolutely summable. -/
theorem summable_weighted_eisensteinGraph
    (j : d) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hdecay : (1 / 65536 : ℝ) * ρ ^ (8 : ℝ) < 1) :
    Summable fun a : d → ℤ ↦ ‖UnitAddTorus.mFourierCoeff (eisensteinGraph j) a‖ *
      ρ ^ (∑ i, |(a i : ℝ)|) :=
  summable_weighted_fourierCoeff_of_expansion _ _
    (fun a ↦ ρ ^ (∑ i, |(a i : ℝ)|)) (fun _ ↦ by positivity)
    summable_norm_eisensteinGraphCoefficient
    (summable_weighted_eisensteinGraphCoefficient j hρ hdecay)

/-- The theta decay condition also suffices for the Eisenstein series,
since its geometric ratio is the square of the theta ratio. -/
theorem summable_weighted_eisensteinGraph_of_theta_decay
    (j : d) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hdecay : (1 / 256 : ℝ) * ρ ^ (4 : ℝ) < 1) :
    Summable fun a : d → ℤ ↦ ‖UnitAddTorus.mFourierCoeff (eisensteinGraph j) a‖ *
      ρ ^ (∑ i, |(a i : ℝ)|) := by
  apply summable_weighted_eisensteinGraph j hρ
  have he : (1 / 65536 : ℝ) * ρ ^ (8 : ℝ) =
      ((1 / 256 : ℝ) * ρ ^ (4 : ℝ)) ^ 2 := by
    rw [show (8 : ℝ) = 4 * 2 by norm_num, Real.rpow_mul (zero_lt_one.trans_le hρ).le,
      Real.rpow_two, mul_pow]
    norm_num
  rw [he]
  have hn : 0 ≤ (1 / 256 : ℝ) * ρ ^ (4 : ℝ) := by positivity
  nlinarith

private theorem canonical_nome :
    Complex.exp (2 * Real.pi * Complex.I * (thetaGaugeBasePoint : ℂ)) =
      (1 / 65536 : ℂ) := by
  have he : 2 * (Real.pi : ℂ) * Complex.I * (thetaGaugeBasePoint : ℂ) =
      (((-Real.pi * thetaGaugeHeight : ℝ) : ℂ)) +
        (((-Real.pi * thetaGaugeHeight : ℝ) : ℂ)) := by
    dsimp [thetaGaugeBasePoint]
    push_cast
    ring_nf
    simp only [Complex.I_sq]
    ring
  rw [he, Complex.exp_add, ← Complex.ofReal_exp, exp_neg_pi_mul_thetaGaugeHeight]
  norm_num

/-- The series agrees with `E₂` at the canonical modular parameter on
every real phase lift. -/
theorem eisensteinGraph_eq_E2 (j : d) (x : d → ℝ) :
    eisensteinGraph j (fun i ↦ (x i : UnitAddCircle)) =
      EisensteinSeries.E2 (fundamentalThetaParameter j x) := by
  rw [EisensteinSeries.E2_eq_tsum_cexp]
  let f := fun n : Unit ⊕ ℕ+ ↦ torusSeriesTerm eisensteinGraphCoefficient
    (eisensteinGraphExponent j) n (fun i ↦ (x i : UnitAddCircle))
  have hs : Summable f := summable_norm_eisensteinGraphCoefficient.of_norm_bounded
    fun n ↦ (norm_torusSeriesTerm _ _ _ _).le
  change (∑' n, f n) = _
  rw [Summable.tsum_sum (hs.comp_injective Sum.inl_injective)
    (hs.comp_injective Sum.inr_injective)]
  have hz : (∑' u : Unit, f (.inl u)) = 1 := by
    simp [f, torusSeriesTerm, eisensteinGraphCoefficient, eisensteinGraphExponent,
      UnitAddTorus.mFourier_zero]
  rw [hz, sub_eq_add_neg, ← neg_mul, ← tsum_mul_left]
  congr 1
  apply tsum_congr
  intro n
  dsimp only [f, torusSeriesTerm, eisensteinGraphCoefficient]
  rw [fourierCharacter_realLift]
  have hp : (∑ i, (eisensteinGraphExponent j (.inr n) i : ℝ) * x i) =
      8 * (n : ℝ) * x j := by
    simp [eisensteinGraphExponent, apply_ite (fun z : ℤ ↦ (z : ℝ))]
  rw [hp]
  have he : (1 / 65536 : ℂ) ^ (n : ℕ) *
      Complex.exp (2 * Real.pi * Complex.I * ((8 * (n : ℝ) * x j : ℝ) : ℂ)) =
        Complex.exp (2 * Real.pi * Complex.I * (fundamentalThetaParameter j x : ℂ)) ^
          (n : ℕ) := by
    rw [← canonical_nome, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    dsimp only [fundamentalThetaParameter]
    push_cast
    ring
  calc
    _ = -(24 : ℂ) * (σ 1 (n : ℕ) : ℕ) *
        ((1 / 65536 : ℂ) ^ (n : ℕ) *
          Complex.exp (2 * Real.pi * Complex.I * ((8 * (n : ℝ) * x j : ℝ) : ℂ))) := by
      ring
    _ = _ := by rw [he]; ring

end Stability.Selection
