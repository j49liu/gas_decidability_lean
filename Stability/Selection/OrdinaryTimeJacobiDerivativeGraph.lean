import Stability.Selection.OrdinaryTimeJacobiGraph

/-!
# The differentiated Jacobi coordinate on the phase torus

The literal coordinate is `Δ = θ₁'/π`. Its series has the same shifted
quadratic as the odd theta function and one additional linear factor.
-/

noncomputable section

open scoped BigOperators

namespace Stability.Selection

open HGAS HGAS.Analysis HGAS.Modular

variable {eqs vars : ℕ}

/-- The normalized odd-theta derivative coefficient, including the
odd-characteristic minus sign and the normalization by `π`. -/
def halfPeriodJacobiDerivativeCoefficient (n : ℤ) : ℂ :=
  -(2 * Complex.I * ((n : ℂ) + 1 / 2)) * halfPeriodJacobiCoefficient 1 1 n

/-- The literal `Δ` coordinate as a periodic series. -/
def halfPeriodJacobiDerivativeGraph (I : DQLSystem eqs vars) (j : Fin vars) :
    UnitAddTorus (Fin (vars + eqs)) → ℂ :=
  torusFourierSeries halfPeriodJacobiDerivativeCoefficient (halfPeriodJacobiExponent I j 1)

theorem derivativeCoefficient_bound (n : ℤ) :
    ‖halfPeriodJacobiDerivativeCoefficient n‖ ≤
      2 * (1 + |(n : ℝ)|) * ‖halfPeriodJacobiCoefficient 1 1 n‖ := by
  have hn : (n : ℂ) + 1 / 2 = (((n : ℝ) + 1 / 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [halfPeriodJacobiDerivativeCoefficient, norm_mul, norm_neg,
    norm_mul, norm_mul, Complex.norm_I, mul_one, hn, Complex.norm_real, Real.norm_eq_abs]
  norm_num only [Complex.norm_ofNat]
  have ha : |(n : ℝ) + 1 / 2| ≤ |(n : ℝ)| + 1 / 2 := by
    simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using
      abs_add_le (n : ℝ) (1 / 2)
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  linarith

private theorem summable_weighted_derivativeCoefficient
    (I : DQLSystem eqs vars) (j : Fin vars) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hdecay : (1 / 256 : ℝ) * ρ ^ (4 : ℝ) < 1) :
    Summable fun n : ℤ ↦ ‖halfPeriodJacobiDerivativeCoefficient n‖ *
      ρ ^ (∑ i, |(halfPeriodJacobiExponent I j 1 n i : ℝ)|) := by
  have hs := (summable_pow_weighted_halfPeriodJacobiCoefficient I j 1 1 1 hρ hdecay).mul_left 2
  apply hs.of_nonneg_of_le (fun _ ↦ by positivity)
  intro n
  simpa only [pow_one, mul_assoc] using
    mul_le_mul_of_nonneg_right (derivativeCoefficient_bound n)
      (by positivity : 0 ≤ ρ ^ (∑ i, |(halfPeriodJacobiExponent I j 1 n i : ℝ)|))

private theorem summable_norm_derivativeCoefficient
    (I : DQLSystem eqs vars) (j : Fin vars) :
    Summable fun n : ℤ ↦ ‖halfPeriodJacobiDerivativeCoefficient n‖ := by
  simpa only [Real.one_rpow, mul_one] using
    summable_weighted_derivativeCoefficient I j (ρ := 1) le_rfl (by norm_num)

theorem continuous_halfPeriodJacobiDerivativeGraph
    (I : DQLSystem eqs vars) (j : Fin vars) :
    Continuous (halfPeriodJacobiDerivativeGraph I j) :=
  continuous_torusFourierSeries _ _ (summable_norm_derivativeCoefficient I j)

/-- Actual weighted Haar coefficients of `Δ` are summable under the
same Gaussian decay condition as the undifferentiated coordinates. -/
theorem summable_weighted_halfPeriodJacobiDerivativeGraph
    (I : DQLSystem eqs vars) (j : Fin vars) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hdecay : (1 / 256 : ℝ) * ρ ^ (4 : ℝ) < 1) :
    Summable fun a : Fin (vars + eqs) → ℤ ↦
      ‖UnitAddTorus.mFourierCoeff (halfPeriodJacobiDerivativeGraph I j) a‖ *
        ρ ^ (∑ i, |(a i : ℝ)|) :=
  summable_weighted_fourierCoeff_of_expansion _ _
    (fun a ↦ ρ ^ (∑ i, |(a i : ℝ)|)) (fun _ ↦ by positivity)
    (summable_norm_derivativeCoefficient I j)
    (summable_weighted_derivativeCoefficient I j hρ hdecay)

/-- The series equals the literal normalized odd-theta derivative at
every real lift of the intended torus phases. -/
theorem halfPeriodJacobiDerivativeGraph_eq_jacobiTheta1Prime
    (I : DQLSystem eqs vars) (j : Fin vars) (x : Fin (vars + eqs) → ℝ) :
    let τ : ℂ := thetaGaugeBasePoint + 8 * (x (finSumFinEquiv (Sum.inl j)) : ℂ)
    let w : ℂ := 4 * ((∑ row, (I.linear row j : ℝ) *
      x (finSumFinEquiv (Sum.inr row)) : ℝ) : ℂ) + (1 + τ) / 2
    halfPeriodJacobiDerivativeGraph I j (fun i ↦ (x i : UnitAddCircle)) =
      jacobiTheta1Prime w τ / Real.pi := by
  dsimp only
  let τ : ℂ := thetaGaugeBasePoint + 8 * (x (finSumFinEquiv (Sum.inl j)) : ℂ)
  let w : ℂ := 4 * ((∑ row, (I.linear row j : ℝ) *
    x (finSumFinEquiv (Sum.inr row)) : ℝ) : ℂ) + (1 + τ) / 2
  change _ = jacobiTheta1Prime w τ / Real.pi
  have hτ : 0 < τ.im := by simpa [τ, thetaGaugeBasePoint] using thetaGaugeHeight_pos
  rw [jacobiTheta1Prime_eq_tsum_half w hτ, ← tsum_div_const]
  unfold halfPeriodJacobiDerivativeGraph torusFourierSeries
  apply tsum_congr
  intro n
  have ht := halfPeriodJacobiTerm_realLift I j 1 1 x n
  norm_num only [Int.cast_one, one_pow, one_mul] at ht
  change torusSeriesTerm (halfPeriodJacobiCoefficient 1 1)
    (halfPeriodJacobiExponent I j 1) n (fun i ↦ (x i : UnitAddCircle)) =
      Complex.exp (Real.pi * Complex.I * (τ / 4 + (w + 1 / 2))) *
        jacobiTheta₂_term n (w + 1 / 2 + τ / 2) τ at ht
  rw [← jacobiThetaHalfTerm_eq] at ht
  rw [torusSeriesTerm, halfPeriodJacobiDerivativeCoefficient, mul_assoc]
  change -(2 * Complex.I * ((n : ℂ) + 1 / 2)) *
    torusSeriesTerm (halfPeriodJacobiCoefficient 1 1) (halfPeriodJacobiExponent I j 1)
      n (fun i ↦ (x i : UnitAddCircle)) = _
  rw [ht, jacobiThetaHalfPrimeTerm]
  field_simp [Real.pi_ne_zero]

end Stability.Selection
