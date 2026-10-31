import Stability.Selection.OrdinaryTimeThetaGraph

/-!
# Half-characteristic Jacobi coordinates on the phase torus

The explicit series below give the four Jacobi coordinates in Section 8,
Lemma `graph`, and retain the shifted quadratic exponents in Section 9,
Lemma `bounds`.
-/

noncomputable section

open scoped BigOperators

namespace Stability.Selection

open HGAS HGAS.Analysis HGAS.Modular

variable {eqs vars : ℕ}

/-- Shifted Gaussian exponent of the half-characteristic series. -/
def jacobiGraphQuadratic (q : ℤ) (n : ℤ) : ℝ :=
  ((n : ℝ) + (q : ℝ) / 2) ^ 2 + ((n : ℝ) + (q : ℝ) / 2)

/-- Static coefficient at the canonical imaginary height. The real
half-characteristic contributes only a unit-modulus factor. -/
def halfPeriodJacobiCoefficient (q r n : ℤ) : ℂ :=
  Complex.exp (Real.pi * Complex.I *
    ((jacobiGraphQuadratic q n : ℂ) * thetaGaugeBasePoint +
      ((n : ℂ) + (q : ℂ) / 2) * (1 + (r : ℂ))))

/-- Integral fundamental-clock frequency of a half-characteristic term. -/
def halfPeriodJacobiExponent (I : DQLSystem eqs vars) (j : Fin vars) (q n : ℤ) :
    Fin (vars + eqs) → ℤ :=
  fun i ↦ let phase := finSumFinEquiv.symm i
    ((2 * n + q) ^ 2 + 2 * (2 * n + q)) *
        DetectorCharacterCode.privateCharacter j phase +
      (4 * n + 2 * q) * DetectorCharacterCode.linearCharacter I j phase

/-- A common torus series for the four literal half-period Jacobi
coordinates. Their characteristic pairs are `(1,1)`, `(1,0)`, `(0,0)`,
and `(0,1)`; the odd coordinate carries an additional minus sign. -/
def halfPeriodJacobiGraph (I : DQLSystem eqs vars) (j : Fin vars) (q r : ℤ) :
    UnitAddTorus (Fin (vars + eqs)) → ℂ :=
  torusFourierSeries (halfPeriodJacobiCoefficient q r) (halfPeriodJacobiExponent I j q)

private theorem jacobiGraphCharacter_realLift (a : Fin (vars + eqs) → ℤ)
    (x : Fin (vars + eqs) → ℝ) :
    UnitAddTorus.mFourier a (fun i ↦ (x i : UnitAddCircle)) =
      Complex.exp (2 * Real.pi * Complex.I * (∑ i, (a i : ℝ) * x i)) := by
  have h := Clocks.RadicalClock.mFourier_torusDisplacement a x 1
  have hp : Clocks.RadicalClock.torusDisplacement x 1 =
      fun i ↦ (x i : UnitAddCircle) := by
    funext i
    change (((1 : ℝ) * x i : ℝ) : UnitAddCircle) = _
    rw [one_mul]
  rw [hp] at h
  simpa only [Clocks.RadicalClock.frequencyPairing, Complex.ofReal_one, one_mul] using h

private theorem halfPeriodJacobiExponent_pairing (I : DQLSystem eqs vars) (j : Fin vars)
    (q n : ℤ) (x : Fin (vars + eqs) → ℝ) :
    (∑ i, (halfPeriodJacobiExponent I j q n i : ℝ) * x i) =
      4 * jacobiGraphQuadratic q n * x (finSumFinEquiv (Sum.inl j)) +
        (4 * (n : ℝ) + 2 * (q : ℝ)) *
          ∑ row, (I.linear row j : ℝ) * x (finSumFinEquiv (Sum.inr row)) := by
  classical
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [halfPeriodJacobiExponent,
    Equiv.symm_apply_apply, DetectorCharacterCode.privateCharacter,
    DetectorCharacterCode.linearCharacter]
  push_cast
  simp [Finset.mul_sum, mul_assoc, jacobiGraphQuadratic]
  ring

/-- Each term is the literal half-characteristic Jacobi summand on a
real lift of the phase torus. -/
theorem halfPeriodJacobiTerm_realLift
    (I : DQLSystem eqs vars) (j : Fin vars) (q r : ℤ)
    (x : Fin (vars + eqs) → ℝ) (n : ℤ) :
    let τ : ℂ := thetaGaugeBasePoint + 8 * (x (finSumFinEquiv (Sum.inl j)) : ℂ)
    let w : ℂ := 4 * ((∑ row, (I.linear row j : ℝ) *
      x (finSumFinEquiv (Sum.inr row)) : ℝ) : ℂ) + (1 + τ) / 2
    torusSeriesTerm (halfPeriodJacobiCoefficient q r) (halfPeriodJacobiExponent I j q)
      n (fun i ↦ (x i : UnitAddCircle)) =
      Complex.exp (Real.pi * Complex.I *
        ((q : ℂ) ^ 2 * τ / 4 + (q : ℂ) * (w + (r : ℂ) / 2))) *
          jacobiTheta₂_term n (w + (r : ℂ) / 2 + (q : ℂ) * τ / 2) τ := by
  dsimp only
  rw [torusSeriesTerm, jacobiGraphCharacter_realLift, halfPeriodJacobiExponent_pairing]
  unfold halfPeriodJacobiCoefficient jacobiTheta₂_term
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  dsimp only [jacobiGraphQuadratic]
  push_cast
  ring

/-- On every real lift, the series is the usual half-characteristic
Jacobi theta value at the literal intended elliptic and modular phases. -/
theorem halfPeriodJacobiGraph_eq_jacobiTheta
    (I : DQLSystem eqs vars) (j : Fin vars) (q r : ℤ)
    (x : Fin (vars + eqs) → ℝ) :
    let τ : ℂ := thetaGaugeBasePoint + 8 * (x (finSumFinEquiv (Sum.inl j)) : ℂ)
    let w : ℂ := 4 * ((∑ row, (I.linear row j : ℝ) *
      x (finSumFinEquiv (Sum.inr row)) : ℝ) : ℂ) + (1 + τ) / 2
    halfPeriodJacobiGraph I j q r (fun i ↦ (x i : UnitAddCircle)) =
      Complex.exp (Real.pi * Complex.I *
        ((q : ℂ) ^ 2 * τ / 4 + (q : ℂ) * (w + (r : ℂ) / 2))) *
          jacobiTheta₂ (w + (r : ℂ) / 2 + (q : ℂ) * τ / 2) τ := by
  dsimp only
  unfold halfPeriodJacobiGraph torusFourierSeries jacobiTheta₂
  rw [← tsum_mul_left]
  exact tsum_congr (halfPeriodJacobiTerm_realLift I j q r x)

/-- The exact term magnitude includes any negative values of the
shifted quadratic, rather than silently replacing them by zero. -/
theorem norm_halfPeriodJacobiCoefficient (q r n : ℤ) :
    ‖halfPeriodJacobiCoefficient q r n‖ = (1 / 256 : ℝ) ^ jacobiGraphQuadratic q n := by
  rw [halfPeriodJacobiCoefficient, Complex.norm_exp]
  have he : (Real.pi * Complex.I *
      ((jacobiGraphQuadratic q n : ℂ) * thetaGaugeBasePoint +
        ((n : ℂ) + (q : ℂ) / 2) * (1 + (r : ℂ)))).re =
      -Real.pi * thetaGaugeHeight * jacobiGraphQuadratic q n := by
    simp [thetaGaugeBasePoint, Complex.mul_re, Complex.mul_im]
    ring
  rw [he, ← exp_neg_pi_mul_thetaGaugeHeight, Real.exp_mul]

theorem halfPeriodJacobiExponent_length (I : DQLSystem eqs vars) (j : Fin vars)
    (q n : ℤ) :
    (∑ i, |(halfPeriodJacobiExponent I j q n i : ℝ)|) =
      4 * |jacobiGraphQuadratic q n| +
        |4 * (n : ℝ) + 2 * (q : ℝ)| * ∑ row, |(I.linear row j : ℝ)| := by
  classical
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [halfPeriodJacobiExponent, Equiv.symm_apply_apply,
    DetectorCharacterCode.privateCharacter, DetectorCharacterCode.linearCharacter]
  push_cast
  simp only [mul_zero, add_zero, zero_add]
  rw [show (2 * (n : ℝ) + (q : ℝ)) ^ 2 + 2 * (2 * (n : ℝ) + (q : ℝ)) =
    4 * jacobiGraphQuadratic q n by dsimp [jacobiGraphQuadratic]; ring]
  simp [abs_mul, Finset.mul_sum, apply_ite abs]

/-- Polynomial index factors preserve the weighted Gaussian estimate;
this also controls differentiated Jacobi coordinates. -/
theorem summable_pow_weighted_halfPeriodJacobiCoefficient
    (I : DQLSystem eqs vars) (j : Fin vars) (q r : ℤ) (d : ℕ) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hdecay : (1 / 256 : ℝ) * ρ ^ (4 : ℝ) < 1) :
    Summable fun n : ℤ ↦ (1 + |(n : ℝ)| ^ d) * ‖halfPeriodJacobiCoefficient q r n‖ *
      ρ ^ (∑ i, |(halfPeriodJacobiExponent I j q n i : ℝ)|) := by
  let D : ℝ := ∑ row, |(I.linear row j : ℝ)|
  have hD : 0 ≤ D := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hs := Analysis.ShiftedThetaBounds.summable_weighted_quadratic
    (lam := 1 / 256) (a := 1) (A := 4) (by norm_num) hρ
    (by norm_num) (by norm_num) hdecay ((q : ℝ) + 1)
    ((q : ℝ) ^ 2 / 4 + (q : ℝ) / 2) (4 * D) (2 * |(q : ℝ)| * D) d
  have hquad (n : ℤ) :
      1 * (n : ℝ) ^ 2 + ((q : ℝ) + 1) * (n : ℝ) +
        ((q : ℝ) ^ 2 / 4 + (q : ℝ) / 2) = jacobiGraphQuadratic q n := by
    dsimp [jacobiGraphQuadratic]
    ring
  simp only [hquad] at hs
  apply hs.of_nonneg_of_le (fun _ ↦ by positivity)
  intro n
  rw [norm_halfPeriodJacobiCoefficient]
  have hlin : |4 * (n : ℝ) + 2 * (q : ℝ)| ≤
      4 * |(n : ℝ)| + 2 * |(q : ℝ)| := by
    calc
      _ ≤ |4 * (n : ℝ)| + |2 * (q : ℝ)| := abs_add_le _ _
      _ = _ := by norm_num [abs_mul]
  have he : (∑ i, |(halfPeriodJacobiExponent I j q n i : ℝ)|) ≤
      4 * |jacobiGraphQuadratic q n| + 4 * D * |(n : ℝ)| + 2 * |(q : ℝ)| * D := by
    rw [halfPeriodJacobiExponent_length]
    dsimp only [D] at hlin hD ⊢
    nlinarith [mul_le_mul_of_nonneg_right hlin hD]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hρ he) (by positivity)

private theorem summable_weighted_halfPeriodJacobiCoefficient
    (I : DQLSystem eqs vars) (j : Fin vars) (q r : ℤ) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hdecay : (1 / 256 : ℝ) * ρ ^ (4 : ℝ) < 1) :
    Summable fun n : ℤ ↦ ‖halfPeriodJacobiCoefficient q r n‖ *
      ρ ^ (∑ i, |(halfPeriodJacobiExponent I j q n i : ℝ)|) := by
  have hs := summable_pow_weighted_halfPeriodJacobiCoefficient I j q r 0 hρ hdecay
  apply hs.of_nonneg_of_le (fun _ ↦ by positivity)
  intro n
  simp only [pow_zero, one_add_one_eq_two]
  have hn : 0 ≤ ‖halfPeriodJacobiCoefficient q r n‖ *
      ρ ^ (∑ i, |(halfPeriodJacobiExponent I j q n i : ℝ)|) := by positivity
  linarith

private theorem summable_norm_halfPeriodJacobiCoefficient
    (I : DQLSystem eqs vars) (j : Fin vars) (q r : ℤ) :
    Summable fun n : ℤ ↦ ‖halfPeriodJacobiCoefficient q r n‖ := by
  simpa only [Real.one_rpow, mul_one] using
    summable_weighted_halfPeriodJacobiCoefficient I j q r (ρ := 1) le_rfl (by norm_num)

theorem continuous_halfPeriodJacobiGraph
    (I : DQLSystem eqs vars) (j : Fin vars) (q r : ℤ) :
    Continuous (halfPeriodJacobiGraph I j q r) :=
  continuous_torusFourierSeries _ _ (summable_norm_halfPeriodJacobiCoefficient I j q r)

/-- All half-characteristic coordinates have summable actual weighted
Fourier coefficients under the manuscript's Gaussian decay condition. -/
theorem summable_weighted_halfPeriodJacobiGraph
    (I : DQLSystem eqs vars) (j : Fin vars) (q r : ℤ) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hdecay : (1 / 256 : ℝ) * ρ ^ (4 : ℝ) < 1) :
    Summable fun a : Fin (vars + eqs) → ℤ ↦
      ‖UnitAddTorus.mFourierCoeff (halfPeriodJacobiGraph I j q r) a‖ *
        ρ ^ (∑ i, |(a i : ℝ)|) :=
  summable_weighted_fourierCoeff_of_expansion _ _
    (fun a ↦ ρ ^ (∑ i, |(a i : ℝ)|)) (fun _ ↦ by positivity)
    (summable_norm_halfPeriodJacobiCoefficient I j q r)
    (summable_weighted_halfPeriodJacobiCoefficient I j q r hρ hdecay)

/-- The four literal Jacobi coordinates in their original order. -/
def halfPeriodJacobiVectorGraph (I : DQLSystem eqs vars) (j : Fin vars)
    (x : UnitAddTorus (Fin (vars + eqs))) : Fin 4 → ℂ :=
  ![-halfPeriodJacobiGraph I j 1 1 x, halfPeriodJacobiGraph I j 1 0 x,
    halfPeriodJacobiGraph I j 0 0 x, halfPeriodJacobiGraph I j 0 1 x]

/-- The four series simultaneously agree with the actual Jacobi vector
at every real phase lift, including its odd-characteristic sign. -/
theorem halfPeriodJacobiVectorGraph_eq_jacobiThetaVector
    (I : DQLSystem eqs vars) (j : Fin vars) (x : Fin (vars + eqs) → ℝ) :
    let τ : ℂ := thetaGaugeBasePoint + 8 * (x (finSumFinEquiv (Sum.inl j)) : ℂ)
    let w : ℂ := 4 * ((∑ row, (I.linear row j : ℝ) *
      x (finSumFinEquiv (Sum.inr row)) : ℝ) : ℂ) + (1 + τ) / 2
    halfPeriodJacobiVectorGraph I j (fun i ↦ (x i : UnitAddCircle)) =
      jacobiThetaVector w τ := by
  have h11 := halfPeriodJacobiGraph_eq_jacobiTheta I j 1 1 x
  have h10 := halfPeriodJacobiGraph_eq_jacobiTheta I j 1 0 x
  have h00 := halfPeriodJacobiGraph_eq_jacobiTheta I j 0 0 x
  have h01 := halfPeriodJacobiGraph_eq_jacobiTheta I j 0 1 x
  funext k
  fin_cases k
  · simpa [halfPeriodJacobiVectorGraph, jacobiThetaVector, jacobiTheta1,
      jacobiTheta2] using congrArg Neg.neg h11
  · simpa [halfPeriodJacobiVectorGraph, jacobiThetaVector, jacobiTheta2] using h10
  · simpa [halfPeriodJacobiVectorGraph, jacobiThetaVector, jacobiTheta3] using h00
  · simpa [halfPeriodJacobiVectorGraph, jacobiThetaVector, jacobiTheta4] using h01

theorem continuous_halfPeriodJacobiVectorGraph
    (I : DQLSystem eqs vars) (j : Fin vars) :
    Continuous (halfPeriodJacobiVectorGraph I j) := by
  apply continuous_pi
  intro k
  fin_cases k
  · exact (continuous_halfPeriodJacobiGraph I j 1 1).neg
  · exact continuous_halfPeriodJacobiGraph I j 1 0
  · exact continuous_halfPeriodJacobiGraph I j 0 0
  · exact continuous_halfPeriodJacobiGraph I j 0 1

/-- The weighted Fourier estimate applies to each of the four literal
coordinates, including the odd-coordinate sign. -/
theorem summable_weighted_halfPeriodJacobiVectorGraph
    (I : DQLSystem eqs vars) (j : Fin vars) (k : Fin 4) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hdecay : (1 / 256 : ℝ) * ρ ^ (4 : ℝ) < 1) :
    Summable fun a : Fin (vars + eqs) → ℤ ↦
      ‖UnitAddTorus.mFourierCoeff (fun x ↦ halfPeriodJacobiVectorGraph I j x k) a‖ *
        ρ ^ (∑ i, |(a i : ℝ)|) := by
  have hneg (f : UnitAddTorus (Fin (vars + eqs)) → ℂ) (a : Fin (vars + eqs) → ℤ) :
      UnitAddTorus.mFourierCoeff (fun x ↦ -f x) a = -UnitAddTorus.mFourierCoeff f a := by
    simp only [UnitAddTorus.mFourierCoeff, smul_eq_mul, mul_neg, MeasureTheory.integral_neg]
  fin_cases k
  · change Summable fun a ↦
      ‖UnitAddTorus.mFourierCoeff (fun x ↦ -halfPeriodJacobiGraph I j 1 1 x) a‖ *
        ρ ^ (∑ i, |(a i : ℝ)|)
    simpa only [hneg, norm_neg] using
      summable_weighted_halfPeriodJacobiGraph I j 1 1 hρ hdecay
  · exact summable_weighted_halfPeriodJacobiGraph I j 1 0 hρ hdecay
  · exact summable_weighted_halfPeriodJacobiGraph I j 0 0 hρ hdecay
  · exact summable_weighted_halfPeriodJacobiGraph I j 0 1 hρ hdecay

end Stability.Selection
