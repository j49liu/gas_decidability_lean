import Stability.Selection.OrdinaryTimeSourceBudget

/-!
# Numerical size and polynomial Fourier resources

The coordinate budget gives an explicit natural size bound and the
degree-dependent RHS factor in Section 9, Lemma `bounds`.
-/

noncomputable section

open scoped BigOperators

namespace Stability.Selection

open HGAS HGAS.Analysis HGAS.Clocks

/-- Absolute Fourier reconstruction bounds every value by the weighted
Haar coefficient norm. -/
theorem norm_le_exponential_fourierCoeff {d : Type*} [Fintype d]
    (f : UnitAddTorus d → ℂ) (hc : Continuous f) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hf : Summable fun a ↦ ‖UnitAddTorus.mFourierCoeff f a‖ * ρ ^ (∑ i, |(a i : ℝ)|))
    (x : UnitAddTorus d) :
    ‖f x‖ ≤ ∑' a, ‖UnitAddTorus.mFourierCoeff f a‖ * ρ ^ (∑ i, |(a i : ℝ)|) := by
  have hw (a : d → ℤ) : 1 ≤ ρ ^ (∑ i, |(a i : ℝ)|) :=
    Real.one_le_rpow hρ (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
  have hs := summable_norm_fourierCoeff_of_weighted f _ hw hf
  have hn := norm_tsum_le_tsum_norm
    (show Summable fun a ↦ ‖torusSeriesTerm (UnitAddTorus.mFourierCoeff f) id a x‖ by
      simpa only [norm_torusSeriesTerm] using hs)
  change ‖torusFourierSeries (UnitAddTorus.mFourierCoeff f) id x‖ ≤ _ at hn
  rw [torusFourierSeries_fourierCoeff f hc hs] at hn
  simp only [norm_torusSeriesTerm] at hn
  exact hn.trans (hs.tsum_le_tsum
    (fun a ↦ le_mul_of_one_le_right (norm_nonneg _) (hw a)) hf)

/-- A natural bound for the squared Euclidean norm of the actual source
graph, independent of every arithmetic RHS coefficient. -/
def sourceGraphSizeBudget (eqs vars : ℕ) : ℕ :=
  FixedDetectorPolynomialCode.dimension eqs vars * sourceCoordinateFourierBudget ^ 2

theorem sourceGraphSizeBudget_pos (eqs vars : ℕ) : 0 < sourceGraphSizeBudget eqs vars := by
  apply Nat.mul_pos
  · change 0 < FixedDetectorPolynomialCode.baseDimension eqs vars + 2
    omega
  · exact Nat.pow_pos sourceCoordinateFourierBudget_pos

/-- The actual normalized positive controller states meet the coordinate
hypothesis of the source budget without an extra assumption. -/
theorem explicitController_coordinates_le_one (p : ℝ) :
    |(ExplicitPositiveControllerEquilibrium.state p).r| ≤ 1 ∧
    |(ExplicitPositiveControllerEquilibrium.state p).s| ≤ 1 := by
  have h := ExplicitPositiveControllerEquilibrium.state_radiusSq p
  dsimp only [Controller.controllerRadiusSq] at h
  constructor
  · apply (sq_le_one_iff_abs_le_one _).mp
    nlinarith [sq_nonneg (ExplicitPositiveControllerEquilibrium.state p).s]
  · apply (sq_le_one_iff_abs_le_one _).mp
    nlinarith [sq_nonneg (ExplicitPositiveControllerEquilibrium.state p).r]

theorem intendedSourceGraph_normSq_le {eqs vars : ℕ}
    (I : DQLSystem eqs vars) (controller : Fin (vars + eqs) → Controller.ControllerState ℝ)
    (hcontroller : ∀ i, |(controller i).r| ≤ 1 ∧ |(controller i).s| ≤ 1)
    (x : UnitAddTorus (Fin (vars + eqs))) :
    normSq (intendedSourceGraph I controller x) ≤ (sourceGraphSizeBudget eqs vars : ℕ) := by
  have hb (i : Fin (FixedDetectorPolynomialCode.dimension eqs vars)) :
      |intendedSourceGraph I controller x i| ≤ (sourceCoordinateFourierBudget : ℝ) := by
    have hs := summable_weighted_intendedSourceGraph_of_matrix_bounds I controller
      (ρ := 1) le_rfl (by norm_num) (by norm_num) i
    have he := norm_le_exponential_fourierCoeff
      (fun x ↦ (intendedSourceGraph I controller x i : ℂ))
      (Complex.continuous_ofReal.comp
        ((continuous_apply i).comp (continuous_intendedSourceGraph I controller))) le_rfl hs x
    have hn := intendedSourceGraph_weightedFourier_bound_of_matrix_bounds I controller
      hcontroller (ρ := 1) le_rfl (by norm_num) (by norm_num) i
    simpa only [Complex.norm_real, Real.norm_eq_abs, Real.one_rpow, mul_one] using he.trans hn
  simpa [sourceGraphSizeBudget] using
    FiniteCoordinateNormSq.normSq_le_card_mul_sq_of_abs_le _ hb

/-- The literal graph with the actual positive controller choices has
an explicit RHS-independent squared-norm bound. -/
theorem positiveControllerSourceGraph_normSq_le {eqs vars : ℕ}
    (I : DQLSystem eqs vars) (p : Fin (vars + eqs) → ℝ)
    (x : UnitAddTorus (Fin (vars + eqs))) :
    normSq (intendedSourceGraph I (fun i ↦ ExplicitPositiveControllerEquilibrium.state (p i)) x) ≤
      (sourceGraphSizeBudget eqs vars : ℕ) :=
  intendedSourceGraph_normSq_le I _ (fun i ↦ explicitController_coordinates_le_one (p i)) x

/-- The source graph's polynomial Fourier estimate has an explicit
natural coordinate budget and the exact exponent `4 D |rhs|₁`. -/
theorem intendedSourceGraph_polynomial_weightedFourier_bound {eqs vars : ℕ}
    (I : DQLSystem eqs vars) (controller : Fin (vars + eqs) → Controller.ControllerState ℝ)
    (hcontroller : ∀ i, |(controller i).r| ≤ 1 ∧ |(controller i).s| ≤ 1)
    {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hθ : (1 / 256 : ℝ) * ρ ^
      (4 + 4 * ∑ row, ∑ j, |(I.linear row j : ℝ)|) ≤ 1 / 8)
    (hP : (1 / 2 : ℝ) * ρ ^
      (4 + 4 * ∑ row, ∑ j, |(I.quadratic row j : ℝ)|) ≤ 3 / 4)
    (P : MvPolynomial (Fin (FixedDetectorPolynomialCode.dimension eqs vars)) ℚ) :
    Summable (fun a : Fin (vars + eqs) → ℤ ↦
      ‖UnitAddTorus.mFourierCoeff (fun x ↦ MvPolynomial.eval₂ (algebraMap ℚ ℂ)
        (fun i ↦ (intendedSourceGraph I controller x i : ℂ)) P) a‖ *
          ρ ^ (∑ k, |(a k : ℝ)|)) ∧
    (∑' a : Fin (vars + eqs) → ℤ,
      ‖UnitAddTorus.mFourierCoeff (fun x ↦ MvPolynomial.eval₂ (algebraMap ℚ ℂ)
        (fun i ↦ (intendedSourceGraph I controller x i : ℂ)) P) a‖ *
          ρ ^ (∑ k, |(a k : ℝ)|)) ≤
      (∑ e ∈ P.support, ‖((P.coeff e : ℚ) : ℂ)‖) *
        (sourceCoordinateFourierBudget : ℝ) ^ P.totalDegree *
          ρ ^ (4 * (P.totalDegree : ℝ) * ∑ row, |(I.rhs row : ℝ)|) := by
  have hC : (1 : ℝ) ≤ sourceCoordinateFourierBudget := by
    exact_mod_cast (Nat.succ_le_iff.mpr sourceCoordinateFourierBudget_pos)
  have hw : 1 ≤ ρ ^ (4 * ∑ row, |(I.rhs row : ℝ)|) :=
    Real.one_le_rpow hρ (by positivity)
  have hp := exponential_fourierCoeff_polynomial P (algebraMap ℚ ℂ)
    (fun i x ↦ (intendedSourceGraph I controller x i : ℂ))
    (fun i ↦ Complex.continuous_ofReal.comp
      ((continuous_apply i).comp (continuous_intendedSourceGraph I controller))) hρ
    (one_le_mul_of_one_le_of_one_le hC hw)
    (summable_weighted_intendedSourceGraph_of_matrix_bounds I controller hρ hθ hP)
    (intendedSourceGraph_weightedFourier_bound_of_matrix_bounds I controller hcontroller hρ hθ hP)
  refine ⟨hp.1, hp.2.trans_eq ?_⟩
  rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans hρ)]
  simp only [← mul_assoc]
  congr 2
  ring

end Stability.Selection
