import Stability.Selection.OrdinaryTimeSourceFourier
import Stability.Selection.OrdinaryTimeSourceSize
import Stability.Selection.OrdinaryTimePolynomialFourier

/-!
# Separating the RHS frequency in source-graph Fourier bounds

The base graph is independent of the RHS. The remaining two real
coordinates have weighted norm at most `ρ^(4 |rhs|₁)`. A common natural
bound for the base coefficients therefore isolates all RHS dependence.
The natural bound here is obtained by Archimedean existence, not by an
effective numerical algorithm.
-/

noncomputable section

open scoped BigOperators

namespace Stability.Selection

open HGAS HGAS.Analysis HGAS.Modular HGAS.Clocks

variable {eqs vars : ℕ}

theorem rhs_coordinates_weighted_bound (I : DQLSystem eqs vars)
    (controller : Fin (vars + eqs) → Controller.ControllerState ℝ)
    {ρ : ℝ} (hρ : 1 ≤ ρ) (k : Fin 2) :
    (∑' a : Fin (vars + eqs) → ℤ, ‖UnitAddTorus.mFourierCoeff
      (fun x ↦ (![ (intendedSourceStateGraph I controller x).rhs.c,
        (intendedSourceStateGraph I controller x).rhs.d] k : ℂ)) a‖ *
          ρ ^ (∑ i, |(a i : ℝ)|)) ≤ ρ ^ (4 * ∑ row, |(I.rhs row : ℝ)|) := by
  let e := DetectorCharacterCode.flattenCharacter (DetectorCharacterCode.rhsCharacter I)
  have hs : Summable fun a : Fin (vars + eqs) → ℤ ↦
      ‖UnitAddTorus.mFourierCoeff (UnitAddTorus.mFourier e) a‖ *
        ρ ^ (∑ i, |(a i : ℝ)|) := by
    simpa only [mul_one, one_mul] using
      (exponential_fourierCoeff_scalar_character_mul
        (fun _ : UnitAddTorus (Fin (vars + eqs)) ↦ 1) 1 e hρ
        (exponential_fourierCoeff_const 1 ρ).1).1
  have he := rhsCharacter_weightedFourierNorm I ρ
  fin_cases k
  · exact (exponential_fourierCoeff_re _ (UnitAddTorus.mFourier e).continuous hρ hs).2.trans_eq he
  · exact (exponential_fourierCoeff_im _ (UnitAddTorus.mFourier e).continuous hρ hs).2.trans_eq he

/-- A single natural bound controls every base coordinate uniformly over
all arithmetic RHS vectors. The RHS oscillator contributes only its exact
exponential frequency factor. -/
theorem exists_uniform_sourceGraph_fourier_bound
    (I : DQLSystem eqs vars) (controller : Fin (vars + eqs) → Controller.ControllerState ℝ)
    {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hθ : (1 / 256 : ℝ) * ρ ^
      (4 + 4 * ∑ row, ∑ j, |(I.linear row j : ℝ)|) ≤ 1 / 8)
    (hP : (1 / 2 : ℝ) * ρ ^
      (4 + 4 * ∑ row, ∑ j, |(I.quadratic row j : ℝ)|) ≤ 3 / 4) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (rhs : Fin eqs → ℤ)
      (i : Fin (FixedDetectorPolynomialCode.dimension eqs vars)),
      Summable (fun a : Fin (vars + eqs) → ℤ ↦
        ‖UnitAddTorus.mFourierCoeff
          (fun x ↦ (intendedSourceGraph { I with rhs := rhs } controller x i : ℂ)) a‖ *
            ρ ^ (∑ k, |(a k : ℝ)|)) ∧
      (∑' a : Fin (vars + eqs) → ℤ, ‖UnitAddTorus.mFourierCoeff
        (fun x ↦ (intendedSourceGraph { I with rhs := rhs } controller x i : ℂ)) a‖ *
          ρ ^ (∑ k, |(a k : ℝ)|)) ≤ (C : ℝ) * ρ ^ (4 * ∑ row, |(rhs row : ℝ)|) := by
  let v := fun i : Fin (FixedDetectorPolynomialCode.dimension eqs vars) ↦
    ∑' a : Fin (vars + eqs) → ℤ, ‖UnitAddTorus.mFourierCoeff
      (fun x ↦ (intendedSourceGraph I controller x i : ℂ)) a‖ * ρ ^ (∑ k, |(a k : ℝ)|)
  have hv (i) : 0 ≤ v i := tsum_nonneg fun _ ↦ by positivity
  obtain ⟨C, hC⟩ := exists_nat_ge (1 + ∑ i, v i)
  have hC1 : (1 : ℝ) ≤ C := by
    have hs : 0 ≤ ∑ i, v i := Finset.sum_nonneg (fun i _ ↦ hv i)
    linarith
  refine ⟨C, by exact_mod_cast hC1, fun rhs i ↦ ⟨?_, ?_⟩⟩
  · exact summable_weighted_intendedSourceGraph_of_matrix_bounds
      { I with rhs := rhs } controller hρ hθ hP i
  · have hw : 1 ≤ ρ ^ (4 * ∑ row, |(rhs row : ℝ)|) :=
      Real.one_le_rpow hρ (by positivity)
    obtain ⟨a | b, rfl⟩ := finSumFinEquiv.surjective i
    · have he : (fun x ↦ (intendedSourceGraph { I with rhs := rhs } controller x
          (finSumFinEquiv (Sum.inl a)) : ℂ)) =
          fun x ↦ (intendedSourceGraph I controller x (finSumFinEquiv (Sum.inl a)) : ℂ) := by
        funext x
        unfold intendedSourceGraph FixedDetectorPolynomialCode.point
          RHSOscillatorPolynomialCode.combinedPoint PolynomialBlockCode.point
        simp only [Equiv.symm_apply_apply, intendedSourceStateGraph_base_replace_rhs]
      rw [he]
      have hsingle : v (finSumFinEquiv (Sum.inl a)) ≤ ∑ i, v i :=
        Finset.single_le_sum (fun i _ ↦ hv i) (Finset.mem_univ _)
      have hbase : v (finSumFinEquiv (Sum.inl a)) ≤ C := by linarith
      exact hbase.trans (le_mul_of_one_le_right (zero_le_one.trans hC1) hw)
    · have hrhs := rhs_coordinates_weighted_bound { I with rhs := rhs } controller hρ b
      have hscale := mul_le_mul_of_nonneg_right hC1
        (by positivity : 0 ≤ ρ ^ (4 * ∑ row, |(rhs row : ℝ)|))
      simpa only [intendedSourceGraph, FixedDetectorPolynomialCode.point,
        RHSOscillatorPolynomialCode.combinedPoint, PolynomialBlockCode.point,
        Equiv.symm_apply_apply] using
        hrhs.trans (by simpa only [one_mul] using hscale)

/-- Polynomial substitution gives the precise RHS exponent `4 D |rhs|₁`.
The common base bound is independent of both the RHS and the polynomial;
its present construction is not an effective resource bound. -/
theorem exists_uniform_sourceGraph_polynomial_fourier_bound
    (I : DQLSystem eqs vars) (controller : Fin (vars + eqs) → Controller.ControllerState ℝ)
    {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hθ : (1 / 256 : ℝ) * ρ ^
      (4 + 4 * ∑ row, ∑ j, |(I.linear row j : ℝ)|) ≤ 1 / 8)
    (hP : (1 / 2 : ℝ) * ρ ^
      (4 + 4 * ∑ row, ∑ j, |(I.quadratic row j : ℝ)|) ≤ 3 / 4) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (rhs : Fin eqs → ℤ)
      (P : MvPolynomial (Fin (FixedDetectorPolynomialCode.dimension eqs vars)) ℚ),
      Summable (fun a : Fin (vars + eqs) → ℤ ↦
        ‖UnitAddTorus.mFourierCoeff
          (fun x ↦ MvPolynomial.eval₂ (algebraMap ℚ ℂ)
            (fun i ↦ (intendedSourceGraph { I with rhs := rhs } controller x i : ℂ)) P) a‖ *
              ρ ^ (∑ k, |(a k : ℝ)|)) ∧
      (∑' a : Fin (vars + eqs) → ℤ, ‖UnitAddTorus.mFourierCoeff
        (fun x ↦ MvPolynomial.eval₂ (algebraMap ℚ ℂ)
          (fun i ↦ (intendedSourceGraph { I with rhs := rhs } controller x i : ℂ)) P) a‖ *
            ρ ^ (∑ k, |(a k : ℝ)|)) ≤
        (∑ e ∈ P.support, ‖((P.coeff e : ℚ) : ℂ)‖) * (C : ℝ) ^ P.totalDegree *
          ρ ^ (4 * (P.totalDegree : ℝ) * ∑ row, |(rhs row : ℝ)|) := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_sourceGraph_fourier_bound I controller hρ hθ hP
  refine ⟨C, hC, fun rhs P ↦ ?_⟩
  have hC' : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have hw : 1 ≤ ρ ^ (4 * ∑ row, |(rhs row : ℝ)|) :=
    Real.one_le_rpow hρ (by positivity)
  have hp := exponential_fourierCoeff_polynomial P (algebraMap ℚ ℂ)
    (fun i x ↦ (intendedSourceGraph { I with rhs := rhs } controller x i : ℂ))
    (fun i ↦ Complex.continuous_ofReal.comp
      ((continuous_apply i).comp (continuous_intendedSourceGraph _ _))) hρ
    (one_le_mul_of_one_le_of_one_le hC' hw) (fun i ↦ (hb rhs i).1)
    (fun i ↦ (hb rhs i).2)
  refine ⟨hp.1, hp.2.trans_eq ?_⟩
  rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans hρ)]
  simp only [← mul_assoc]
  congr 2
  ring

end Stability.Selection
