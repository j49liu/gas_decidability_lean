import Stability.Selection.OrdinaryTimeThetaBudget
import Stability.Selection.OrdinaryTimeSourceFourierBound

/-!
# A numerical Fourier budget for the full source graph

The printed ratio conditions give uniform natural bounds for every base
coordinate. Only the RHS oscillator retains its exponential frequency
factor. The estimates use the actual real source encoder.
-/

noncomputable section

open scoped BigOperators

namespace Stability.Selection

open HGAS HGAS.Analysis HGAS.Modular HGAS.Clocks

/-- A deliberately coarse, fixed natural budget for source coordinates. -/
def sourceCoordinateFourierBudget : ℕ := 262144 ^ 4 + 1048576 + 385 + 32 + 1

theorem sourceCoordinateFourierBudget_pos : 0 < sourceCoordinateFourierBudget := by
  norm_num [sourceCoordinateFourierBudget]

private abbrev FourierNorm {d : Type*} [Fintype d] (ρ : ℝ)
    (f : UnitAddTorus d → ℂ) : ℝ :=
  ∑' a : d → ℤ, ‖UnitAddTorus.mFourierCoeff f a‖ * ρ ^ (∑ i, |(a i : ℝ)|)

/-- The two explicit half-period expansions agree on the whole torus,
including the odd characteristic's minus sign. -/
theorem halfPeriodThetaGraph_eq_neg_halfPeriodJacobiGraph {eqs vars : ℕ}
    (I : DQLSystem eqs vars) (j : Fin vars)
    (x : UnitAddTorus (Fin (vars + eqs))) :
    halfPeriodThetaGraph I j x = -halfPeriodJacobiGraph I j 1 1 x := by
  have hl (i : Fin (vars + eqs)) : ∃ y : ℝ, (y : UnitAddCircle) = x i :=
    QuotientAddGroup.mk_surjective (x i)
  choose y hy using hl
  have hx : (fun i ↦ (y i : UnitAddCircle)) = x := funext hy
  rw [← hx, halfPeriodThetaGraph_eq_jacobiTheta1]
  have ht := congrFun (halfPeriodJacobiVectorGraph_eq_jacobiThetaVector I j y) 0
  simpa only [halfPeriodJacobiVectorGraph, jacobiThetaVector, Matrix.cons_val_zero] using ht.symm

/-- Every encoded complex linked coordinate has the explicit natural
budget, independent of arithmetic matrix sizes and entries. -/
theorem sourceLinkedThetaGraph_weightedFourier_bound {eqs vars : ℕ}
    (I : DQLSystem eqs vars) (j : Fin vars) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hratio : (1 / 256 : ℝ) * ρ ^ (4 + 4 * ∑ row, |(I.linear row j : ℝ)|) ≤ 1 / 8)
    (i : Fin LinkedJacobiPolynomialCode.dimension) :
    (∑' a : Fin (vars + eqs) → ℤ, ‖UnitAddTorus.mFourierCoeff
      (fun x ↦ LinkedJacobiPolynomialCode.point (sourceLinkedThetaGraph I j x) i) a‖ *
        ρ ^ (∑ k, |(a k : ℝ)|)) ≤ sourceCoordinateFourierBudget := by
  let p : Fin (vars + eqs) := finSumFinEquiv (Sum.inl j)
  have hD : 0 ≤ ∑ row, |(I.linear row j : ℝ)| :=
    Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have huRatio : (1 / 256 : ℝ) * ρ ^ (4 : ℝ) ≤ 1 / 8 :=
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hρ (by linarith)) (by norm_num)).trans hratio
  have hu (q r : ℤ) (hq : q = 0 ∨ q = 1) :=
    unaryThetaGraph_weightedFourier_bound p q r hq hρ huRatio
  have hup (q r : ℤ) (hq : q = 0 ∨ q = 1) (n : ℕ) :
      FourierNorm ρ (fun x ↦ unaryThetaGraph p q r x ^ n) ≤ 262144 ^ n :=
    (exponential_fourierCoeff_pow _ (continuous_unaryThetaGraph p q r) hρ
      (hu q r hq).1 n).2.trans
        (pow_le_pow_left₀ (tsum_nonneg fun _ ↦ by positivity) (hu q r hq).2 _)
  have hE := eisensteinGraph_weightedFourier_bound p hρ huRatio
  have hH : FourierNorm ρ (fun x ↦ eisensteinGraph p x / 12) ≤ 385 / 12 := by
    have he := (exponential_fourierCoeff_const_mul (eisensteinGraph p)
      (1 / 12 : ℂ) ρ hE.1).2
    norm_num only [norm_div, norm_one, Complex.norm_ofNat] at he
    have hb := mul_le_mul_of_nonneg_left hE.2 (by norm_num : (0 : ℝ) ≤ 1 / 12)
    rw [← he] at hb
    simpa only [FourierNorm, div_eq_mul_inv, one_mul, mul_comm] using hb
  have hJ (q r : ℤ) (hq : q = 0 ∨ q = 1) :=
    halfPeriodJacobiGraph_weightedFourier_bound I j q r hq hρ hratio
  have hT1 : FourierNorm ρ (halfPeriodThetaGraph I j) ≤ 262144 := by
    have he : halfPeriodThetaGraph I j = fun x ↦ -halfPeriodJacobiGraph I j 1 1 x :=
      funext (halfPeriodThetaGraph_eq_neg_halfPeriodJacobiGraph I j)
    rw [he]
    simpa only [FourierNorm, UnitAddTorus.mFourierCoeff, smul_eq_mul, mul_neg,
      MeasureTheory.integral_neg, norm_neg] using (hJ 1 1 (Or.inr rfl)).2
  have hT (k : Fin 4) : FourierNorm ρ (fun x ↦ halfPeriodJacobiVectorGraph I j x k) ≤
      262144 := by
    fin_cases k
    · change FourierNorm ρ (fun x ↦ -halfPeriodJacobiGraph I j 1 1 x) ≤ 262144
      simpa only [FourierNorm, UnitAddTorus.mFourierCoeff, smul_eq_mul, mul_neg,
        MeasureTheory.integral_neg, norm_neg] using (hJ 1 1 (Or.inr rfl)).2
    · exact (hJ 1 0 (Or.inr rfl)).2
    · exact (hJ 0 0 (Or.inl rfl)).2
    · exact (hJ 0 1 (Or.inl rfl)).2
  have hDelta := (halfPeriodJacobiDerivativeGraph_weightedFourier_bound I j hρ hratio).2
  have hGauge : ρ ^ (1 + 2 * ∑ row, |(I.linear row j : ℝ)|) ≤ 32 := by
    have he := Real.rpow_le_rpow_of_exponent_le hρ
      (show 1 + 2 * ∑ row, |(I.linear row j : ℝ)| ≤
        4 + 4 * ∑ row, |(I.linear row j : ℝ)| by linarith)
    linarith
  have hU : FourierNorm ρ (thetaReciprocalGraph I j) ≤ 12 := by
    have hb := (thetaReciprocalGraph_weightedFourier_bound I j hρ hratio).2
    exact hb.trans (by nlinarith)
  obtain ⟨u | q, rfl⟩ := finSumFinEquiv.surjective i
  · fin_cases u
    · exact (hup 1 0 (Or.inr rfl) 4).trans (by norm_num [sourceCoordinateFourierBudget])
    · exact (hup 0 1 (Or.inl rfl) 4).trans (by norm_num [sourceCoordinateFourierBudget])
    · exact hE.2.trans (by norm_num [sourceCoordinateFourierBudget])
    · exact (hu 0 0 (Or.inl rfl)).2.trans (by norm_num [sourceCoordinateFourierBudget])
  · fin_cases q
    · exact (hup 1 0 (Or.inr rfl) 2).trans (by norm_num [sourceCoordinateFourierBudget])
    · exact (hup 0 0 (Or.inl rfl) 2).trans (by norm_num [sourceCoordinateFourierBudget])
    · exact (hup 0 1 (Or.inl rfl) 2).trans (by norm_num [sourceCoordinateFourierBudget])
    · exact hH.trans (by norm_num [sourceCoordinateFourierBudget])
    · exact hT1.trans (by norm_num [sourceCoordinateFourierBudget])
    · exact (hT 1).trans (by norm_num [sourceCoordinateFourierBudget])
    · exact (hT 2).trans (by norm_num [sourceCoordinateFourierBudget])
    · exact (hT 3).trans (by norm_num [sourceCoordinateFourierBudget])
    · exact hDelta.trans (by norm_num [sourceCoordinateFourierBudget])
    · exact hU.trans (by norm_num [sourceCoordinateFourierBudget])

private theorem budget_blockPoint {X R : Type*} {m n : ℕ}
    (P : (X → R) → Prop) (f : X → Fin m → R) (g : X → Fin n → R)
    (hf : ∀ i, P (fun x ↦ f x i)) (hg : ∀ i, P (fun x ↦ g x i))
    (i : Fin (m + n)) : P (fun x ↦ PolynomialBlockCode.point (f x) (g x) i) := by
  obtain ⟨a | b, rfl⟩ := finSumFinEquiv.surjective i
  · simpa only [PolynomialBlockCode.point, Equiv.symm_apply_apply] using hf a
  · simpa only [PolynomialBlockCode.point, Equiv.symm_apply_apply] using hg b

private theorem budget_realifyPoint {d : Type*} [Fintype d] {n : ℕ}
    (f : UnitAddTorus d → Fin n → ℂ) (hc : Continuous f) {ρ B : ℝ} (hρ : 1 ≤ ρ)
    (hf : ∀ i, Summable fun a ↦ ‖UnitAddTorus.mFourierCoeff (fun x ↦ f x i) a‖ *
      ρ ^ (∑ j, |(a j : ℝ)|)) (hb : ∀ i, FourierNorm ρ (fun x ↦ f x i) ≤ B)
    (i : Fin (n + n)) :
    FourierNorm ρ (fun x ↦ (ComplexCoordinates.realifyPoint (f x) i : ℂ)) ≤ B := by
  obtain ⟨a | b, rfl⟩ := finSumFinEquiv.surjective i
  · simpa only [ComplexCoordinates.realifyPoint, Equiv.symm_apply_apply] using
      (exponential_fourierCoeff_re _ ((continuous_apply a).comp hc) hρ (hf a)).2.trans (hb a)
  · simpa only [ComplexCoordinates.realifyPoint, Equiv.symm_apply_apply] using
      (exponential_fourierCoeff_im _ ((continuous_apply b).comp hc) hρ (hf b)).2.trans (hb b)

private theorem budget_reciprocalPoint {d : Type*} [Fintype d] {n : ℕ}
    (f : UnitAddTorus d → Fin n → ℂ) (hc : Continuous f) {ρ B : ℝ} (hρ : 1 ≤ ρ)
    (hf : ∀ i, Summable fun a ↦ ‖UnitAddTorus.mFourierCoeff (fun x ↦ f x i) a‖ *
      ρ ^ (∑ j, |(a j : ℝ)|)) (hb : ∀ i, FourierNorm ρ (fun x ↦ f x i) ≤ B)
    (i : Fin (ComplexReciprocalFamilyPolynomialCode.reciprocalDimension n)) :
    FourierNorm ρ
      (fun x ↦ (ComplexReciprocalFamilyPolynomialCode.reciprocalPoint (f x) i : ℂ)) ≤ B := by
  obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective i
  fin_cases b
  · simpa only [ComplexReciprocalFamilyPolynomialCode.reciprocalPoint,
      PolynomialFiniteProductCode.flattenPoint, Equiv.symm_apply_apply,
      Matrix.cons_val_zero] using
      (exponential_fourierCoeff_re _ ((continuous_apply a).comp hc) hρ (hf a)).2.trans (hb a)
  · simpa [ComplexReciprocalFamilyPolynomialCode.reciprocalPoint,
      PolynomialFiniteProductCode.flattenPoint] using
      (exponential_fourierCoeff_im _ ((continuous_apply a).comp hc) hρ (hf a)).2.trans (hb a)

private theorem budget_character_summable {d : Type*} [Fintype d]
    (e : d → ℤ) {ρ : ℝ} (hρ : 1 ≤ ρ) :
    Summable fun a ↦ ‖UnitAddTorus.mFourierCoeff (UnitAddTorus.mFourier e) a‖ *
      ρ ^ (∑ i, |(a i : ℝ)|) := by
  simpa only [mul_one, one_mul] using
    (exponential_fourierCoeff_scalar_character_mul
      (fun _ : UnitAddTorus d ↦ 1) 1 e hρ (exponential_fourierCoeff_const 1 ρ).1).1

/-- An effective bound for every real source coordinate. Unit controller
coordinates are explicit hypotheses; no controller equilibrium or ODE
claim is needed for this Fourier estimate. -/
theorem intendedSourceGraph_weightedFourier_bound {eqs vars : ℕ}
    (I : DQLSystem eqs vars) (controller : Fin (vars + eqs) → Controller.ControllerState ℝ)
    (hcontroller : ∀ i, |(controller i).r| ≤ 1 ∧ |(controller i).s| ≤ 1)
    {ρ : ℝ} (hρ : 1 ≤ ρ) (huRatio : (1 / 256 : ℝ) * ρ ^ (4 : ℝ) ≤ 1 / 8)
    (hθ : ∀ j, (1 / 256 : ℝ) * ρ ^ (4 + 4 * ∑ row, |(I.linear row j : ℝ)|) ≤ 1 / 8)
    (hP : ∀ j, (1 / 2 : ℝ) * ρ ^ (4 + 4 * ∑ row, |(I.quadratic row j : ℝ)|) ≤ 3 / 4)
    (i : Fin (FixedDetectorPolynomialCode.dimension eqs vars)) :
    (∑' a : Fin (vars + eqs) → ℤ, ‖UnitAddTorus.mFourierCoeff
      (fun x ↦ (intendedSourceGraph I controller x i : ℂ)) a‖ *
        ρ ^ (∑ k, |(a k : ℝ)|)) ≤
      (sourceCoordinateFourierBudget : ℝ) * ρ ^ (4 * ∑ row, |(I.rhs row : ℝ)|) := by
  let C : ℝ := sourceCoordinateFourierBudget
  let B : ℝ := C * ρ ^ (4 * ∑ row, |(I.rhs row : ℝ)|)
  let P : (UnitAddTorus (Fin (vars + eqs)) → ℝ) → Prop := fun f ↦
    FourierNorm ρ (fun x ↦ (f x : ℂ)) ≤ B
  have hC : 1 ≤ C := by norm_num [C, sourceCoordinateFourierBudget]
  have hCB : C ≤ B := le_mul_of_one_le_right (zero_le_one.trans hC)
    (Real.one_le_rpow hρ (by positivity))
  have h32 : (32 : ℝ) ≤ B :=
    (by norm_num [C, sourceCoordinateFourierBudget] : (32 : ℝ) ≤ C).trans hCB
  have hρ32 : ρ ≤ 32 := by
    have he := Real.rpow_le_rpow_of_exponent_le hρ (by norm_num : (1 : ℝ) ≤ 4)
    rw [Real.rpow_one] at he
    linarith
  have hc (j : Fin (vars + eqs)) (k : Fin ControllerPolynomialCode.dimension) :
      P (fun x ↦ ControllerPolynomialCode.point
        { controller := controller j, phase := sourcePhaseGraph x j } k) := by
    have hp : FourierNorm ρ (UnitAddTorus.mFourier (Pi.single j 1)) ≤ B := by
      have he : (∑ k, |(((Pi.single j 1 : Fin (vars + eqs) → ℤ) k : ℤ) : ℝ)|) = 1 := by
        simp [Pi.single_apply, apply_ite abs]
      change (∑' a, ‖UnitAddTorus.mFourierCoeff (UnitAddTorus.mFourier (Pi.single j 1)) a‖ *
        ρ ^ (∑ k, |(a k : ℝ)|)) ≤ B
      rw [tsum_weighted_fourierCoeff_character, he, Real.rpow_one]
      exact hρ32.trans h32
    fin_cases k
    · change FourierNorm ρ (fun _ ↦ ((controller j).r : ℂ)) ≤ B
      exact (exponential_fourierCoeff_const _ ρ).2.le.trans (by
        simpa only [Complex.norm_real, Real.norm_eq_abs] using
          (hcontroller j).1.trans (hC.trans hCB))
    · change FourierNorm ρ (fun _ ↦ ((controller j).s : ℂ)) ≤ B
      exact (exponential_fourierCoeff_const _ ρ).2.le.trans (by
        simpa only [Complex.norm_real, Real.norm_eq_abs] using
          (hcontroller j).2.trans (hC.trans hCB))
    · exact (exponential_fourierCoeff_re _ (UnitAddTorus.mFourier _).continuous hρ
        (budget_character_summable (Pi.single j 1) hρ)).2.trans hp
    · exact (exponential_fourierCoeff_im _ (UnitAddTorus.mFourier _).continuous hρ
        (budget_character_summable (Pi.single j 1) hρ)).2.trans hp
  have hcontrollers (k) : P (fun x ↦
      ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint
        (intendedSourceStateGraph I controller x).base.base.source k) :=
    hc (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  have hlinked (k) : P (fun x ↦
      ControllerProductLinkedJacobiFamilyPolynomialCode.linkedFamilyPoint
        (intendedSourceStateGraph I controller x).base.base.source k) :=
    budget_realifyPoint _
      (continuous_sourceLinkedThetaGraph_point I (finProdFinEquiv.symm k).1) hρ
      (summable_weighted_sourceLinkedThetaGraph I (finProdFinEquiv.symm k).1 hρ
        (huRatio.trans_lt (by norm_num)) (hθ _))
      (fun c ↦ (sourceLinkedThetaGraph_weightedFourier_bound I _ hρ (hθ _) c).trans hCB)
      (finProdFinEquiv.symm k).2
  have hsource (k) : P (fun x ↦ ControllerProductLinkedJacobiFamilyPolynomialCode.point
      (intendedSourceStateGraph I controller x).base.base.source k) :=
    budget_blockPoint P _ _ hcontrollers hlinked k
  have hgauge (j) := exponential_fourierCoeff_const_mul
    (UnitAddTorus.mFourier (CanonicalFixedDetectorTrajectory.gaugeRootExponent I j))
    (1 / 4 : ℂ) ρ (budget_character_summable _ hρ)
  have hgaugeBound (j) : FourierNorm ρ (fun x ↦
      (intendedSourceStateGraph I controller x).base.base.gauge j) ≤ B := by
    have he := (hgauge j).2
    rw [tsum_weighted_fourierCoeff_character, gaugeRootExponent_length] at he
    norm_num only [norm_div, norm_one, Complex.norm_ofNat] at he
    have hD : 0 ≤ ∑ row, |(I.linear row j : ℝ)| :=
      Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
    have hw := Real.rpow_le_rpow_of_exponent_le hρ
      (show 1 + 2 * ∑ row, |(I.linear row j : ℝ)| ≤
        4 + 4 * ∑ row, |(I.linear row j : ℝ)| by linarith)
    have ht := hθ j
    exact he.le.trans (by linarith)
  have hgaugeCont : Continuous (fun x ↦
      (intendedSourceStateGraph I controller x).base.base.gauge) := by
    apply continuous_pi
    intro j
    exact continuous_const.mul (UnitAddTorus.mFourier _).continuous
  have hbase (k) : P (fun x ↦ ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.point
      (intendedSourceStateGraph I controller x).base.base k) :=
    budget_blockPoint P _ _ hsource
      (budget_reciprocalPoint _ hgaugeCont hρ (fun j ↦ (hgauge j).1) hgaugeBound) k
  have hreciprocal (k : Fin (DetectorPoissonReciprocalCode.reciprocalCount vars)) :=
    poissonReciprocalGraph_weightedFourier_bound I
    (finProdFinEquiv.symm k).1 (if (finProdFinEquiv.symm k).2 = 0 then 1 else -1)
    (by split_ifs <;> norm_num) hρ (hP (finProdFinEquiv.symm k).1)
  have hreciprocalCont : Continuous (fun x ↦
      (intendedSourceStateGraph I controller x).base.reciprocal) := by
    apply continuous_pi
    intro k
    exact continuous_poissonReciprocalGraph I _ _
  have hpoisson (k) : P (fun x ↦ DetectorPoissonReciprocalCode.point
      (intendedSourceStateGraph I controller x).base k) :=
    budget_blockPoint P _ _ hbase
      (budget_reciprocalPoint _ hreciprocalCont hρ (fun k ↦ (hreciprocal k).1)
        (fun k ↦ (hreciprocal k).2.trans ((by norm_num : (4 : ℝ) ≤ 32).trans h32))) k
  have hrhs (k : Fin 2) : P (fun x ↦ ![(intendedSourceStateGraph I controller x).rhs.c,
      (intendedSourceStateGraph I controller x).rhs.d] k) :=
    (rhs_coordinates_weighted_bound I controller hρ k).trans
      (le_mul_of_one_le_left (by positivity) hC)
  exact budget_blockPoint P _ _ hpoisson hrhs i

/-- The global matrix inequalities suffice for the explicit budget,
including an empty family of linked blocks. -/
theorem intendedSourceGraph_weightedFourier_bound_of_matrix_bounds {eqs vars : ℕ}
    (I : DQLSystem eqs vars) (controller : Fin (vars + eqs) → Controller.ControllerState ℝ)
    (hcontroller : ∀ i, |(controller i).r| ≤ 1 ∧ |(controller i).s| ≤ 1)
    {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hθ : (1 / 256 : ℝ) * ρ ^
      (4 + 4 * ∑ row, ∑ j, |(I.linear row j : ℝ)|) ≤ 1 / 8)
    (hP : (1 / 2 : ℝ) * ρ ^
      (4 + 4 * ∑ row, ∑ j, |(I.quadratic row j : ℝ)|) ≤ 3 / 4)
    (i : Fin (FixedDetectorPolynomialCode.dimension eqs vars)) :
    (∑' a : Fin (vars + eqs) → ℤ, ‖UnitAddTorus.mFourierCoeff
      (fun x ↦ (intendedSourceGraph I controller x i : ℂ)) a‖ *
        ρ ^ (∑ k, |(a k : ℝ)|)) ≤
      (sourceCoordinateFourierBudget : ℝ) * ρ ^ (4 * ∑ row, |(I.rhs row : ℝ)|) := by
  have hB : 0 ≤ ∑ row, ∑ j, |(I.linear row j : ℝ)| :=
    Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  apply intendedSourceGraph_weightedFourier_bound I controller hcontroller hρ ?_ ?_ ?_ i
  · exact (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hρ (by linarith)) (by norm_num)).trans hθ
  · intro j
    have hcol : (∑ row, |(I.linear row j : ℝ)|) ≤
        ∑ row, ∑ k, |(I.linear row k : ℝ)| := by
      apply Finset.sum_le_sum
      intro row _
      exact Finset.single_le_sum (fun k _ ↦ abs_nonneg (I.linear row k : ℝ))
        (Finset.mem_univ j)
    exact (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hρ (by linarith)) (by norm_num)).trans hθ
  · intro j
    have hcol : (∑ row, |(I.quadratic row j : ℝ)|) ≤
        ∑ row, ∑ k, |(I.quadratic row k : ℝ)| := by
      apply Finset.sum_le_sum
      intro row _
      exact Finset.single_le_sum (fun k _ ↦ abs_nonneg (I.quadratic row k : ℝ))
        (Finset.mem_univ j)
    exact (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hρ (by linarith)) (by norm_num)).trans hP

end Stability.Selection
