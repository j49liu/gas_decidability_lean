import Stability.Selection.OrdinaryTimeSourceGraph
import Stability.Selection.OrdinaryTimeFourierAlgebra
import Stability.Selection.OrdinaryTimeFourierRealification

/-!
# Weighted Fourier summability of the literal source graph

The coordinate estimates are assembled through the actual source encoder.
Every final coefficient below is a Haar Fourier coefficient of a real
coordinate of `Γ`, viewed as a complex-valued function.
-/

noncomputable section

open scoped BigOperators

namespace Stability.Selection

open HGAS HGAS.Analysis HGAS.Modular HGAS.Clocks

variable {eqs vars : ℕ}

private abbrev WeightedSummable {d : Type*} [Fintype d] (ρ : ℝ)
    (f : UnitAddTorus d → ℂ) : Prop :=
  Summable fun a : d → ℤ ↦ ‖UnitAddTorus.mFourierCoeff f a‖ * ρ ^ (∑ i, |(a i : ℝ)|)

private theorem weighted_character {d : Type*} [Fintype d] (a : d → ℤ)
    {ρ : ℝ} (hρ : 1 ≤ ρ) : WeightedSummable ρ (UnitAddTorus.mFourier a) := by
  have h := exponential_fourierCoeff_scalar_character_mul
    (fun _ : UnitAddTorus d ↦ 1) 1 a hρ (exponential_fourierCoeff_const 1 ρ).1
  simpa only [mul_one, one_mul] using h.1

private theorem weighted_scalar {d : Type*} [Fintype d] (c : ℂ)
    (f : UnitAddTorus d → ℂ) {ρ : ℝ} (hρ : 1 ≤ ρ) (hf : WeightedSummable ρ f) :
    WeightedSummable ρ (fun x ↦ c * f x) := by
  have h := exponential_fourierCoeff_scalar_character_mul f c 0 hρ hf
  simpa only [UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, mul_one] using h.1

/-- Each of the fourteen literal linked complex coordinates has finite
weighted Fourier norm under the theta and reciprocal ratio bounds. -/
theorem summable_weighted_sourceLinkedThetaGraph
    (I : DQLSystem eqs vars) (j : Fin vars) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hdecay : (1 / 256 : ℝ) * ρ ^ (4 : ℝ) < 1)
    (hratio : (1 / 256 : ℝ) * ρ ^ (4 + 4 * ∑ row, |(I.linear row j : ℝ)|) ≤ 1 / 8)
    (i : Fin LinkedJacobiPolynomialCode.dimension) :
    Summable fun a : Fin (vars + eqs) → ℤ ↦
      ‖UnitAddTorus.mFourierCoeff
        (fun x ↦ LinkedJacobiPolynomialCode.point (sourceLinkedThetaGraph I j x) i) a‖ *
          ρ ^ (∑ k, |(a k : ℝ)|) := by
  let p : Fin (vars + eqs) := finSumFinEquiv (Sum.inl j)
  have hu (q r : ℤ) : WeightedSummable ρ (unaryThetaGraph p q r) :=
    summable_weighted_unaryThetaGraph p q r hρ hdecay
  have hup (q r : ℤ) (n : ℕ) : WeightedSummable ρ (fun x ↦ unaryThetaGraph p q r x ^ n) :=
    (exponential_fourierCoeff_pow _ (continuous_unaryThetaGraph p q r) hρ (hu q r) n).1
  have hE : WeightedSummable ρ (eisensteinGraph p) :=
    summable_weighted_eisensteinGraph_of_theta_decay p hρ hdecay
  have hH : WeightedSummable ρ (fun x ↦ eisensteinGraph p x / 12) := by
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using
      weighted_scalar (1 / 12 : ℂ) (eisensteinGraph p) hρ hE
  have hT1 := summable_weighted_halfPeriodThetaGraph I j hρ hdecay
  have hT (k : Fin 4) := summable_weighted_halfPeriodJacobiVectorGraph I j k hρ hdecay
  have hD := summable_weighted_halfPeriodJacobiDerivativeGraph I j hρ hdecay
  have hU := (thetaReciprocalGraph_weightedFourier_bound I j hρ hratio).1
  obtain ⟨u | q, rfl⟩ := finSumFinEquiv.surjective i
  · fin_cases u
    · exact hup 1 0 4
    · exact hup 0 1 4
    · exact hE
    · exact hu 0 0
  · fin_cases q
    · exact hup 1 0 2
    · exact hup 0 0 2
    · exact hup 0 1 2
    · exact hH
    · exact hT1
    · exact hT 1
    · exact hT 2
    · exact hT 3
    · exact hD
    · exact hU

private theorem blockPoint_property {X R : Type*} {m n : ℕ}
    (P : (X → R) → Prop) (f : X → Fin m → R) (g : X → Fin n → R)
    (hf : ∀ i, P (fun x ↦ f x i)) (hg : ∀ i, P (fun x ↦ g x i))
    (i : Fin (m + n)) : P (fun x ↦ PolynomialBlockCode.point (f x) (g x) i) := by
  obtain ⟨a | b, rfl⟩ := finSumFinEquiv.surjective i
  · simpa only [PolynomialBlockCode.point, Equiv.symm_apply_apply] using hf a
  · simpa only [PolynomialBlockCode.point, Equiv.symm_apply_apply] using hg b

private theorem weighted_realifyPoint {d : Type*} [Fintype d] {n : ℕ}
    (f : UnitAddTorus d → Fin n → ℂ) (hc : Continuous f) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hf : ∀ i, WeightedSummable ρ (fun x ↦ f x i)) (i : Fin (n + n)) :
    WeightedSummable ρ (fun x ↦ (ComplexCoordinates.realifyPoint (f x) i : ℂ)) := by
  obtain ⟨a | b, rfl⟩ := finSumFinEquiv.surjective i
  · simpa only [ComplexCoordinates.realifyPoint, Equiv.symm_apply_apply] using
      (exponential_fourierCoeff_re _ ((continuous_apply a).comp hc) hρ (hf a)).1
  · simpa only [ComplexCoordinates.realifyPoint, Equiv.symm_apply_apply] using
      (exponential_fourierCoeff_im _ ((continuous_apply b).comp hc) hρ (hf b)).1

private theorem weighted_reciprocalPoint {d : Type*} [Fintype d] {n : ℕ}
    (f : UnitAddTorus d → Fin n → ℂ) (hc : Continuous f) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hf : ∀ i, WeightedSummable ρ (fun x ↦ f x i))
    (i : Fin (ComplexReciprocalFamilyPolynomialCode.reciprocalDimension n)) :
    WeightedSummable ρ
      (fun x ↦ (ComplexReciprocalFamilyPolynomialCode.reciprocalPoint (f x) i : ℂ)) := by
  obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective i
  fin_cases b
  · simpa [ComplexReciprocalFamilyPolynomialCode.reciprocalPoint,
      PolynomialFiniteProductCode.flattenPoint] using
      (exponential_fourierCoeff_re _ ((continuous_apply a).comp hc) hρ (hf a)).1
  · simpa [ComplexReciprocalFamilyPolynomialCode.reciprocalPoint,
      PolynomialFiniteProductCode.flattenPoint] using
      (exponential_fourierCoeff_im _ ((continuous_apply a).comp hc) hρ (hf a)).1

/-- Every coordinate of the actual real source graph has finite weighted
Fourier norm. The hypotheses are precisely sufficient columnwise ratio
bounds, and no trajectory, selected measure, or Fourier presentation is assumed. -/
theorem summable_weighted_intendedSourceGraph
    (I : DQLSystem eqs vars) (controller : Fin (vars + eqs) → Controller.ControllerState ℝ)
    {ρ : ℝ} (hρ : 1 ≤ ρ) (hdecay : (1 / 256 : ℝ) * ρ ^ (4 : ℝ) < 1)
    (hθ : ∀ j, (1 / 256 : ℝ) * ρ ^ (4 + 4 * ∑ row, |(I.linear row j : ℝ)|) ≤ 1 / 8)
    (hP : ∀ j, (1 / 2 : ℝ) * ρ ^ (4 + 4 * ∑ row, |(I.quadratic row j : ℝ)|) ≤ 3 / 4)
    (i : Fin (FixedDetectorPolynomialCode.dimension eqs vars)) :
    Summable fun a : Fin (vars + eqs) → ℤ ↦
      ‖UnitAddTorus.mFourierCoeff (fun x ↦ (intendedSourceGraph I controller x i : ℂ)) a‖ *
        ρ ^ (∑ k, |(a k : ℝ)|) := by
  let P : (UnitAddTorus (Fin (vars + eqs)) → ℝ) → Prop := fun f ↦
    WeightedSummable ρ (fun x ↦ (f x : ℂ))
  have hc (j : Fin (vars + eqs)) (k : Fin ControllerPolynomialCode.dimension) :
      P (fun x ↦ ControllerPolynomialCode.point
        { controller := controller j, phase := sourcePhaseGraph x j } k) := by
    fin_cases k
    · exact (exponential_fourierCoeff_const ((controller j).r : ℂ) ρ).1
    · exact (exponential_fourierCoeff_const ((controller j).s : ℂ) ρ).1
    · exact (exponential_fourierCoeff_re _ (UnitAddTorus.mFourier _).continuous
        hρ (weighted_character (Pi.single j 1) hρ)).1
    · exact (exponential_fourierCoeff_im _ (UnitAddTorus.mFourier _).continuous
        hρ (weighted_character (Pi.single j 1) hρ)).1
  have hcontrollers (i) : P (fun x ↦
      ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint
        (intendedSourceStateGraph I controller x).base.base.source i) :=
    hc (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
  have hlinked (i) : P (fun x ↦
      ControllerProductLinkedJacobiFamilyPolynomialCode.linkedFamilyPoint
        (intendedSourceStateGraph I controller x).base.base.source i) :=
    weighted_realifyPoint _
      (continuous_sourceLinkedThetaGraph_point I (finProdFinEquiv.symm i).1) hρ
      (summable_weighted_sourceLinkedThetaGraph I (finProdFinEquiv.symm i).1 hρ hdecay
        (hθ (finProdFinEquiv.symm i).1)) (finProdFinEquiv.symm i).2
  have hsource (i) : P (fun x ↦ ControllerProductLinkedJacobiFamilyPolynomialCode.point
      (intendedSourceStateGraph I controller x).base.base.source i) :=
    blockPoint_property P _ _ hcontrollers hlinked i
  have hgauge (j) : WeightedSummable ρ (fun x ↦
      (intendedSourceStateGraph I controller x).base.base.gauge j) :=
    weighted_scalar (1 / 4 : ℂ) _ hρ (weighted_character _ hρ)
  have hgaugeCont : Continuous (fun x ↦
      (intendedSourceStateGraph I controller x).base.base.gauge) := by
    apply continuous_pi
    intro j
    exact continuous_const.mul (UnitAddTorus.mFourier _).continuous
  have hbase (i) : P (fun x ↦ ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.point
      (intendedSourceStateGraph I controller x).base.base i) :=
    blockPoint_property P _ _ hsource (weighted_reciprocalPoint _ hgaugeCont hρ hgauge) i
  have hreciprocal (k) : WeightedSummable ρ (fun x ↦
      (intendedSourceStateGraph I controller x).base.reciprocal k) := by
    apply (poissonReciprocalGraph_weightedFourier_bound I (finProdFinEquiv.symm k).1
      (if (finProdFinEquiv.symm k).2 = 0 then 1 else -1) ?_ hρ
      (hP (finProdFinEquiv.symm k).1)).1
    split_ifs <;> norm_num
  have hreciprocalCont : Continuous (fun x ↦
      (intendedSourceStateGraph I controller x).base.reciprocal) := by
    apply continuous_pi
    intro k
    exact continuous_poissonReciprocalGraph I _ _
  have hpoisson (i) : P (fun x ↦ DetectorPoissonReciprocalCode.point
      (intendedSourceStateGraph I controller x).base i) :=
    blockPoint_property P _ _ hbase
      (weighted_reciprocalPoint _ hreciprocalCont hρ hreciprocal) i
  have hrhs (k : Fin 2) : P (fun x ↦ ![(intendedSourceStateGraph I controller x).rhs.c,
      (intendedSourceStateGraph I controller x).rhs.d] k) := by
    fin_cases k
    · exact (exponential_fourierCoeff_re _ (UnitAddTorus.mFourier _).continuous
        hρ (weighted_character _ hρ)).1
    · exact (exponential_fourierCoeff_im _ (UnitAddTorus.mFourier _).continuous
        hρ (weighted_character _ hρ)).1
  exact blockPoint_property P _ _ hpoisson hrhs i

/-- The two global matrix-norm inequalities printed in the manuscript
imply every columnwise estimate, including when there are no variables. -/
theorem summable_weighted_intendedSourceGraph_of_matrix_bounds
    (I : DQLSystem eqs vars) (controller : Fin (vars + eqs) → Controller.ControllerState ℝ)
    {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hθ : (1 / 256 : ℝ) * ρ ^
      (4 + 4 * ∑ row, ∑ j, |(I.linear row j : ℝ)|) ≤ 1 / 8)
    (hP : (1 / 2 : ℝ) * ρ ^
      (4 + 4 * ∑ row, ∑ j, |(I.quadratic row j : ℝ)|) ≤ 3 / 4)
    (i : Fin (FixedDetectorPolynomialCode.dimension eqs vars)) :
    Summable fun a : Fin (vars + eqs) → ℤ ↦
      ‖UnitAddTorus.mFourierCoeff (fun x ↦ (intendedSourceGraph I controller x i : ℂ)) a‖ *
        ρ ^ (∑ k, |(a k : ℝ)|) := by
  have hB : 0 ≤ ∑ row, ∑ j, |(I.linear row j : ℝ)| :=
    Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hdecay : (1 / 256 : ℝ) * ρ ^ (4 : ℝ) < 1 := by
    have he := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hρ (by linarith :
        (4 : ℝ) ≤ 4 + 4 * ∑ row, ∑ j, |(I.linear row j : ℝ)|))
      (by norm_num : (0 : ℝ) ≤ 1 / 256)
    linarith
  apply summable_weighted_intendedSourceGraph I controller hρ hdecay ?_ ?_ i
  · intro j
    have hcol : (∑ row, |(I.linear row j : ℝ)|) ≤
        ∑ row, ∑ k, |(I.linear row k : ℝ)| := by
      apply Finset.sum_le_sum
      intro row _
      exact Finset.single_le_sum (fun k _ ↦ abs_nonneg (I.linear row k : ℝ))
        (Finset.mem_univ j)
    exact (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hρ (by linarith))
      (by norm_num : (0 : ℝ) ≤ 1 / 256)).trans hθ
  · intro j
    have hcol : (∑ row, |(I.quadratic row j : ℝ)|) ≤
        ∑ row, ∑ k, |(I.quadratic row k : ℝ)| := by
      apply Finset.sum_le_sum
      intro row _
      exact Finset.single_le_sum (fun k _ ↦ abs_nonneg (I.quadratic row k : ℝ))
        (Finset.mem_univ j)
    exact (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hρ (by linarith))
      (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans hP

end Stability.Selection
