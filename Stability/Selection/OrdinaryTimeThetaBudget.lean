import Stability.Selection.OrdinaryTimeJacobiDerivativeGraph
import Stability.Selection.OrdinaryTimeEisensteinGraph
import Stability.Selection.OrdinaryTimeWeightedFourier
import HGAS.Analysis.ExplicitPolynomialGeometricBudget

/-!
# Explicit weighted theta budgets

A shift by two absorbs the finitely many negative quadratic exponents.
The resulting geometric majorant gives natural-number bounds for the
literal theta and differentiated-theta coordinates in Section 9.
-/

noncomputable section

open scoped BigOperators

namespace Stability.Selection

open HGAS HGAS.Analysis

/-- A numerical shift handles negative exponents without changing them
in the original summand. -/
theorem shifted_weighted_term_le_halfGeometric {ρ K σ L : ℝ} (n : ℤ)
    (hρ : 1 ≤ ρ) (hratio : (1 / 256 : ℝ) * ρ ^ K ≤ 1 / 8)
    (hσ : |(n : ℝ)| ≤ σ + 2) (hL : L ≤ K * (σ + 2)) :
    (1 / 256 : ℝ) ^ σ * ρ ^ L ≤ 65536 * (1 / 2 : ℝ) ^ n.natAbs := by
  have hs : 0 ≤ σ + 2 := (abs_nonneg _).trans hσ
  have hl : (1 / 256 : ℝ) ^ (σ + 2) = (1 / 256 : ℝ) ^ σ / 65536 := by
    rw [Real.rpow_add (by norm_num), Real.rpow_two]
    ring
  calc
    _ ≤ (1 / 256 : ℝ) ^ σ * ρ ^ (K * (σ + 2)) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hρ hL) (by positivity)
    _ = 65536 * ((1 / 256 : ℝ) * ρ ^ K) ^ (σ + 2) := by
      rw [Real.mul_rpow (by norm_num) (by positivity),
        Real.rpow_mul (zero_le_one.trans hρ), hl]
      ring
    _ ≤ 65536 * (1 / 2 : ℝ) ^ (σ + 2) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (hratio.trans (by norm_num)) hs) (by norm_num)
    _ ≤ 65536 * (1 / 2 : ℝ) ^ |(n : ℝ)| :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hσ) (by norm_num)
    _ = _ := by rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast, Real.rpow_natCast]

set_option maxHeartbeats 800000 in
-- Comparing the encoded Haar coefficients and raw expansion requires extra elaboration time.
/-- An explicit polynomial/geometric majorant bounds the actual Haar
coefficients after every repeated frequency has been collected. -/
theorem weighted_fourierCoeff_of_halfPolynomial_majorant
    {d : Type*} [Fintype d] (c : ℤ → ℂ) (e : ℤ → d → ℤ)
    {ρ : ℝ} (hρ : 1 ≤ ρ) (M r : ℕ)
    (hbound : ∀ n, ‖c n‖ * ρ ^ (∑ i, |(e n i : ℝ)|) ≤
      (M : ℝ) * halfPolynomialIntWeight r n) :
    Summable (fun a : d → ℤ ↦
      ‖UnitAddTorus.mFourierCoeff (torusFourierSeries c e) a‖ *
        ρ ^ (∑ i, |(a i : ℝ)|)) ∧
    (∑' a : d → ℤ, ‖UnitAddTorus.mFourierCoeff (torusFourierSeries c e) a‖ *
      ρ ^ (∑ i, |(a i : ℝ)|)) ≤ (M * halfPolynomialIntBudget r : ℕ) := by
  have hm := (summable_halfPolynomialIntWeight r).mul_left (M : ℝ)
  have hs : Summable fun n ↦ ‖c n‖ * ρ ^ (∑ i, |(e n i : ℝ)|) :=
    hm.of_nonneg_of_le (fun _ ↦ by positivity) hbound
  have hc : Summable fun n ↦ ‖c n‖ := hs.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun n ↦
    le_mul_of_one_le_right (norm_nonneg _)
      (Real.one_le_rpow hρ (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _))
  refine ⟨summable_weighted_fourierCoeff_of_expansion _ _ _
    (fun _ ↦ by positivity) hc hs, ?_⟩
  refine (tsum_weighted_fourierCoeff_le _ _ _ (fun _ ↦ by positivity) hc hs).trans ?_
  calc
    _ ≤ ∑' n, (M : ℝ) * halfPolynomialIntWeight r n := hs.tsum_le_tsum hbound hm
    _ = (M : ℝ) * ∑' n, halfPolynomialIntWeight r n := tsum_mul_left
    _ ≤ (M : ℝ) * halfPolynomialIntBudget r :=
      mul_le_mul_of_nonneg_left (tsum_halfPolynomialIntWeight_le r) (Nat.cast_nonneg _)
    _ = _ := by norm_cast

private theorem jacobi_shift_bounds (q n : ℤ) (hq : q = 0 ∨ q = 1) :
    |(n : ℝ)| ≤ jacobiGraphQuadratic q n + 2 ∧
    |jacobiGraphQuadratic q n| ≤ jacobiGraphQuadratic q n + 2 ∧
    |(n : ℝ) + (q : ℝ) / 2| ≤ jacobiGraphQuadratic q n + 2 := by
  have hsq := sq_nonneg ((n : ℝ) + (q : ℝ) / 2 + 1 / 2)
  have hsq' := sq_nonneg ((n : ℝ) + (q : ℝ) / 2 + 1)
  have hsq'' := sq_nonneg ((n : ℝ) + (q : ℝ) / 2)
  refine ⟨?_, ?_, ?_⟩
  · rcases hq with rfl | rfl <;>
      norm_num [jacobiGraphQuadratic, abs_le] <;>
      constructor <;> nlinarith [sq_nonneg ((n : ℝ) + 1),
        sq_nonneg ((n : ℝ) + 3 / 2), sq_nonneg ((n : ℝ) + 1 / 2), sq_nonneg (n : ℝ)]
  · rw [abs_le]
    dsimp [jacobiGraphQuadratic]
    constructor <;> nlinarith
  · rw [abs_le]
    dsimp [jacobiGraphQuadratic]
    constructor <;> nlinarith

/-- The half-period Jacobi coefficients have a uniform numerical
majorant under the printed columnwise ratio inequality. -/
theorem halfPeriodJacobi_weighted_term_bound {eqs vars : ℕ}
    (I : DQLSystem eqs vars) (j : Fin vars) (q r n : ℤ) (hq : q = 0 ∨ q = 1)
    {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hratio : (1 / 256 : ℝ) * ρ ^ (4 + 4 * ∑ row, |(I.linear row j : ℝ)|) ≤ 1 / 8) :
    ‖halfPeriodJacobiCoefficient q r n‖ *
      ρ ^ (∑ i, |(halfPeriodJacobiExponent I j q n i : ℝ)|) ≤
        65536 * (1 / 2 : ℝ) ^ n.natAbs := by
  obtain ⟨hn, hs, ht⟩ := jacobi_shift_bounds q n hq
  rw [norm_halfPeriodJacobiCoefficient]
  apply shifted_weighted_term_le_halfGeometric n hρ hratio hn
  rw [halfPeriodJacobiExponent_length]
  have he : |4 * (n : ℝ) + 2 * (q : ℝ)| = 4 * |(n : ℝ) + (q : ℝ) / 2| := by
    rw [show 4 * (n : ℝ) + 2 * (q : ℝ) = 4 * ((n : ℝ) + (q : ℝ) / 2) by ring,
      abs_mul]
    norm_num
  rw [he]
  have hD : 0 ≤ ∑ row, |(I.linear row j : ℝ)| :=
    Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right ht hD]

/-- A coarse natural bound for each literal half-characteristic Jacobi
function, retaining its finitely many negative shifted exponents. -/
theorem halfPeriodJacobiGraph_weightedFourier_bound {eqs vars : ℕ}
    (I : DQLSystem eqs vars) (j : Fin vars) (q r : ℤ) (hq : q = 0 ∨ q = 1)
    {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hratio : (1 / 256 : ℝ) * ρ ^ (4 + 4 * ∑ row, |(I.linear row j : ℝ)|) ≤ 1 / 8) :
    Summable (fun a : Fin (vars + eqs) → ℤ ↦
      ‖UnitAddTorus.mFourierCoeff (halfPeriodJacobiGraph I j q r) a‖ *
        ρ ^ (∑ i, |(a i : ℝ)|)) ∧
    (∑' a : Fin (vars + eqs) → ℤ,
      ‖UnitAddTorus.mFourierCoeff (halfPeriodJacobiGraph I j q r) a‖ *
        ρ ^ (∑ i, |(a i : ℝ)|)) ≤ 262144 := by
  convert weighted_fourierCoeff_of_halfPolynomial_majorant
    (halfPeriodJacobiCoefficient q r) (halfPeriodJacobiExponent I j q) hρ 65536 0
    (fun n ↦ by simpa [halfPolynomialIntWeight] using
      halfPeriodJacobi_weighted_term_bound I j q r n hq hρ hratio) using 1

/-- The same natural bound applies to all three even unary theta
constants. -/
theorem unaryThetaGraph_weightedFourier_bound
    {d : Type*} [Fintype d] [DecidableEq d] (j : d) (q r : ℤ)
    (hq : q = 0 ∨ q = 1) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hratio : (1 / 256 : ℝ) * ρ ^ (4 : ℝ) ≤ 1 / 8) :
    Summable (fun a : d → ℤ ↦
      ‖UnitAddTorus.mFourierCoeff (unaryThetaGraph j q r) a‖ *
        ρ ^ (∑ i, |(a i : ℝ)|)) ∧
    (∑' a : d → ℤ, ‖UnitAddTorus.mFourierCoeff (unaryThetaGraph j q r) a‖ *
      ρ ^ (∑ i, |(a i : ℝ)|)) ≤ 262144 := by
  have hb (n : ℤ) : ‖unaryThetaGraphCoefficient q r n‖ *
      ρ ^ (∑ i, |(unaryThetaGraphExponent j q n i : ℝ)|) ≤
        65536 * (1 / 2 : ℝ) ^ n.natAbs := by
    rw [norm_unaryThetaGraphCoefficient, unaryThetaGraphExponent_length]
    apply shifted_weighted_term_le_halfGeometric n hρ hratio
    · rcases hq with rfl | rfl <;> norm_num [abs_le] <;>
        constructor <;> nlinarith [sq_nonneg ((n : ℝ) + 1),
          sq_nonneg ((n : ℝ) - 1), sq_nonneg (n : ℝ)]
    · linarith
  convert weighted_fourierCoeff_of_halfPolynomial_majorant
    (unaryThetaGraphCoefficient q r) (unaryThetaGraphExponent j q) hρ 65536 0
    (fun n ↦ by simpa [halfPolynomialIntWeight] using hb n) using 1

/-- Differentiating adds one polynomial index factor, still bounded by
a concrete natural number. -/
theorem halfPeriodJacobiDerivativeGraph_weightedFourier_bound {eqs vars : ℕ}
    (I : DQLSystem eqs vars) (j : Fin vars) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hratio : (1 / 256 : ℝ) * ρ ^ (4 + 4 * ∑ row, |(I.linear row j : ℝ)|) ≤ 1 / 8) :
    Summable (fun a : Fin (vars + eqs) → ℤ ↦
      ‖UnitAddTorus.mFourierCoeff (halfPeriodJacobiDerivativeGraph I j) a‖ *
        ρ ^ (∑ i, |(a i : ℝ)|)) ∧
    (∑' a : Fin (vars + eqs) → ℤ,
      ‖UnitAddTorus.mFourierCoeff (halfPeriodJacobiDerivativeGraph I j) a‖ *
        ρ ^ (∑ i, |(a i : ℝ)|)) ≤ 1048576 := by
  have hb (n : ℤ) : ‖halfPeriodJacobiDerivativeCoefficient n‖ *
      ρ ^ (∑ i, |(halfPeriodJacobiExponent I j 1 n i : ℝ)|) ≤
        (131072 : ℝ) * halfPolynomialIntWeight 1 n := by
    calc
      _ ≤ (2 * (1 + |(n : ℝ)|) * ‖halfPeriodJacobiCoefficient 1 1 n‖) *
          ρ ^ (∑ i, |(halfPeriodJacobiExponent I j 1 n i : ℝ)|) :=
        mul_le_mul_of_nonneg_right (derivativeCoefficient_bound n) (by positivity)
      _ = 2 * (1 + |(n : ℝ)|) *
          (‖halfPeriodJacobiCoefficient 1 1 n‖ *
            ρ ^ (∑ i, |(halfPeriodJacobiExponent I j 1 n i : ℝ)|)) := by ring
      _ ≤ 2 * (1 + |(n : ℝ)|) * (65536 * (1 / 2 : ℝ) ^ n.natAbs) :=
        mul_le_mul_of_nonneg_left
          (halfPeriodJacobi_weighted_term_bound I j 1 1 n (Or.inr rfl) hρ hratio)
          (by positivity)
      _ = _ := by
        rw [halfPolynomialIntWeight, pow_one, Nat.cast_natAbs, Int.cast_abs]
        ring
  convert weighted_fourierCoeff_of_halfPolynomial_majorant
    halfPeriodJacobiDerivativeCoefficient (halfPeriodJacobiExponent I j 1) hρ 131072 1 hb
    using 1

set_option maxHeartbeats 800000 in
-- The subtype and sum-indexed Fourier majorants require extra definitional reduction.
/-- The Eisenstein coordinate has a coarse rational budget under the
same unary theta ratio bound. -/
theorem eisensteinGraph_weightedFourier_bound
    {d : Type*} [Fintype d] [DecidableEq d] (j : d) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hratio : (1 / 256 : ℝ) * ρ ^ (4 : ℝ) ≤ 1 / 8) :
    Summable (fun a : d → ℤ ↦ ‖UnitAddTorus.mFourierCoeff (eisensteinGraph j) a‖ *
      ρ ^ (∑ i, |(a i : ℝ)|)) ∧
    (∑' a : d → ℤ, ‖UnitAddTorus.mFourierCoeff (eisensteinGraph j) a‖ *
      ρ ^ (∑ i, |(a i : ℝ)|)) ≤ 385 := by
  have he : (1 / 65536 : ℝ) * ρ ^ (8 : ℝ) =
      ((1 / 256 : ℝ) * ρ ^ (4 : ℝ)) ^ 2 := by
    rw [show (8 : ℝ) = 4 * 2 by norm_num, Real.rpow_mul (zero_le_one.trans hρ),
      Real.rpow_two, mul_pow]
    norm_num
  have hratio' : (1 / 65536 : ℝ) * ρ ^ (8 : ℝ) ≤ 1 / 2 := by
    rw [he]
    nlinarith [show 0 ≤ (1 / 256 : ℝ) * ρ ^ (4 : ℝ) by positivity]
  let f : Unit ⊕ ℕ+ → ℝ := fun n ↦ ‖eisensteinGraphCoefficient n‖ *
    ρ ^ (∑ i, |(eisensteinGraphExponent j n i : ℝ)|)
  have hfn (n : ℕ+) : f (.inr n) ≤ 24 * halfPolynomialNatWeight 2 n := by
    dsimp only [f]
    rw [eisenstein_weighted_term j n hρ]
    have hn : ((ArithmeticFunction.sigma 1 (n : ℕ) : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
      exact_mod_cast (ArithmeticFunction.sigma_le_pow_succ 1 (n : ℕ)).trans_eq (by norm_num)
    have hn' : (n : ℝ) ^ 2 ≤ (1 + (n : ℝ)) ^ 2 := by
      nlinarith [show 0 ≤ (n : ℝ) by positivity]
    calc
      _ ≤ 24 * (1 + (n : ℝ)) ^ 2 * (1 / 2 : ℝ) ^ (n : ℕ) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (hn.trans hn') (by norm_num)
        · exact pow_le_pow_left₀ (by positivity) hratio' _
        · positivity
        · positivity
      _ = _ := by rw [halfPolynomialNatWeight]; ring
  have hm := (summable_halfPolynomialNatWeight 2).mul_left (24 : ℝ)
  have hmp : Summable fun n : ℕ+ ↦ 24 * halfPolynomialNatWeight 2 n :=
    hm.subtype fun n ↦ 0 < n
  have hp : Summable fun n : ℕ+ ↦ f (.inr n) :=
    hmp.of_nonneg_of_le (fun _ ↦ by dsimp only [f]; positivity) hfn
  have hz : Summable (f ∘ Sum.inl) := Summable.of_finite
  have hs : Summable f := Summable.sum _ hz hp
  have hc : Summable fun n ↦ ‖eisensteinGraphCoefficient n‖ :=
    hs.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun n ↦
      le_mul_of_one_le_right (norm_nonneg _)
        (Real.one_le_rpow hρ (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _))
  refine ⟨summable_weighted_fourierCoeff_of_expansion _ _ _
    (fun _ ↦ by positivity) hc hs, ?_⟩
  refine (tsum_weighted_fourierCoeff_le _ _ _ (fun _ ↦ by positivity) hc hs).trans ?_
  change (∑' n, f n) ≤ 385
  rw [Summable.tsum_sum hz hp]
  have hzero : (∑' u : Unit, f (.inl u)) = 1 := by
    simp [f, eisensteinGraphCoefficient, eisensteinGraphExponent]
  rw [hzero]
  have hb := (hp.tsum_le_tsum hfn hmp).trans
    (Summable.tsum_subtype_le _ {n : ℕ | 0 < n}
      (fun n ↦ mul_nonneg (by norm_num) (halfPolynomialNatWeight_nonneg 2 n)) hm)
  rw [tsum_mul_left] at hb
  have hsum := tsum_halfPolynomialNatWeight_le 2
  norm_num at hsum
  linarith

end Stability.Selection
