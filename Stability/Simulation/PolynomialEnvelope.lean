import Stability.Simulation.PolynomialCurveDerivative

/-!
# Explicit polynomial envelopes on arbitrary finite coordinate spaces

The rational sum of absolute coefficients bounds a polynomial on the
unit cube. On a cube of radius R ≥ 1, multiplying by R to the total degree
gives a bound. Substituting the polynomial 1 + Σ xᵢ² for R yields a global
nonnegative polynomial majorant. These are actual coefficient formulas,
not bounds selected from compactness.
-/

namespace Stability.Simulation.AbsFormula

noncomputable section

variable {σ : Type*}

def coefficientMass (p : MvPolynomial σ ℚ) : ℚ :=
  ∑ e ∈ p.support, |p.coeff e|

theorem coefficientMass_nonneg (p : MvPolynomial σ ℚ) : 0 ≤ coefficientMass p :=
  Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

/-- Coefficient evaluation bound on a cube of any radius at least one. -/
theorem abs_polynomialValue_le_cube [Finite σ] (p : MvPolynomial σ ℚ) (x : σ → ℝ)
    {R : ℝ} (hR : 1 ≤ R) (hx : ∀ i, |x i| ≤ R) :
    |polynomialValue x p| ≤ (coefficientMass p : ℝ) * R ^ p.totalDegree := by
  classical
  letI := Fintype.ofFinite σ
  have hmonomial (e : σ →₀ ℕ) (he : e ∈ p.support) :
      |∏ i, x i ^ e i| ≤ R ^ p.totalDegree := by
    rw [Finset.abs_prod]
    calc
      (∏ i, |x i ^ e i|) ≤ ∏ i, R ^ e i := by
        apply Finset.prod_le_prod (fun _ _ ↦ abs_nonneg _)
        intro i _
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hx i) _
      _ = R ^ (∑ i, e i) := Finset.prod_pow_eq_pow_sum _ _ _
      _ ≤ R ^ p.totalDegree := by
        apply pow_le_pow_right₀ hR
        have heq : (∑ i, e i) = e.sum (fun _ n ↦ n) := by
          symm
          apply Finsupp.sum_fintype
          intro i
          rfl
        rw [heq]
        exact MvPolynomial.le_totalDegree he
  unfold polynomialValue
  rw [MvPolynomial.eval₂_eq']
  calc
    |∑ e ∈ p.support, algebraMap ℚ ℝ (p.coeff e) * ∏ i, x i ^ e i| ≤
        ∑ e ∈ p.support, |algebraMap ℚ ℝ (p.coeff e) * ∏ i, x i ^ e i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ p.support, |algebraMap ℚ ℝ (p.coeff e)| * R ^ p.totalDegree := by
      apply Finset.sum_le_sum
      intro e he
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hmonomial e he) (abs_nonneg _)
    _ = (coefficientMass p : ℝ) * R ^ p.totalDegree := by
      simp [coefficientMass, Finset.sum_mul]

variable [Fintype σ]

/-- A polynomial radius that dominates every absolute coordinate. -/
def coordinateEnvelope : MvPolynomial σ ℚ :=
  1 + ∑ i, MvPolynomial.X i ^ 2

theorem coordinateEnvelope_value (x : σ → ℝ) :
    polynomialValue x (coordinateEnvelope (σ := σ)) = 1 + ∑ i, x i ^ 2 := by
  simp [coordinateEnvelope, polynomialValue]

theorem coordinateEnvelope_one_le (x : σ → ℝ) :
    1 ≤ polynomialValue x (coordinateEnvelope (σ := σ)) := by
  rw [coordinateEnvelope_value]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ ↦ sq_nonneg (x i))

theorem abs_coordinate_le_envelope (x : σ → ℝ) (i : σ) :
    |x i| ≤ polynomialValue x (coordinateEnvelope (σ := σ)) := by
  rw [coordinateEnvelope_value]
  have hsingle := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) ↦ sq_nonneg (x j))
    (Finset.mem_univ i)
  have habs : |x i| ≤ 1 + x i ^ 2 := by
    nlinarith [sq_nonneg (|x i| - 1), sq_abs (x i), sq_nonneg (x i)]
  linarith

def polynomialEnvelope (p : MvPolynomial σ ℚ) : MvPolynomial σ ℚ :=
  MvPolynomial.C (coefficientMass p) * coordinateEnvelope ^ p.totalDegree

/-- A global polynomial bound built directly from rational coefficients. -/
theorem abs_polynomialValue_le_envelope (p : MvPolynomial σ ℚ) (x : σ → ℝ) :
    |polynomialValue x p| ≤ polynomialValue x (polynomialEnvelope p) := by
  simpa only [polynomialEnvelope, polynomialValue, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_C, MvPolynomial.eval₂_pow] using
    abs_polynomialValue_le_cube p x (coordinateEnvelope_one_le x)
      (abs_coordinate_le_envelope x)

theorem polynomialEnvelope_nonneg (p : MvPolynomial σ ℚ) (x : σ → ℝ) :
    0 ≤ polynomialValue x (polynomialEnvelope p) :=
  (abs_nonneg _).trans (abs_polynomialValue_le_envelope p x)

theorem coordinateEnvelope_totalDegree_le :
    (coordinateEnvelope (σ := σ)).totalDegree ≤ 2 := by
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le (by simp)
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  simp

/-- The envelope's degree grows by at most a factor of two. -/
theorem polynomialEnvelope_totalDegree_le (p : MvPolynomial σ ℚ) :
    (polynomialEnvelope p).totalDegree ≤ 2 * p.totalDegree := by
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C, zero_add]
  exact (MvPolynomial.totalDegree_pow _ _).trans
    ((Nat.mul_le_mul_left p.totalDegree coordinateEnvelope_totalDegree_le).trans_eq
      (Nat.mul_comm _ _))

end

end Stability.Simulation.AbsFormula
