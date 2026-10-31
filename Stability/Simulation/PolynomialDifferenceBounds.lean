import Stability.Simulation.PolynomialEnvelope
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Coordinatewise polynomial difference bounds

The affine segment between two points in a cube stays in that cube.
Applying the scalar mean-value theorem to polynomial evaluation along
this segment gives a weighted sum of coordinate differences. Each weight
uses the actual corresponding partial derivative, so absent variables
contribute zero; no global norm bound hides this triangular structure.
-/

namespace Stability.Simulation.AbsFormula

open Set

noncomputable section

variable {σ : Type*}

/-- Formal partial differentiation does not increase total degree.
The proof expands the actual support into differentiated monomials. -/
theorem pderiv_totalDegree_le [Finite σ] (p : MvPolynomial σ ℚ) (i : σ) :
    (MvPolynomial.pderiv i p).totalDegree ≤ p.totalDegree := by
  classical
  letI := Fintype.ofFinite σ
  have hexpand : MvPolynomial.pderiv i p =
      ∑ e ∈ p.support, MvPolynomial.monomial (e - Finsupp.single i 1)
        (p.coeff e * e i) := by
    conv_lhs => rw [MvPolynomial.as_sum p]
    simp only [map_sum, MvPolynomial.pderiv_monomial]
  rw [hexpand]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro e he
  apply (MvPolynomial.totalDegree_monomial_le _ _).trans
  have hsum (f : σ →₀ ℕ) : f.sum (fun _ n ↦ n) = ∑ j, f j := by
    apply Finsupp.sum_fintype
    intro j
    rfl
  calc
    (e - Finsupp.single i 1).sum (fun _ ↦ id) ≤ e.sum (fun _ n ↦ n) := by
      change (e - Finsupp.single i 1).sum (fun _ n ↦ n) ≤ _
      rw [hsum, hsum]
      exact Finset.sum_le_sum fun j _ ↦ Nat.sub_le _ _
    _ ≤ p.totalDegree := MvPolynomial.le_totalDegree he

variable [Fintype σ]

/-- The exact coefficient-based coordinatewise difference bound on a
cube. Its zero partial-derivative weights remain zero. -/
theorem abs_polynomialValue_sub_le_cube (p : MvPolynomial σ ℚ) (x y : σ → ℝ)
    {R : ℝ} (hR : 1 ≤ R) (hx : ∀ i, |x i| ≤ R) (hy : ∀ i, |y i| ≤ R) :
    |polynomialValue y p - polynomialValue x p| ≤
      ∑ i, (coefficientMass (MvPolynomial.pderiv i p) : ℝ) *
        R ^ (MvPolynomial.pderiv i p).totalDegree * |y i - x i| := by
  classical
  let γ : ℝ → σ → ℝ := fun t i ↦ x i + t * (y i - x i)
  have hγzero : γ 0 = x := by ext i; simp [γ]
  have hγone : γ 1 = y := by ext i; simp [γ]
  have hγderiv (t : ℝ) : HasDerivAt (fun s ↦ polynomialValue (γ s) p)
      (∑ i, polynomialValue (γ t) (MvPolynomial.pderiv i p) * (y i - x i)) t := by
    apply hasDerivAt_polynomialValue
    intro i
    simpa only [one_mul] using
      ((hasDerivAt_id t).mul_const (y i - x i)).const_add (x i)
  have hγcube {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (i : σ) : |γ t i| ≤ R := by
    have heq : γ t i = (1 - t) * x i + t * y i := by dsimp [γ]; ring
    rw [heq]
    calc
      |(1 - t) * x i + t * y i| ≤ |(1 - t) * x i| + |t * y i| := abs_add_le _ _
      _ = (1 - t) * |x i| + t * |y i| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr ht.2), abs_of_nonneg ht.1]
      _ ≤ (1 - t) * R + t * R :=
        add_le_add (mul_le_mul_of_nonneg_left (hx i) (sub_nonneg.mpr ht.2))
          (mul_le_mul_of_nonneg_left (hy i) ht.1)
      _ = R := by ring
  obtain ⟨t, ht, hmean⟩ := exists_hasDerivAt_eq_slope
    (f := fun t ↦ polynomialValue (γ t) p)
    (f' := fun t ↦ ∑ i, polynomialValue (γ t) (MvPolynomial.pderiv i p) * (y i - x i))
    (show (0 : ℝ) < 1 by norm_num)
    (fun t _ ↦ (hγderiv t).continuousAt.continuousWithinAt) (fun t _ ↦ hγderiv t)
  simp only [hγzero, hγone, sub_zero, div_one] at hmean
  rw [← hmean]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right
    (abs_polynomialValue_le_cube (MvPolynomial.pderiv i p) (γ t) hR
      (hγcube ⟨ht.1.le, ht.2.le⟩)) (abs_nonneg _)

/-- A supplied degree budget can replace all derivative exponents while
retaining the individual coefficient weights and coordinate errors. -/
theorem abs_polynomialValue_sub_le_cube_of_degree_le
    (p : MvPolynomial σ ℚ) (x y : σ → ℝ) {R : ℝ} {d : ℕ}
    (hR : 1 ≤ R) (hx : ∀ i, |x i| ≤ R) (hy : ∀ i, |y i| ≤ R)
    (hd : p.totalDegree ≤ d) :
    |polynomialValue y p - polynomialValue x p| ≤
      ∑ i, (coefficientMass (MvPolynomial.pderiv i p) : ℝ) * R ^ d * |y i - x i| := by
  apply (abs_polynomialValue_sub_le_cube p x y hR hx hy).trans
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  apply mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hR ((pderiv_totalDegree_le p i).trans hd))
  exact_mod_cast coefficientMass_nonneg (MvPolynomial.pderiv i p)

end

end Stability.Simulation.AbsFormula
