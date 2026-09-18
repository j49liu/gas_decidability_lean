import HGAS.Algebra.ComplexPolynomialCode
import HGAS.Algebra.PolynomialFiniteProductCode
import HGAS.Algebra.FiniteEuclidean
import Mathlib.Tactic

/-!
# Squared norms of the standard finite-coordinate encodings

The polynomial compilers repeatedly assemble Euclidean points by block
sum, finite block product, and realification of complex coordinates.
These elementary identities let later estimates be carried out on the
structured mathematical state instead of by case-splitting raw `Fin`
indices.
-/

noncomputable section

open scoped BigOperators

namespace HGAS.Analysis.FiniteCoordinateNormSq

open HGAS

theorem normSq_blockPoint
    {m p : ℕ}
    (x : Fin m → ℝ) (y : Fin p → ℝ) :
    normSq (PolynomialBlockCode.point x y) =
      normSq x + normSq y := by
  unfold normSq dot
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp [PolynomialBlockCode.point]

theorem normSq_flattenPoint
    {q n : ℕ}
    (x : Fin q → Fin n → ℝ) :
    normSq (PolynomialFiniteProductCode.flattenPoint x) =
      ∑ a : Fin q, normSq (x a) := by
  unfold normSq dot
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  simp [PolynomialFiniteProductCode.flattenPoint]

theorem normSq_realifyPoint
    {n : ℕ} (z : Fin n → ℂ) :
    normSq (ComplexCoordinates.realifyPoint z) =
      ∑ i : Fin n, ‖z i‖ ^ 2 := by
  unfold normSq dot
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [ComplexCoordinates.realifyPoint,
    finSumFinEquiv.symm_apply_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.sq_norm, Complex.normSq_apply]

/-- A coordinatewise bound is preserved by canonical block sum. -/
theorem abs_blockPoint_le
    {m p : ℕ} {M : ℝ}
    (x : Fin m → ℝ) (y : Fin p → ℝ)
    (hx : ∀ i, |x i| ≤ M)
    (hy : ∀ j, |y j| ≤ M)
    (q : Fin (m + p)) :
    |PolynomialBlockCode.point x y q| ≤ M := by
  obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective q
  · simpa [PolynomialBlockCode.point] using hx i
  · simpa [PolynomialBlockCode.point] using hy j

/-- A coordinatewise bound is preserved by canonical finite block
flattening. -/
theorem abs_flattenPoint_le
    {q n : ℕ} {M : ℝ}
    (x : Fin q → Fin n → ℝ)
    (hx : ∀ a i, |x a i| ≤ M)
    (k : Fin (q * n)) :
    |PolynomialFiniteProductCode.flattenPoint x k| ≤ M := by
  obtain ⟨⟨a, i⟩, rfl⟩ := finProdFinEquiv.surjective k
  simpa [PolynomialFiniteProductCode.flattenPoint] using hx a i

/-- Real and imaginary coordinates are no larger than the complex norm,
so a common complex norm bound survives realification. -/
theorem abs_realifyPoint_le
    {n : ℕ} {M : ℝ}
    (z : Fin n → ℂ)
    (hz : ∀ i, ‖z i‖ ≤ M)
    (q : Fin (n + n)) :
    |ComplexCoordinates.realifyPoint z q| ≤ M := by
  obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective q
  · calc
      |ComplexCoordinates.realifyPoint z
          (finSumFinEquiv (Sum.inl i))| =
          |(z i).re| := by
            simp [ComplexCoordinates.realifyPoint]
      _ ≤ ‖z i‖ := Complex.abs_re_le_norm _
      _ ≤ M := hz i
  · calc
      |ComplexCoordinates.realifyPoint z
          (finSumFinEquiv (Sum.inr i))| =
          |(z i).im| := by
            change
              |ComplexCoordinates.realifyPoint z
                (ComplexCoordinates.imagIndex i)| = _
            rw [ComplexCoordinates.realifyPoint_imagIndex]
      _ ≤ ‖z i‖ := Complex.abs_im_le_norm _
      _ ≤ M := hz i

/-- Flattening a finite family of complex numbers into interleaved
real/imaginary coordinates preserves a common norm bound.  This is the
coordinate estimate used by both the gauge-family and reciprocal-family
compilers. -/
theorem abs_flattenComplexPoint_le
    {b : ℕ} {M : ℝ}
    (z : Fin b → ℂ)
    (hz : ∀ a, ‖z a‖ ≤ M)
    (q : Fin (b * 2)) :
    |PolynomialFiniteProductCode.flattenPoint
        (fun a ↦ ![(z a).re, (z a).im]) q| ≤ M := by
  apply abs_flattenPoint_le
  intro a i
  fin_cases i
  · exact (Complex.abs_re_le_norm (z a)).trans (hz a)
  · exact (Complex.abs_im_le_norm (z a)).trans (hz a)

/-- A real base block followed by an interleaved finite complex family
inherits any common coordinate/norm bound. -/
theorem abs_blockComplexFamilyPoint_le
    {n b : ℕ} {M : ℝ}
    (x : Fin n → ℝ) (z : Fin b → ℂ)
    (hx : ∀ i, |x i| ≤ M)
    (hz : ∀ a, ‖z a‖ ≤ M)
    (q : Fin (n + b * 2)) :
    |PolynomialBlockCode.point x
        (PolynomialFiniteProductCode.flattenPoint
          (fun a ↦ ![(z a).re, (z a).im])) q| ≤ M := by
  exact abs_blockPoint_le x _ hx
    (abs_flattenComplexPoint_le z hz) q

/-- A common absolute coordinate bound gives the expected
finite-dimensional squared-norm estimate. -/
theorem normSq_le_card_mul_sq_of_abs_le
    {n : ℕ} {M : ℝ}
    (x : Fin n → ℝ)
    (hx : ∀ i, |x i| ≤ M) :
    normSq x ≤ n * M ^ 2 := by
  unfold normSq dot
  calc
    (∑ i : Fin n, x i * x i) =
        ∑ i : Fin n, |x i| ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [sq_abs, pow_two]
    _ ≤ ∑ _i : Fin n, M ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact pow_le_pow_left₀ (abs_nonneg _) (hx i) 2
    _ = n * M ^ 2 := by
      simp

end HGAS.Analysis.FiniteCoordinateNormSq
