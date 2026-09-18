import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic

/-!
# Summable geometric and Gaussian weights on integer lattices

The theta/Poisson detector uses products of the one-dimensional weights

```
q ^ |z|       and       q ^ |z|²,      0 ≤ q < 1.
```

This file proves their summability on `ℤ` and then proves a reusable finite
product theorem for functions on `Fin n → ℤ`.  Keeping these estimates
separate avoids repeating convergence bookkeeping in every Fourier-series
construction.
-/

noncomputable section

open scoped BigOperators

namespace HGAS.Analysis

/-- Two-sided geometric weight on the integers. -/
def geometricIntWeight (q : ℝ) (z : ℤ) : ℝ :=
  q ^ z.natAbs

/-- Two-sided discrete Gaussian weight on the integers. -/
def gaussianIntWeight (q : ℝ) (z : ℤ) : ℝ :=
  q ^ (z.natAbs ^ 2)

/-- The two-sided geometric weight is summable for `0 ≤ q < 1`. -/
theorem summable_geometricIntWeight
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (geometricIntWeight q) := by
  have hnorm : ‖q‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1
  apply Summable.of_nat_of_neg
  · simpa [geometricIntWeight] using
      (summable_geometric_of_norm_lt_one hnorm)
  · simpa [geometricIntWeight] using
      (summable_geometric_of_norm_lt_one hnorm)

/-- The Gaussian weight is dominated by the geometric weight and is
therefore summable. -/
theorem summable_gaussianIntWeight
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (gaussianIntWeight q) := by
  apply Summable.of_nonneg_of_le
  · intro z
    exact pow_nonneg hq0 _
  · intro z
    change q ^ (z.natAbs ^ 2) ≤ q ^ z.natAbs
    apply pow_le_pow_of_le_one hq0 hq1.le
    simpa only [pow_two] using z.natAbs.le_mul_self
  · exact summable_geometricIntWeight hq0 hq1

/-- A finite Cartesian product of a nonnegative summable integer weight is
summable. -/
theorem summable_finIntegerProduct
    (weight : ℤ → ℝ)
    (hweight : Summable weight)
    (hweight0 : ∀ z, 0 ≤ weight z)
    (n : ℕ) :
    Summable (fun x : Fin n → ℤ ↦ ∏ i, weight (x i)) := by
  induction n with
  | zero =>
      exact Summable.of_finite
  | succ n ih =>
      let e : ℤ × (Fin n → ℤ) ≃ (Fin (n + 1) → ℤ) :=
        Fin.consEquiv fun _ ↦ ℤ
      have hproduct :
          Summable (fun p : ℤ × (Fin n → ℤ) ↦
            weight p.1 * ∏ i, weight (p.2 i)) :=
        Summable.mul_of_nonneg
          (f := weight)
          (g := fun x : Fin n → ℤ ↦ ∏ i, weight (x i))
          hweight ih hweight0
          (fun x ↦ Finset.prod_nonneg fun _ _ ↦ hweight0 _)
      apply e.summable_iff.mp
      convert hproduct using 1
      funext p
      simp [e, Fin.prod_univ_succ]

/-- Geometric product weights are summable on every finite integer
lattice. -/
theorem summable_finGeometricWeight
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    Summable (fun x : Fin n → ℤ ↦
      ∏ i, geometricIntWeight q (x i)) :=
  summable_finIntegerProduct (geometricIntWeight q)
    (summable_geometricIntWeight hq0 hq1)
    (fun _ ↦ pow_nonneg hq0 _) n

/-- Gaussian product weights are summable on every finite integer
lattice. -/
theorem summable_finGaussianWeight
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    Summable (fun x : Fin n → ℤ ↦
      ∏ i, gaussianIntWeight q (x i)) :=
  summable_finIntegerProduct (gaussianIntWeight q)
    (summable_gaussianIntWeight hq0 hq1)
    (fun _ ↦ pow_nonneg hq0 _) n

end HGAS.Analysis
