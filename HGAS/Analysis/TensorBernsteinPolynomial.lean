import HGAS.Analysis.MvPolynomialCalculus
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Tactic

/-!
# Tensor-product Bernstein polynomials

This file defines the actual multivariate polynomial used in the
Bernstein proof.  For a function `f` sampled on the uniform grid of the
unit cube, the degree-`m` tensor approximation is

```
∑ k, f(k / m) ∏ i binom(m,kᵢ) Xᵢ^kᵢ (1-Xᵢ)^(m-kᵢ).
```

The construction lives in `MvPolynomial`, rather than merely defining a
function on the cube.  Consequently its output can be passed directly to
the symmetrization and radial-homogenization modules.
-/

namespace HGAS

open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-- The grid point indexed by `k`.  The degree-zero convention is harmless:
all coordinates are then `0 / 0 = 0` in the field. -/
def tensorBernsteinGrid (m : ℕ) (k : Fin n → Fin (m + 1)) :
    Fin n → ℝ :=
  fun i ↦ (k i : ℝ) / m

/-- The univariate Bernstein basis polynomial in coordinate `i`, embedded
in the multivariate polynomial ring. -/
def coordinateBernsteinPolynomial
    (m : ℕ) (k : Fin (m + 1)) (i : Fin n) :
    MvPolynomial (Fin n) ℝ :=
  (_root_.bernsteinPolynomial ℝ m k).toMvPolynomial i

/-- Tensor product of the coordinate Bernstein basis polynomials. -/
def tensorBernsteinBasis
    (m : ℕ) (k : Fin n → Fin (m + 1)) :
    MvPolynomial (Fin n) ℝ :=
  ∏ i : Fin n, coordinateBernsteinPolynomial m (k i) i

/-- The scalar Bernstein weight obtained by evaluating a tensor basis
polynomial. -/
def tensorBernsteinWeight
    (m : ℕ) (k : Fin n → Fin (m + 1))
    (x : Fin n → ℝ) : ℝ :=
  ∏ i : Fin n,
    (m.choose (k i) : ℝ) * x i ^ (k i : ℕ) *
      (1 - x i) ^ (m - (k i : ℕ))

/-- The tensor-product Bernstein polynomial of a scalar function.  Only
the finitely many grid values of `f` enter this definition. -/
def tensorBernsteinPolynomial
    (m : ℕ) (f : (Fin n → ℝ) → ℝ) :
    MvPolynomial (Fin n) ℝ :=
  ∑ k : Fin n → Fin (m + 1),
    MvPolynomial.C (f (tensorBernsteinGrid m k)) *
      tensorBernsteinBasis m k

@[simp]
theorem eval_coordinateBernsteinPolynomial
    (m : ℕ) (k : Fin (m + 1)) (i : Fin n)
    (x : Fin n → ℝ) :
    MvPolynomial.eval x (coordinateBernsteinPolynomial m k i) =
      (m.choose k : ℝ) * x i ^ (k : ℕ) *
        (1 - x i) ^ (m - (k : ℕ)) := by
  rw [coordinateBernsteinPolynomial,
    MvPolynomial.eval_toMvPolynomial]
  simp [_root_.bernsteinPolynomial]

@[simp]
theorem eval_tensorBernsteinBasis
    (m : ℕ) (k : Fin n → Fin (m + 1))
    (x : Fin n → ℝ) :
    MvPolynomial.eval x (tensorBernsteinBasis m k) =
      tensorBernsteinWeight m k x := by
  simp [tensorBernsteinBasis, tensorBernsteinWeight]

/-- Evaluation is the expected finite weighted sum over the tensor grid. -/
theorem eval_tensorBernsteinPolynomial
    (m : ℕ) (f : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) :
    MvPolynomial.eval x (tensorBernsteinPolynomial m f) =
      ∑ k : Fin n → Fin (m + 1),
        f (tensorBernsteinGrid m k) *
          tensorBernsteinWeight m k x := by
  simp [tensorBernsteinPolynomial]

/-- Bernstein tensor weights are nonnegative on the unit cube. -/
theorem tensorBernsteinWeight_nonneg
    (m : ℕ) (k : Fin n → Fin (m + 1))
    (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    0 ≤ tensorBernsteinWeight m k x := by
  apply Finset.prod_nonneg
  intro i hi
  have hxi : 0 ≤ x i := (hx i).1
  have h_one_sub : 0 ≤ 1 - x i := sub_nonneg.mpr (hx i).2
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hxi _))
    (pow_nonneg h_one_sub _)

/-- The tensor weights form a partition of unity on the unit cube. -/
theorem sum_tensorBernsteinWeight_eq_one
    (m : ℕ) (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    ∑ k : Fin n → Fin (m + 1),
      tensorBernsteinWeight m k x = 1 := by
  simp only [tensorBernsteinWeight]
  have hone :
      ∀ i : Fin n,
        (∑ k : Fin (m + 1),
          (m.choose k : ℝ) * x i ^ (k : ℕ) *
            (1 - x i) ^ (m - (k : ℕ))) = 1 := by
    intro i
    let xi : Set.Icc (0 : ℝ) 1 := ⟨x i, hx i⟩
    simpa only [bernstein_apply] using
      (_root_.bernstein.probability m xi)
  calc
    (∑ k : Fin n → Fin (m + 1),
        ∏ i : Fin n,
          (m.choose (k i) : ℝ) * x i ^ (k i : ℕ) *
            (1 - x i) ^ (m - (k i : ℕ))) =
        ∏ i : Fin n,
          ∑ k : Fin (m + 1),
            (m.choose k : ℝ) * x i ^ (k : ℕ) *
              (1 - x i) ^ (m - (k : ℕ)) :=
      (Fintype.prod_sum
        (fun i : Fin n ↦ fun k : Fin (m + 1) ↦
          (m.choose k : ℝ) * x i ^ (k : ℕ) *
            (1 - x i) ^ (m - (k : ℕ)))).symm
    _ = 1 := by
      simp_rw [hone]
      simp

/-- Tensor Bernstein construction is additive in the sampled function. -/
theorem tensorBernsteinPolynomial_add
    (m : ℕ) (f g : (Fin n → ℝ) → ℝ) :
    tensorBernsteinPolynomial m (fun x ↦ f x + g x) =
      tensorBernsteinPolynomial m f +
        tensorBernsteinPolynomial m g := by
  classical
  simp only [tensorBernsteinPolynomial, map_add,
    add_mul, Finset.sum_add_distrib]

/-- Tensor Bernstein construction commutes with scalar multiplication. -/
theorem tensorBernsteinPolynomial_smul
    (m : ℕ) (c : ℝ) (f : (Fin n → ℝ) → ℝ) :
    tensorBernsteinPolynomial m (fun x ↦ c * f x) =
      MvPolynomial.C c * tensorBernsteinPolynomial m f := by
  classical
  simp only [tensorBernsteinPolynomial, map_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Every tensor Bernstein approximation defines a smooth real function. -/
theorem contDiff_tensorBernsteinPolynomial_eval
    (m : ℕ) (f : (Fin n → ℝ) → ℝ) :
    ContDiff ℝ ⊤
      (fun x : Fin n → ℝ ↦
        MvPolynomial.eval x (tensorBernsteinPolynomial m f)) :=
  contDiff_mvPolynomial_eval _

end

end HGAS
