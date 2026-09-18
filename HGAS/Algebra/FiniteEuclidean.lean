import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

/-!
# Elementary finite-dimensional Euclidean algebra

The reduction repeatedly uses finite coordinate vectors but rarely needs the
topological machinery of normed spaces.  This module provides a deliberately
small algebraic interface: a dot product and its associated squared norm.
Keeping these definitions algebraic makes the compactification and wrapper
identities reusable over rings and fields, while analytic modules can later
identify them with the usual Euclidean inner product.
-/

namespace HGAS

open scoped BigOperators

/-- A coordinate vector of length `n` over `R`. -/
abbrev FinVector (n : ℕ) (R : Type*) := Fin n → R

/-- The coordinate dot product. -/
def dot {n : ℕ} {R : Type*} [CommSemiring R]
    (x y : FinVector n R) : R :=
  ∑ i, x i * y i

/-- The algebraic squared Euclidean norm. -/
def normSq {n : ℕ} {R : Type*} [CommSemiring R]
    (x : FinVector n R) : R :=
  dot x x

variable {n : ℕ} {R : Type*}

@[simp]
theorem dot_zero [CommSemiring R] (x : FinVector n R) :
    dot x 0 = 0 := by
  simp [dot]

@[simp]
theorem zero_dot [CommSemiring R] (x : FinVector n R) :
    dot 0 x = 0 := by
  simp [dot]

theorem dot_comm [CommSemiring R] (x y : FinVector n R) :
    dot x y = dot y x := by
  simp only [dot]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem dot_add_right [CommSemiring R]
    (x y z : FinVector n R) :
    dot x (y + z) = dot x y + dot x z := by
  simp [dot, mul_add, Finset.sum_add_distrib]

theorem dot_add_left [CommSemiring R]
    (x y z : FinVector n R) :
    dot (x + y) z = dot x z + dot y z := by
  rw [dot_comm, dot_add_right, dot_comm x z, dot_comm y z]

theorem dot_smul_right [CommSemiring R] (c : R)
    (x y : FinVector n R) :
    dot x (c • y) = c * dot x y := by
  simp [dot, Finset.mul_sum, mul_left_comm]

theorem dot_smul_left [CommSemiring R] (c : R)
    (x y : FinVector n R) :
    dot (c • x) y = c * dot x y := by
  rw [dot_comm, dot_smul_right, dot_comm]

@[simp]
theorem normSq_zero [CommSemiring R] :
    normSq (0 : FinVector n R) = 0 := by
  simp [normSq]

theorem normSq_nonneg (x : FinVector n ℝ) :
    0 ≤ normSq x := by
  simp only [normSq, dot]
  exact Finset.sum_nonneg (fun i _ ↦ mul_self_nonneg (x i))

theorem normSq_smul [CommSemiring R] (c : R)
    (x : FinVector n R) :
    normSq (c • x) = c ^ 2 * normSq x := by
  simp only [normSq, dot_smul_left, dot_smul_right]
  ring

/-- Squared norm is invariant under the antipodal map. -/
@[simp]
theorem normSq_neg [CommRing R] (x : FinVector n R) :
    normSq (-x) = normSq x := by
  rw [← neg_one_smul R x, normSq_smul]
  simp

end HGAS
