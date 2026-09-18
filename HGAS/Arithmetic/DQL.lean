import Mathlib.NumberTheory.SumFourSquares
import Mathlib.Tactic

/-!
# Diagonal–quadratic–linear arithmetic

Section 4 of the paper reduces an arbitrary Diophantine equation to a finite
system

`A (n ⊙ n) + B n = c`

over integer variables.  This file defines that target syntax and proves the
two elementary arithmetic gadgets used by the compiler:

* four squares encode nonnegative integers while their square-root
  auxiliaries range freely over `ℤ`;
* one multiplication gate is equivalent to two equations involving only
  individual squares and linear terms.

The MRDP source theorem and the full circuit compiler are intentionally
separate later obligations.
-/

namespace HGAS

open scoped BigOperators

/-- A finite diagonal–quadratic–linear system with `vars` integer variables
and `eqs` equations. Rows are functions rather than bundled matrices so the
evaluation formula remains transparent. -/
structure DQLSystem (eqs vars : ℕ) where
  quadratic : Fin eqs → Fin vars → ℤ
  linear : Fin eqs → Fin vars → ℤ
  rhs : Fin eqs → ℤ

namespace DQLSystem

variable {eqs vars : ℕ}

/-- An integer vector satisfies every row of a DQL system. -/
def Satisfies (I : DQLSystem eqs vars) (x : Fin vars → ℤ) : Prop :=
  ∀ row,
    (∑ j, (I.quadratic row j * (x j) ^ 2 +
      I.linear row j * x j)) = I.rhs row

/-- The existential decision predicate associated with a DQL system. -/
def Solvable (I : DQLSystem eqs vars) : Prop :=
  ∃ x : Fin vars → ℤ, I.Satisfies x

instance (I : DQLSystem eqs vars) (x : Fin vars → ℤ) :
    Decidable (I.Satisfies x) :=
  by
    unfold Satisfies
    infer_instance

end DQLSystem

/-- The polarization gadget used in equation (4.4) of the paper. It removes
the mixed product `x*y`: after introducing `w = x+y`, the remaining equation
contains only individual squares and linear terms. -/
theorem mul_eq_iff_exists_polarization (x y z : ℤ) :
    x * y = z ↔
      ∃ w : ℤ, w = x + y ∧ w ^ 2 - x ^ 2 - y ^ 2 - 2 * z = 0 := by
  constructor
  · intro h
    refine ⟨x + y, rfl, ?_⟩
    nlinarith
  · rintro ⟨w, rfl, h⟩
    nlinarith

/-- A sum of four integer squares is nonnegative. -/
theorem sum_four_int_squares_nonneg (a b c d : ℤ) :
    0 ≤ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  positivity

/-- Integer nonnegativity is equivalent to representability by four freely
quantified integer squares. This is the exact bridge needed when an MRDP
polynomial uses natural-number variables but the final DQL variables range
over all integers. -/
theorem nonneg_iff_exists_sum_four_int_squares (x : ℤ) :
    0 ≤ x ↔ ∃ a b c d : ℤ, x = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  constructor
  · intro hx
    obtain ⟨a, b, c, d, habcd⟩ := Nat.sum_four_squares x.toNat
    refine ⟨a, b, c, d, ?_⟩
    rw [← Int.toNat_of_nonneg hx]
    exact_mod_cast habcd.symm
  · rintro ⟨a, b, c, d, rfl⟩
    exact sum_four_int_squares_nonneg a b c d

/-- The toy equation from the paper has exactly the two asserted integer
solutions. -/
theorem sq_add_self_eq_two_iff (n : ℤ) :
    n ^ 2 + n = 2 ↔ n = 1 ∨ n = -2 := by
  constructor
  · intro h
    have hfactor : (n - 1) * (n + 2) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hfactor with h₁ | h₂
    · left
      omega
    · right
      omega
  · rintro (rfl | rfl) <;> norm_num

end HGAS
