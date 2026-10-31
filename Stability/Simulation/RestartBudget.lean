import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# The budget increase caused by productive turns

Reference: the finite counting argument in Proposition 4.5, Step 3,
https://arxiv.org/html/2609.22058v2#S4.

The result is a finite sequence inequality; it does not assume or establish
correctness of an ODE simulation.
-/

namespace Stability.Simulation

open scoped BigOperators

/-- The number of productive turns strictly before turn `n`. -/
def productiveCount (productive : ℕ → Prop) [DecidablePred productive]
    (n : ℕ) : ℕ :=
  ((Finset.range n).filter productive).card

@[simp] theorem productiveCount_zero
    (productive : ℕ → Prop) [DecidablePred productive] :
    productiveCount productive 0 = 0 := by
  simp [productiveCount]

/-- Adding one turn adds one to the count exactly when that turn is productive. -/
theorem productiveCount_succ
    (productive : ℕ → Prop) [DecidablePred productive] (n : ℕ) :
    productiveCount productive (n + 1) =
      productiveCount productive n + if productive n then 1 else 0 := by
  by_cases hp : productive n <;>
    simp [productiveCount, Finset.range_add_one, Finset.filter_insert, hp]

/-- After the first productive turn, the budget is bounded below independently
of its initial value. Each turn can lose at most its error; a productive turn
also raises the budget by one and resets it to at least one, before that error.

All hypotheses are restricted to the finite prefix under consideration. -/
theorem productiveCount_sub_error_le_budget
    (budget error : ℕ → ℝ)
    (productive : ℕ → Prop) [DecidablePred productive]
    (n : ℕ)
    (herror : ∀ j < n, 0 ≤ error j)
    (hstep : ∀ j < n, budget j - error j ≤ budget (j + 1))
    (hproductive : ∀ j < n, productive j →
      max (budget j + 1) 1 - error j ≤ budget (j + 1))
    (hcount : 0 < productiveCount productive n) :
    (productiveCount productive n : ℝ) -
      ∑ j ∈ Finset.range n, error j ≤ budget n := by
  induction n with
  | zero => simp at hcount
  | succ n ih =>
    have herror' : ∀ j < n, 0 ≤ error j :=
      fun j hj ↦ herror j (Nat.lt_succ_of_lt hj)
    have hstep' : ∀ j < n, budget j - error j ≤ budget (j + 1) :=
      fun j hj ↦ hstep j (Nat.lt_succ_of_lt hj)
    have hproductive' : ∀ j < n, productive j →
        max (budget j + 1) 1 - error j ≤ budget (j + 1) :=
      fun j hj ↦ hproductive j (Nat.lt_succ_of_lt hj)
    rw [productiveCount_succ] at hcount ⊢
    rw [Finset.sum_range_succ]
    by_cases hp : productive n
    · simp only [hp, if_true, Nat.cast_add, Nat.cast_one]
      have hpaid := hproductive n (Nat.lt_succ_self n) hp
      by_cases hbefore : 0 < productiveCount productive n
      · have hbound := ih herror' hstep' hproductive' hbefore
        have hmax := le_max_left (budget n + 1) (1 : ℝ)
        linarith
      · have hzero : productiveCount productive n = 0 := by omega
        have hsum : 0 ≤ ∑ j ∈ Finset.range n, error j :=
          Finset.sum_nonneg fun j hj ↦ herror' j (Finset.mem_range.mp hj)
        have hmax := le_max_right (budget n + 1) (1 : ℝ)
        simp only [hzero, Nat.cast_zero]
        linarith
    · simp only [hp, if_false, add_zero] at hcount ⊢
      have hbound := ih herror' hstep' hproductive' hcount
      have hnext := hstep n (Nat.lt_succ_self n)
      linarith

/-- If the cumulative error is less than one, a clean restart after at least
`T` productive turns grants a budget strictly larger than `T`. This includes
`T = 0`, without imposing a lower bound on the initial budget. -/
theorem restartBudget_gt_of_productiveCount_ge
    (budget error : ℕ → ℝ)
    (productive : ℕ → Prop) [DecidablePred productive]
    (n T : ℕ)
    (herror : ∀ j < n, 0 ≤ error j)
    (hstep : ∀ j < n, budget j - error j ≤ budget (j + 1))
    (hproductive : ∀ j < n, productive j →
      max (budget j + 1) 1 - error j ≤ budget (j + 1))
    (hcount : T ≤ productiveCount productive n)
    (htotal : ∑ j ∈ Finset.range n, error j < 1) :
    (T : ℝ) < max (budget n) 0 + 1 := by
  by_cases hpositive : 0 < productiveCount productive n
  · have hbound := productiveCount_sub_error_le_budget
      budget error productive n herror hstep hproductive hpositive
    have hcount' : (T : ℝ) ≤ (productiveCount productive n : ℝ) := by
      exact_mod_cast hcount
    have hmax := le_max_left (budget n) (0 : ℝ)
    linarith
  · have hzero : T = 0 := by omega
    have hmax := le_max_right (budget n) (0 : ℝ)
    simp only [hzero, Nat.cast_zero]
    linarith

end Stability.Simulation
