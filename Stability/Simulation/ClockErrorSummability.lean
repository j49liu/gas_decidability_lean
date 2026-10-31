import Stability.Simulation.ClockGain
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Uniform summability of clock errors

Reference: the separated-center estimate in Lemma 4.2,
https://arxiv.org/html/2609.22058v2#S4.

A telescoping comparison gives the stronger bound `29 / 10`, uniformly
over every real clock offset. In particular the sum is strictly below `3`.
-/

namespace Stability.Simulation

open scoped BigOperators

/-- The inverse-quadratic clock error associated with an arc centered at
`center`, before multiplication by the inverse square root of the gain. -/
noncomputable def clockError (center : ℝ) : ℝ :=
  (1 + (max (|center| - Real.pi / 3) 0) ^ 2)⁻¹

/-- Every clock error is nonnegative. -/
theorem clockError_nonneg (center : ℝ) : 0 ≤ clockError center := by
  unfold clockError
  positivity

private noncomputable def referenceError (n : ℕ) : ℝ :=
  (1 + 4 * (n : ℝ) ^ 2)⁻¹

private theorem referenceError_nonneg (n : ℕ) : 0 ≤ referenceError n := by
  unfold referenceError
  positivity

private theorem referenceError_tail_le (n : ℕ) :
    referenceError (n + 2) ≤
      1 / (4 * ((n : ℝ) + 1)) - 1 / (4 * ((n : ℝ) + 2)) := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have hn2 : (n : ℝ) + 2 ≠ 0 := by positivity
  calc
    referenceError (n + 2) = 1 / (1 + 4 * ((n : ℝ) + 2) ^ 2) := by
      simp only [referenceError, Nat.cast_add, Nat.cast_ofNat, inv_eq_one_div]
    _ ≤ 1 / (4 * ((n : ℝ) + 1) * ((n : ℝ) + 2)) :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith)
    _ = _ := by field_simp; ring

private theorem referenceError_sum_range_add_two_le (n : ℕ) :
    ∑ j ∈ Finset.range (n + 2), referenceError j ≤
      29 / 20 - 1 / (4 * ((n : ℝ) + 1)) := by
  induction n with
  | zero => norm_num [referenceError, Finset.sum_range_succ]
  | succ n ih =>
    rw [show n + 1 + 2 = (n + 2) + 1 by omega, Finset.sum_range_succ]
    have htail := referenceError_tail_le n
    push_cast
    rw [show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring]
    linarith

private theorem referenceError_sum_range_le (n : ℕ) :
    ∑ j ∈ Finset.range n, referenceError j ≤ 29 / 20 := by
  rcases n with _ | (_ | n)
  · norm_num
  · norm_num [referenceError, Finset.sum_range_succ]
  · have hbound := referenceError_sum_range_add_two_le n
    have hnonneg : 0 ≤ 1 / (4 * ((n : ℝ) + 1)) := by positivity
    exact hbound.trans (sub_le_self _ hnonneg)

private theorem referenceError_summable : Summable referenceError :=
  summable_of_sum_range_le referenceError_nonneg referenceError_sum_range_le

private theorem referenceError_tsum_le : ∑' n, referenceError n ≤ 29 / 20 :=
  referenceError_summable.tsum_le_of_sum_range_le referenceError_sum_range_le

private theorem clockError_le_referenceError {center : ℝ} (n : ℕ)
    (hfar : (n : ℝ) * Real.pi ≤ |center|) :
    clockError center ≤ referenceError n := by
  have hdist : 2 * (n : ℝ) ≤ max (|center| - Real.pi / 3) 0 := by
    by_cases hn : n = 0
    · simp [hn]
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hproduct := mul_nonneg (sub_nonneg.mpr hn1)
        (sub_nonneg.mpr Real.pi_gt_three.le)
      have hmax := le_max_left (|center| - Real.pi / 3) (0 : ℝ)
      nlinarith [Real.pi_gt_three]
  have hsquare := (sq_le_sq₀ (by positivity : 0 ≤ 2 * (n : ℝ))
    (le_max_right (|center| - Real.pi / 3) 0)).mpr hdist
  unfold clockError referenceError
  rw [inv_eq_one_div, inv_eq_one_div]
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

private theorem centeredLattice_summable_and_tsum_le
    {offset : ℝ} (hzero : 0 ≤ offset) (hpi : offset ≤ Real.pi) :
    Summable (fun j : ℤ ↦ clockError (offset + j * Real.pi)) ∧
      (∑' j : ℤ, clockError (offset + j * Real.pi)) ≤ 29 / 10 := by
  let f : ℤ → ℝ := fun j ↦ clockError (offset + j * Real.pi)
  have hpos : ∀ n : ℕ, f n ≤ referenceError n := by
    intro n
    apply clockError_le_referenceError
    change (n : ℝ) * Real.pi ≤ |offset + (n : ℝ) * Real.pi|
    rw [abs_of_nonneg (by positivity)]
    linarith
  have hneg : ∀ n : ℕ, f (-(n + 1)) ≤ referenceError n := by
    intro n
    apply clockError_le_referenceError
    change (n : ℝ) * Real.pi ≤ |offset + ((-((n : ℤ) + 1) : ℤ) : ℝ) * Real.pi|
    simp only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one]
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [abs_of_nonpos (by nlinarith [Real.pi_pos])]
    nlinarith
  have hspos : Summable (fun n : ℕ ↦ f n) :=
    Summable.of_nonneg_of_le (fun n ↦ clockError_nonneg _) hpos referenceError_summable
  have hsneg : Summable (fun n : ℕ ↦ f (-(n + 1))) :=
    Summable.of_nonneg_of_le (fun n ↦ clockError_nonneg _) hneg referenceError_summable
  refine ⟨hspos.of_nat_of_neg_add_one hsneg, ?_⟩
  change (∑' j : ℤ, f j) ≤ 29 / 10
  rw [tsum_of_nat_of_neg_add_one hspos hsneg]
  have hpbound := (hspos.tsum_le_tsum hpos referenceError_summable).trans referenceError_tsum_le
  have hnbound := (hsneg.tsum_le_tsum hneg referenceError_summable).trans referenceError_tsum_le
  linarith

/-- The entire integer lattice of arc centers has uniformly bounded total
error, independently of its real translation. -/
theorem clockError_int_summable_and_tsum_le (offset : ℝ) :
    Summable (fun j : ℤ ↦ clockError (offset + j * Real.pi)) ∧
      (∑' j : ℤ, clockError (offset + j * Real.pi)) ≤ 29 / 10 := by
  let shift : ℤ := ⌊offset / Real.pi⌋
  let reduced : ℝ := offset - shift * Real.pi
  have hzero : 0 ≤ reduced := by
    have hfloor := Int.floor_le (offset / Real.pi)
    have hscaled := (le_div_iff₀ Real.pi_pos).mp hfloor
    dsimp [reduced, shift]
    linarith
  have hpi : reduced ≤ Real.pi := by
    have hfloor := Int.lt_floor_add_one (offset / Real.pi)
    have hscaled := (div_lt_iff₀ Real.pi_pos).mp hfloor
    dsimp [reduced, shift]
    linarith
  obtain ⟨hsummable, hbound⟩ := centeredLattice_summable_and_tsum_le hzero hpi
  let reindex : ℤ ≃ ℤ := Equiv.addRight shift
  have hreindex (j : ℤ) :
      clockError (offset + j * Real.pi) = clockError (reduced + reindex j * Real.pi) := by
    congr 1
    change offset + (j : ℝ) * Real.pi = reduced + ((j + shift : ℤ) : ℝ) * Real.pi
    rw [Int.cast_add]
    dsimp [reduced]
    ring
  constructor
  · exact (reindex.summable_iff.mpr hsummable).congr fun j ↦ (hreindex j).symm
  · calc
      (∑' j : ℤ, clockError (offset + j * Real.pi)) =
          ∑' j : ℤ, clockError (reduced + reindex j * Real.pi) := tsum_congr hreindex
      _ = ∑' j : ℤ, clockError (reduced + j * Real.pi) :=
        reindex.tsum_eq (fun j : ℤ ↦ clockError (reduced + j * Real.pi))
      _ ≤ 29 / 10 := hbound

/-- Forward arc centers have summable errors with a total strictly below
three, uniformly in the initial clock state. -/
theorem clockError_nat_summable_and_tsum_lt_three (offset : ℝ) :
    Summable (fun n : ℕ ↦ clockError (offset + n * Real.pi)) ∧
      (∑' n : ℕ, clockError (offset + n * Real.pi)) < 3 := by
  obtain ⟨hsummable, hbound⟩ := clockError_int_summable_and_tsum_le offset
  have hinjective : Function.Injective ((↑) : ℕ → ℤ) := Nat.cast_injective
  constructor
  · simpa only [Int.cast_natCast] using hsummable.comp_injective hinjective
  · have hsubset := tsum_comp_le_tsum_of_inj hsummable
      (fun j ↦ clockError_nonneg (offset + j * Real.pi)) hinjective
    simp only [Function.comp_def, Int.cast_natCast] at hsubset
    linarith

/-- Every finite selection of forward arc centers obeys the same uniform
error budget. -/
theorem clockError_sum_lt_three (offset : ℝ) (indices : Finset ℕ) :
    ∑ n ∈ indices, clockError (offset + n * Real.pi) < 3 := by
  obtain ⟨hsummable, hbound⟩ := clockError_nat_summable_and_tsum_lt_three offset
  exact (Summable.sum_le_tsum indices (fun n _ ↦ clockError_nonneg _) hsummable).trans_lt hbound

/-- Scaling by the inverse square root of the relaxation gain gives the
uniform summable error estimate for all forward central arcs. -/
theorem scaledClockErrors_summable_and_tsum_lt
    {gain : ℝ} (hgain : 0 < gain) (offset : ℝ) :
    Summable (fun n : ℕ ↦ (Real.sqrt gain)⁻¹ * clockError (offset + n * Real.pi)) ∧
      (∑' n : ℕ, (Real.sqrt gain)⁻¹ * clockError (offset + n * Real.pi)) <
        3 * (Real.sqrt gain)⁻¹ := by
  obtain ⟨hsummable, hbound⟩ := clockError_nat_summable_and_tsum_lt_three offset
  refine ⟨hsummable.mul_left _, ?_⟩
  rw [tsum_mul_left]
  have hpositive : 0 < (Real.sqrt gain)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hgain)
  simpa only [mul_comm] using mul_lt_mul_of_pos_left hbound hpositive

/-- The same scaled error budget holds for any finite selection of arcs. -/
theorem scaledClockErrors_sum_lt
    {gain : ℝ} (hgain : 0 < gain) (offset : ℝ) (indices : Finset ℕ) :
    ∑ n ∈ indices, (Real.sqrt gain)⁻¹ * clockError (offset + n * Real.pi) <
      3 * (Real.sqrt gain)⁻¹ := by
  obtain ⟨hsummable, hbound⟩ := scaledClockErrors_summable_and_tsum_lt hgain offset
  apply (Summable.sum_le_tsum indices ?_ hsummable).trans_lt hbound
  intro n _
  exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg gain)) (clockError_nonneg _)

end Stability.Simulation
