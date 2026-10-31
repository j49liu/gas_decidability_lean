import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Tactic

/-!
# Gates for the real register-machine transition map

The label gate has a plateau of radius `1/8` and support of radius `1/4`.
The zero gate separates values at most `1/4` from values at least `3/4`.
Both are finite expressions in rational constants and absolute value.

Source: Section 3, https://arxiv.org/html/2609.22058v2#S3.
-/

namespace Stability.Simulation

noncomputable section

/-- Clamp a real number to the unit interval. -/
def unitClamp (x : ℝ) : ℝ := min (max x 0) 1

/-- The plateau gate centered at a machine label. -/
def labelGate (x : ℝ) : ℝ := unitClamp (2 - 8 * |x|)

/-- The test used for a zero register or an exhausted countdown. -/
def zeroGate (x : ℝ) : ℝ := unitClamp (3 / 2 - 2 * x)

theorem unitClamp_nonneg (x : ℝ) : 0 ≤ unitClamp x :=
  le_min (le_max_right _ _) zero_le_one

theorem unitClamp_le_one (x : ℝ) : unitClamp x ≤ 1 := min_le_right _ _

theorem unitClamp_eq_zero {x : ℝ} (hx : x ≤ 0) : unitClamp x = 0 := by
  simp [unitClamp, max_eq_right hx]

theorem unitClamp_eq_one {x : ℝ} (hx : 1 ≤ x) : unitClamp x = 1 := by
  rw [unitClamp, max_eq_left (zero_le_one.trans hx), min_eq_right hx]

/-- An absolute-value expression makes the permitted algebra explicit. -/
theorem unitClamp_eq_abs (x : ℝ) : unitClamp x = (|x| - |x - 1| + 1) / 2 := by
  rcases le_total x 0 with hx | hx
  · rw [unitClamp_eq_zero hx, abs_of_nonpos hx, abs_of_nonpos (by linarith : x - 1 ≤ 0)]
    ring
  · rcases le_total x 1 with hxOne | hxOne
    · rw [unitClamp, max_eq_left hx, min_eq_left hxOne,
        abs_of_nonneg hx, abs_of_nonpos (by linarith : x - 1 ≤ 0)]
      ring
    · rw [unitClamp_eq_one hxOne, abs_of_nonneg hx,
        abs_of_nonneg (by linarith : 0 ≤ x - 1)]
      ring

theorem continuous_unitClamp : Continuous unitClamp :=
  (continuous_id.max continuous_const).min continuous_const

theorem continuous_labelGate : Continuous labelGate :=
  continuous_unitClamp.comp (continuous_const.sub (continuous_const.mul continuous_abs))

theorem continuous_zeroGate : Continuous zeroGate :=
  continuous_unitClamp.comp (continuous_const.sub (continuous_const.mul continuous_id))

theorem labelGate_nonneg (x : ℝ) : 0 ≤ labelGate x := unitClamp_nonneg _

theorem labelGate_le_one (x : ℝ) : labelGate x ≤ 1 := unitClamp_le_one _

theorem labelGate_eq_one {x : ℝ} (hx : |x| ≤ 1 / 8) : labelGate x = 1 := by
  apply unitClamp_eq_one
  linarith

theorem labelGate_eq_zero {x : ℝ} (hx : 1 / 4 ≤ |x|) : labelGate x = 0 := by
  apply unitClamp_eq_zero
  linarith

theorem zeroGate_eq_one {x : ℝ} (hx : x ≤ 1 / 4) : zeroGate x = 1 := by
  apply unitClamp_eq_one
  linarith

theorem zeroGate_eq_zero {x : ℝ} (hx : 3 / 4 ≤ x) : zeroGate x = 0 := by
  apply unitClamp_eq_zero
  linarith

/-- Within a plateau around one natural-number label, every other label
gate vanishes. This also handles the restart and halting labels. -/
theorem labelGate_eq_zero_of_near_other_nat {x : ℝ} {i j : ℕ}
    (hnear : |x - (i : ℝ)| ≤ 1 / 8) (hne : i ≠ j) :
    labelGate (x - (j : ℝ)) = 0 := by
  apply labelGate_eq_zero
  have hsmall := abs_le.mp hnear
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hsep : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hij
    have h := neg_le_abs (x - (j : ℝ))
    linarith
  · have hsep : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hji
    have h := le_abs_self (x - (j : ℝ))
    linarith

end

end Stability.Simulation
