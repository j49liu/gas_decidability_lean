import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# Quadratic growth dominates every linear loss

The nonreal-Bloch argument produces a lower bound of the form

```
                  log ‖state(t)‖ ≥ A t² - B t - C,
                         A > 0.
```

This file packages the elementary final step: the right-hand side tends
to `+∞`, hence so does the norm after exponentiation.  Keeping this
real-analysis fact separate makes the later theta module responsible only
for the genuinely analytic work—lattice reduction, a compact lower bound,
and the exact multiplier.
-/

namespace HGAS.Analysis

open Filter

noncomputable section

/-- A real quadratic with positive leading coefficient tends to positive
infinity, with no sign assumption on its linear or constant terms. -/
theorem quadratic_sub_linear_tendsto_atTop
    (A B C : ℝ) (hA : 0 < A) :
    Tendsto
      (fun t : ℝ ↦ A * t ^ 2 - B * t - C)
      atTop atTop := by
  have hid :
      Tendsto (fun t : ℝ ↦ t) atTop atTop := by
    simpa using
      (tendsto_id :
        Tendsto (id : ℝ → ℝ) atTop atTop)
  have hsq :
      Tendsto (fun t : ℝ ↦ t ^ 2) atTop atTop := by
    simpa only [pow_two] using
      hid.atTop_mul_atTop₀ hid
  have hhalf : 0 < A / 2 := by positivity
  have hbase :
      Tendsto
        (fun t : ℝ ↦ (A / 2) * t ^ 2 - C)
        atTop atTop := by
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-C)
        (hsq.const_mul_atTop hhalf)
  apply Filter.tendsto_atTop_mono' atTop _ hbase
  filter_upwards
    [eventually_ge_atTop
      (max 0 (2 * |B| / A))] with t ht
  have ht0 : 0 ≤ t := (le_max_left _ _).trans ht
  have htlarge : 2 * |B| / A ≤ t :=
    (le_max_right _ _).trans ht
  have hlinear : 2 * |B| ≤ A * t := by
    apply (div_le_iff₀ hA).mp at htlarge
    nlinarith
  have hlinearMul :
      2 * |B| * t ≤ A * t ^ 2 := by
    have :=
      mul_le_mul_of_nonneg_right hlinear ht0
    nlinarith
  have hB : B * t ≤ |B| * t :=
    mul_le_mul_of_nonneg_right (le_abs_self B) ht0
  nlinarith

/-- Exponentiating a positive-leading quadratic still tends to positive
infinity. -/
theorem exp_quadratic_sub_linear_tendsto_atTop
    (A B C : ℝ) (hA : 0 < A) :
    Tendsto
      (fun t : ℝ ↦
        Real.exp (A * t ^ 2 - B * t - C))
      atTop atTop :=
  Real.tendsto_exp_atTop.comp
    (quadratic_sub_linear_tendsto_atTop
      A B C hA)

/-- Any function eventually bounded below by a positive-leading
quadratic tends to positive infinity. -/
theorem tendsto_atTop_of_eventually_quadratic_lower_bound
    {f : ℝ → ℝ} (A B C : ℝ) (hA : 0 < A)
    (hbound :
      ∀ᶠ t in atTop,
        A * t ^ 2 - B * t - C ≤ f t) :
    Tendsto f atTop atTop :=
  Filter.tendsto_atTop_mono' atTop hbound
    (quadratic_sub_linear_tendsto_atTop
      A B C hA)

/-- Exponential version of the preceding comparison principle. -/
theorem tendsto_atTop_of_eventually_exp_quadratic_lower_bound
    {f : ℝ → ℝ} (A B C : ℝ) (hA : 0 < A)
    (hbound :
      ∀ᶠ t in atTop,
        Real.exp (A * t ^ 2 - B * t - C) ≤
          f t) :
    Tendsto f atTop atTop :=
  Filter.tendsto_atTop_mono' atTop hbound
    (exp_quadratic_sub_linear_tendsto_atTop
      A B C hA)

/-- A quantity with nonzero asymptotic linear slope has a square that
dominates every prescribed linear loss.

This is the form used after elliptic lattice reduction.  The integer
translation index is viewed as a real-valued function `n`; an `O(1)`
error from the nonzero line `a t` suffices. -/
theorem affine_boundedError_quadratic_escape
    {n : ℝ → ℝ} {a gamma loss scale err : ℝ}
    (ha : a ≠ 0)
    (hgamma : 0 < gamma)
    (hloss : 0 ≤ loss)
    (hn :
      ∀ᶠ t in atTop,
        |n t - a * t| ≤ err) :
    Tendsto
      (fun t : ℝ ↦
        gamma * (n t) ^ 2 -
          loss * |n t| -
          scale * (1 + t))
      atTop atTop := by
  have habs : 0 < |a| := abs_pos.mpr ha
  let A : ℝ := gamma * |a| ^ 2 / 4
  let B : ℝ := loss * |a| + scale
  let C : ℝ := loss * err + scale
  have hA : 0 < A := by
    dsimp [A]
    positivity
  apply
    tendsto_atTop_of_eventually_quadratic_lower_bound
      A B C hA
  filter_upwards
    [hn,
      eventually_ge_atTop
        (max 0 (2 * err / |a|))] with t htError ht
  have ht0 : 0 ≤ t := (le_max_left _ _).trans ht
  have htlarge :
      2 * err / |a| ≤ t :=
    (le_max_right _ _).trans ht
  have htwice : 2 * err ≤ |a| * t := by
    have :=
      (div_le_iff₀ habs).mp htlarge
    nlinarith
  have hnLower :
      |a| * t - err ≤ |n t| := by
    have hreverse :=
      abs_sub_abs_le_abs_sub (a * t) (n t)
    rw [abs_mul, abs_of_nonneg ht0,
      abs_sub_comm] at hreverse
    linarith
  have hnHalf :
      |a| * t / 2 ≤ |n t| := by
    nlinarith
  have hnUpper :
      |n t| ≤ |a| * t + err := by
    calc
      |n t| =
          |(n t - a * t) + a * t| := by
            congr 1
            ring
      _ ≤ |n t - a * t| + |a * t| :=
        abs_add_le _ _
      _ ≤ err + |a| * t := by
        rw [abs_mul, abs_of_nonneg ht0]
        simpa only [add_comm] using
          add_le_add_right htError (|a| * t)
      _ = |a| * t + err := by ring
  have hsquare :
      (|a| * t / 2) ^ 2 ≤ (n t) ^ 2 := by
    calc
      (|a| * t / 2) ^ 2 ≤ |n t| ^ 2 :=
        (sq_le_sq₀
          (by positivity : 0 ≤ |a| * t / 2)
          (abs_nonneg _)).mpr hnHalf
      _ = (n t) ^ 2 := sq_abs (n t)
  have hgammaSquare :
      gamma * (|a| * t / 2) ^ 2 ≤
        gamma * (n t) ^ 2 :=
    mul_le_mul_of_nonneg_left hsquare hgamma.le
  have hlossUpper :
      loss * |n t| ≤
        loss * (|a| * t + err) :=
    mul_le_mul_of_nonneg_left hnUpper hloss
  dsimp [A, B, C]
  nlinarith [sq_abs a]

/-- Symmetric-loss version at positive infinity.  Writing the linear loss
as `1 + |t|` makes the same estimate usable in both time directions. -/
theorem affine_boundedError_quadratic_escape_abs_atTop
    {n : ℝ → ℝ} {a gamma loss scale err : ℝ}
    (ha : a ≠ 0)
    (hgamma : 0 < gamma)
    (hloss : 0 ≤ loss)
    (hn :
      ∀ᶠ t in atTop,
        |n t - a * t| ≤ err) :
    Tendsto
      (fun t : ℝ ↦
        gamma * (n t) ^ 2 -
          loss * |n t| -
          scale * (1 + |t|))
      atTop atTop := by
  have h :=
    affine_boundedError_quadratic_escape
      (n := n) (a := a) (gamma := gamma)
      (loss := loss) (scale := scale) (err := err)
      ha hgamma hloss hn
  apply h.congr'
  filter_upwards [eventually_ge_atTop 0] with t ht
  simp only [abs_of_nonneg ht]

/-- Symmetric-loss version at negative infinity.  The proof is the
positive-time theorem applied after the substitution `t ↦ -t`. -/
theorem affine_boundedError_quadratic_escape_abs_atBot
    {n : ℝ → ℝ} {a gamma loss scale err : ℝ}
    (ha : a ≠ 0)
    (hgamma : 0 < gamma)
    (hloss : 0 ≤ loss)
    (hn :
      ∀ᶠ t in atBot,
        |n t - a * t| ≤ err) :
    Tendsto
      (fun t : ℝ ↦
        gamma * (n t) ^ 2 -
          loss * |n t| -
          scale * (1 + |t|))
      atBot atTop := by
  have hnNeg :
      ∀ᶠ t in atTop,
        |n (-t) - (-a) * t| ≤ err := by
    filter_upwards
      [tendsto_neg_atTop_atBot.eventually hn] with t ht
    convert ht using 1
    ring_nf
  have htop :=
    affine_boundedError_quadratic_escape_abs_atTop
      (n := fun t ↦ n (-t))
      (a := -a) (gamma := gamma)
      (loss := loss) (scale := scale) (err := err)
      (neg_ne_zero.mpr ha) hgamma hloss hnNeg
  have hcomp :=
    htop.comp tendsto_neg_atBot_atTop
  simpa only [Function.comp_def, neg_neg, abs_neg] using hcomp

end

end HGAS.Analysis
