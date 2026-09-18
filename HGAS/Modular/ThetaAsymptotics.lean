import HGAS.Analysis.AtImInfty
import HGAS.Modular.ThetaConstants
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.Tactic

/-!
# Cusp limits of the even theta constants

At the cusp `Im τ → +∞`, the defining Gaussian series give

```
θ₂(τ) → 0,   θ₃(τ) → 1,   θ₄(τ) → 1.
```

The proof below is an explicit dominated-convergence argument.  In
particular it does not assume modularity or a pre-existing Fourier
expansion of the three functions, so it can be used to establish those
facts later without circularity.

The majorants are Gaussian and summable by Mathlib's convergence theorem
for `jacobiTheta₂`.  This argument is adapted from the formal proof in
`Sphere-Packing-Lean` and uses Mathlib 4.30's Tannery theorem.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I
open Complex Real Filter Topology
open HGAS.Analysis
open scoped Real Topology

noncomputable section

/-- The diagonal summand occurring in the `θ₂` specialization. -/
lemma jacobiTheta₂Term_half_apply (n : ℤ) (z : ℂ) :
    jacobiTheta₂_term n (z / 2) z =
      cexp (π * I * (n ^ 2 + n) * z) := by
  rw [jacobiTheta₂_term]
  ring_nf

/-- A Gaussian majorant for the diagonal `θ₂` specialization. -/
lemma jacobiTheta₂_gaussian_half (n : ℤ) (t : ℝ) :
    rexp (-π * (n + 1 / 2) ^ 2 * t) =
      rexp (-π * t / 4) *
        jacobiTheta₂_term n (I * t / 2) (I * t) := by
  rw [jacobiTheta₂Term_half_apply, ofReal_exp,
    ofReal_exp, ← Complex.exp_add, ofReal_mul]
  congr
  ring_nf
  simp
  ring_nf!

/-- Norm of an exponential whose exponent ends in `i`. -/
lemma norm_cexp_mul_I (z : ℂ) :
    ‖cexp (z * I)‖ = rexp (-z.im) := by
  simp [norm_exp]

/-- The diagonal theta specialization tends to `2`; precisely the
summands `n=-1,0` survive. -/
theorem jacobiTheta₂_half_mul_tendsto_atImInfty :
    Tendsto
      (fun x : ℍ ↦ jacobiTheta₂ (x / 2) x)
      atImInfty (𝓝 2) := by
  simp_rw [jacobiTheta₂, jacobiTheta₂_term]
  convert tendsto_tsum_of_dominated_convergence
    (f := fun z (n : ℤ) ↦
      cexp
        (2 * π * I * n * (z / 2) +
          π * I * n ^ 2 * z))
    (𝓕 := atImInfty)
    (g := Set.indicator {-1, 0} 1)
    (bound := fun n : ℤ ↦
      rexp (π / 4) *
        rexp (-π * ((n : ℝ) + 1 / 2) ^ 2))
      ?_ ?_ ?_
  · simp [← tsum_subtype]
  · apply summable_ofReal.mp
    have hn (n : ℤ) :=
      jacobiTheta₂_gaussian_half n 1
    simp_rw [mul_one] at hn
    simp_rw [ofReal_mul, hn, ← smul_eq_mul]
    apply Summable.const_smul
    apply Summable.const_smul
    rw [summable_jacobiTheta₂_term_iff]
    simp
  · intro n
    have hn :
        n = -1 ∨ n = 0 ∨
          n ∉ ({-1, 0} : Set ℤ) := by
      rw [Set.mem_insert_iff,
        Set.mem_singleton_iff]
      tauto
    rcases hn with rfl | rfl | hn
    · ring_nf
      simp
    · ring_nf
      simp
    · ring_nf
      simp only [hn, not_false_eq_true,
        Set.indicator_of_notMem]
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      have hexp (z : ℂ) :
          π * I * n * z + π * I * n ^ 2 * z =
            π * (n + n ^ 2) * z * I := by
        ring_nf
      have hbase :
          rexp (-π) ^ ((n : ℝ) + n ^ 2) < 1 := by
        apply Real.rpow_lt_one
        · positivity
        · exact Real.exp_lt_one_iff.mpr
            (neg_lt_zero.mpr Real.pi_pos)
        convert_to 0 <
          ((n * (n + 1) : ℤ) : ℝ)
        · push_cast
          ring_nf
        · apply Int.cast_pos.mpr
          by_cases hpos : 0 < n
          · exact mul_pos hpos (by omega)
          · rw [Set.mem_insert_iff,
              Set.mem_singleton_iff] at hn
            exact mul_pos_of_neg_of_neg
              (by omega) (by omega)
      simp_rw [hexp, norm_cexp_mul_I, mul_assoc,
        im_ofReal_mul, ← Int.cast_pow,
        ← Int.cast_add, ← ofReal_intCast,
        im_ofReal_mul, ← mul_assoc, Int.cast_add,
        Int.cast_pow, ← neg_mul, Real.exp_mul,
        coe_im]
      refine
        (tendsto_rpow_atTop_of_base_lt_one
          _ ?_ hbase).comp tendsto_im_atImInfty
      exact neg_one_lt_zero.trans (by positivity)
  · rw [eventually_atImInfty]
    use 1
    intro z hz n
    simp_rw [← Real.exp_add]
    ring_nf
    trans
      ‖cexp
        (((π * n + π * n ^ 2 : ℝ) * z) * I)‖
    · apply le_of_eq
      simpa [add_mul] using by ring_nf
    · rw [norm_cexp_mul_I, im_ofReal_mul]
      have hn :
          0 ≤ (n : ℝ) ^ 2 + n := by
        nth_rw 2 [← mul_one n]
        rw [sq, Int.cast_mul, Int.cast_one,
          ← mul_add]
        rcases lt_trichotomy (-1) n with h | rfl | h
        · apply mul_nonneg <;> norm_cast
          all_goals omega
        · norm_num
        · apply mul_nonneg_of_nonpos_of_nonpos <;>
            norm_cast <;> omega
      simpa using
        le_mul_of_one_le_right
          (by
            rw [← mul_add, add_comm]
            exact mul_nonneg Real.pi_nonneg hn)
          hz

/-- At the cusp, the zero-characteristic theta specialization tends to
its constant coefficient `1`. -/
theorem jacobiTheta₂_zero_tendsto_atImInfty :
    Tendsto
      (fun x : ℍ ↦ jacobiTheta₂ 0 x)
      atImInfty (𝓝 1) := by
  simp_rw [jacobiTheta₂, jacobiTheta₂_term,
    mul_zero, zero_add]
  convert tendsto_tsum_of_dominated_convergence
    (f := fun (z : ℍ) (n : ℤ) ↦
      cexp (π * I * n ^ 2 * z))
    (𝓕 := atImInfty)
    (g := fun n ↦ if n = 0 then 1 else 0)
    (bound := fun n : ℤ ↦
      rexp (-π * n ^ 2)) ?_ ?_ ?_
  · simp
  · have hsum :=
      ((summable_jacobiTheta₂_term_iff
        0 UpperHalfPlane.I).mpr (by simp)).norm
    have hnorm (n : ℤ) :
        ‖jacobiTheta₂_term n 0
          UpperHalfPlane.I‖ =
          rexp (-π * (n : ℝ) ^ 2) := by
      simpa using
        norm_jacobiTheta₂_term
          n 0 UpperHalfPlane.I
    simpa only [hnorm] using hsum
  · intro n
    change
      Tendsto
        (fun z : ℍ ↦ cexp (π * I * n ^ 2 * z))
        atImInfty
        (𝓝 (if n = 0 then 1 else 0))
    split_ifs with hn
    · subst hn
      simp
    · rw [tendsto_zero_iff_norm_tendsto_zero]
      simp_rw [mul_right_comm _ I,
        norm_cexp_mul_I, mul_assoc,
        im_ofReal_mul, ← ofReal_intCast,
        ← ofReal_pow, im_ofReal_mul,
        ← mul_assoc]
      simpa using
        tendsto_im_atImInfty.const_mul_atTop
          (by positivity)
  · rw [eventually_atImInfty]
    use 1
    intro z hz n
    simp_rw [mul_right_comm _ I,
      norm_cexp_mul_I]
    simpa [← ofReal_intCast, ← ofReal_pow] using
      le_mul_of_one_le_right (by positivity) hz

/-- At the cusp, the half-characteristic specialization also tends to
its constant coefficient `1`. -/
theorem jacobiTheta₂_oneHalf_tendsto_atImInfty :
    Tendsto
      (fun x : ℍ ↦
        jacobiTheta₂ (1 / 2 : ℂ) x)
      atImInfty (𝓝 1) := by
  have hnorm (z : ℍ) (n : ℤ) :
      ‖cexp
        (2 * π * I * n * (1 / 2 : ℂ) +
          π * I * n ^ 2 * z)‖ =
        rexp (-π * n ^ 2 * z.im) := by
    simpa [jacobiTheta₂_term, coe_im] using
      (norm_jacobiTheta₂_term
        n (1 / 2 : ℂ) (z : ℂ))
  simp_rw [jacobiTheta₂, jacobiTheta₂_term]
  convert tendsto_tsum_of_dominated_convergence
    (f := fun (z : ℍ) (n : ℤ) ↦
      cexp
        (2 * π * I * n * (1 / 2 : ℂ) +
          π * I * n ^ 2 * z))
    (𝓕 := atImInfty)
    (g := fun n ↦ if n = 0 then 1 else 0)
    (bound := fun n : ℤ ↦
      rexp (-π * n ^ 2)) ?_ ?_ ?_
  · simp
  · have hsum :=
      ((summable_jacobiTheta₂_term_iff
        0 UpperHalfPlane.I).mpr (by simp)).norm
    have hnorm' (n : ℤ) :
        ‖jacobiTheta₂_term n 0
          UpperHalfPlane.I‖ =
          rexp (-π * (n : ℝ) ^ 2) := by
      simpa using
        norm_jacobiTheta₂_term
          n 0 UpperHalfPlane.I
    simpa only [hnorm'] using hsum
  · intro n
    change
      Tendsto
        (fun z : ℍ ↦
          cexp
            (2 * π * I * n * (1 / 2 : ℂ) +
              π * I * n ^ 2 * z))
        atImInfty
        (𝓝 (if n = 0 then 1 else 0))
    split_ifs with hn
    · subst hn
      simp
    · rw [tendsto_zero_iff_norm_tendsto_zero]
      simp_rw [hnorm]
      have hnpos : 0 < (n : ℝ) ^ 2 :=
        sq_pos_of_ne_zero
          (Int.cast_ne_zero.mpr hn)
      exact
        Real.tendsto_exp_atBot.comp
          (tendsto_im_atImInfty
            |>.const_mul_atTop_of_neg
              (by nlinarith [Real.pi_pos, hnpos]))
  · rw [eventually_atImInfty]
    use 1
    intro z hz n
    rw [hnorm]
    have hnonpos :
        -π * (n : ℝ) ^ 2 ≤ 0 := by
      nlinarith [Real.pi_pos,
        sq_nonneg (n : ℝ)]
    have hmul :
        -π * (n : ℝ) ^ 2 * z.im ≤
          -π * (n : ℝ) ^ 2 * 1 :=
      mul_le_mul_of_nonpos_left hz hnonpos
    simpa using Real.exp_le_exp.mpr hmul

/-- `θ₂` tends to zero at the cusp. -/
theorem theta₂_tendsto_atImInfty :
    Tendsto theta₂ atImInfty (𝓝 0) := by
  rw [funext theta₂_eq_jacobiTheta₂,
    ← zero_mul (2 : ℂ)]
  refine Tendsto.mul ?_
    jacobiTheta₂_half_mul_tendsto_atImInfty
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hnorm (z : ℍ) :
      ‖cexp (π * I * z / 4)‖ =
        rexp (-π * z.im / 4) := by
    rw [mul_right_comm, mul_div_right_comm,
      norm_cexp_mul_I]
    simp [neg_div]
  simp_rw [hnorm]
  exact
    Real.tendsto_exp_atBot.comp
      ((tendsto_div_const_atBot_of_pos
        zero_lt_four).mpr
        (tendsto_im_atImInfty
          |>.const_mul_atTop_of_neg
            (neg_lt_zero.mpr Real.pi_pos)))

/-- `θ₃` tends to one at the cusp. -/
theorem theta₃_tendsto_atImInfty :
    Tendsto theta₃ atImInfty (𝓝 1) := by
  simpa [funext theta₃_eq_jacobiTheta₂] using
    jacobiTheta₂_zero_tendsto_atImInfty

/-- `θ₄` tends to one at the cusp. -/
theorem theta₄_tendsto_atImInfty :
    Tendsto theta₄ atImInfty (𝓝 1) := by
  simpa [funext theta₄_eq_jacobiTheta₂] using
    jacobiTheta₂_oneHalf_tendsto_atImInfty

/-- `H₂=θ₂⁴` tends to zero at the cusp. -/
theorem H₂_tendsto_atImInfty :
    Tendsto H₂ atImInfty (𝓝 0) := by
  change Tendsto
    (fun x : ℍ ↦ theta₂ x ^ 4)
    atImInfty (𝓝 0)
  simpa using theta₂_tendsto_atImInfty.pow 4

/-- `H₃=θ₃⁴` tends to one at the cusp. -/
theorem H₃_tendsto_atImInfty :
    Tendsto H₃ atImInfty (𝓝 1) := by
  change Tendsto
    (fun x : ℍ ↦ theta₃ x ^ 4)
    atImInfty (𝓝 1)
  simpa using theta₃_tendsto_atImInfty.pow 4

/-- `H₄=θ₄⁴` tends to one at the cusp. -/
theorem H₄_tendsto_atImInfty :
    Tendsto H₄ atImInfty (𝓝 1) := by
  change Tendsto
    (fun x : ℍ ↦ theta₄ x ^ 4)
    atImInfty (𝓝 1)
  simpa using theta₄_tendsto_atImInfty.pow 4

end

end HGAS.Modular
