import HGAS.Modular.JacobiThetaVector
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Duplication identities for the four Jacobi theta functions

This file derives the quadratic Jacobi identities directly from Mathlib's
absolutely convergent two-variable theta series.  The elementary reindexing
behind every formula is

```
  (m,n) = (a+b,a-b)       or       (a+b+1,a-b),
```

according as `m+n` is even or odd.  Thus the square of a theta series at
modulus `τ` splits into an integral and a half-integral theta product at
modulus `2τ`.

No product expansion, zero classification, or external theta identity is
used.  The formulas proved here are the analytic input needed to put the
projective four-theta map on the two residual quadrics.
-/

namespace HGAS.Modular

open Complex Real

noncomputable section

/-! ## The parity reindexing of `ℤ × ℤ` -/

/-- The even/odd decomposition of a pair of integers used in the theta
duplication formulas. -/
def thetaParityReindex :
    (ℤ × ℤ) ⊕ (ℤ × ℤ) ≃ (ℤ × ℤ) :=
  Equiv.ofBijective
    (fun x ↦
      match x with
      | Sum.inl (a, b) => (a + b, a - b)
      | Sum.inr (a, b) => (a + b + 1, a - b))
    (by
      constructor
      · intro x y hxy
        rcases x with ⟨x⟩ | ⟨x⟩ <;>
          rcases y with ⟨y⟩ | ⟨y⟩ <;>
          rcases x with ⟨a, b⟩ <;>
          rcases y with ⟨c, d⟩
        · simp only at hxy
          have h1 := congrArg Prod.fst hxy
          have h2 := congrArg Prod.snd hxy
          simp only at h1 h2
          congr <;> omega
        · simp only at hxy
          have h1 := congrArg Prod.fst hxy
          have h2 := congrArg Prod.snd hxy
          simp only at h1 h2
          omega
        · simp only at hxy
          have h1 := congrArg Prod.fst hxy
          have h2 := congrArg Prod.snd hxy
          simp only at h1 h2
          omega
        · simp only at hxy
          have h1 := congrArg Prod.fst hxy
          have h2 := congrArg Prod.snd hxy
          simp only at h1 h2
          congr <;> omega
      · rintro ⟨m, n⟩
        obtain ⟨a, ha | ha⟩ := Int.even_or_odd' (m + n)
        · refine ⟨Sum.inl (a, m - a), ?_⟩
          simp only
          apply Prod.ext <;> simp only
          · omega
          · omega
        · refine ⟨Sum.inr (a, m - a - 1), ?_⟩
          simp only
          apply Prod.ext <;> simp only
          · omega
          · omega)

@[simp] theorem thetaParityReindex_inl
    (a b : ℤ) :
    thetaParityReindex (Sum.inl (a, b)) =
      (a + b, a - b) :=
  rfl

@[simp] theorem thetaParityReindex_inr
    (a b : ℤ) :
    thetaParityReindex (Sum.inr (a, b)) =
      (a + b + 1, a - b) :=
  rfl

/-! ## Integral and half-integral summands -/

/-- The summand with half-integral characteristic. -/
def jacobiThetaHalfTerm
    (n : ℤ) (z τ : ℂ) : ℂ :=
  cexp
    (2 * π * I * ((n : ℂ) + 1 / 2) * z +
      π * I * ((n : ℂ) + 1 / 2) ^ 2 * τ)

/-- A half-integral summand is an elementary exponential factor times
Mathlib's integral summand at the shifted argument `z+τ/2`. -/
theorem jacobiThetaHalfTerm_eq
    (n : ℤ) (z τ : ℂ) :
    jacobiThetaHalfTerm n z τ =
      cexp (π * I * (τ / 4 + z)) *
        jacobiTheta₂_term n (z + τ / 2) τ := by
  rw [jacobiThetaHalfTerm, jacobiTheta₂_term,
    ← Complex.exp_add]
  congr 1
  ring

/-- Absolute summability of the half-integral theta series in the upper
half-plane. -/
theorem summable_jacobiThetaHalfTerm
    (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun n : ℤ ↦ jacobiThetaHalfTerm n z τ) := by
  simp_rw [jacobiThetaHalfTerm_eq]
  exact
    ((summable_jacobiTheta₂_term_iff
      (z + τ / 2) τ).mpr hτ).mul_left _

/-- The shifted definition of `θ₂` is exactly the half-integral series. -/
theorem jacobiTheta2_eq_tsum_half
    (z τ : ℂ) :
    jacobiTheta2 z τ =
      ∑' n : ℤ, jacobiThetaHalfTerm n z τ := by
  rw [jacobiTheta2, jacobiTheta₂, ← tsum_mul_left]
  apply tsum_congr
  intro n
  exact (jacobiThetaHalfTerm_eq n z τ).symm

/-! ## Termwise parity calculations -/

private theorem theta3_square_term_even
    (a b : ℤ) (z τ : ℂ) :
    jacobiTheta₂_term (a + b) z τ *
        jacobiTheta₂_term (a - b) z τ =
      jacobiTheta₂_term a (2 * z) (2 * τ) *
        jacobiTheta₂_term b 0 (2 * τ) := by
  rw [jacobiTheta₂_term, jacobiTheta₂_term,
    jacobiTheta₂_term, jacobiTheta₂_term,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem theta3_square_term_odd
    (a b : ℤ) (z τ : ℂ) :
    jacobiTheta₂_term (a + b + 1) z τ *
        jacobiTheta₂_term (a - b) z τ =
      jacobiThetaHalfTerm a (2 * z) (2 * τ) *
        jacobiThetaHalfTerm b 0 (2 * τ) := by
  rw [jacobiTheta₂_term, jacobiTheta₂_term,
    jacobiThetaHalfTerm, jacobiThetaHalfTerm,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem theta2_square_term_even
    (a b : ℤ) (z τ : ℂ) :
    jacobiThetaHalfTerm (a + b) z τ *
        jacobiThetaHalfTerm (a - b) z τ =
      jacobiThetaHalfTerm a (2 * z) (2 * τ) *
        jacobiTheta₂_term b 0 (2 * τ) := by
  rw [jacobiThetaHalfTerm, jacobiThetaHalfTerm,
    jacobiThetaHalfTerm, jacobiTheta₂_term,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem theta2_square_term_odd
    (a b : ℤ) (z τ : ℂ) :
    jacobiThetaHalfTerm (a + b + 1) z τ *
        jacobiThetaHalfTerm (a - b) z τ =
      jacobiTheta₂_term (a + 1) (2 * z) (2 * τ) *
        jacobiThetaHalfTerm b 0 (2 * τ) := by
  rw [jacobiThetaHalfTerm, jacobiThetaHalfTerm,
    jacobiTheta₂_term, jacobiThetaHalfTerm,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-! ## The first two duplication formulas -/

/-- Duplication formula for `θ₃²`. -/
theorem jacobiTheta3_sq_duplication
    (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta3 z τ ^ 2 =
      jacobiTheta3 (2 * z) (2 * τ) *
          jacobiTheta3 0 (2 * τ) +
        jacobiTheta2 (2 * z) (2 * τ) *
          jacobiTheta2 0 (2 * τ) := by
  have hτ2 : 0 < (2 * τ).im := by
    simpa [mul_im] using
      mul_pos (by norm_num : (0 : ℝ) < 2) hτ
  have hIntZ :
      Summable
        (fun n : ℤ ↦
          jacobiTheta₂_term n z τ) :=
    (summable_jacobiTheta₂_term_iff z τ).mpr hτ
  have hInt2Z :
      Summable
        (fun n : ℤ ↦
          jacobiTheta₂_term n (2 * z) (2 * τ)) :=
    (summable_jacobiTheta₂_term_iff
      (2 * z) (2 * τ)).mpr hτ2
  have hInt20 :
      Summable
        (fun n : ℤ ↦
          jacobiTheta₂_term n 0 (2 * τ)) :=
    (summable_jacobiTheta₂_term_iff
      0 (2 * τ)).mpr hτ2
  have hHalf2Z :=
    summable_jacobiThetaHalfTerm (2 * z) hτ2
  have hHalf20 :=
    summable_jacobiThetaHalfTerm 0 hτ2
  have hEven :
      Summable
        (fun x : ℤ × ℤ ↦
          jacobiTheta₂_term
              (thetaParityReindex (Sum.inl x)).1 z τ *
            jacobiTheta₂_term
              (thetaParityReindex (Sum.inl x)).2 z τ) := by
    apply (summable_mul_of_summable_norm
      hInt2Z.norm hInt20.norm).congr
    rintro ⟨a, b⟩
    exact (theta3_square_term_even a b z τ).symm
  have hOdd :
      Summable
        (fun x : ℤ × ℤ ↦
          jacobiTheta₂_term
              (thetaParityReindex (Sum.inr x)).1 z τ *
            jacobiTheta₂_term
              (thetaParityReindex (Sum.inr x)).2 z τ) := by
    apply (summable_mul_of_summable_norm
      hHalf2Z.norm hHalf20.norm).congr
    rintro ⟨a, b⟩
    exact (theta3_square_term_odd a b z τ).symm
  calc
    jacobiTheta3 z τ ^ 2 =
        ∑' x : ℤ × ℤ,
          jacobiTheta₂_term x.1 z τ *
            jacobiTheta₂_term x.2 z τ := by
      rw [jacobiTheta3, jacobiTheta₂, pow_two,
        tsum_mul_tsum_of_summable_norm
          hIntZ.norm hIntZ.norm]
    _ =
        ∑' x : (ℤ × ℤ) ⊕ (ℤ × ℤ),
          jacobiTheta₂_term
              (thetaParityReindex x).1 z τ *
            jacobiTheta₂_term
              (thetaParityReindex x).2 z τ :=
      (thetaParityReindex.tsum_eq _).symm
    _ =
        (∑' x : ℤ × ℤ,
          jacobiTheta₂_term
              (thetaParityReindex (Sum.inl x)).1 z τ *
            jacobiTheta₂_term
              (thetaParityReindex (Sum.inl x)).2 z τ) +
        ∑' x : ℤ × ℤ,
          jacobiTheta₂_term
              (thetaParityReindex (Sum.inr x)).1 z τ *
            jacobiTheta₂_term
              (thetaParityReindex (Sum.inr x)).2 z τ :=
      Summable.tsum_sum hEven hOdd
    _ =
        ((∑' a : ℤ,
            jacobiTheta₂_term a (2 * z) (2 * τ)) *
          ∑' b : ℤ,
            jacobiTheta₂_term b 0 (2 * τ)) +
        ((∑' a : ℤ,
            jacobiThetaHalfTerm a (2 * z) (2 * τ)) *
          ∑' b : ℤ,
            jacobiThetaHalfTerm b 0 (2 * τ)) := by
      congr 1
      · rw [tsum_mul_tsum_of_summable_norm
          hInt2Z.norm hInt20.norm]
        apply tsum_congr
        rintro ⟨a, b⟩
        exact theta3_square_term_even a b z τ
      · rw [tsum_mul_tsum_of_summable_norm
          hHalf2Z.norm hHalf20.norm]
        apply tsum_congr
        rintro ⟨a, b⟩
        exact theta3_square_term_odd a b z τ
    _ =
      jacobiTheta3 (2 * z) (2 * τ) *
          jacobiTheta3 0 (2 * τ) +
        jacobiTheta2 (2 * z) (2 * τ) *
          jacobiTheta2 0 (2 * τ) := by
      simp only [jacobiTheta3, jacobiTheta₂,
        jacobiTheta2_eq_tsum_half]

/-- Duplication formula for `θ₂²`. -/
theorem jacobiTheta2_sq_duplication
    (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta2 z τ ^ 2 =
      jacobiTheta2 (2 * z) (2 * τ) *
          jacobiTheta3 0 (2 * τ) +
        jacobiTheta3 (2 * z) (2 * τ) *
          jacobiTheta2 0 (2 * τ) := by
  have hτ2 : 0 < (2 * τ).im := by
    simpa [mul_im] using
      mul_pos (by norm_num : (0 : ℝ) < 2) hτ
  have hHalfZ :=
    summable_jacobiThetaHalfTerm z hτ
  have hHalf2Z :=
    summable_jacobiThetaHalfTerm (2 * z) hτ2
  have hHalf20 :=
    summable_jacobiThetaHalfTerm 0 hτ2
  have hInt2Z :
      Summable
        (fun n : ℤ ↦
          jacobiTheta₂_term n (2 * z) (2 * τ)) :=
    (summable_jacobiTheta₂_term_iff
      (2 * z) (2 * τ)).mpr hτ2
  have hInt20 :
      Summable
        (fun n : ℤ ↦
          jacobiTheta₂_term n 0 (2 * τ)) :=
    (summable_jacobiTheta₂_term_iff
      0 (2 * τ)).mpr hτ2
  have hEven :
      Summable
        (fun x : ℤ × ℤ ↦
          jacobiThetaHalfTerm
              (thetaParityReindex (Sum.inl x)).1 z τ *
            jacobiThetaHalfTerm
              (thetaParityReindex (Sum.inl x)).2 z τ) := by
    apply (summable_mul_of_summable_norm
      hHalf2Z.norm hInt20.norm).congr
    rintro ⟨a, b⟩
    exact (theta2_square_term_even a b z τ).symm
  have hOdd :
      Summable
        (fun x : ℤ × ℤ ↦
          jacobiThetaHalfTerm
              (thetaParityReindex (Sum.inr x)).1 z τ *
            jacobiThetaHalfTerm
              (thetaParityReindex (Sum.inr x)).2 z τ) := by
    have hIntShift :
        Summable
          (fun a : ℤ ↦
            jacobiTheta₂_term (a + 1) (2 * z) (2 * τ)) :=
      hInt2Z.comp_injective (fun _ _ h ↦ by omega)
    apply (summable_mul_of_summable_norm
      hIntShift.norm hHalf20.norm).congr
    rintro ⟨a, b⟩
    exact (theta2_square_term_odd a b z τ).symm
  calc
    jacobiTheta2 z τ ^ 2 =
        ∑' x : ℤ × ℤ,
          jacobiThetaHalfTerm x.1 z τ *
            jacobiThetaHalfTerm x.2 z τ := by
      rw [jacobiTheta2_eq_tsum_half, pow_two,
        tsum_mul_tsum_of_summable_norm
          hHalfZ.norm hHalfZ.norm]
    _ =
        ∑' x : (ℤ × ℤ) ⊕ (ℤ × ℤ),
          jacobiThetaHalfTerm
              (thetaParityReindex x).1 z τ *
            jacobiThetaHalfTerm
              (thetaParityReindex x).2 z τ :=
      (thetaParityReindex.tsum_eq _).symm
    _ =
        (∑' x : ℤ × ℤ,
          jacobiThetaHalfTerm
              (thetaParityReindex (Sum.inl x)).1 z τ *
            jacobiThetaHalfTerm
              (thetaParityReindex (Sum.inl x)).2 z τ) +
        ∑' x : ℤ × ℤ,
          jacobiThetaHalfTerm
              (thetaParityReindex (Sum.inr x)).1 z τ *
            jacobiThetaHalfTerm
              (thetaParityReindex (Sum.inr x)).2 z τ :=
      Summable.tsum_sum hEven hOdd
    _ =
        ((∑' a : ℤ,
            jacobiThetaHalfTerm a (2 * z) (2 * τ)) *
          ∑' b : ℤ,
            jacobiTheta₂_term b 0 (2 * τ)) +
        ((∑' a : ℤ,
            jacobiTheta₂_term (a + 1) (2 * z) (2 * τ)) *
          ∑' b : ℤ,
            jacobiThetaHalfTerm b 0 (2 * τ)) := by
      congr 1
      · rw [tsum_mul_tsum_of_summable_norm
          hHalf2Z.norm hInt20.norm]
        apply tsum_congr
        rintro ⟨a, b⟩
        exact theta2_square_term_even a b z τ
      · rw [tsum_mul_tsum_of_summable_norm]
        · apply tsum_congr
          rintro ⟨a, b⟩
          exact theta2_square_term_odd a b z τ
        · exact
            (hInt2Z.comp_injective
              (fun _ _ h ↦ by omega)).norm
        · exact hHalf20.norm
    _ =
      jacobiTheta2 (2 * z) (2 * τ) *
          jacobiTheta3 0 (2 * τ) +
        jacobiTheta3 (2 * z) (2 * τ) *
          jacobiTheta2 0 (2 * τ) := by
      have hIntShift :
          (∑' a : ℤ,
              jacobiTheta₂_term
                (a + 1) (2 * z) (2 * τ)) =
            ∑' a : ℤ,
              jacobiTheta₂_term
                a (2 * z) (2 * τ) :=
        (Equiv.addRight (1 : ℤ)).tsum_eq
          (fun a : ℤ ↦
            jacobiTheta₂_term a (2 * z) (2 * τ))
      rw [hIntShift]
      simp only [jacobiTheta3, jacobiTheta₂,
        jacobiTheta2_eq_tsum_half]

/-! ## The two translated duplication formulas -/

/-- Translation by one changes the sign of `θ₂`. -/
theorem jacobiTheta2_add_one
    (z τ : ℂ) :
    jacobiTheta2 (z + 1) τ =
      -jacobiTheta2 z τ := by
  rw [jacobiTheta2, jacobiTheta2,
    show z + 1 + τ / 2 =
      (z + τ / 2) + 1 by ring,
    jacobiTheta₂_add_left]
  rw [show
      π * I * (τ / 4 + (z + 1)) =
        π * I * (τ / 4 + z) + π * I by ring,
    Complex.exp_add, Complex.exp_pi_mul_I]
  ring

/-- Translation by one fixes `θ₃`. -/
theorem jacobiTheta3_add_one
    (z τ : ℂ) :
    jacobiTheta3 (z + 1) τ =
      jacobiTheta3 z τ := by
  exact jacobiTheta₂_add_left z τ

/-- Duplication formula for `θ₄²`. -/
theorem jacobiTheta4_sq_duplication
    (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta4 z τ ^ 2 =
      jacobiTheta3 (2 * z) (2 * τ) *
          jacobiTheta3 0 (2 * τ) -
        jacobiTheta2 (2 * z) (2 * τ) *
          jacobiTheta2 0 (2 * τ) := by
  have h :=
    jacobiTheta3_sq_duplication
      (z + 1 / 2) hτ
  rw [show 2 * (z + 1 / 2) =
      2 * z + 1 by ring,
    jacobiTheta3_add_one,
    jacobiTheta2_add_one] at h
  simpa only [jacobiTheta4, neg_mul] using h

/-- Duplication formula for `θ₁²`. -/
theorem jacobiTheta1_sq_duplication
    (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta1 z τ ^ 2 =
      jacobiTheta3 (2 * z) (2 * τ) *
          jacobiTheta2 0 (2 * τ) -
        jacobiTheta2 (2 * z) (2 * τ) *
          jacobiTheta3 0 (2 * τ) := by
  have h :=
    jacobiTheta2_sq_duplication
      (z + 1 / 2) hτ
  rw [show 2 * (z + 1 / 2) =
      2 * z + 1 by ring,
    jacobiTheta2_add_one,
    jacobiTheta3_add_one] at h
  rw [jacobiTheta1, neg_sq]
  linear_combination h

end

end HGAS.Modular
