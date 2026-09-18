import HGAS.Modular.JacobiThetaInitialRank
import HGAS.Modular.ThetaAsymptotics
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic

/-!
# Unconditional Jacobi theta Wronskians

This module closes the three analytic identities isolated by
`CanonicalJacobiThetaWronskiansAt`.

The proof is product-free.  Its core is an absolutely convergent
double-series parity reindexing for the first Wronskian.  This produces a
doubling formula involving `θ₁'(0|2τ)`.  Iteration of the same identity,
together with a direct cusp limit of the differentiated theta series,
proves Jacobi's derivative formula

```
 θ₁'(0|τ) = π θ₂(0|τ) θ₃(0|τ) θ₄(0|τ).
```

The first Wronskian then follows from two bilinear duplication formulas.
The remaining two follow by differentiating the already formalized
residual quadrics and cancelling nonzero holomorphic factors.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I
open Complex Real Filter Topology
open HGAS.Analysis

noncomputable section

/-! ## Differentiated half-characteristic series -/

/-- Termwise `z`-derivative of the half-characteristic summand. -/
def jacobiThetaHalfPrimeTerm
    (n : ℤ) (z τ : ℂ) : ℂ :=
  2 * π * I * ((n : ℂ) + 1 / 2) *
    jacobiThetaHalfTerm n z τ

/-- Express the differentiated half-characteristic term through
Mathlib's integral theta term and its derivative. -/
theorem jacobiThetaHalfPrimeTerm_eq
    (n : ℤ) (z τ : ℂ) :
    jacobiThetaHalfPrimeTerm n z τ =
      cexp (π * I * (τ / 4 + z)) *
        (π * I * jacobiTheta₂_term n (z + τ / 2) τ +
          jacobiTheta₂'_term n (z + τ / 2) τ) := by
  rw [jacobiThetaHalfPrimeTerm,
    jacobiThetaHalfTerm_eq,
    jacobiTheta₂'_term]
  ring

theorem summable_jacobiThetaHalfPrimeTerm
    (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    Summable
      (fun n : ℤ ↦
        jacobiThetaHalfPrimeTerm n z τ) := by
  have hterm :
      Summable
        (fun n : ℤ ↦
          jacobiTheta₂_term n (z + τ / 2) τ) :=
    (summable_jacobiTheta₂_term_iff
      (z + τ / 2) τ).2 hτ
  have hprime :
      Summable
        (fun n : ℤ ↦
          jacobiTheta₂'_term n (z + τ / 2) τ) :=
    (summable_jacobiTheta₂'_term_iff
      (z + τ / 2) τ).2 hτ
  apply
    ((hterm.mul_left (π * I)).add hprime
      |>.mul_left
        (cexp (π * I * (τ / 4 + z)))).congr
  intro n
  exact (jacobiThetaHalfPrimeTerm_eq n z τ).symm

/-- The explicit `jacobiTheta2Prime` is the sum of the differentiated
half-characteristic series. -/
theorem jacobiTheta2Prime_eq_tsum_half
    (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta2Prime z τ =
      ∑' n : ℤ,
        jacobiThetaHalfPrimeTerm n z τ := by
  unfold jacobiTheta2Prime jacobiTheta₂ jacobiTheta₂'
  rw [← tsum_mul_left]
  have hterm :
      Summable
        (fun n : ℤ ↦
          π * I *
            jacobiTheta₂_term n (z + τ / 2) τ) := by
    exact
      ((summable_jacobiTheta₂_term_iff
        (z + τ / 2) τ).2 hτ).mul_left _
  have hprime :
      Summable
        (fun n : ℤ ↦
          jacobiTheta₂'_term n (z + τ / 2) τ) := by
    exact
      (summable_jacobiTheta₂'_term_iff
        (z + τ / 2) τ).2 hτ
  rw [← hterm.tsum_add hprime]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  exact (jacobiThetaHalfPrimeTerm_eq n z τ).symm

/-- Series representation of the odd theta derivative. -/
theorem jacobiTheta1Prime_eq_tsum_half
    (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta1Prime z τ =
      ∑' n : ℤ,
        -jacobiThetaHalfPrimeTerm
          n (z + 1 / 2) τ := by
  rw [jacobiTheta1Prime,
    jacobiTheta2Prime_eq_tsum_half (z + 1 / 2) hτ,
    tsum_neg]

/-! ## The doubled-modulus first Wronskian -/

/-- One double-series term in
`θ₂'θ₁-θ₂θ₁'`, arranged in the sign convenient for the definitions of
`θ₁` and `θ₁'`. -/
def jacobiThetaWronskian2Term
    (x : ℤ × ℤ) (z τ : ℂ) : ℂ :=
  jacobiThetaHalfTerm x.1 z τ *
      jacobiThetaHalfPrimeTerm x.2
        (z + 1 / 2) τ -
    jacobiThetaHalfPrimeTerm x.1 z τ *
      jacobiThetaHalfTerm x.2
        (z + 1 / 2) τ

/-- Factorization of the even parity branch. -/
theorem jacobiThetaWronskian2Term_even
    (a b : ℤ) (z τ : ℂ) :
    jacobiThetaWronskian2Term
        (a + b, a - b) z τ =
      -2 *
        jacobiThetaHalfTerm a
          (2 * z + 1 / 2) (2 * τ) *
        jacobiTheta₂'_term b
          (1 / 2) (2 * τ) := by
  have hproduct :
      jacobiThetaHalfTerm (a + b) z τ *
          jacobiThetaHalfTerm (a - b)
            (z + 1 / 2) τ =
        jacobiThetaHalfTerm a
            (2 * z + 1 / 2) (2 * τ) *
          jacobiTheta₂_term b
            (1 / 2) (2 * τ) := by
    unfold jacobiThetaHalfTerm jacobiTheta₂_term
    rw [← Complex.exp_add, ← Complex.exp_add]
    rw [Complex.exp_eq_exp_iff_exists_int]
    refine ⟨-b, ?_⟩
    push_cast
    ring
  unfold jacobiThetaWronskian2Term
    jacobiThetaHalfPrimeTerm
    jacobiTheta₂'_term
  push_cast
  calc
    jacobiThetaHalfTerm (a + b) z τ *
          (2 * π * I * ((a : ℂ) - b + 1 / 2) *
            jacobiThetaHalfTerm (a - b)
              (z + 1 / 2) τ) -
        2 * π * I * ((a : ℂ) + b + 1 / 2) *
            jacobiThetaHalfTerm (a + b) z τ *
          jacobiThetaHalfTerm (a - b)
            (z + 1 / 2) τ =
        (2 * π * I * ((a - b : ℂ) + 1 / 2) -
            2 * π * I * ((a + b : ℂ) + 1 / 2)) *
          (jacobiThetaHalfTerm (a + b) z τ *
            jacobiThetaHalfTerm (a - b)
              (z + 1 / 2) τ) := by
                ring
    _ = _ := by
      rw [hproduct]
      ring

/-- Factorization of the odd parity branch. -/
theorem jacobiThetaWronskian2Term_odd
    (a b : ℤ) (z τ : ℂ) :
    jacobiThetaWronskian2Term
        (a + b + 1, a - b) z τ =
      2 *
        jacobiTheta₂_term (a + 1)
          (2 * z + 1 / 2) (2 * τ) *
        jacobiThetaHalfPrimeTerm b
          (1 / 2) (2 * τ) := by
  have hproduct :
      jacobiThetaHalfTerm (a + b + 1) z τ *
          jacobiThetaHalfTerm (a - b)
            (z + 1 / 2) τ =
        -(jacobiTheta₂_term (a + 1)
            (2 * z + 1 / 2) (2 * τ) *
          jacobiThetaHalfTerm b
            (1 / 2) (2 * τ)) := by
    unfold jacobiThetaHalfTerm jacobiTheta₂_term
    rw [← Complex.exp_add, ← Complex.exp_add]
    rw [neg_eq_neg_one_mul,
      ← Complex.exp_pi_mul_I,
      ← Complex.exp_add]
    rw [Complex.exp_eq_exp_iff_exists_int]
    refine ⟨-(b + 1), ?_⟩
    push_cast
    ring
  unfold jacobiThetaWronskian2Term
    jacobiThetaHalfPrimeTerm
  push_cast
  calc
    jacobiThetaHalfTerm (a + b + 1) z τ *
          (2 * π * I * ((a : ℂ) - b + 1 / 2) *
            jacobiThetaHalfTerm (a - b)
              (z + 1 / 2) τ) -
        2 * π * I *
            ((a : ℂ) + b + 1 + 1 / 2) *
            jacobiThetaHalfTerm (a + b + 1) z τ *
          jacobiThetaHalfTerm (a - b)
            (z + 1 / 2) τ =
        (2 * π * I * ((a - b : ℂ) + 1 / 2) -
            2 * π * I *
              ((a + b + 1 : ℂ) + 1 / 2)) *
          (jacobiThetaHalfTerm (a + b + 1) z τ *
            jacobiThetaHalfTerm (a - b)
              (z + 1 / 2) τ) := by
                ring
    _ = _ := by
      rw [hproduct]
      ring

/-! ## Summing the parity branches -/

/-- The derivative of the integral theta series vanishes at the real
half-period.  This is just periodicity together with oddness. -/
theorem jacobiTheta₂'_half_eq_zero
    (τ : ℂ) :
    jacobiTheta₂' (1 / 2) τ = 0 := by
  have hperiod :
      jacobiTheta₂' (1 / 2) τ =
        jacobiTheta₂' (-1 / 2) τ := by
    rw [← show
      (-1 / 2 : ℂ) + 1 = 1 / 2 by ring]
    exact jacobiTheta₂'_add_left (-1 / 2) τ
  have hodd :
      jacobiTheta₂' (-1 / 2) τ =
        -jacobiTheta₂' (1 / 2) τ := by
    simpa only [show
      -(1 / 2 : ℂ) = -1 / 2 by ring] using
      jacobiTheta₂'_neg_left (1 / 2) τ
  have hself :
      jacobiTheta₂' (1 / 2) τ =
        -jacobiTheta₂' (1 / 2) τ :=
    hperiod.trans hodd
  linear_combination (1 / 2 : ℂ) * hself

/-! The next elementary lemma keeps the analytic proof readable: it
packages the multiplication of four absolutely convergent series into
one skew double sum. -/

theorem tsum_skew_product
    {f g f' g' : ℤ → ℂ}
    (hf : Summable f) (hg : Summable g)
    (hf' : Summable f') (hg' : Summable g') :
    (∑' n, f' n) * -(∑' n, g n) -
        (∑' n, f n) * -(∑' n, g' n) =
      ∑' x : ℤ × ℤ,
        (f x.1 * g' x.2 - f' x.1 * g x.2) := by
  have hfg' :
      Summable
        (fun x : ℤ × ℤ ↦ f x.1 * g' x.2) :=
    summable_mul_of_summable_norm hf.norm hg'.norm
  have hf'g :
      Summable
        (fun x : ℤ × ℤ ↦ f' x.1 * g x.2) :=
    summable_mul_of_summable_norm hf'.norm hg.norm
  calc
    (∑' n, f' n) * -(∑' n, g n) -
          (∑' n, f n) * -(∑' n, g' n) =
        (∑' n, f n) * (∑' n, g' n) -
          (∑' n, f' n) * (∑' n, g n) := by
      ring
    _ =
        (∑' x : ℤ × ℤ, f x.1 * g' x.2) -
          ∑' x : ℤ × ℤ, f' x.1 * g x.2 := by
      rw [tsum_mul_tsum_of_summable_norm
          hf.norm hg'.norm,
        tsum_mul_tsum_of_summable_norm
          hf'.norm hg.norm]
    _ = _ := by
      rw [← hfg'.tsum_sub hf'g]

/-- Expanding the two products in the first Wronskian gives the
absolutely convergent double series of `jacobiThetaWronskian2Term`. -/
theorem jacobiTheta_wronskian2_eq_tsum
    (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta2Prime z τ * jacobiTheta1 z τ -
        jacobiTheta2 z τ * jacobiTheta1Prime z τ =
      ∑' x : ℤ × ℤ,
        jacobiThetaWronskian2Term x z τ := by
  have hHalfZ :=
    summable_jacobiThetaHalfTerm z hτ
  have hHalfShift :=
    summable_jacobiThetaHalfTerm (z + 1 / 2) hτ
  have hPrimeZ :=
    summable_jacobiThetaHalfPrimeTerm z hτ
  have hPrimeShift :=
    summable_jacobiThetaHalfPrimeTerm (z + 1 / 2) hτ
  rw [jacobiTheta2Prime_eq_tsum_half z hτ,
    jacobiTheta2_eq_tsum_half,
    jacobiTheta1, jacobiTheta1Prime,
    jacobiTheta2_eq_tsum_half,
    jacobiTheta2Prime_eq_tsum_half
      (z + 1 / 2) hτ]
  simpa only [jacobiThetaWronskian2Term] using
    tsum_skew_product
      hHalfZ hHalfShift hPrimeZ hPrimeShift

/-- The parity reindexing evaluates the double series in the first
Wronskian at doubled modulus. -/
theorem tsum_jacobiThetaWronskian2Term
    (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    (∑' x : ℤ × ℤ,
        jacobiThetaWronskian2Term x z τ) =
      -2 * jacobiTheta1Prime 0 (2 * τ) *
        jacobiTheta4 (2 * z) (2 * τ) := by
  have hτ2 : 0 < (2 * τ).im := by
    simpa [mul_im] using
      mul_pos (by norm_num : (0 : ℝ) < 2) hτ
  have hHalf2 :=
    summable_jacobiThetaHalfTerm
      (2 * z + 1 / 2) hτ2
  have hIntPrime20 :
      Summable
        (fun n : ℤ ↦
          jacobiTheta₂'_term n (1 / 2) (2 * τ)) :=
    (summable_jacobiTheta₂'_term_iff
      (1 / 2) (2 * τ)).2 hτ2
  have hInt2 :
      Summable
        (fun n : ℤ ↦
          jacobiTheta₂_term n
            (2 * z + 1 / 2) (2 * τ)) :=
    (summable_jacobiTheta₂_term_iff
      (2 * z + 1 / 2) (2 * τ)).2 hτ2
  have hHalfPrime20 :=
    summable_jacobiThetaHalfPrimeTerm
      (1 / 2) hτ2
  have hIntShift :
      Summable
        (fun a : ℤ ↦
          jacobiTheta₂_term (a + 1)
            (2 * z + 1 / 2) (2 * τ)) :=
    hInt2.comp_injective (fun _ _ h ↦ by omega)
  have hEven :
      Summable
        (fun x : ℤ × ℤ ↦
          jacobiThetaWronskian2Term
            (thetaParityReindex (Sum.inl x)) z τ) := by
    apply
      ((summable_mul_of_summable_norm
        hHalf2.norm hIntPrime20.norm).mul_left (-2)).congr
    rintro ⟨a, b⟩
    simpa only [thetaParityReindex_inl, mul_assoc] using
      (jacobiThetaWronskian2Term_even
        a b z τ).symm
  have hOdd :
      Summable
        (fun x : ℤ × ℤ ↦
          jacobiThetaWronskian2Term
            (thetaParityReindex (Sum.inr x)) z τ) := by
    apply
      ((summable_mul_of_summable_norm
        hIntShift.norm hHalfPrime20.norm).mul_left 2).congr
    rintro ⟨a, b⟩
    simpa only [thetaParityReindex_inr, mul_assoc] using
      (jacobiThetaWronskian2Term_odd
        a b z τ).symm
  calc
    (∑' x : ℤ × ℤ,
          jacobiThetaWronskian2Term x z τ) =
        ∑' x : (ℤ × ℤ) ⊕ (ℤ × ℤ),
          jacobiThetaWronskian2Term
            (thetaParityReindex x) z τ :=
      (thetaParityReindex.tsum_eq
        (fun x ↦
          jacobiThetaWronskian2Term x z τ)).symm
    _ =
        (∑' x : ℤ × ℤ,
          jacobiThetaWronskian2Term
            (thetaParityReindex (Sum.inl x)) z τ) +
        ∑' x : ℤ × ℤ,
          jacobiThetaWronskian2Term
            (thetaParityReindex (Sum.inr x)) z τ :=
      Summable.tsum_sum hEven hOdd
    _ =
        -2 *
            ((∑' a : ℤ,
                jacobiThetaHalfTerm a
                  (2 * z + 1 / 2) (2 * τ)) *
              ∑' b : ℤ,
                jacobiTheta₂'_term b
                  (1 / 2) (2 * τ)) +
          2 *
            ((∑' a : ℤ,
                jacobiTheta₂_term (a + 1)
                  (2 * z + 1 / 2) (2 * τ)) *
              ∑' b : ℤ,
                jacobiThetaHalfPrimeTerm b
                  (1 / 2) (2 * τ)) := by
      congr 1
      · rw [tsum_mul_tsum_of_summable_norm
          hHalf2.norm hIntPrime20.norm,
          ← tsum_mul_left]
        apply tsum_congr
        rintro ⟨a, b⟩
        simpa only [thetaParityReindex_inl,
          mul_assoc] using
          jacobiThetaWronskian2Term_even a b z τ
      · rw [tsum_mul_tsum_of_summable_norm
          hIntShift.norm hHalfPrime20.norm,
          ← tsum_mul_left]
        apply tsum_congr
        rintro ⟨a, b⟩
        simpa only [thetaParityReindex_inr,
          mul_assoc] using
          jacobiThetaWronskian2Term_odd a b z τ
    _ =
      -2 * jacobiTheta1Prime 0 (2 * τ) *
        jacobiTheta4 (2 * z) (2 * τ) := by
      have hIntShiftSum :
          (∑' a : ℤ,
              jacobiTheta₂_term (a + 1)
                (2 * z + 1 / 2) (2 * τ)) =
            ∑' a : ℤ,
              jacobiTheta₂_term a
                (2 * z + 1 / 2) (2 * τ) :=
        (Equiv.addRight (1 : ℤ)).tsum_eq
          (fun a : ℤ ↦
            jacobiTheta₂_term a
              (2 * z + 1 / 2) (2 * τ))
      rw [show
          (∑' b : ℤ,
              jacobiTheta₂'_term b
                (1 / 2) (2 * τ)) =
            jacobiTheta₂' (1 / 2) (2 * τ) by
          rfl,
        jacobiTheta₂'_half_eq_zero,
        mul_zero, mul_zero, zero_add,
        hIntShiftSum,
        ← jacobiTheta2Prime_eq_tsum_half
          (1 / 2) hτ2]
      simp only [jacobiTheta1Prime, zero_add,
        jacobiTheta4, jacobiTheta₂]
      ring

/-- Direct double-series factorization of the first Wronskian.  The
even parity branch vanishes; the odd branch is the product of
`θ₄(2z|2τ)` and `θ₁'(0|2τ)`. -/
theorem jacobiTheta_wronskian2_doubling
    (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta2Prime z τ * jacobiTheta1 z τ -
        jacobiTheta2 z τ * jacobiTheta1Prime z τ =
      -2 * jacobiTheta1Prime 0 (2 * τ) *
        jacobiTheta4 (2 * z) (2 * τ) :=
  (jacobiTheta_wronskian2_eq_tsum z hτ).trans
    (tsum_jacobiThetaWronskian2Term z hτ)

/-! ## A bilinear duplication identity -/

/-- A shifted half-characteristic summand is paired with its negative
under `n ↦ -n-1`. -/
theorem jacobiThetaHalfTerm_neg_sub_one_half
    (n : ℤ) (τ : ℂ) :
    jacobiThetaHalfTerm (-n - 1) (1 / 2) τ =
      -jacobiThetaHalfTerm n (1 / 2) τ := by
  unfold jacobiThetaHalfTerm
  conv_rhs => rw [neg_eq_neg_one_mul]
  rw [← Complex.exp_pi_mul_I,
    ← Complex.exp_add]
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-(n + 1), ?_⟩
  push_cast
  ring

/-- The half-characteristic theta series vanishes at the real
half-period. -/
theorem tsum_jacobiThetaHalfTerm_half_eq_zero
    (τ : ℂ) :
    (∑' n : ℤ,
        jacobiThetaHalfTerm n (1 / 2) τ) = 0 := by
  let e : ℤ ≃ ℤ :=
    (Equiv.neg ℤ).trans
      (Equiv.addRight (-1 : ℤ))
  have he (n : ℤ) : e n = -n - 1 := by
    simp [e, sub_eq_add_neg]
  have hself :
      (∑' n : ℤ,
          jacobiThetaHalfTerm n (1 / 2) τ) =
        -(∑' n : ℤ,
          jacobiThetaHalfTerm n (1 / 2) τ) := by
    calc
      (∑' n : ℤ,
          jacobiThetaHalfTerm n (1 / 2) τ) =
          ∑' n : ℤ,
            jacobiThetaHalfTerm (e n) (1 / 2) τ :=
        (e.tsum_eq
          (fun n : ℤ ↦
            jacobiThetaHalfTerm n (1 / 2) τ)).symm
      _ =
          ∑' n : ℤ,
            -jacobiThetaHalfTerm n (1 / 2) τ := by
        apply tsum_congr
        intro n
        rw [he, jacobiThetaHalfTerm_neg_sub_one_half]
      _ = _ := tsum_neg
  linear_combination (1 / 2 : ℂ) * hself

/-- One summand in `θ₃(z|τ) θ₄(z|τ)`. -/
def jacobiTheta34ProductTerm
    (x : ℤ × ℤ) (z τ : ℂ) : ℂ :=
  jacobiTheta₂_term x.1 z τ *
    jacobiTheta₂_term x.2 (z + 1 / 2) τ

theorem jacobiTheta34ProductTerm_even
    (a b : ℤ) (z τ : ℂ) :
    jacobiTheta34ProductTerm
        (a + b, a - b) z τ =
      jacobiTheta₂_term a
          (2 * z + 1 / 2) (2 * τ) *
        jacobiTheta₂_term b
          (1 / 2) (2 * τ) := by
  unfold jacobiTheta34ProductTerm
    jacobiTheta₂_term
  rw [← Complex.exp_add, ← Complex.exp_add]
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-b, ?_⟩
  push_cast
  ring

theorem jacobiTheta34ProductTerm_odd
    (a b : ℤ) (z τ : ℂ) :
    jacobiTheta34ProductTerm
        (a + b + 1, a - b) z τ =
      -(jacobiThetaHalfTerm a
          (2 * z + 1 / 2) (2 * τ) *
        jacobiThetaHalfTerm b
          (1 / 2) (2 * τ)) := by
  unfold jacobiTheta34ProductTerm
    jacobiTheta₂_term jacobiThetaHalfTerm
  rw [← Complex.exp_add, ← Complex.exp_add]
  rw [neg_eq_neg_one_mul,
    ← Complex.exp_pi_mul_I,
    ← Complex.exp_add]
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-(b + 1), ?_⟩
  push_cast
  ring

theorem jacobiTheta34_product_eq_tsum
    (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta3 z τ * jacobiTheta4 z τ =
      ∑' x : ℤ × ℤ,
        jacobiTheta34ProductTerm x z τ := by
  have hIntZ :
      Summable
        (fun n : ℤ ↦
          jacobiTheta₂_term n z τ) :=
    (summable_jacobiTheta₂_term_iff z τ).2 hτ
  have hIntShift :
      Summable
        (fun n : ℤ ↦
          jacobiTheta₂_term n
            (z + 1 / 2) τ) :=
    (summable_jacobiTheta₂_term_iff
      (z + 1 / 2) τ).2 hτ
  rw [jacobiTheta3, jacobiTheta4,
    jacobiTheta₂, jacobiTheta₂,
    tsum_mul_tsum_of_summable_norm
      hIntZ.norm hIntShift.norm]
  rfl

/-- Bilinear duplication:
`θ₃(z|τ) θ₄(z|τ)=θ₄(0|2τ) θ₄(2z|2τ)`. -/
theorem jacobiTheta3_mul_jacobiTheta4_duplication
    (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta3 z τ * jacobiTheta4 z τ =
      jacobiTheta4 0 (2 * τ) *
        jacobiTheta4 (2 * z) (2 * τ) := by
  have hτ2 : 0 < (2 * τ).im := by
    simpa [mul_im] using
      mul_pos (by norm_num : (0 : ℝ) < 2) hτ
  have hInt2Z :
      Summable
        (fun n : ℤ ↦
          jacobiTheta₂_term n
            (2 * z + 1 / 2) (2 * τ)) :=
    (summable_jacobiTheta₂_term_iff
      (2 * z + 1 / 2) (2 * τ)).2 hτ2
  have hInt20 :
      Summable
        (fun n : ℤ ↦
          jacobiTheta₂_term n
            (1 / 2) (2 * τ)) :=
    (summable_jacobiTheta₂_term_iff
      (1 / 2) (2 * τ)).2 hτ2
  have hHalf2Z :=
    summable_jacobiThetaHalfTerm
      (2 * z + 1 / 2) hτ2
  have hHalf20 :=
    summable_jacobiThetaHalfTerm
      (1 / 2) hτ2
  have hEven :
      Summable
        (fun x : ℤ × ℤ ↦
          jacobiTheta34ProductTerm
            (thetaParityReindex
              (Sum.inl x)) z τ) := by
    apply
      (summable_mul_of_summable_norm
        hInt2Z.norm hInt20.norm).congr
    rintro ⟨a, b⟩
    simpa only [thetaParityReindex_inl] using
      (jacobiTheta34ProductTerm_even
        a b z τ).symm
  have hOdd :
      Summable
        (fun x : ℤ × ℤ ↦
          jacobiTheta34ProductTerm
            (thetaParityReindex
              (Sum.inr x)) z τ) := by
    apply
      (summable_mul_of_summable_norm
        hHalf2Z.norm hHalf20.norm).neg.congr
    rintro ⟨a, b⟩
    simpa only [thetaParityReindex_inr] using
      (jacobiTheta34ProductTerm_odd
        a b z τ).symm
  calc
    jacobiTheta3 z τ * jacobiTheta4 z τ =
        ∑' x : ℤ × ℤ,
          jacobiTheta34ProductTerm x z τ :=
      jacobiTheta34_product_eq_tsum z hτ
    _ =
        ∑' x : (ℤ × ℤ) ⊕ (ℤ × ℤ),
          jacobiTheta34ProductTerm
            (thetaParityReindex x) z τ :=
      (thetaParityReindex.tsum_eq
        (fun x ↦
          jacobiTheta34ProductTerm x z τ)).symm
    _ =
        (∑' x : ℤ × ℤ,
          jacobiTheta34ProductTerm
            (thetaParityReindex
              (Sum.inl x)) z τ) +
        ∑' x : ℤ × ℤ,
          jacobiTheta34ProductTerm
            (thetaParityReindex
              (Sum.inr x)) z τ :=
      Summable.tsum_sum hEven hOdd
    _ =
        ((∑' a : ℤ,
            jacobiTheta₂_term a
              (2 * z + 1 / 2) (2 * τ)) *
          ∑' b : ℤ,
            jacobiTheta₂_term b
              (1 / 2) (2 * τ)) -
        ((∑' a : ℤ,
            jacobiThetaHalfTerm a
              (2 * z + 1 / 2) (2 * τ)) *
          ∑' b : ℤ,
            jacobiThetaHalfTerm b
              (1 / 2) (2 * τ)) := by
      have heven :
          (∑' x : ℤ × ℤ,
              jacobiTheta34ProductTerm
                (thetaParityReindex
                  (Sum.inl x)) z τ) =
            (∑' a : ℤ,
                jacobiTheta₂_term a
                  (2 * z + 1 / 2) (2 * τ)) *
              ∑' b : ℤ,
                jacobiTheta₂_term b
                  (1 / 2) (2 * τ) := by
        rw [tsum_mul_tsum_of_summable_norm
          hInt2Z.norm hInt20.norm]
        apply tsum_congr
        rintro ⟨a, b⟩
        simpa only [thetaParityReindex_inl] using
          jacobiTheta34ProductTerm_even a b z τ
      have hodd :
          (∑' x : ℤ × ℤ,
              jacobiTheta34ProductTerm
                (thetaParityReindex
                  (Sum.inr x)) z τ) =
            -((∑' a : ℤ,
                jacobiThetaHalfTerm a
                  (2 * z + 1 / 2) (2 * τ)) *
              ∑' b : ℤ,
                jacobiThetaHalfTerm b
                  (1 / 2) (2 * τ)) := by
        rw [tsum_mul_tsum_of_summable_norm
          hHalf2Z.norm hHalf20.norm,
          ← tsum_neg]
        apply tsum_congr
        rintro ⟨a, b⟩
        simpa only [thetaParityReindex_inr] using
          jacobiTheta34ProductTerm_odd a b z τ
      rw [heven, hodd]
      ring
    _ =
      jacobiTheta4 0 (2 * τ) *
        jacobiTheta4 (2 * z) (2 * τ) := by
      rw [tsum_jacobiThetaHalfTerm_half_eq_zero,
        mul_zero, sub_zero]
      simp only [jacobiTheta4, zero_add,
        jacobiTheta₂]
      ring

/-! ## The derivative formula: doubling recurrences -/

theorem jacobiTheta1_zero
    (τ : ℂ) :
    jacobiTheta1 0 τ = 0 := by
  rw [jacobiTheta1, zero_add,
    jacobiTheta2_eq_tsum_half,
    tsum_jacobiThetaHalfTerm_half_eq_zero,
    neg_zero]

/-- The doubled-Wronskian identity at `z=0`. -/
theorem jacobiTheta1Prime_doubling_recurrence
    {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta2 0 τ * jacobiTheta1Prime 0 τ =
      2 * jacobiTheta1Prime 0 (2 * τ) *
        jacobiTheta4 0 (2 * τ) := by
  have h :=
    jacobiTheta_wronskian2_doubling
      (0 : ℂ) hτ
  rw [jacobiTheta1_zero] at h
  simp only [mul_zero, zero_sub] at h
  linear_combination -h

/-- The even-theta product occurring in Jacobi's derivative formula. -/
def jacobiThetaDerivativeProduct
    (τ : ℂ) : ℂ :=
  π * jacobiTheta2 0 τ *
    jacobiTheta3 0 τ *
      jacobiTheta4 0 τ

/-- The candidate right-hand side of Jacobi's derivative formula obeys
the same doubling recurrence as `θ₁'(0|τ)`. -/
theorem jacobiThetaDerivativeProduct_doubling_recurrence
    {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta2 0 τ *
        jacobiThetaDerivativeProduct τ =
      2 * jacobiThetaDerivativeProduct (2 * τ) *
        jacobiTheta4 0 (2 * τ) := by
  have h2 :=
    jacobiTheta2_sq_duplication
      (0 : ℂ) hτ
  have h34 :=
    jacobiTheta3_mul_jacobiTheta4_duplication
      (0 : ℂ) hτ
  simp only [mul_zero] at h2 h34
  unfold jacobiThetaDerivativeProduct
  linear_combination
    π * jacobiTheta3 0 τ *
      jacobiTheta4 0 τ * h2 +
    (2 * π * jacobiTheta2 0 (2 * τ) *
      jacobiTheta3 0 (2 * τ)) * h34

/-! ## The derivative formula: cusp normalization -/

/-- The coefficient remaining after the leading
`π exp(π i τ/4)` is removed from the differentiated odd theta series. -/
def jacobiTheta1PrimeCuspCoeff
    (n : ℤ) : ℂ :=
  -2 * I * ((n : ℂ) + 1 / 2) *
    cexp (π * I * ((n : ℂ) + 1 / 2))

/-- The normalized summand in the cusp expansion of `θ₁'(0|τ)`. -/
def jacobiTheta1PrimeCuspTerm
    (n : ℤ) (τ : ℂ) : ℂ :=
  jacobiTheta1PrimeCuspCoeff n *
    cexp
      (π * I * ((n : ℂ) ^ 2 + n) * τ)

theorem neg_halfPrimeTerm_eq_cuspTerm
    (n : ℤ) (τ : ℂ) :
    -jacobiThetaHalfPrimeTerm n (1 / 2) τ =
      (π * cexp (π * I * τ / 4)) *
        jacobiTheta1PrimeCuspTerm n τ := by
  have hexp :
      cexp (π * I * τ / 4) *
          cexp (π * I * ((n : ℂ) + 1 / 2)) *
          cexp
            (π * I * ((n : ℂ) ^ 2 + n) * τ) =
        cexp
          (2 * π * I * ((n : ℂ) + 1 / 2) *
              (1 / 2) +
            π * I * ((n : ℂ) + 1 / 2) ^ 2 * τ) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  unfold jacobiThetaHalfPrimeTerm
    jacobiThetaHalfTerm
    jacobiTheta1PrimeCuspTerm
    jacobiTheta1PrimeCuspCoeff
  rw [← hexp]
  ring

theorem summable_jacobiTheta1PrimeCuspTerm
    {τ : ℂ} (hτ : 0 < τ.im) :
    Summable
      (fun n : ℤ ↦
        jacobiTheta1PrimeCuspTerm n τ) := by
  have hc :
      π * cexp (π * I * τ / 4) ≠ 0 :=
    mul_ne_zero (ofReal_ne_zero.mpr
      (ne_of_gt Real.pi_pos))
      (Complex.exp_ne_zero _)
  have hprime :=
    summable_jacobiThetaHalfPrimeTerm
      (1 / 2) hτ
  apply
    (hprime.neg.mul_left
      (π * cexp (π * I * τ / 4))⁻¹).congr
  intro n
  rw [neg_halfPrimeTerm_eq_cuspTerm]
  field_simp

theorem jacobiTheta1Prime_eq_cuspSeries
    {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta1Prime 0 τ =
      (π * cexp (π * I * τ / 4)) *
        ∑' n : ℤ,
          jacobiTheta1PrimeCuspTerm n τ := by
  rw [jacobiTheta1Prime_eq_tsum_half
      (0 : ℂ) hτ,
    zero_add, ← tsum_mul_left]
  apply tsum_congr
  intro n
  exact neg_halfPrimeTerm_eq_cuspTerm n τ

theorem norm_jacobiTheta1PrimeCuspTerm
    (n : ℤ) (τ : ℂ) :
    ‖jacobiTheta1PrimeCuspTerm n τ‖ =
      ‖jacobiTheta1PrimeCuspCoeff n‖ *
        rexp
          (-π * ((n : ℝ) ^ 2 + n) * τ.im) := by
  have hexp :
      π * I * ((n : ℂ) ^ 2 + n) * τ =
        ((π * ((n : ℝ) ^ 2 + n) : ℝ) * τ) * I := by
    push_cast
    ring
  rw [jacobiTheta1PrimeCuspTerm,
    norm_mul, hexp, norm_cexp_mul_I,
    im_ofReal_mul]
  congr 2
  ring

@[simp] theorem jacobiTheta1PrimeCuspTerm_zero
    (τ : ℂ) :
    jacobiTheta1PrimeCuspTerm 0 τ = 1 := by
  have hexp :
      cexp (π * I * (1 / 2)) = I := by
    rw [show
      (π : ℂ) * I * (1 / 2) =
        ((π / 2 : ℝ) : ℂ) * I by
          push_cast
          ring,
      Complex.exp_mul_I]
    simp
  have hcoeff :
      jacobiTheta1PrimeCuspCoeff 0 = 1 := by
    unfold jacobiTheta1PrimeCuspCoeff
    simp only [Int.cast_zero, zero_add]
    rw [hexp]
    calc
      -2 * I * (1 / 2) * I =
          -(I * I) := by ring
      _ = 1 := by rw [I_mul_I]; ring
  simp [jacobiTheta1PrimeCuspTerm, hcoeff]

@[simp] theorem jacobiTheta1PrimeCuspTerm_neg_one
    (τ : ℂ) :
    jacobiTheta1PrimeCuspTerm (-1) τ = 1 := by
  have hexp :
      cexp (π * I * (-1 + 1 / 2)) = -I := by
    rw [show
      (π : ℂ) * I * (-1 + 1 / 2) =
        ((-(π / 2) : ℝ) : ℂ) * I by
          push_cast
          ring,
      Complex.exp_mul_I]
    simp
  have hcoeff :
      jacobiTheta1PrimeCuspCoeff (-1) = 1 := by
    unfold jacobiTheta1PrimeCuspCoeff
    simp only [Int.cast_neg, Int.cast_one]
    rw [hexp]
    calc
      -2 * I * (-1 + 1 / 2) * -I =
          -(I * I) := by ring
      _ = 1 := by rw [I_mul_I]; ring
  simp [jacobiTheta1PrimeCuspTerm, hcoeff]

theorem jacobiTheta1PrimeCuspTerm_tendsto
    (n : ℤ) :
    Tendsto
      (fun τ : ℍ ↦
        jacobiTheta1PrimeCuspTerm n (τ : ℂ))
      atImInfty
      (𝓝 (Set.indicator ({-1, 0} : Set ℤ) 1 n)) := by
  by_cases hn1 : n = -1
  · subst n
    simp
  by_cases hn0 : n = 0
  · subst n
    simp
  have hnmem :
      n ∉ ({-1, 0} : Set ℤ) := by
    simp [hn1, hn0]
  rw [Set.indicator_of_notMem hnmem]
  have hkpos :
      0 < (n : ℝ) ^ 2 + n := by
    convert_to
      0 < ((n * (n + 1) : ℤ) : ℝ)
    · push_cast
      ring
    · apply Int.cast_pos.mpr
      by_cases hpos : 0 < n
      · exact mul_pos hpos (by omega)
      · exact mul_pos_of_neg_of_neg
          (by omega) (by omega)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [norm_jacobiTheta1PrimeCuspTerm]
  have hexp :
      Tendsto
        (fun τ : ℍ ↦
          rexp
            ((-π * ((n : ℝ) ^ 2 + n)) * τ.im))
        atImInfty (𝓝 0) := by
    exact
      Real.tendsto_exp_atBot.comp
        (tendsto_im_atImInfty
          |>.const_mul_atTop_of_neg
            (by nlinarith [Real.pi_pos]))
  have hconst :
      Tendsto
        (fun _ : ℍ ↦
          ‖jacobiTheta1PrimeCuspCoeff n‖)
        atImInfty
        (𝓝 ‖jacobiTheta1PrimeCuspCoeff n‖) :=
    tendsto_const_nhds
  simpa only [neg_mul, mul_assoc, mul_zero] using
    hconst.mul hexp

theorem norm_jacobiTheta1PrimeCuspTerm_le_I
    (n : ℤ) (τ : ℍ) (hτ : 1 ≤ τ.im) :
    ‖jacobiTheta1PrimeCuspTerm n (τ : ℂ)‖ ≤
      ‖jacobiTheta1PrimeCuspTerm n
        UpperHalfPlane.I‖ := by
  have hk :
      0 ≤ (n : ℝ) ^ 2 + n := by
    convert_to
      0 ≤ ((n * (n + 1) : ℤ) : ℝ)
    · push_cast
      ring
    · norm_cast
      by_cases hpos : 0 ≤ n
      · exact mul_nonneg hpos (by omega)
      · exact mul_nonneg_of_nonpos_of_nonpos
          (by omega) (by omega)
  rw [norm_jacobiTheta1PrimeCuspTerm,
    norm_jacobiTheta1PrimeCuspTerm]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  have hcoeff :
      -π * ((n : ℝ) ^ 2 + n) ≤ 0 := by
    nlinarith [Real.pi_pos]
  simpa using
    mul_le_mul_of_nonpos_left hτ hcoeff

/-- After removal of its leading exponential,
`θ₁'(0|τ)` has cusp limit `2π`.  At the series level the two surviving
summands are exactly `n=-1` and `n=0`. -/
theorem jacobiTheta1PrimeCuspSeries_tendsto_atImInfty :
    Tendsto
      (fun τ : ℍ ↦
        ∑' n : ℤ,
          jacobiTheta1PrimeCuspTerm n (τ : ℂ))
      atImInfty (𝓝 2) := by
  convert tendsto_tsum_of_dominated_convergence
    (f := fun (τ : ℍ) (n : ℤ) ↦
      jacobiTheta1PrimeCuspTerm n (τ : ℂ))
    (𝓕 := atImInfty)
    (g := Set.indicator ({-1, 0} : Set ℤ) 1)
    (bound := fun n : ℤ ↦
      ‖jacobiTheta1PrimeCuspTerm n
        UpperHalfPlane.I‖)
      ?_ ?_ ?_
  · simp [← tsum_subtype]
  · exact
      (summable_jacobiTheta1PrimeCuspTerm
        (τ := (UpperHalfPlane.I : ℂ))
        (by simp)).norm
  · exact jacobiTheta1PrimeCuspTerm_tendsto
  · rw [eventually_atImInfty]
    exact ⟨1, fun τ hτ n ↦
      norm_jacobiTheta1PrimeCuspTerm_le_I
        n τ hτ⟩

/-! ## The derivative formula: constancy of the doubled ratio -/

theorem jacobiTheta2_zero_ne_zero_for_wronskians
    (τ : ℍ) :
    jacobiTheta2 0 (τ : ℂ) ≠ 0 := by
  rw [jacobiTheta2_zero_eq_theta₂]
  intro h
  apply H₂_ne_zero τ
  simp [H₂, h]

theorem jacobiTheta3_zero_ne_zero
    (τ : ℍ) :
    jacobiTheta3 0 (τ : ℂ) ≠ 0 := by
  rw [jacobiTheta3_zero_eq_theta₃]
  intro h
  apply H₃_ne_zero τ
  simp [H₃, h]

theorem jacobiTheta4_zero_ne_zero
    (τ : ℍ) :
    jacobiTheta4 0 (τ : ℂ) ≠ 0 := by
  rw [jacobiTheta4_zero_eq_theta₄]
  intro h
  apply H₄_ne_zero τ
  simp [H₄, h]

theorem jacobiThetaDerivativeProduct_ne_zero
    (τ : ℍ) :
    jacobiThetaDerivativeProduct (τ : ℂ) ≠ 0 := by
  unfold jacobiThetaDerivativeProduct
  exact
    mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (ofReal_ne_zero.mpr
            (ne_of_gt Real.pi_pos))
          (jacobiTheta2_zero_ne_zero_for_wronskians τ))
        (jacobiTheta3_zero_ne_zero τ))
      (jacobiTheta4_zero_ne_zero τ)

/-- Ratio of the two sides of Jacobi's derivative formula. -/
def jacobiThetaDerivativeRatio
    (τ : ℍ) : ℂ :=
  jacobiTheta1Prime 0 (τ : ℂ) /
    jacobiThetaDerivativeProduct (τ : ℂ)

/-- Cusp-friendly form of the derivative ratio: the vanishing leading
exponential has cancelled before taking the limit. -/
theorem jacobiThetaDerivativeRatio_eq_cuspSeries
    (τ : ℍ) :
    jacobiThetaDerivativeRatio τ =
      (∑' n : ℤ,
          jacobiTheta1PrimeCuspTerm n (τ : ℂ)) /
        (jacobiTheta₂ ((τ : ℂ) / 2) (τ : ℂ) *
          theta₃ τ * theta₄ τ) := by
  have hD :=
    jacobiTheta1Prime_eq_cuspSeries
      (τ := (τ : ℂ)) τ.im_pos
  have hA :
      jacobiTheta₂ ((τ : ℂ) / 2) (τ : ℂ) ≠ 0 := by
    intro h
    apply jacobiTheta2_zero_ne_zero_for_wronskians τ
    rw [jacobiTheta2]
    simp only [zero_add]
    rw [h, mul_zero]
  have hden :
      jacobiTheta₂ ((τ : ℂ) / 2) (τ : ℂ) *
          theta₃ τ * theta₄ τ ≠ 0 := by
    have h3 : theta₃ τ ≠ 0 := by
      intro h
      apply jacobiTheta3_zero_ne_zero τ
      simpa [jacobiTheta3_zero_eq_theta₃]
    have h4 : theta₄ τ ≠ 0 := by
      intro h
      apply jacobiTheta4_zero_ne_zero τ
      simpa [jacobiTheta4_zero_eq_theta₄]
    exact mul_ne_zero (mul_ne_zero hA h3) h4
  rw [jacobiThetaDerivativeRatio]
  apply
    (div_eq_div_iff
      (jacobiThetaDerivativeProduct_ne_zero τ)
      hden).2
  rw [hD]
  unfold jacobiThetaDerivativeProduct
  rw [jacobiTheta2, jacobiTheta3_zero_eq_theta₃,
    jacobiTheta4_zero_eq_theta₄]
  simp only [zero_add]
  ring

/-- The derivative ratio tends to one at the top cusp. -/
theorem jacobiThetaDerivativeRatio_tendsto_atImInfty :
    Tendsto jacobiThetaDerivativeRatio
      atImInfty (𝓝 1) := by
  have hden :
      Tendsto
        (fun τ : ℍ ↦
          jacobiTheta₂ ((τ : ℂ) / 2) (τ : ℂ) *
            theta₃ τ * theta₄ τ)
        atImInfty (𝓝 2) := by
    simpa only [mul_one] using
      (jacobiTheta₂_half_mul_tendsto_atImInfty.mul
        theta₃_tendsto_atImInfty).mul
          theta₄_tendsto_atImInfty
  have hquot :=
    jacobiTheta1PrimeCuspSeries_tendsto_atImInfty.div
      hden (by norm_num : (2 : ℂ) ≠ 0)
  convert hquot using 1
  · funext τ
    exact
      (jacobiThetaDerivativeRatio_eq_cuspSeries
        τ)
  · norm_num

/-- Doubling the modular parameter inside the upper half-plane. -/
def upperHalfPlaneDouble
    (τ : ℍ) : ℍ :=
  ⟨2 * (τ : ℂ), by
    simpa [mul_im] using
      mul_pos (by norm_num : (0 : ℝ) < 2)
        τ.im_pos⟩

@[simp] theorem upperHalfPlaneDouble_coe
    (τ : ℍ) :
    (upperHalfPlaneDouble τ : ℂ) =
      2 * (τ : ℂ) :=
  rfl

@[simp] theorem upperHalfPlaneDouble_im
    (τ : ℍ) :
    (upperHalfPlaneDouble τ).im =
      2 * τ.im := by
  simp [upperHalfPlaneDouble, mul_im]

/-- The derivative ratio is invariant under doubling. -/
theorem jacobiThetaDerivativeRatio_double
    (τ : ℍ) :
    jacobiThetaDerivativeRatio τ =
      jacobiThetaDerivativeRatio
        (upperHalfPlaneDouble τ) := by
  have hD :=
    jacobiTheta1Prime_doubling_recurrence
      (τ := (τ : ℂ)) τ.im_pos
  have hP :=
    jacobiThetaDerivativeProduct_doubling_recurrence
      (τ := (τ : ℂ)) τ.im_pos
  have ha :=
    jacobiTheta2_zero_ne_zero_for_wronskians τ
  have hcross :
      jacobiTheta2 0 (τ : ℂ) *
          (jacobiTheta1Prime 0 (τ : ℂ) *
              jacobiThetaDerivativeProduct
                (2 * (τ : ℂ)) -
            jacobiTheta1Prime
                0 (2 * (τ : ℂ)) *
              jacobiThetaDerivativeProduct
                (τ : ℂ)) = 0 := by
    linear_combination
      jacobiThetaDerivativeProduct
          (2 * (τ : ℂ)) * hD -
        jacobiTheta1Prime
          0 (2 * (τ : ℂ)) * hP
  have hnum :
      jacobiTheta1Prime 0 (τ : ℂ) *
            jacobiThetaDerivativeProduct
              (2 * (τ : ℂ)) =
        jacobiTheta1Prime 0 (2 * (τ : ℂ)) *
          jacobiThetaDerivativeProduct
            (τ : ℂ) := by
    exact
      sub_eq_zero.mp
        ((mul_eq_zero.mp hcross).resolve_left ha)
  unfold jacobiThetaDerivativeRatio
  apply
    (div_eq_div_iff
      (jacobiThetaDerivativeProduct_ne_zero τ)
      (jacobiThetaDerivativeProduct_ne_zero
        (upperHalfPlaneDouble τ))).2
  simpa using hnum

/-- Iterated doubling. -/
def upperHalfPlaneDoubleIter
    (τ : ℍ) : ℕ → ℍ
  | 0 => τ
  | n + 1 =>
      upperHalfPlaneDouble
        (upperHalfPlaneDoubleIter τ n)

@[simp] theorem upperHalfPlaneDoubleIter_zero
    (τ : ℍ) :
    upperHalfPlaneDoubleIter τ 0 = τ :=
  rfl

@[simp] theorem upperHalfPlaneDoubleIter_succ
    (τ : ℍ) (n : ℕ) :
    upperHalfPlaneDoubleIter τ (n + 1) =
      upperHalfPlaneDouble
        (upperHalfPlaneDoubleIter τ n) :=
  rfl

theorem upperHalfPlaneDoubleIter_im
    (τ : ℍ) (n : ℕ) :
    (upperHalfPlaneDoubleIter τ n).im =
      (2 : ℝ) ^ n * τ.im := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [upperHalfPlaneDoubleIter_succ,
        upperHalfPlaneDouble_im, ih, pow_succ]
      ring

theorem upperHalfPlaneDoubleIter_tendsto
    (τ : ℍ) :
    Tendsto (upperHalfPlaneDoubleIter τ)
      atTop atImInfty := by
  rw [UpperHalfPlane.atImInfty,
    tendsto_comap_iff]
  change
    Tendsto
      (fun n : ℕ ↦
        (upperHalfPlaneDoubleIter τ n).im)
      atTop atTop
  simp_rw [upperHalfPlaneDoubleIter_im]
  exact
    (tendsto_pow_atTop_atTop_of_one_lt
      (by norm_num : (1 : ℝ) < 2)).atTop_mul_const
        τ.im_pos

theorem jacobiThetaDerivativeRatio_doubleIter
    (τ : ℍ) (n : ℕ) :
    jacobiThetaDerivativeRatio
        (upperHalfPlaneDoubleIter τ n) =
      jacobiThetaDerivativeRatio τ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [upperHalfPlaneDoubleIter_succ]
      exact
        (jacobiThetaDerivativeRatio_double
          (upperHalfPlaneDoubleIter τ n)).symm.trans ih

/-- The doubling invariance and cusp normalization force the ratio to
be identically one. -/
theorem jacobiThetaDerivativeRatio_eq_one
    (τ : ℍ) :
    jacobiThetaDerivativeRatio τ = 1 := by
  have hlim :
      Tendsto
        (fun n : ℕ ↦
          jacobiThetaDerivativeRatio
            (upperHalfPlaneDoubleIter τ n))
        atTop (𝓝 1) :=
    jacobiThetaDerivativeRatio_tendsto_atImInfty.comp
      (upperHalfPlaneDoubleIter_tendsto τ)
  have hconst :
      Tendsto
        (fun _ : ℕ ↦
          jacobiThetaDerivativeRatio τ)
        atTop (𝓝 1) := by
    convert hlim using 1
    funext n
    exact
      (jacobiThetaDerivativeRatio_doubleIter
        τ n).symm
  exact
    (tendsto_nhds_unique
      hconst tendsto_const_nhds).symm

/-- Jacobi's derivative formula in the present theta conventions. -/
theorem jacobiTheta1Prime_zero_eq_product
    (τ : ℍ) :
    jacobiTheta1Prime 0 (τ : ℂ) =
      π * jacobiTheta2 0 (τ : ℂ) *
        jacobiTheta3 0 (τ : ℂ) *
          jacobiTheta4 0 (τ : ℂ) := by
  have hratio :=
    jacobiThetaDerivativeRatio_eq_one τ
  rw [jacobiThetaDerivativeRatio,
    div_eq_one_iff_eq
      (jacobiThetaDerivativeProduct_ne_zero τ)] at hratio
  exact hratio

theorem jacobiTheta1Prime_zero_eq_product_of_im_pos
    {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta1Prime 0 τ =
      π * jacobiTheta2 0 τ *
        jacobiTheta3 0 τ *
          jacobiTheta4 0 τ := by
  simpa using
    jacobiTheta1Prime_zero_eq_product
      (⟨τ, hτ⟩ : ℍ)

/-! ## The first canonical Wronskian -/

theorem jacobiTheta_wronskian2
    (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta2Prime z τ * jacobiTheta1 z τ -
        jacobiTheta2 z τ * jacobiTheta1Prime z τ =
      -π * jacobiTheta2 0 τ ^ 2 *
        jacobiTheta3 z τ * jacobiTheta4 z τ := by
  have hτ2 : 0 < (2 * τ).im := by
    simpa [mul_im] using
      mul_pos (by norm_num : (0 : ℝ) < 2) hτ
  have hW :=
    jacobiTheta_wronskian2_doubling z hτ
  have hD :=
    jacobiTheta1Prime_zero_eq_product_of_im_pos hτ2
  have h2 :=
    jacobiTheta2_sq_duplication
      (0 : ℂ) hτ
  have h34 :=
    jacobiTheta3_mul_jacobiTheta4_duplication
      z hτ
  simp only [mul_zero] at h2
  calc
    jacobiTheta2Prime z τ * jacobiTheta1 z τ -
          jacobiTheta2 z τ * jacobiTheta1Prime z τ =
        -2 * jacobiTheta1Prime 0 (2 * τ) *
          jacobiTheta4 (2 * z) (2 * τ) :=
      hW
    _ =
        -2 *
          (π * jacobiTheta2 0 (2 * τ) *
            jacobiTheta3 0 (2 * τ) *
              jacobiTheta4 0 (2 * τ)) *
          jacobiTheta4 (2 * z) (2 * τ) := by
      rw [hD]
    _ =
      -π * jacobiTheta2 0 τ ^ 2 *
        jacobiTheta3 z τ * jacobiTheta4 z τ := by
      calc
        -2 *
              (π * jacobiTheta2 0 (2 * τ) *
                jacobiTheta3 0 (2 * τ) *
                  jacobiTheta4 0 (2 * τ)) *
              jacobiTheta4 (2 * z) (2 * τ) =
            -π * jacobiTheta2 0 τ ^ 2 *
              (jacobiTheta3 z τ *
                jacobiTheta4 z τ) := by
          rw [h2, h34]
          ring
        _ = _ := by ring

/-! ## The other two Wronskians -/

theorem analyticOnNhd_jacobiTheta1_fixed_for_wronskians
    (τ : ℍ) :
    AnalyticOnNhd ℂ
      (fun z ↦ jacobiTheta1 z (τ : ℂ))
      Set.univ := by
  rw [analyticOnNhd_univ_iff_differentiable]
  intro z
  exact
    (hasDerivAt_jacobiTheta1 z (τ : ℂ)
      τ.im_pos).differentiableAt

theorem analyticOnNhd_jacobiTheta2_fixed_for_wronskians
    (τ : ℍ) :
    AnalyticOnNhd ℂ
      (fun z ↦ jacobiTheta2 z (τ : ℂ))
      Set.univ := by
  rw [analyticOnNhd_univ_iff_differentiable]
  intro z
  exact
    (hasDerivAt_jacobiTheta2 z (τ : ℂ)
      τ.im_pos).differentiableAt

theorem analyticOnNhd_jacobiTheta3_fixed_for_wronskians
    (τ : ℍ) :
    AnalyticOnNhd ℂ
      (fun z ↦ jacobiTheta3 z (τ : ℂ))
      Set.univ := by
  rw [analyticOnNhd_univ_iff_differentiable]
  intro z
  exact
    (hasDerivAt_jacobiTheta3 z (τ : ℂ)
      τ.im_pos).differentiableAt

theorem analyticOnNhd_jacobiTheta4_fixed_for_wronskians
    (τ : ℍ) :
    AnalyticOnNhd ℂ
      (fun z ↦ jacobiTheta4 z (τ : ℂ))
      Set.univ := by
  rw [analyticOnNhd_univ_iff_differentiable]
  intro z
  exact
    (hasDerivAt_jacobiTheta4 z (τ : ℂ)
      τ.im_pos).differentiableAt

theorem analyticOnNhd_jacobiTheta1Prime_fixed
    (τ : ℍ) :
    AnalyticOnNhd ℂ
      (fun z ↦ jacobiTheta1Prime z (τ : ℂ))
      Set.univ := by
  have h :=
    (analyticOnNhd_jacobiTheta1_fixed_for_wronskians
      τ).deriv
  convert h using 1
  funext z
  exact
    (hasDerivAt_jacobiTheta1 z (τ : ℂ)
      τ.im_pos).deriv.symm

theorem analyticOnNhd_jacobiTheta2Prime_fixed
    (τ : ℍ) :
    AnalyticOnNhd ℂ
      (fun z ↦ jacobiTheta2Prime z (τ : ℂ))
      Set.univ := by
  have h :=
    (analyticOnNhd_jacobiTheta2_fixed_for_wronskians
      τ).deriv
  convert h using 1
  funext z
  exact
    (hasDerivAt_jacobiTheta2 z (τ : ℂ)
      τ.im_pos).deriv.symm

theorem analyticOnNhd_jacobiTheta3Prime_fixed
    (τ : ℍ) :
    AnalyticOnNhd ℂ
      (fun z ↦ jacobiTheta3Prime z (τ : ℂ))
      Set.univ := by
  have h :=
    (analyticOnNhd_jacobiTheta3_fixed_for_wronskians
      τ).deriv
  convert h using 1
  funext z
  exact
    (hasDerivAt_jacobiTheta3 z (τ : ℂ)
      τ.im_pos).deriv.symm

theorem analyticOnNhd_jacobiTheta4Prime_fixed
    (τ : ℍ) :
    AnalyticOnNhd ℂ
      (fun z ↦ jacobiTheta4Prime z (τ : ℂ))
      Set.univ := by
  have h :=
    (analyticOnNhd_jacobiTheta4_fixed_for_wronskians
      τ).deriv
  convert h using 1
  funext z
  exact
    (hasDerivAt_jacobiTheta4 z (τ : ℂ)
      τ.im_pos).deriv.symm

/-- Derivative in `z` of the second residual quadric, with the common
factor `2` removed. -/
theorem jacobiTheta_residualQ2_derivative_identity
    (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta2 0 τ ^ 2 *
          jacobiTheta3 z τ *
            jacobiTheta3Prime z τ -
        jacobiTheta3 0 τ ^ 2 *
          jacobiTheta2 z τ *
            jacobiTheta2Prime z τ -
      jacobiTheta4 0 τ ^ 2 *
        jacobiTheta1 z τ *
          jacobiTheta1Prime z τ =
      0 := by
  let F : ℂ → ℂ := fun w ↦
    jacobiTheta2 0 τ ^ 2 *
          jacobiTheta3 w τ ^ 2 -
        jacobiTheta3 0 τ ^ 2 *
          jacobiTheta2 w τ ^ 2 -
      jacobiTheta4 0 τ ^ 2 *
        jacobiTheta1 w τ ^ 2
  have hraw :
      HasDerivAt F
        (2 *
          (jacobiTheta2 0 τ ^ 2 *
                jacobiTheta3 z τ *
                  jacobiTheta3Prime z τ -
            jacobiTheta3 0 τ ^ 2 *
                jacobiTheta2 z τ *
                  jacobiTheta2Prime z τ -
              jacobiTheta4 0 τ ^ 2 *
                jacobiTheta1 z τ *
                  jacobiTheta1Prime z τ)) z := by
    dsimp only [F]
    convert
      (((hasDerivAt_jacobiTheta3 z τ hτ).pow 2
          |>.const_mul
            (jacobiTheta2 0 τ ^ 2)).sub
        ((hasDerivAt_jacobiTheta2 z τ hτ).pow 2
          |>.const_mul
            (jacobiTheta3 0 τ ^ 2))).sub
        ((hasDerivAt_jacobiTheta1 z τ hτ).pow 2
          |>.const_mul
            (jacobiTheta4 0 τ ^ 2)) using 1
    simp only [Nat.reduceSub, pow_one]
    ring
  have hzero :
      HasDerivAt F 0 z := by
    apply
      (hasDerivAt_const z (0 : ℂ)).congr_of_eventuallyEq
    filter_upwards
    intro w
    exact
      jacobiTheta_residualQ2_identity
        w τ hτ
  have hu := hraw.unique hzero
  linear_combination (1 / 2 : ℂ) * hu

/-- Derivative in `z` of the first residual quadric. -/
theorem jacobiTheta_residualQ1_derivative_identity
    (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta2 0 τ ^ 2 *
          jacobiTheta4 z τ *
            jacobiTheta4Prime z τ -
        jacobiTheta4 0 τ ^ 2 *
          jacobiTheta2 z τ *
            jacobiTheta2Prime z τ -
      jacobiTheta3 0 τ ^ 2 *
        jacobiTheta1 z τ *
          jacobiTheta1Prime z τ =
      0 := by
  let F : ℂ → ℂ := fun w ↦
    jacobiTheta2 0 τ ^ 2 *
          jacobiTheta4 w τ ^ 2 -
        jacobiTheta4 0 τ ^ 2 *
          jacobiTheta2 w τ ^ 2 -
      jacobiTheta3 0 τ ^ 2 *
        jacobiTheta1 w τ ^ 2
  have hraw :
      HasDerivAt F
        (2 *
          (jacobiTheta2 0 τ ^ 2 *
                jacobiTheta4 z τ *
                  jacobiTheta4Prime z τ -
            jacobiTheta4 0 τ ^ 2 *
                jacobiTheta2 z τ *
                  jacobiTheta2Prime z τ -
              jacobiTheta3 0 τ ^ 2 *
                jacobiTheta1 z τ *
                  jacobiTheta1Prime z τ)) z := by
    dsimp only [F]
    convert
      (((hasDerivAt_jacobiTheta4 z τ hτ).pow 2
          |>.const_mul
            (jacobiTheta2 0 τ ^ 2)).sub
        ((hasDerivAt_jacobiTheta2 z τ hτ).pow 2
          |>.const_mul
            (jacobiTheta4 0 τ ^ 2))).sub
        ((hasDerivAt_jacobiTheta1 z τ hτ).pow 2
          |>.const_mul
            (jacobiTheta3 0 τ ^ 2)) using 1
    simp only [Nat.reduceSub, pow_one]
    ring
  have hzero :
      HasDerivAt F 0 z := by
    apply
      (hasDerivAt_const z (0 : ℂ)).congr_of_eventuallyEq
    filter_upwards
    intro w
    exact
      jacobiTheta_residualQ1_identity
        w τ hτ
  have hu := hraw.unique hzero
  linear_combination (1 / 2 : ℂ) * hu

/-- Error term in the third-coordinate Wronskian. -/
def jacobiThetaWronskian3Error
    (z τ : ℂ) : ℂ :=
  jacobiTheta3Prime z τ * jacobiTheta1 z τ -
      jacobiTheta3 z τ * jacobiTheta1Prime z τ +
    π * jacobiTheta3 0 τ ^ 2 *
      jacobiTheta4 z τ * jacobiTheta2 z τ

/-- Error term in the fourth-coordinate Wronskian. -/
def jacobiThetaWronskian4Error
    (z τ : ℂ) : ℂ :=
  jacobiTheta4Prime z τ * jacobiTheta1 z τ -
      jacobiTheta4 z τ * jacobiTheta1Prime z τ +
    π * jacobiTheta4 0 τ ^ 2 *
      jacobiTheta2 z τ * jacobiTheta3 z τ

theorem jacobiTheta3_mul_wronskian3Error_eq_zero
    (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta3 z τ *
      jacobiThetaWronskian3Error z τ = 0 := by
  have hq :=
    jacobiTheta_residualQ2_identity z τ hτ
  have hd :=
    jacobiTheta_residualQ2_derivative_identity
      z hτ
  have hw :=
    jacobiTheta_wronskian2 z hτ
  have hp2 :
      jacobiTheta2 0 τ ^ 2 ≠ 0 := by
    exact
      pow_ne_zero 2
        (jacobiTheta2_zero_ne_zero_for_wronskians
          (⟨τ, hτ⟩ : ℍ))
  have hbig :
      jacobiTheta2 0 τ ^ 2 *
        (jacobiTheta3 z τ *
          jacobiThetaWronskian3Error z τ) = 0 := by
    unfold jacobiThetaWronskian3Error
    linear_combination
      jacobiTheta1 z τ * hd -
        jacobiTheta1Prime z τ * hq +
      jacobiTheta3 0 τ ^ 2 *
        jacobiTheta2 z τ * hw
  exact
    (mul_eq_zero.mp hbig).resolve_left hp2

theorem jacobiTheta4_mul_wronskian4Error_eq_zero
    (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta4 z τ *
      jacobiThetaWronskian4Error z τ = 0 := by
  have hq :=
    jacobiTheta_residualQ1_identity z τ hτ
  have hd :=
    jacobiTheta_residualQ1_derivative_identity
      z hτ
  have hw :=
    jacobiTheta_wronskian2 z hτ
  have hp2 :
      jacobiTheta2 0 τ ^ 2 ≠ 0 := by
    exact
      pow_ne_zero 2
        (jacobiTheta2_zero_ne_zero_for_wronskians
          (⟨τ, hτ⟩ : ℍ))
  have hbig :
      jacobiTheta2 0 τ ^ 2 *
        (jacobiTheta4 z τ *
          jacobiThetaWronskian4Error z τ) = 0 := by
    unfold jacobiThetaWronskian4Error
    linear_combination
      jacobiTheta1 z τ * hd -
        jacobiTheta1Prime z τ * hq +
      jacobiTheta4 0 τ ^ 2 *
        jacobiTheta2 z τ * hw
  exact
    (mul_eq_zero.mp hbig).resolve_left hp2

theorem analyticOnNhd_jacobiThetaWronskian3Error
    (τ : ℍ) :
    AnalyticOnNhd ℂ
      (fun z ↦
        jacobiThetaWronskian3Error
          z (τ : ℂ)) Set.univ := by
  have h1 :=
    analyticOnNhd_jacobiTheta1_fixed_for_wronskians τ
  have h2 :=
    analyticOnNhd_jacobiTheta2_fixed_for_wronskians τ
  have h3 :=
    analyticOnNhd_jacobiTheta3_fixed_for_wronskians τ
  have h4 :=
    analyticOnNhd_jacobiTheta4_fixed_for_wronskians τ
  have h1p :=
    analyticOnNhd_jacobiTheta1Prime_fixed τ
  have h3p :=
    analyticOnNhd_jacobiTheta3Prime_fixed τ
  have hc :
      AnalyticOnNhd ℂ
        (fun _ : ℂ ↦
          π * jacobiTheta3 0 (τ : ℂ) ^ 2)
        Set.univ :=
    analyticOnNhd_const
  simpa only [jacobiThetaWronskian3Error,
    mul_assoc] using
      ((h3p.mul h1).sub (h3.mul h1p)).add
        (hc.mul (h4.mul h2))

theorem analyticOnNhd_jacobiThetaWronskian4Error
    (τ : ℍ) :
    AnalyticOnNhd ℂ
      (fun z ↦
        jacobiThetaWronskian4Error
          z (τ : ℂ)) Set.univ := by
  have h1 :=
    analyticOnNhd_jacobiTheta1_fixed_for_wronskians τ
  have h2 :=
    analyticOnNhd_jacobiTheta2_fixed_for_wronskians τ
  have h3 :=
    analyticOnNhd_jacobiTheta3_fixed_for_wronskians τ
  have h4 :=
    analyticOnNhd_jacobiTheta4_fixed_for_wronskians τ
  have h1p :=
    analyticOnNhd_jacobiTheta1Prime_fixed τ
  have h4p :=
    analyticOnNhd_jacobiTheta4Prime_fixed τ
  have hc :
      AnalyticOnNhd ℂ
        (fun _ : ℂ ↦
          π * jacobiTheta4 0 (τ : ℂ) ^ 2)
        Set.univ :=
    analyticOnNhd_const
  simpa only [jacobiThetaWronskian4Error,
    mul_assoc] using
      ((h4p.mul h1).sub (h4.mul h1p)).add
        (hc.mul (h2.mul h3))

theorem jacobiThetaWronskian3Error_eq_zero
    (z : ℂ) (τ : ℍ) :
    jacobiThetaWronskian3Error
      z (τ : ℂ) = 0 := by
  have hor :=
    (analyticOnNhd_jacobiTheta3_fixed_for_wronskians τ)
      |>.eq_zero_or_eq_zero_of_mul_eq_zero
        (analyticOnNhd_jacobiThetaWronskian3Error τ)
        (fun w _ ↦
          jacobiTheta3_mul_wronskian3Error_eq_zero
            w τ.im_pos)
        isPreconnected_univ
  rcases hor with htheta | herr
  · exact
      (jacobiTheta3_zero_ne_zero τ
        (htheta 0 (Set.mem_univ 0))).elim
  · exact herr z (Set.mem_univ z)

theorem jacobiThetaWronskian4Error_eq_zero
    (z : ℂ) (τ : ℍ) :
    jacobiThetaWronskian4Error
      z (τ : ℂ) = 0 := by
  have hor :=
    (analyticOnNhd_jacobiTheta4_fixed_for_wronskians τ)
      |>.eq_zero_or_eq_zero_of_mul_eq_zero
        (analyticOnNhd_jacobiThetaWronskian4Error τ)
        (fun w _ ↦
          jacobiTheta4_mul_wronskian4Error_eq_zero
            w τ.im_pos)
        isPreconnected_univ
  rcases hor with htheta | herr
  · exact
      (jacobiTheta4_zero_ne_zero τ
        (htheta 0 (Set.mem_univ 0))).elim
  · exact herr z (Set.mem_univ z)

theorem jacobiTheta_wronskian3
    (z : ℂ) (τ : ℍ) :
    jacobiTheta3Prime z (τ : ℂ) *
          jacobiTheta1 z (τ : ℂ) -
        jacobiTheta3 z (τ : ℂ) *
          jacobiTheta1Prime z (τ : ℂ) =
      -π * jacobiTheta3 0 (τ : ℂ) ^ 2 *
        jacobiTheta4 z (τ : ℂ) *
          jacobiTheta2 z (τ : ℂ) := by
  have h :=
    jacobiThetaWronskian3Error_eq_zero z τ
  unfold jacobiThetaWronskian3Error at h
  linear_combination h

theorem jacobiTheta_wronskian4
    (z : ℂ) (τ : ℍ) :
    jacobiTheta4Prime z (τ : ℂ) *
          jacobiTheta1 z (τ : ℂ) -
        jacobiTheta4 z (τ : ℂ) *
          jacobiTheta1Prime z (τ : ℂ) =
      -π * jacobiTheta4 0 (τ : ℂ) ^ 2 *
        jacobiTheta2 z (τ : ℂ) *
          jacobiTheta3 z (τ : ℂ) := by
  have h :=
    jacobiThetaWronskian4Error_eq_zero z τ
  unfold jacobiThetaWronskian4Error at h
  linear_combination h

/-! ## Canonical packaging -/

/-- The three Wronskian identities required by the projective
initial-rank argument hold unconditionally for the canonical theta
vector. -/
theorem canonicalJacobiThetaWronskiansAt
    (z : ℂ) (τ : ℍ) :
    CanonicalJacobiThetaWronskiansAt z τ := by
  unfold CanonicalJacobiThetaWronskiansAt
    JacobiThetaWronskiansAt
  simp only [canonicalUnaryRoots_p2,
    canonicalUnaryRoots_p3,
    canonicalUnaryRoots_p4,
    jacobiThetaVector, jacobiThetaVectorPrime,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← jacobiTheta2_zero_eq_theta₂,
    ← jacobiTheta3_zero_eq_theta₃,
    ← jacobiTheta4_zero_eq_theta₄]
  exact
    ⟨jacobiTheta_wronskian2 z τ.im_pos,
      jacobiTheta_wronskian3 z τ,
      jacobiTheta_wronskian4 z τ⟩

end

end HGAS.Modular
