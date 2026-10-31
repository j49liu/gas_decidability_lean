import Stability.Selection.OrdinaryTimeFourierLinear
import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Polynomial evaluation in the weighted Fourier norm

A polynomial of degree `D` in coordinates with weighted norm at most
`C ≥ 1` has weighted norm at most its coefficient mass times `C^D`.
This is the polynomial composition estimate in Section 9, Lemma `bounds`.
-/

noncomputable section

open scoped BigOperators

namespace Stability.Selection

variable {d : Type*} [Fintype d]

/-- Finite products obey the weighted product estimate, including an
empty product. Every coefficient is an actual Haar coefficient. -/
theorem exponential_fourierCoeff_finset_prod {ι : Type*}
    (s : Finset ι) (f : ι → UnitAddTorus d → ℂ) (hfc : ∀ i, Continuous (f i))
    {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hf : ∀ i, Summable fun a ↦ ‖UnitAddTorus.mFourierCoeff (f i) a‖ *
      ρ ^ (∑ j, |(a j : ℝ)|)) :
    Summable (fun a ↦ ‖UnitAddTorus.mFourierCoeff (fun x ↦ ∏ i ∈ s, f i x) a‖ *
      ρ ^ (∑ j, |(a j : ℝ)|)) ∧
    (∑' a, ‖UnitAddTorus.mFourierCoeff (fun x ↦ ∏ i ∈ s, f i x) a‖ *
      ρ ^ (∑ j, |(a j : ℝ)|)) ≤
        ∏ i ∈ s, ∑' a, ‖UnitAddTorus.mFourierCoeff (f i) a‖ * ρ ^ (∑ j, |(a j : ℝ)|) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.prod_empty, norm_one] using
      (exponential_fourierCoeff_const (d := d) 1 ρ).imp_right (fun h ↦ h.le)
  | @insert i s hi ih =>
    have hs : Continuous fun x ↦ ∏ j ∈ s, f j x := by fun_prop
    have hm := exponential_fourierCoeff_mul (f i) (fun x ↦ ∏ j ∈ s, f j x)
      (hfc i) hs hρ (hf i) ih.1
    simp only [Finset.prod_insert hi]
    exact ⟨hm.1, hm.2.trans
      (mul_le_mul_of_nonneg_left ih.2 (tsum_nonneg fun _ ↦ by positivity))⟩

/-- Polynomial substitution preserves actual weighted summability and
has the coefficient-mass/degree bound. The coefficient homomorphism is
explicit, so the theorem applies directly to rational decoded polynomials. -/
theorem exponential_fourierCoeff_polynomial {σ R : Type*} [CommSemiring R]
    (P : MvPolynomial σ R) (c : R →+* ℂ) (f : σ → UnitAddTorus d → ℂ)
    (hfc : ∀ i, Continuous (f i)) {ρ C : ℝ} (hρ : 1 ≤ ρ) (hC : 1 ≤ C)
    (hf : ∀ i, Summable fun a ↦ ‖UnitAddTorus.mFourierCoeff (f i) a‖ *
      ρ ^ (∑ j, |(a j : ℝ)|))
    (hbound : ∀ i, (∑' a, ‖UnitAddTorus.mFourierCoeff (f i) a‖ *
      ρ ^ (∑ j, |(a j : ℝ)|)) ≤ C) :
    Summable (fun a ↦ ‖UnitAddTorus.mFourierCoeff
      (fun x ↦ MvPolynomial.eval₂ c (fun i ↦ f i x) P) a‖ * ρ ^ (∑ j, |(a j : ℝ)|)) ∧
    (∑' a, ‖UnitAddTorus.mFourierCoeff
      (fun x ↦ MvPolynomial.eval₂ c (fun i ↦ f i x) P) a‖ * ρ ^ (∑ j, |(a j : ℝ)|)) ≤
      (∑ e ∈ P.support, ‖c (P.coeff e)‖) * C ^ P.totalDegree := by
  classical
  let monomial : (σ →₀ ℕ) → UnitAddTorus d → ℂ := fun e x ↦
    ∏ i ∈ e.support, f i x ^ e i
  let term : (σ →₀ ℕ) → UnitAddTorus d → ℂ := fun e x ↦ c (P.coeff e) * monomial e x
  have hmonCont (e : σ →₀ ℕ) : Continuous (monomial e) := by
    dsimp [monomial]
    fun_prop
  have hpower (e : σ →₀ ℕ) (i : σ) :=
    exponential_fourierCoeff_pow (f i) (hfc i) hρ (hf i) (e i)
  have hmon (e : σ →₀ ℕ) := exponential_fourierCoeff_finset_prod e.support
    (fun i x ↦ f i x ^ e i) (fun i ↦ (hfc i).pow _) hρ (fun i ↦ (hpower e i).1)
  have hmonBound (e : σ →₀ ℕ) :
      (∑' a, ‖UnitAddTorus.mFourierCoeff (monomial e) a‖ * ρ ^ (∑ j, |(a j : ℝ)|)) ≤
        C ^ (e.sum fun _ n ↦ n) := by
    refine (hmon e).2.trans ?_
    calc
      _ ≤ ∏ i ∈ e.support, C ^ e i := by
        apply Finset.prod_le_prod (fun _ _ ↦ tsum_nonneg fun _ ↦ by positivity)
        intro i _
        exact (hpower e i).2.trans
          (pow_le_pow_left₀ (tsum_nonneg fun _ ↦ by positivity) (hbound i) _)
      _ = _ := Finset.prod_pow_eq_pow_sum _ _ _
  have htermCont (e : σ →₀ ℕ) : Continuous (term e) := continuous_const.mul (hmonCont e)
  have hterm (e : σ →₀ ℕ) :=
    exponential_fourierCoeff_const_mul (monomial e) (c (P.coeff e)) ρ (hmon e).1
  have heval : (fun x ↦ MvPolynomial.eval₂ c (fun i ↦ f i x) P) =
      fun x ↦ ∑ e ∈ P.support, term e x := by
    funext x
    exact MvPolynomial.eval₂_eq c (fun i ↦ f i x) P
  rw [heval]
  have hs := exponential_fourierCoeff_finset_sum P.support term htermCont hρ
    (fun e ↦ (hterm e).1)
  refine ⟨hs.1, hs.2.trans ?_⟩
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro e he
  change (∑' a, ‖UnitAddTorus.mFourierCoeff
    (fun x ↦ c (P.coeff e) * monomial e x) a‖ * ρ ^ (∑ j, |(a j : ℝ)|)) ≤ _
  rw [(hterm e).2]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact (hmonBound e).trans (pow_le_pow_right₀ hC (MvPolynomial.le_totalDegree he))

end Stability.Selection
