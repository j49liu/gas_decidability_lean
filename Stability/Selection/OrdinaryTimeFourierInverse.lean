import Stability.Selection.OrdinaryTimeWeightedFourier
import HGAS.Analysis.FiniteProductSeries
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Weighted Fourier estimates for a geometric inverse

Section 9, Lemma `bounds`, uses the geometric series in the weighted
Fourier norm. We index its terms by finite tuples of characters and
collect the resulting exponents only after proving absolute convergence.
-/

noncomputable section

open scoped BigOperators

namespace Stability.Selection

open HGAS.Analysis

variable {d ι : Type*} [Fintype d]

private theorem summable_finProduct_real
    (u : ι → ℝ) (hu : Summable u) (hu0 : ∀ i, 0 ≤ u i) (n : ℕ) :
    Summable fun x : Fin n → ι ↦ ∏ j, u (x j) := by
  have hc : Summable fun i ↦ ‖(u i : ℂ)‖ := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hu0 _)] using hu
  have h := summable_norm_finProductComplex (fun _ : Fin n ↦ fun i ↦ (u i : ℂ))
    (fun _ ↦ hc)
  simpa only [norm_prod, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hu0 _)] using h

private theorem tsum_finProduct_real
    (u : ι → ℝ) (hu : Summable u) (hu0 : ∀ i, 0 ≤ u i) (n : ℕ) :
    (∑' x : Fin n → ι, ∏ j, u (x j)) = (∑' i, u i) ^ n := by
  have hc : Summable fun i ↦ ‖(u i : ℂ)‖ := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hu0 _)] using hu
  have h := prod_tsum_eq_tsum_finProduct (fun _ : Fin n ↦ fun i ↦ (u i : ℂ))
    (fun _ ↦ hc)
  dsimp only at h
  have hcast : (((∑' i, u i) : ℝ) : ℂ) = ∑' i, (u i : ℂ) := Complex.ofReal_tsum u
  have hprod (x : Fin n → ι) : ((∏ j, u (x j) : ℝ) : ℂ) =
      ∏ j, (u (x j) : ℂ) := by push_cast; rfl
  rw [← hcast] at h
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  rw [← funext hprod, ← Complex.ofReal_tsum, ← Complex.ofReal_pow] at h
  exact Complex.ofReal_injective h.symm

omit [Fintype d] in
private theorem weight_sum_le_prod
    (w : (d → ℤ) → ℝ) (hw : ∀ a, 0 ≤ w a) (hzero : w 0 = 1)
    (hadd : ∀ a b, w (a + b) ≤ w a * w b)
    {κ : Type*} (s : Finset κ) (a : κ → d → ℤ) :
    w (∑ j ∈ s, a j) ≤ ∏ j ∈ s, w (a j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hzero]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi]
      exact (hadd _ _).trans (mul_le_mul_of_nonneg_left ih (hw _))

private theorem fourier_sum_eq_prod {κ : Type*}
    (s : Finset κ) (a : κ → d → ℤ) (x : UnitAddTorus d) :
    UnitAddTorus.mFourier (∑ j ∈ s, a j) x =
      ∏ j ∈ s, UnitAddTorus.mFourier (a j) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [UnitAddTorus.mFourier_zero]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi, UnitAddTorus.mFourier_add, ih]

private abbrev NeumannIndex (ι : Type*) := Σ n : ℕ, Fin n → ι

private def neumannCoefficient (c : ι → ℂ) (p : NeumannIndex ι) : ℂ :=
  ∏ j, c (p.2 j)

private def neumannExponent (e : ι → d → ℤ) (p : NeumannIndex ι) : d → ℤ :=
  ∑ j, e (p.2 j)

omit [Fintype d] in
private theorem neumann_weighted_bound
    (c : ι → ℂ) (e : ι → d → ℤ) (w : (d → ℤ) → ℝ)
    (hw : ∀ a, 1 ≤ w a) (hzero : w 0 = 1)
    (hadd : ∀ a b, w (a + b) ≤ w a * w b)
    (hcw : Summable fun i ↦ ‖c i‖ * w (e i))
    (hsmall : (∑' i, ‖c i‖ * w (e i)) < 1) :
    Summable (fun p : NeumannIndex ι ↦
      ‖neumannCoefficient c p‖ * w (neumannExponent e p)) ∧
    (∑' p : NeumannIndex ι, ‖neumannCoefficient c p‖ * w (neumannExponent e p)) ≤
      (1 - ∑' i, ‖c i‖ * w (e i))⁻¹ := by
  let u : ι → ℝ := fun i ↦ ‖c i‖ * w (e i)
  have hu0 : ∀ i, 0 ≤ u i := fun i ↦ mul_nonneg (norm_nonneg _) (zero_le_one.trans (hw _))
  have hs0 : 0 ≤ ∑' i, u i := tsum_nonneg hu0
  have hmajor : Summable fun p : NeumannIndex ι ↦ ∏ j, u (p.2 j) := by
    apply (summable_sigma_of_nonneg (fun p ↦ Finset.prod_nonneg fun _ _ ↦ hu0 _)).2
    refine ⟨fun n ↦ summable_finProduct_real u hcw hu0 n, ?_⟩
    simp_rw [tsum_finProduct_real u hcw hu0]
    exact summable_geometric_of_lt_one hs0 hsmall
  have hle (p : NeumannIndex ι) :
      ‖neumannCoefficient c p‖ * w (neumannExponent e p) ≤ ∏ j, u (p.2 j) := by
    unfold neumannCoefficient neumannExponent
    simp only [u, norm_prod, Finset.prod_mul_distrib]
    exact mul_le_mul_of_nonneg_left
      (weight_sum_le_prod w (fun a ↦ zero_le_one.trans (hw a)) hzero hadd _ _)
      (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)
  have hs : Summable fun p : NeumannIndex ι ↦
      ‖neumannCoefficient c p‖ * w (neumannExponent e p) :=
    hmajor.of_nonneg_of_le
      (fun p ↦ mul_nonneg (norm_nonneg _) (zero_le_one.trans (hw _))) hle
  refine ⟨hs, (hs.tsum_le_tsum hle hmajor).trans_eq ?_⟩
  rw [hmajor.tsum_sigma]
  simp_rw [tsum_finProduct_real u hcw hu0]
  exact (hasSum_geometric_of_lt_one hs0 hsmall).tsum_eq

/-- A geometric inverse has a summable actual weighted Fourier family,
and its weighted norm is bounded by the geometric sum. The weight may be
any submultiplicative weight at least one with weight one at zero. -/
theorem weighted_fourierCoeff_inverse_one_sub [Countable ι]
    (c : ι → ℂ) (e : ι → d → ℤ) (w : (d → ℤ) → ℝ)
    (hw : ∀ a, 1 ≤ w a) (hzero : w 0 = 1)
    (hadd : ∀ a b, w (a + b) ≤ w a * w b)
    (hcw : Summable fun i ↦ ‖c i‖ * w (e i))
    (hsmall : (∑' i, ‖c i‖ * w (e i)) < 1) :
    Summable (fun a ↦
      ‖UnitAddTorus.mFourierCoeff (fun x ↦ (1 - torusFourierSeries c e x)⁻¹) a‖ * w a) ∧
    (∑' a, ‖UnitAddTorus.mFourierCoeff
      (fun x ↦ (1 - torusFourierSeries c e x)⁻¹) a‖ * w a) ≤
        (1 - ∑' i, ‖c i‖ * w (e i))⁻¹ := by
  have hw0 : ∀ a, 0 ≤ w a := fun a ↦ zero_le_one.trans (hw a)
  have hcoeff (i : ι) : ‖c i‖ ≤ ‖c i‖ * w (e i) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hw (e i)) (norm_nonneg (c i))
  have hc : Summable fun i ↦ ‖c i‖ :=
    hcw.of_nonneg_of_le (fun i ↦ norm_nonneg _) hcoeff
  obtain ⟨hnw, hbound⟩ := neumann_weighted_bound c e w hw hzero hadd hcw hsmall
  have hn : Summable fun p : NeumannIndex ι ↦ ‖neumannCoefficient c p‖ := by
    apply hnw.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    intro p
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (hw (neumannExponent e p)) (norm_nonneg (neumannCoefficient c p))
  have heq : torusFourierSeries (neumannCoefficient c) (neumannExponent e) =
      fun x ↦ (1 - torusFourierSeries c e x)⁻¹ := by
    funext x
    have ht : Summable fun p : NeumannIndex ι ↦
        torusSeriesTerm (neumannCoefficient c) (neumannExponent e) p x :=
      hn.of_norm_bounded fun p ↦ (norm_torusSeriesTerm _ _ _ _).le
    have ht0 : Summable fun i ↦ ‖torusSeriesTerm c e i x‖ := by
      simpa only [norm_torusSeriesTerm] using hc
    have hnorm : ‖torusFourierSeries c e x‖ < 1 := by
      have hraw : ‖torusFourierSeries c e x‖ ≤ ∑' i, ‖c i‖ := by
        simpa only [torusFourierSeries, norm_torusSeriesTerm] using
          norm_tsum_le_tsum_norm ht0
      exact (hraw.trans (hc.tsum_le_tsum hcoeff hcw)).trans_lt hsmall
    unfold torusFourierSeries
    rw [ht.tsum_sigma]
    have hinner (n : ℕ) :
        (∑' p : Fin n → ι,
          torusSeriesTerm (neumannCoefficient c) (neumannExponent e) ⟨n, p⟩ x) =
        (torusFourierSeries c e x) ^ n := by
      have hp := prod_tsum_eq_tsum_finProduct
        (fun _ : Fin n ↦ fun i ↦ torusSeriesTerm c e i x) (fun _ ↦ ht0)
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hp
      rw [torusFourierSeries, hp]
      apply tsum_congr
      intro p
      simp only [torusSeriesTerm, neumannCoefficient, neumannExponent,
        fourier_sum_eq_prod, Finset.prod_mul_distrib]
    simp_rw [hinner]
    exact tsum_geometric_of_norm_lt_one hnorm
  rw [← heq]
  exact ⟨summable_weighted_fourierCoeff_of_expansion _ _ w hw0 hn hnw,
    (tsum_weighted_fourierCoeff_le _ _ w hw0 hn hnw).trans hbound⟩

/-- The usual exponential `ℓ¹` frequency weight satisfies the hypotheses
of the geometric-inverse theorem. -/
theorem exponential_fourierCoeff_inverse_one_sub [Countable ι]
    (c : ι → ℂ) (e : ι → d → ℤ) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hcw : Summable fun i ↦ ‖c i‖ * ρ ^ (∑ j, |(e i j : ℝ)|))
    (hsmall : (∑' i, ‖c i‖ * ρ ^ (∑ j, |(e i j : ℝ)|)) < 1) :
    Summable (fun a ↦
      ‖UnitAddTorus.mFourierCoeff (fun x ↦ (1 - torusFourierSeries c e x)⁻¹) a‖ *
        ρ ^ (∑ j, |(a j : ℝ)|)) ∧
    (∑' a, ‖UnitAddTorus.mFourierCoeff
      (fun x ↦ (1 - torusFourierSeries c e x)⁻¹) a‖ * ρ ^ (∑ j, |(a j : ℝ)|)) ≤
        (1 - ∑' i, ‖c i‖ * ρ ^ (∑ j, |(e i j : ℝ)|))⁻¹ := by
  refine weighted_fourierCoeff_inverse_one_sub c e
    (fun a : d → ℤ ↦ ρ ^ (∑ j, |(a j : ℝ)|)) ?_ ?_ ?_ hcw hsmall
  · intro a
    exact Real.one_le_rpow hρ (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
  · simp
  · intro a b
    rw [← Real.rpow_add (zero_lt_one.trans_le hρ)]
    apply Real.rpow_le_rpow_of_exponent_le hρ
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    simpa only [Pi.add_apply, Int.cast_add] using abs_add_le (a j : ℝ) (b j : ℝ)

/-- A single character gives the geometric reciprocal used by each
Poisson coordinate, with its exact weighted geometric majorant. -/
theorem exponential_fourierCoeff_reciprocal_character
    (a : d → ℤ) {η ρ : ℝ} (hη : 0 ≤ η) (hρ : 1 ≤ ρ)
    (hsmall : η * ρ ^ (∑ j, |(a j : ℝ)|) < 1) :
    Summable (fun b ↦
      ‖UnitAddTorus.mFourierCoeff
        (fun x ↦ (1 - (η : ℂ) * UnitAddTorus.mFourier a x)⁻¹) b‖ *
        ρ ^ (∑ j, |(b j : ℝ)|)) ∧
    (∑' b, ‖UnitAddTorus.mFourierCoeff
      (fun x ↦ (1 - (η : ℂ) * UnitAddTorus.mFourier a x)⁻¹) b‖ *
        ρ ^ (∑ j, |(b j : ℝ)|)) ≤
        (1 - η * ρ ^ (∑ j, |(a j : ℝ)|))⁻¹ := by
  have h := exponential_fourierCoeff_inverse_one_sub
    (fun _ : Unit ↦ (η : ℂ)) (fun _ ↦ a) hρ Summable.of_finite
    (by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hη] using hsmall)
  simpa [torusFourierSeries, torusSeriesTerm, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hη] using h

end Stability.Selection
