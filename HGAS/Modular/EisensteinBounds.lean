import Mathlib.NumberTheory.ModularForms.Derivative
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Summable
import Mathlib.Analysis.Calculus.DiffContOnCl
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic

/-!
# Elementary bounds for `E₂` and normalized derivatives

This module supplies two analytic estimates needed to turn the formal
Serre derivative into a bundled modular form.

* `E₂` is bounded as the imaginary part tends to infinity.  We prove this
  directly from Mathlib's divisor-sum expansion and dominate
  `σ₁(n)|q|ⁿ` by `n²rⁿ`.
* The normalized derivative of a bounded holomorphic function is bounded
  at infinity.  The proof is the Cauchy estimate on the disk of radius
  `Im τ / 2`.

Neither result is specific to the undecidability construction.  In
particular, the derivative estimate is stated for an arbitrary
MDifferentiable function on the upper half-plane.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I σ
open Complex Real Filter Asymptotics
open scoped ArithmeticFunction.sigma Manifold MatrixGroups Real Topology

noncomputable section

local notation "D" => Derivative.normalizedDerivOfComplex

/-! ## A uniform majorant for `E₂` -/

/-- Above the horizontal line `Im τ = 1`, the nome is uniformly bounded
by `exp (-2π)`. -/
theorem norm_exp_two_pi_I_le_exp_neg_two_pi
    (z : ℍ) (hz : 1 ≤ z.im) :
    ‖cexp (2 * π * I * z)‖ ≤ Real.exp (-2 * π) := by
  have hreal :
      ((2 : ℂ) * π * I * (z : ℂ)).re = -2 * π * z.im := by
    rw [show (2 : ℂ) * π * I * z = I * (2 * π * z) by ring]
    simp [Complex.I_re, Complex.I_im, mul_comm]
  rw [norm_exp, hreal, Real.exp_le_exp]
  nlinarith [Real.pi_pos]

/-- The fixed real majorant used for the positive-index divisor sum. -/
def e2Majorant (n : ℕ+) : ℝ :=
  (n : ℝ) ^ 2 * Real.exp (-2 * π) ^ (n : ℕ)

theorem summable_e2Majorant : Summable e2Majorant := by
  have hr : ‖Real.exp (-2 * π)‖ < 1 := by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  exact
    ((summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 hr).subtype
      (fun n : ℕ ↦ 0 < n)).congr (fun n ↦ by
        rfl)

/-- Each term of the divisor-sum expansion of `E₂` is dominated by the
fixed majorant when `Im τ ≥ 1`. -/
theorem norm_e2_qterm_le_majorant
    (z : ℍ) (hz : 1 ≤ z.im) (n : ℕ+) :
    ‖(((σ 1 n : ℕ) : ℂ) *
        cexp (2 * π * I * z) ^ (n : ℕ))‖ ≤ e2Majorant n := by
  let q : ℂ := cexp (2 * π * I * z)
  have hq : ‖q‖ ≤ Real.exp (-2 * π) :=
    norm_exp_two_pi_I_le_exp_neg_two_pi z hz
  change ‖(((σ 1 n : ℕ) : ℂ) * q ^ (n : ℕ))‖ ≤ _
  rw [norm_mul, Complex.norm_natCast, norm_pow]
  unfold e2Majorant
  have hsigma :
      ((σ 1 (n : ℕ) : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
    exact_mod_cast
      (ArithmeticFunction.sigma_le_pow_succ 1 (n : ℕ)).trans_eq
        (by norm_num)
  have hqnonneg : 0 ≤ ‖q‖ := norm_nonneg _
  have hrnonneg : 0 ≤ Real.exp (-2 * π) := (Real.exp_pos _).le
  exact mul_le_mul hsigma
    (pow_le_pow_left₀ hqnonneg hq (n : ℕ))
    (pow_nonneg hqnonneg _) (sq_nonneg _)

/-- The normalized weight-two Eisenstein series is bounded at infinity. -/
theorem e2_isBoundedAtImInfty :
    IsBoundedAtImInfty EisensteinSeries.E2 := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  let M : ℝ := 1 + 24 * ∑' n : ℕ+, e2Majorant n
  refine ⟨M, 1, fun z hz ↦ ?_⟩
  rw [EisensteinSeries.E2_eq_tsum_cexp]
  let term : ℕ+ → ℂ := fun n ↦
    ((σ 1 n : ℕ) : ℂ) *
      cexp (2 * π * I * z) ^ (n : ℕ)
  have hterm :
      Summable fun n : ℕ+ ↦ ‖term n‖ :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      (fun n ↦ norm_e2_qterm_le_majorant z hz n)
      summable_e2Majorant
  have hsum :
      ‖∑' n : ℕ+, term n‖ ≤ ∑' n : ℕ+, e2Majorant n :=
    (norm_tsum_le_tsum_norm hterm).trans
      (hterm.tsum_le_tsum
        (fun n ↦ norm_e2_qterm_le_majorant z hz n)
        summable_e2Majorant)
  change ‖1 - 24 * ∑' n : ℕ+, term n‖ ≤ M
  calc
    ‖1 - 24 * ∑' n : ℕ+, term n‖
        ≤ ‖(1 : ℂ)‖ + ‖(24 : ℂ) * ∑' n : ℕ+, term n‖ :=
      norm_sub_le _ _
    _ = 1 + 24 * ‖∑' n : ℕ+, term n‖ := by simp
    _ ≤ 1 + 24 * ∑' n : ℕ+, e2Majorant n := by gcongr
    _ = M := rfl

/-- The divisor-sum part of `E₂` tends to zero at the cusp.  Tannery's
theorem makes the interchange of limit and infinite sum explicit. -/
theorem e2_divisorSum_tendsto_zero :
    Tendsto
      (fun z : ℍ ↦
        ∑' n : ℕ+,
          ((σ 1 n : ℕ) : ℂ) *
            cexp (2 * π * I * z) ^ (n : ℕ))
      atImInfty (𝓝 0) := by
  let term : ℍ → ℕ+ → ℂ := fun z n ↦
    ((σ 1 n : ℕ) : ℂ) *
      cexp (2 * π * I * z) ^ (n : ℕ)
  have hq :
      Tendsto (fun z : ℍ ↦ cexp (2 * π * I * z))
        atImInfty (𝓝 0) := by
    simpa [Function.Periodic.qParam, div_one] using
      (UpperHalfPlane.qParam_tendsto_atImInfty one_pos)
  have hterm (n : ℕ+) :
      Tendsto (fun z ↦ term z n) atImInfty (𝓝 0) := by
    have hp :=
      (hq.pow (n : ℕ)).const_mul (((σ 1 n : ℕ) : ℂ))
    simpa [term, n.ne_zero] using hp
  have hbound :
      ∀ᶠ z : ℍ in atImInfty,
        ∀ n : ℕ+, ‖term z n‖ ≤ e2Majorant n :=
    by
      rw [Filter.eventually_iff_exists_mem]
      exact
        ⟨{z : ℍ | 1 ≤ z.im},
          (atImInfty_mem _).mpr ⟨1, fun _ hz ↦ hz⟩,
          fun z hz n ↦ norm_e2_qterm_le_majorant z hz n⟩
  have ht :=
    tendsto_tsum_of_dominated_convergence
      summable_e2Majorant hterm hbound
  simpa [term] using ht

/-- The normalized Eisenstein series satisfies `E₂(τ) → 1` at the
infinite cusp. -/
theorem e2_tendsto_one_atImInfty :
    Tendsto EisensteinSeries.E2 atImInfty (𝓝 1) := by
  have h :=
    (tendsto_const_nhds :
      Tendsto (fun _ : ℍ ↦ (1 : ℂ)) atImInfty (𝓝 1)).sub
      (e2_divisorSum_tendsto_zero.const_mul (24 : ℂ))
  have h' :
      Tendsto
        (fun z : ℍ ↦
          1 - 24 *
            ∑' n : ℕ+,
              ((σ 1 n : ℕ) : ℂ) *
                cexp (2 * π * I * z) ^ (n : ℕ))
        atImInfty (𝓝 1) := by
    simpa using h
  apply h'.congr'
  filter_upwards with z
  exact (EisensteinSeries.E2_eq_tsum_cexp z).symm

/-! ## Cauchy estimates for the normalized derivative -/

/-- A holomorphic function on the upper half-plane is holomorphic and
continuous on every closed Euclidean disk contained in it. -/
theorem diffContOnCl_comp_ofComplex_of_mdifferentiable
    {f : ℍ → ℂ} (hf : MDiff f) {c : ℂ} {R : ℝ}
    (hclosed :
      Metric.closedBall c R ⊆ {z : ℂ | 0 < z.im}) :
    DiffContOnCl ℂ (f ∘ ofComplex) (Metric.ball c R) :=
  ⟨fun z hz ↦
      (UpperHalfPlane.mdifferentiableAt_iff.mp
        (hf ⟨z, hclosed (Metric.ball_subset_closedBall hz)⟩)).differentiableWithinAt,
    fun z hz ↦ by
      have hd : DifferentiableAt ℂ (f ∘ ofComplex) z :=
        UpperHalfPlane.mdifferentiableAt_iff.mp
          (hf ⟨z, hclosed (Metric.closure_ball_subset_closedBall hz)⟩)
      exact hd.continuousAt.continuousWithinAt⟩

/-- The disk centered at `τ` of radius `Im τ / 2` stays in the
upper half-plane. -/
theorem closedBall_center_subset_upperHalfPlane (z : ℍ) :
    Metric.closedBall (z : ℂ) (z.im / 2) ⊆
      {w : ℂ | 0 < w.im} := by
  intro w hw
  have hdist : dist w z ≤ z.im / 2 :=
    Metric.mem_closedBall.mp hw
  have habs : |w.im - z.im| ≤ z.im / 2 := calc
    |w.im - z.im| = |(w - z).im| := by simp [Complex.sub_im]
    _ ≤ ‖w - z‖ := abs_im_le_norm _
    _ = dist w z := (dist_eq_norm _ _).symm
    _ ≤ z.im / 2 := hdist
  have hlower : z.im / 2 ≤ w.im := by
    linarith [(abs_le.mp habs).1]
  exact lt_of_lt_of_le (by linarith [z.im_pos]) hlower

/-- Cauchy's estimate in the normalization `D=(2πi)⁻¹d/dτ`. -/
theorem norm_normalizedDeriv_le_of_sphere_bound
    {f : ℍ → ℂ} {z : ℍ} {r M : ℝ}
    (hr : 0 < r)
    (hDiff :
      DiffContOnCl ℂ (f ∘ ofComplex) (Metric.ball (z : ℂ) r))
    (hbdd :
      ∀ w ∈ Metric.sphere (z : ℂ) r,
        ‖(f ∘ ofComplex) w‖ ≤ M) :
    ‖D f z‖ ≤ M / (2 * π * r) := calc
  ‖D f z‖ =
      ‖(2 * π * I)⁻¹‖ * ‖deriv (f ∘ ofComplex) z‖ := by
        simp [Derivative.normalizedDerivOfComplex]
  _ = (2 * π)⁻¹ * ‖deriv (f ∘ ofComplex) z‖ := by
        simp [abs_of_pos Real.pi_pos]
  _ ≤ (2 * π)⁻¹ * (M / r) := by
        gcongr
        exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
          hr hDiff hbdd
  _ = M / (2 * π * r) := by ring

/-- The normalized derivative of a bounded holomorphic function is
bounded at infinity. -/
theorem normalizedDeriv_isBoundedAtImInfty_of_bounded
    {f : ℍ → ℂ} (hf : MDiff f)
    (hbdd : IsBoundedAtImInfty f) :
    IsBoundedAtImInfty (D f) := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff] at hbdd ⊢
  obtain ⟨M, A, hMA⟩ := hbdd
  refine ⟨M / π, 2 * max A 0 + 1, fun z hz ↦ ?_⟩
  have hR : 0 < z.im / 2 := by linarith [z.im_pos]
  have hclosed := closedBall_center_subset_upperHalfPlane z
  have hDiff :
      DiffContOnCl ℂ (f ∘ ofComplex)
        (Metric.ball (z : ℂ) (z.im / 2)) :=
    diffContOnCl_comp_ofComplex_of_mdifferentiable hf hclosed
  have hsphere :
      ∀ w ∈ Metric.sphere (z : ℂ) (z.im / 2),
        ‖(f ∘ ofComplex) w‖ ≤ M := by
    intro w hw
    have hwpos :
        0 < w.im :=
      hclosed (Metric.sphere_subset_closedBall hw)
    have hdist : dist w z = z.im / 2 :=
      Metric.mem_sphere.mp hw
    have habs : |w.im - z.im| ≤ z.im / 2 := calc
      |w.im - z.im| = |(w - z).im| := by simp [Complex.sub_im]
      _ ≤ ‖w - z‖ := abs_im_le_norm _
      _ = dist w z := (dist_eq_norm _ _).symm
      _ = z.im / 2 := hdist
    have hwA : A ≤ w.im := by
      linarith [(abs_le.mp habs).1, le_max_left A 0]
    simpa [ofComplex_apply_of_im_pos hwpos] using
      hMA ⟨w, hwpos⟩ hwA
  have hz1 : 1 ≤ z.im := by
    linarith [le_max_right A 0]
  have hM : 0 ≤ M :=
    le_trans (norm_nonneg _) (hMA z (by linarith [le_max_left A 0]))
  calc
    ‖D f z‖ ≤ M / (2 * π * (z.im / 2)) :=
      norm_normalizedDeriv_le_of_sphere_bound hR hDiff hsphere
    _ = M / (π * z.im) := by ring
    _ ≤ M / (π * 1) := by gcongr
    _ = M / π := by ring

/-- The normalized derivative of a bounded holomorphic function tends to
zero at the infinite cusp.  This is the vanishing version of the preceding
Cauchy estimate. -/
theorem normalizedDeriv_tendsto_zero_of_bounded
    {f : ℍ → ℂ} (hf : MDiff f)
    (hbdd : IsBoundedAtImInfty f) :
    Tendsto (D f) atImInfty (𝓝 0) := by
  obtain ⟨M, A, hMA⟩ :=
    UpperHalfPlane.isBoundedAtImInfty_iff.mp hbdd
  suffices
      h :
        ∀ᶠ z : ℍ in atImInfty,
          ‖D f z‖ ≤ M / (π * z.im) by
    apply squeeze_zero_norm' h
    have him :
        Tendsto (fun z : ℍ ↦ z.im) atImInfty atTop := by
      rw [UpperHalfPlane.atImInfty]
      exact tendsto_comap
    have ht :=
      him.inv_tendsto_atTop.const_mul (M / π)
    simp only [Pi.inv_apply, mul_zero] at ht
    exact ht.congr fun z ↦ by field_simp
  have hsphere :
      ∀ z : ℍ, 2 * max A 0 + 1 ≤ z.im →
        ∀ w ∈ Metric.sphere (z : ℂ) (z.im / 2),
          ‖(f ∘ ofComplex) w‖ ≤ M := by
    intro z hz w hw
    have hwpos :
        0 < w.im :=
      closedBall_center_subset_upperHalfPlane z
        (Metric.sphere_subset_closedBall hw)
    have hdist : dist w z = z.im / 2 :=
      Metric.mem_sphere.mp hw
    have habs : |w.im - z.im| ≤ z.im / 2 := calc
      |w.im - z.im| = |(w - z).im| := by simp [Complex.sub_im]
      _ ≤ ‖w - z‖ := abs_im_le_norm _
      _ = dist w z := (dist_eq_norm _ _).symm
      _ = z.im / 2 := hdist
    have hwA : A ≤ w.im := by
      linarith [(abs_le.mp habs).1, le_max_left A 0]
    simpa [ofComplex_apply_of_im_pos hwpos] using
      hMA ⟨w, hwpos⟩ hwA
  rw [Filter.eventually_iff_exists_mem]
  refine
    ⟨{z : ℍ | 2 * max A 0 + 1 ≤ z.im},
      (atImInfty_mem _).mpr ⟨_, fun _ hz ↦ hz⟩,
      fun z hz ↦ ?_⟩
  calc
    ‖D f z‖
        ≤ M / (2 * π * (z.im / 2)) :=
      norm_normalizedDeriv_le_of_sphere_bound
        (by linarith [z.im_pos])
        (diffContOnCl_comp_ofComplex_of_mdifferentiable hf
          (closedBall_center_subset_upperHalfPlane z))
        (hsphere z hz)
    _ = M / (π * z.im) := by ring

/-- Hence every Serre derivative of a bounded holomorphic function is
bounded at infinity. -/
theorem serreDerivative_isBoundedAtImInfty_of_bounded
    {f : ℍ → ℂ} (k : ℂ) (hf : MDiff f)
    (hbdd : IsBoundedAtImInfty f) :
    IsBoundedAtImInfty (Derivative.serreDerivative k f) := by
  simp only [Derivative.serreDerivative_eq]
  have hD : IsBoundedAtImInfty (D f) :=
    normalizedDeriv_isBoundedAtImInfty_of_bounded hf hbdd
  have hconst :
      IsBoundedAtImInfty (fun _ : ℍ ↦ k * 12⁻¹) :=
    Filter.const_boundedAtFilter _ _
  have hproduct :
      IsBoundedAtImInfty
        (fun z ↦ (k * 12⁻¹) * (EisensteinSeries.E2 z * f z)) :=
    hconst.mul (e2_isBoundedAtImInfty.mul hbdd)
  have hproduct' :
      IsBoundedAtImInfty
        (fun z ↦ k * 12⁻¹ * EisensteinSeries.E2 z * f z) := by
    simpa only [mul_assoc] using hproduct
  exact hD.sub hproduct'

/-! ## Limits of bundled level-one modular forms -/

/-- A bundled modular form tends to the value of its holomorphic
q-expansion at the cusp. -/
theorem modularForm_tendsto_valueAtInfty
    {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    Tendsto (f : ℍ → ℂ) atImInfty
      (𝓝 (UpperHalfPlane.valueAtInfty (f : ℍ → ℂ))) := by
  obtain ⟨c, hc, hO⟩ :=
    ModularFormClass.exp_decay_sub_atImInfty' f
  have hexp :
      Tendsto (fun z : ℍ ↦ Real.exp (-c * z.im))
        atImInfty (𝓝 0) := by
    have hlin :
        Tendsto (fun y : ℝ ↦ -c * y) atTop atBot := by
      simpa using
        Filter.tendsto_id.const_mul_atTop_of_neg
          (neg_neg_of_pos hc)
    have him :
        Tendsto (fun z : ℍ ↦ z.im) atImInfty atTop := by
      rw [UpperHalfPlane.atImInfty]
      exact tendsto_comap
    exact Real.tendsto_exp_atBot.comp
      (hlin.comp him)
  have hsub :=
    hO.trans_tendsto hexp
  simpa using
    hsub.add_const
      (UpperHalfPlane.valueAtInfty (f : ℍ → ℂ))

/-- Equivalent q-expansion formulation of the preceding limit. -/
theorem modularForm_tendsto_qExpansion_constant
    {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    Tendsto (f : ℍ → ℂ) atImInfty
      (𝓝 ((UpperHalfPlane.qExpansion 1 (f : ℍ → ℂ)).coeff 0)) := by
  have hcoeff :
      (UpperHalfPlane.qExpansion 1 (f : ℍ → ℂ)).coeff 0 =
        UpperHalfPlane.valueAtInfty (f : ℍ → ℂ) :=
    UpperHalfPlane.qExpansion_coeff_zero one_pos
      (ModularFormClass.analyticAt_cuspFunction_zero f one_pos
        one_mem_strictPeriods_SL)
      (SlashInvariantFormClass.periodic_comp_ofComplex f
        one_mem_strictPeriods_SL)
  rw [hcoeff]
  exact modularForm_tendsto_valueAtInfty f

/-- Every normalized even Eisenstein series tends to its normalized
constant term `1`. -/
theorem eisensteinSeries_tendsto_one_atImInfty
    {k : ℕ} (hk : 3 ≤ k) (heven : Even k) :
    Tendsto (ModularForm.E hk : ℍ → ℂ)
      atImInfty (𝓝 1) := by
  simpa [EisensteinSeries.E_qExpansion_coeff_zero hk heven] using
    modularForm_tendsto_qExpansion_constant (ModularForm.E hk)

end

end HGAS.Modular
