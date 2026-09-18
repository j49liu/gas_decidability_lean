import HGAS.Lyapunov.GridRationalCertificate
import HGAS.Analysis.StrictPolynomialPositivity
import HGAS.Dynamics.LyapunovForwardCompleteness
import Mathlib.Tactic

/-!
# Analytic soundness of exact-grid rational Lyapunov certificates

This file proves the analytic half of the exact-grid certificate method.
Its central theorem says:

> If `p` has degree `2(r+1)`, `p(x)>0` away from zero, and the compiled
> decay numerator `q(F,p,r)` is positive away from zero, then
> `V=p/ρ^r` proves global asymptotic stability.

The proof keeps every standard ODE step visible.

1. Compactness of the unit sphere gives a positive lower bound for `V`.
   Two-homogeneity scales it to a global quadratic coercivity bound.
2. The same compactness argument gives a positive lower bound for
   `q/ρ^(r+1)` on the unit sphere.
3. Homogeneity scales that decay by `‖x‖^(d+1)`.  A positive Lyapunov
   superlevel is bounded away from the origin, so the decay has a uniform
   positive lower bound there.
4. Coercivity and nonincrease give forward completeness by the smooth
   cutoff argument in `LyapunovForwardCompleteness`.
5. The quantitative direct Lyapunov theorem gives stability and global
   attraction.

The final corollary applies this semantic theorem to the finite exact-grid
checker from `GridRationalCertificate`.
-/

namespace HGAS

open Set MvPolynomial

noncomputable section

variable {n : ℕ}

/-! ## Uniform value bounds -/

/-- Strict positivity of the numerator gives a positive minimum of the
rational Lyapunov value on the unit sphere. -/
theorem exists_pos_lower_bound_rationalLyapunovValue_on_unitSphere
    {p : MvPolynomial (Fin n) ℚ} {r : ℕ}
    (hp : p.IsHomogeneous (2 * (r + 1)))
    (hpos : ∀ x : Fin n → ℝ, x ≠ 0 →
      0 < ratMvPolynomialEval p x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : Fin n → ℝ, ‖x‖ = 1 →
      ε ≤ rationalLyapunovValue p r x := by
  obtain ⟨ε, hε, hbound⟩ :=
    (isCompact_sphere (0 : Fin n → ℝ) 1).exists_forall_le'
      (continuous_rationalLyapunovValue hp).continuousOn
      (a := 0) (by
        intro x hx
        have hxnorm : ‖x‖ = 1 := by
          simpa [Metric.mem_sphere, dist_zero_right] using hx
        have hxne : x ≠ 0 := by
          intro hzero
          subst x
          simp at hxnorm
        exact div_pos (hpos x hxne)
          (pow_pos (normSq_pos_of_ne_zero hxne) r))
  refine ⟨ε, hε, ?_⟩
  intro x hx
  exact hbound x (by
    simpa [Metric.mem_sphere, dist_zero_right] using hx)

/-- A positive two-homogeneous rational Lyapunov value has a global
quadratic lower bound. -/
theorem exists_rationalLyapunovValue_positive_quadratic_bound
    {p : MvPolynomial (Fin n) ℚ} {r : ℕ}
    (hp : p.IsHomogeneous (2 * (r + 1)))
    (hpos : ∀ x : Fin n → ℝ, x ≠ 0 →
      0 < ratMvPolynomialEval p x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : Fin n → ℝ,
      ε * ‖x‖ ^ 2 ≤ rationalLyapunovValue p r x := by
  obtain ⟨ε, hε, hunit⟩ :=
    exists_pos_lower_bound_rationalLyapunovValue_on_unitSphere hp hpos
  refine ⟨ε, hε, ?_⟩
  intro x
  by_cases hx : x = 0
  · subst x
    simp [rationalLyapunovValue_zero_of_isHomogeneous hp]
  let y : Fin n → ℝ := ‖x‖⁻¹ • x
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hynorm : ‖y‖ = 1 := by
    simp [y, norm_smul, hxnorm.ne']
  have hxy : ‖x‖ • y = x := by
    simp [y, smul_smul, hxnorm.ne']
  have hscale :
      rationalLyapunovValue p r x =
        ‖x‖ ^ 2 * rationalLyapunovValue p r y := by
    calc
      rationalLyapunovValue p r x =
          rationalLyapunovValue p r (‖x‖ • y) := by rw [hxy]
      _ = ‖x‖ ^ 2 * rationalLyapunovValue p r y :=
        rationalLyapunovValue_smul hp y hxnorm.ne'
  rw [hscale]
  simpa [mul_comm] using
    (mul_le_mul_of_nonneg_left (hunit y hynorm)
      (sq_nonneg ‖x‖))

/-! ## Uniform decay bounds -/

/-- The rational decay quotient is continuous at every nonzero point. -/
theorem continuousAt_rationalLyapunovDecay_of_ne_zero
    (F : PolynomialField n) (p : MvPolynomial (Fin n) ℚ)
    (r : ℕ) {x : Fin n → ℝ} (hx : x ≠ 0) :
    ContinuousAt (rationalLyapunovDecay F p r) x := by
  unfold rationalLyapunovDecay
  have hnormSq :
      Continuous (normSq : (Fin n → ℝ) → ℝ) := by
    unfold normSq dot
    fun_prop
  apply ContinuousAt.div
    (contDiff_ratMvPolynomialEval
      (rationalLyapunovNumerator F p r)).continuous.continuousAt
    (hnormSq.pow (r + 1)).continuousAt
  exact pow_ne_zero (r + 1) (normSq_pos_of_ne_zero hx).ne'

/-- A strictly positive homogeneous numerator gives a positive minimum of
the analytic decay quotient on the unit sphere. -/
theorem exists_pos_lower_bound_rationalLyapunovDecay_on_unitSphere
    (F : PolynomialField n) (p : MvPolynomial (Fin n) ℚ) (r : ℕ)
    (hqpos : ∀ x : Fin n → ℝ, x ≠ 0 →
      0 < ratMvPolynomialEval
        (rationalLyapunovNumerator F p r) x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : Fin n → ℝ, ‖x‖ = 1 →
      δ ≤ rationalLyapunovDecay F p r x := by
  have hcontinuous :
      ContinuousOn (rationalLyapunovDecay F p r)
        (Metric.sphere (0 : Fin n → ℝ) 1) := by
    intro x hx
    have hxnorm : ‖x‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using hx
    have hxne : x ≠ 0 := by
      intro hzero
      subst x
      simp at hxnorm
    exact
      (continuousAt_rationalLyapunovDecay_of_ne_zero
        F p r hxne).continuousWithinAt
  obtain ⟨δ, hδ, hbound⟩ :=
    (isCompact_sphere (0 : Fin n → ℝ) 1).exists_forall_le'
      hcontinuous (a := 0) (by
        intro x hx
        have hxnorm : ‖x‖ = 1 := by
          simpa [Metric.mem_sphere, dist_zero_right] using hx
        have hxne : x ≠ 0 := by
          intro hzero
          subst x
          simp at hxnorm
        exact div_pos (hqpos x hxne)
          (pow_pos (normSq_pos_of_ne_zero hxne) (r + 1)))
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  exact hbound x (by
    simpa [Metric.mem_sphere, dist_zero_right] using hx)

/-- Scaling law for the decay quotient.  If `F` has degree `d` and `p`
has degree `2(r+1)`, its numerator has degree `2r+d+3`; division by
`ρ^(r+1)` leaves degree `d+1`. -/
theorem rationalLyapunovDecay_smul_of_numerator_isHomogeneous
    {F : PolynomialField n} {p : MvPolynomial (Fin n) ℚ}
    {r d : ℕ}
    (hq :
      (rationalLyapunovNumerator F p r).IsHomogeneous
        (2 * r + d + 3))
    (x : Fin n → ℝ) (hx : x ≠ 0)
    {c : ℝ} (hc : c ≠ 0) :
    rationalLyapunovDecay F p r (c • x) =
      c ^ (d + 1) * rationalLyapunovDecay F p r x := by
  have hρ : normSq x ≠ 0 := (normSq_eq_zero_iff x).not.mpr hx
  rw [rationalLyapunovDecay, rationalLyapunovDecay,
    ratMvPolynomialEval_eq_eval₂Hom,
    MvPolynomial.IsHomogeneous.eval₂Hom_smul hq
      (algebraMap ℚ ℝ) x c,
    normSq_smul,
    ratMvPolynomialEval_eq_eval₂Hom]
  field_simp [hc, hρ]
  ring

/-- On every positive Lyapunov superlevel, strict homogeneous decay is
bounded below by one positive constant. -/
theorem rationalLyapunovDecay_positive_on_superlevels
    {F : PolynomialField n} {p : MvPolynomial (Fin n) ℚ}
    {r d : ℕ}
    (hp : p.IsHomogeneous (2 * (r + 1)))
    (hq :
      (rationalLyapunovNumerator F p r).IsHomogeneous
        (2 * r + d + 3))
    (hqpos : ∀ x : Fin n → ℝ, x ≠ 0 →
      0 < ratMvPolynomialEval
        (rationalLyapunovNumerator F p r) x)
    {B : ℝ} (hB : 0 < B)
    (hupper : ∀ x : Fin n → ℝ,
      rationalLyapunovValue p r x ≤ B * ‖x‖ ^ 2) :
    ∀ η : ℝ, 0 < η →
      ∃ a : ℝ, 0 < a ∧ ∀ x : Fin n → ℝ,
        η ≤ rationalLyapunovValue p r x →
          a ≤ rationalLyapunovDecay F p r x := by
  obtain ⟨δ, hδ, hδunit⟩ :=
    exists_pos_lower_bound_rationalLyapunovDecay_on_unitSphere
      F p r hqpos
  intro η hη
  let s : ℝ := Real.sqrt (η / B)
  have hs : 0 < s := Real.sqrt_pos.2 (div_pos hη hB)
  let a : ℝ := δ * s ^ (d + 1)
  have ha : 0 < a := mul_pos hδ (pow_pos hs (d + 1))
  refine ⟨a, ha, ?_⟩
  intro x hxlevel
  have hxne : x ≠ 0 := by
    intro hzero
    subst x
    rw [rationalLyapunovValue_zero_of_isHomogeneous hp] at hxlevel
    linarith
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hxne
  have hnormsq : η / B ≤ ‖x‖ ^ 2 := by
    apply (div_le_iff₀ hB).2
    have := hxlevel.trans (hupper x)
    simpa [mul_comm] using this
  have hsSq : s ^ 2 = η / B := by
    dsimp [s]
    exact Real.sq_sqrt (div_nonneg hη.le hB.le)
  have hsnorm : s ≤ ‖x‖ := by
    nlinarith [hs.le, norm_nonneg x]
  let y : Fin n → ℝ := ‖x‖⁻¹ • x
  have hynorm : ‖y‖ = 1 := by
    simp [y, norm_smul, hxnorm.ne']
  have hyne : y ≠ 0 := by
    intro hy
    have : ‖y‖ = 0 := by rw [hy]; simp
    linarith
  have hxy : ‖x‖ • y = x := by
    simp [y, smul_smul, hxnorm.ne']
  have hscale :
      rationalLyapunovDecay F p r x =
        ‖x‖ ^ (d + 1) * rationalLyapunovDecay F p r y := by
    calc
      rationalLyapunovDecay F p r x =
          rationalLyapunovDecay F p r (‖x‖ • y) := by rw [hxy]
      _ = ‖x‖ ^ (d + 1) * rationalLyapunovDecay F p r y :=
        rationalLyapunovDecay_smul_of_numerator_isHomogeneous
          hq y hyne hxnorm.ne'
  have hpow : s ^ (d + 1) ≤ ‖x‖ ^ (d + 1) :=
    pow_le_pow_left₀ hs.le hsnorm (d + 1)
  calc
    a = δ * s ^ (d + 1) := rfl
    _ ≤ δ * ‖x‖ ^ (d + 1) :=
      mul_le_mul_of_nonneg_left hpow hδ.le
    _ ≤ rationalLyapunovDecay F p r y * ‖x‖ ^ (d + 1) :=
      mul_le_mul_of_nonneg_right (hδunit y hynorm)
        (pow_nonneg (norm_nonneg x) (d + 1))
    _ = rationalLyapunovDecay F p r x := by
      rw [hscale]
      ring

/-! ## Derivative and forward-completeness lemmas -/

/-- The Fréchet derivative of the rational Lyapunov value in the field
direction is exactly minus the compiled decay, including at the origin. -/
theorem fderiv_rationalLyapunovValue_apply_field
    (F : PolynomialField n) (p : MvPolynomial (Fin n) ℚ)
    (r : ℕ) (hp : p.IsHomogeneous (2 * (r + 1)))
    (x : Fin n → ℝ) :
    fderiv ℝ (rationalLyapunovValue p r) x
        (evalPolynomialField F x) =
      -rationalLyapunovDecay F p r x := by
  by_cases hx : x = 0
  · subst x
    rw [(hasFDerivAt_rationalLyapunovValue_zero hp).fderiv]
    simp
  · let v : Fin n → ℝ := evalPolynomialField F x
    let γ : ℝ → (Fin n → ℝ) := fun t ↦ x + t • v
    have hγ : HasDerivAt γ v 0 := by
      have hv : HasDerivAt (fun t : ℝ ↦ t • v) v 0 := by
        simpa using ((hasDerivAt_id' (0 : ℝ)).smul_const v)
      have h := hv.const_add x
      change HasDerivAt (fun t : ℝ ↦ x + t • v) v 0 at h
      exact h
    have hγzero : γ 0 = x := by simp [γ]
    have halong :
        HasDerivAt
          (fun t ↦ rationalLyapunovValue p r (γ t))
          (-rationalLyapunovDecay F p r x) 0 := by
      have hfield :
          HasDerivAt γ (evalPolynomialField F (γ 0)) 0 := by
        rw [hγzero]
        simpa [v] using hγ
      have h :=
        hasDerivAt_rationalLyapunovValue_along_field
          F p r hfield (hγzero ▸ hx)
      simpa [hγzero] using h
    have hchain :
        HasDerivAt
          (fun t ↦ rationalLyapunovValue p r (γ t))
          (fderiv ℝ (rationalLyapunovValue p r) x v) 0 := by
      have h :=
        (differentiable_rationalLyapunovValue hp (γ 0)).hasFDerivAt
          |>.comp_hasDerivAt 0 hγ
      simpa [hγzero] using h
    simpa [v] using hchain.unique halong

/-- Positivity of the compiled numerator makes the Lyapunov value
nonincreasing in the exact form required by the cutoff continuation
theorem. -/
theorem forwardComplete_of_positive_rationalLyapunov
    (F : PolynomialFieldCode n) (p : MvPolynomial (Fin n) ℚ)
    (r : ℕ)
    (hp : p.IsHomogeneous (2 * (r + 1)))
    (hpPos : ∀ x : Fin n → ℝ, x ≠ 0 →
      0 < ratMvPolynomialEval p x)
    (hqNonneg : ∀ x : Fin n → ℝ,
      0 ≤ ratMvPolynomialEval
        (rationalLyapunovNumerator
          (PolynomialFieldCode.decode F) p r) x) :
    ForwardComplete (PolynomialFieldCode.realize F) := by
  obtain ⟨ε, hε, hlower⟩ :=
    exists_rationalLyapunovValue_positive_quadratic_bound hp hpPos
  apply forwardComplete_of_coercive_lyapunov
    (PolynomialFieldCode.realize F)
    (rationalLyapunovValue p r)
    (contDiff_polynomialFieldCode_realize F)
    (differentiable_rationalLyapunovValue hp)
    hε hlower
  intro x
  change
    fderiv ℝ (rationalLyapunovValue p r) x
        (evalPolynomialField (PolynomialFieldCode.decode F) x) ≤ 0
  rw [fderiv_rationalLyapunovValue_apply_field
    (PolynomialFieldCode.decode F) p r hp x]
  exact neg_nonpos.mpr
    (rationalLyapunovDecay_nonneg
      (PolynomialFieldCode.decode F) p r x (hqNonneg x))

/-! ## Full semantic and checked soundness -/

/-- A positive rational homogeneous Lyapunov pair proves GAS. -/
theorem globallyAsymptoticallyStable_of_positive_rationalLyapunov
    {d r : ℕ} (hd : 0 < d)
    (F : PolynomialFieldCode n) (p : MvPolynomial (Fin n) ℚ)
    (hF : ∀ i : Fin n,
      (PolynomialCode.decode (F i)).IsHomogeneous d)
    (hp : p.IsHomogeneous (2 * (r + 1)))
    (hpPos : ∀ x : Fin n → ℝ, x ≠ 0 →
      0 < ratMvPolynomialEval p x)
    (hqPos : ∀ x : Fin n → ℝ, x ≠ 0 →
      0 < ratMvPolynomialEval
        (rationalLyapunovNumerator
          (PolynomialFieldCode.decode F) p r) x) :
    GloballyAsymptoticallyStable
      (PolynomialFieldCode.realize F) 0 := by
  let q :=
    rationalLyapunovNumerator (PolynomialFieldCode.decode F) p r
  have hq :
      q.IsHomogeneous (2 * r + d + 3) := by
    exact rationalLyapunovNumerator_isHomogeneous
      (PolynomialFieldCode.decode F) p r hF (by
        convert hp using 1)
  have hqdegree : 0 < 2 * r + d + 3 := by omega
  have hqNonneg : ∀ x : Fin n → ℝ,
      0 ≤ ratMvPolynomialEval q x := by
    intro x
    by_cases hx : x = 0
    · subst x
      rw [ratMvPolynomialEval_zero_of_isHomogeneous hq hqdegree]
    · exact (hqPos x hx).le
  obtain ⟨ε, hε, hlower⟩ :=
    exists_rationalLyapunovValue_positive_quadratic_bound hp hpPos
  obtain ⟨B, hB, habsUpper⟩ :=
    exists_rationalLyapunovValue_quadratic_bound hp
  let b : ℝ := max B ε⁻¹
  have hb : 0 < b :=
    lt_of_lt_of_le hB (le_max_left _ _)
  have hVnonneg : ∀ x : Fin n → ℝ,
      0 ≤ rationalLyapunovValue p r x := by
    intro x
    exact
      (mul_nonneg hε.le (sq_nonneg ‖x‖)).trans (hlower x)
  have hupperB : ∀ x : Fin n → ℝ,
      rationalLyapunovValue p r x ≤ B * ‖x‖ ^ 2 := by
    intro x
    exact (le_abs_self _).trans (habsUpper x)
  have hupper : ∀ x : Fin n → ℝ,
      rationalLyapunovValue p r x ≤ b * dist x 0 ^ 2 := by
    intro x
    rw [dist_zero_right]
    exact (hupperB x).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (sq_nonneg ‖x‖))
  have hstableLower : ∀ x : Fin n → ℝ,
      dist x 0 ^ 2 ≤ b * rationalLyapunovValue p r x := by
    intro x
    have hbase :
        ‖x‖ ^ 2 ≤ ε⁻¹ * rationalLyapunovValue p r x := by
      rw [inv_mul_eq_div]
      exact (le_div_iff₀ hε).2
        (by simpa [mul_comm] using hlower x)
    rw [dist_zero_right]
    exact hbase.trans
      (mul_le_mul_of_nonneg_right (le_max_right B ε⁻¹)
        (hVnonneg x))
  have hattractLower : ∀ x : Fin n → ℝ,
      ε * dist x 0 ^ 2 ≤ rationalLyapunovValue p r x := by
    intro x
    simpa [dist_zero_right] using hlower x
  have hcomplete :
      ForwardComplete (PolynomialFieldCode.realize F) :=
    forwardComplete_of_positive_rationalLyapunov
      F p r hp hpPos (by simpa [q] using hqNonneg)
  have hdecayNonneg : ∀ x : Fin n → ℝ,
      0 ≤ rationalLyapunovDecay
        (PolynomialFieldCode.decode F) p r x := by
    intro x
    exact rationalLyapunovDecay_nonneg
      (PolynomialFieldCode.decode F) p r x
      (by simpa [q] using hqNonneg x)
  have hdecayLevel :
      ∀ η : ℝ, 0 < η →
        ∃ a : ℝ, 0 < a ∧ ∀ x : Fin n → ℝ,
          η ≤ rationalLyapunovValue p r x →
            a ≤ rationalLyapunovDecay
              (PolynomialFieldCode.decode F) p r x :=
    rationalLyapunovDecay_positive_on_superlevels
      hp (by simpa [q] using hq) hqPos hB hupperB
  apply globallyAsymptoticallyStable_of_lyapunov_decay
    (PolynomialFieldCode.realize F) 0
    (rationalLyapunovValue p r)
    (rationalLyapunovDecay (PolynomialFieldCode.decode F) p r)
    (polynomialFieldCode_realize_zero_of_homogeneous F hd hF)
    hcomplete hb hε
    (continuous_rationalLyapunovValue hp)
    hstableLower hupper hattractLower hdecayNonneg hdecayLevel
  intro x₀ γ t hγ ht
  by_cases hx : γ t = 0
  · have hγt :
        HasDerivAt γ
          (PolynomialFieldCode.realize F (γ t)) t :=
      (hγ.2 t ht.le).hasDerivAt (Ici_mem_nhds ht)
    have hVat :
        HasFDerivAt (rationalLyapunovValue p r)
          (0 : (Fin n → ℝ) →L[ℝ] ℝ) (γ t) := by
      simpa [hx] using hasFDerivAt_rationalLyapunovValue_zero hp
    have hcomp := hVat.comp_hasDerivAt t hγt
    simpa [hx] using hcomp
  · have hγt :
        HasDerivAt γ
          (evalPolynomialField
            (PolynomialFieldCode.decode F) (γ t)) t := by
      simpa [PolynomialFieldCode.realize] using
        (hγ.2 t ht.le).hasDerivAt (Ici_mem_nhds ht)
    exact hasDerivAt_rationalLyapunovValue_along_field
      (PolynomialFieldCode.decode F) p r hγt hx

/-- Every accepted positive-degree exact-grid candidate is a genuine GAS
field. -/
theorem globallyAsymptoticallyStable_of_checkGridRationalLyapunov
    {d : ℕ} (hd : 0 < d)
    (F : PolynomialFieldCode n)
    (c : GridRationalLyapunovCandidate.Candidate n)
    (hcheck : checkGridRationalLyapunov d F c = true) :
    GloballyAsymptoticallyStable
      (PolynomialFieldCode.realize F) 0 := by
  obtain ⟨hF, hp, hpPos, hqPos⟩ :=
    semantic_of_checkGridRationalLyapunov hcheck
  exact globallyAsymptoticallyStable_of_positive_rationalLyapunov
    hd F
    (PolynomialCode.decode
      (GridRationalLyapunovCandidate.numerator c))
    hF hp hpPos hqPos

/-- Paper-facing soundness in the raw fixed-dimension, fixed-degree
language. -/
theorem hgasQ_of_checkGridRationalLyapunov
    {d : ℕ} (hd : 0 < d)
    (F : PolynomialFieldCode n)
    (c : GridRationalLyapunovCandidate.Candidate n)
    (hcheck : checkGridRationalLyapunov d F c = true) :
    HGASQ n d F := by
  have hvalid :=
    (checkGridRationalLyapunov_eq_true_iff d F c).mp hcheck |>.1
  exact
    ⟨hvalid,
      globallyAsymptoticallyStable_of_checkGridRationalLyapunov
        hd F c hcheck⟩

end

end HGAS
