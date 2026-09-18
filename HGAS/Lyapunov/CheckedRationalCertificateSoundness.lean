import HGAS.Lyapunov.HomogeneousRationalBounds
import HGAS.Lyapunov.RationalCertificateEnumeration
import HGAS.Dynamics.LyapunovForwardCompleteness
import Mathlib.Tactic

/-!
# Semantic soundness of the finite rational-certificate checker

`RationalCertificateEnumeration` defines a primitive-recursive Boolean
checker.  This file connects an accepted finite code to the analytic
Lyapunov theorem.

The first theorem below keeps forward completeness explicit so that its
quadratic comparison argument is reusable.  Later in this same file,
`forwardComplete_of_checkRationalLyapunov` discharges that hypothesis from
the coercive certificate itself, using the cutoff continuation theorem from
`LyapunovForwardCompleteness`.  This distinction matters: general polynomial
ODEs can blow up in finite time, so forward completeness must be proved, not
silently built into GAS.
-/

namespace HGAS

open MvPolynomial

noncomputable section

variable {n : ℕ}

/-- The value-margin part of an accepted certificate gives a positive
quadratic lower bound in the ambient finite-product norm, including at the
origin. -/
theorem checkedRationalLyapunov_lower_bound
    (F : PolynomialFieldCode n)
    (candidate : RationalLyapunovCandidate n)
    (hcheck : checkRationalLyapunov F candidate = true) :
    ∀ x : Fin n → ℝ,
      ((valueCertificateOfCheck F candidate hcheck).epsilon : ℝ) *
          dist x 0 ^ 2 ≤
        rationalLyapunovValue
          (PolynomialCode.decode candidate.numerator)
          candidate.denominatorExponent x := by
  let cert := valueCertificateOfCheck F candidate hcheck
  have hp :
      (PolynomialCode.decode candidate.numerator).IsHomogeneous
        (2 * (candidate.denominatorExponent + 1)) :=
    cert.target_isHomogeneous
  intro x
  by_cases hx : x = 0
  · subst x
    simp [rationalLyapunovValue_zero_of_isHomogeneous hp]
  calc
    (cert.epsilon : ℝ) * dist x 0 ^ 2 =
        (cert.epsilon : ℝ) * ‖x‖ ^ 2 := by
          rw [dist_zero_right]
    _ ≤ (cert.epsilon : ℝ) * normSq x :=
      mul_le_mul_of_nonneg_left (norm_sq_le_normSq x)
        cert.real_epsilon_pos.le
    _ ≤ rationalLyapunovValue
          (PolynomialCode.decode candidate.numerator)
          candidate.denominatorExponent x :=
      cert.value_lower_bound_of_ne_zero hx

/-- The checked Lyapunov value is nonnegative everywhere. -/
theorem checkedRationalLyapunov_nonneg
    (F : PolynomialFieldCode n)
    (candidate : RationalLyapunovCandidate n)
    (hcheck : checkRationalLyapunov F candidate = true) :
    ∀ x : Fin n → ℝ,
      0 ≤ rationalLyapunovValue
        (PolynomialCode.decode candidate.numerator)
        candidate.denominatorExponent x := by
  intro x
  have hlower :=
    checkedRationalLyapunov_lower_bound F candidate hcheck x
  exact le_trans
    (mul_nonneg
      (valueCertificateOfCheck F candidate hcheck).real_epsilon_pos.le
      (sq_nonneg (dist x 0)))
    hlower

/-- Soundness of the complete finite checker, assuming forward completeness
of the realized field and the equilibrium identity.

Every remaining hypothesis of `rationalCertificate_gas` is derived from the
two exact SOS-margin identities stored in the finite candidate. -/
theorem globallyAsymptoticallyStable_of_checkRationalLyapunov_of_forwardComplete
    (F : PolynomialFieldCode n)
    (candidate : RationalLyapunovCandidate n)
    (hcheck : checkRationalLyapunov F candidate = true)
    (hequilibrium :
      (PolynomialFieldCode.realize F :
        (Fin n → ℝ) → (Fin n → ℝ)) 0 = 0)
    (hcomplete :
      ForwardComplete
        (PolynomialFieldCode.realize F :
          (Fin n → ℝ) → (Fin n → ℝ))) :
    GloballyAsymptoticallyStable
      (PolynomialFieldCode.realize F :
        (Fin n → ℝ) → (Fin n → ℝ)) 0 := by
  let p := PolynomialCode.decode candidate.numerator
  let r := candidate.denominatorExponent
  let valueCert := valueCertificateOfCheck F candidate hcheck
  let decayCert := decayCertificateOfCheck F candidate hcheck
  have hp : p.IsHomogeneous (2 * (r + 1)) :=
    valueCert.target_isHomogeneous
  obtain ⟨B, hB, habs⟩ :=
    exists_rationalLyapunovValue_quadratic_bound hp
  let ε : ℝ := valueCert.epsilon
  have hε : 0 < ε := valueCert.real_epsilon_pos
  let b : ℝ := max B ε⁻¹
  have hb : 0 < b :=
    lt_of_lt_of_le hB (le_max_left _ _)
  have hVnonneg : ∀ x : Fin n → ℝ,
      0 ≤ rationalLyapunovValue p r x := by
    simpa [p, r, valueCert] using
      checkedRationalLyapunov_nonneg F candidate hcheck
  have hlower : ∀ x : Fin n → ℝ,
      ε * dist x 0 ^ 2 ≤ rationalLyapunovValue p r x := by
    simpa [p, r, valueCert, ε] using
      checkedRationalLyapunov_lower_bound F candidate hcheck
  have hupper : ∀ x : Fin n → ℝ,
      rationalLyapunovValue p r x ≤ b * dist x 0 ^ 2 := by
    intro x
    calc
      rationalLyapunovValue p r x ≤
          |rationalLyapunovValue p r x| :=
        le_abs_self _
      _ ≤ B * ‖x‖ ^ 2 := habs x
      _ ≤ b * ‖x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _)
          (sq_nonneg ‖x‖)
      _ = b * dist x 0 ^ 2 := by rw [dist_zero_right]
  have hstableLower : ∀ x : Fin n → ℝ,
      dist x 0 ^ 2 ≤ b * rationalLyapunovValue p r x := by
    intro x
    have hbase :
        dist x 0 ^ 2 ≤ ε⁻¹ * rationalLyapunovValue p r x := by
      rw [inv_mul_eq_div]
      exact (le_div_iff₀ hε).2 (by simpa [mul_comm] using hlower x)
    exact hbase.trans
      (mul_le_mul_of_nonneg_right (le_max_right B ε⁻¹)
        (hVnonneg x))
  have hupperRho : ∀ x : Fin n → ℝ,
      rationalLyapunovValue p r x ≤ B * normSq x := by
    intro x
    calc
      rationalLyapunovValue p r x ≤
          |rationalLyapunovValue p r x| := le_abs_self _
      _ ≤ B * ‖x‖ ^ 2 := habs x
      _ ≤ B * normSq x :=
        mul_le_mul_of_nonneg_left (norm_sq_le_normSq x) hB.le
  have hzeroDerivative :
      ∀ {x₀ : Fin n → ℝ} {γ : ℝ → (Fin n → ℝ)} {t : ℝ},
        IsForwardTrajectory
          (PolynomialFieldCode.realize F :
            (Fin n → ℝ) → (Fin n → ℝ))
          γ x₀ →
        0 < t → γ t = 0 →
        HasDerivAt (fun s ↦ rationalLyapunovValue p r (γ s)) 0 t := by
    intro x₀ γ t hγ ht hγzero
    have hγt :
        HasDerivAt γ
          (PolynomialFieldCode.realize F (γ t)) t :=
      (hγ.2 t ht.le).hasDerivAt (Ici_mem_nhds ht)
    have hVat :
        HasFDerivAt (rationalLyapunovValue p r)
          (0 : (Fin n → ℝ) →L[ℝ] ℝ) (γ t) := by
      simpa [hγzero] using
        hasFDerivAt_rationalLyapunovValue_zero hp
    have hcomp := hVat.comp_hasDerivAt t hγt
    simpa using hcomp
  apply rationalCertificate_gas
    (PolynomialFieldCode.decode F) p r hequilibrium hcomplete
    hb hε (continuous_rationalLyapunovValue hp)
    hstableLower hupper hlower
  · intro x
    exact decayCert.numerator_nonneg x
  · exact decayCert.numerator_level_of_upper
      (denominatorExponent_le_decayExponent_of_check
        F candidate hcheck)
      hB hupperRho
  · exact hzeroDerivative

/-! ## Discharging forward completeness from the same certificate -/

/-- Every sparse rational polynomial field denotes a `C¹` real vector
field. -/
theorem contDiff_polynomialFieldCode_realize
    (F : PolynomialFieldCode n) :
    ContDiff ℝ 1 (PolynomialFieldCode.realize F) := by
  rw [contDiff_pi]
  intro i
  have hfun :
      (fun x ↦ PolynomialFieldCode.realize F x i) =
        ratMvPolynomialEval (PolynomialCode.decode (F i)) := by
    funext x
    rw [PolynomialFieldCode.realize_apply,
      ratMvPolynomialEval_eq_eval₂Hom]
  rw [hfun]
  exact (contDiff_ratMvPolynomialEval
    (PolynomialCode.decode (F i))).of_le (by simp)

set_option maxHeartbeats 800000 in
-- Comparing the two independently derived directional derivatives unfolds
-- several nested sparse-code decoders and benefits from a larger budget.
/-- An accepted rational certificate makes its Lyapunov value
nonincreasing in the exact Fréchet-derivative sense needed by the cutoff
continuation theorem. -/
theorem fderiv_rationalLyapunov_nonpos_of_check
    (F : PolynomialFieldCode n)
    (candidate : RationalLyapunovCandidate n)
    (hcheck : checkRationalLyapunov F candidate = true) :
    ∀ x : Fin n → ℝ,
      fderiv ℝ
          (rationalLyapunovValue
            (PolynomialCode.decode candidate.numerator)
            candidate.denominatorExponent)
          x (PolynomialFieldCode.realize F x) ≤ 0 := by
  let p := PolynomialCode.decode candidate.numerator
  let r := candidate.denominatorExponent
  let valueCert := valueCertificateOfCheck F candidate hcheck
  let decayCert := decayCertificateOfCheck F candidate hcheck
  have hp : p.IsHomogeneous (2 * (r + 1)) :=
    valueCert.target_isHomogeneous
  have hVdiff :
      Differentiable ℝ (rationalLyapunovValue p r) :=
    differentiable_rationalLyapunovValue hp
  intro x
  by_cases hx : x = 0
  · subst x
    have hfderiv :=
      (hasFDerivAt_rationalLyapunovValue_zero hp).fderiv
    rw [hfderiv]
    simp
  · let v : Fin n → ℝ := PolynomialFieldCode.realize F x
    let γ : ℝ → (Fin n → ℝ) := fun t ↦ x + t • v
    have hγ : HasDerivAt γ v 0 := by
      have hv : HasDerivAt (fun t : ℝ ↦ t • v) v 0 := by
        simpa using
          ((hasDerivAt_id' (0 : ℝ)).smul_const v)
      have h := hv.const_add x
      change HasDerivAt (fun t : ℝ ↦ x + t • v) v 0 at h
      exact h
    have hγzero : γ 0 = x := by
      simp [γ]
    have hγfield :
        HasDerivAt γ
          (evalPolynomialField
            (PolynomialFieldCode.decode F) (γ 0)) 0 := by
      rw [hγzero]
      simpa [v, PolynomialFieldCode.realize] using hγ
    have halong :
        HasDerivAt
          (fun t ↦ rationalLyapunovValue p r (γ t))
          (-rationalLyapunovDecay
            (PolynomialFieldCode.decode F) p r x) 0 := by
      have h :=
        hasDerivAt_rationalLyapunovValue_along_field
          (PolynomialFieldCode.decode F) p r hγfield
          (hγzero ▸ hx)
      rw [hγzero] at h
      exact h
    have hchain :
        HasDerivAt
          (fun t ↦ rationalLyapunovValue p r (γ t))
          (fderiv ℝ (rationalLyapunovValue p r) x v) 0 := by
      have h :=
        (hVdiff (γ 0)).hasFDerivAt.comp_hasDerivAt 0 hγ
      rw [hγzero] at h
      exact h
    have heq :
        fderiv ℝ (rationalLyapunovValue p r) x v =
          -rationalLyapunovDecay
            (PolynomialFieldCode.decode F) p r x :=
      hchain.unique halong
    change
      fderiv ℝ (rationalLyapunovValue p r) x v ≤ 0
    rw [heq]
    exact neg_nonpos.mpr
      (rationalLyapunovDecay_nonneg
        (PolynomialFieldCode.decode F) p r x
        (decayCert.numerator_nonneg x))

/-- Forward completeness is a theorem of an accepted certificate, not an
extra assumption.  The proof applies the generic smooth-cutoff continuation
argument to the checked quadratic lower bound and decay identity. -/
theorem forwardComplete_of_checkRationalLyapunov
    (F : PolynomialFieldCode n)
    (candidate : RationalLyapunovCandidate n)
    (hcheck : checkRationalLyapunov F candidate = true) :
    ForwardComplete (PolynomialFieldCode.realize F) := by
  let p := PolynomialCode.decode candidate.numerator
  let r := candidate.denominatorExponent
  let valueCert := valueCertificateOfCheck F candidate hcheck
  have hp : p.IsHomogeneous (2 * (r + 1)) :=
    valueCert.target_isHomogeneous
  apply forwardComplete_of_coercive_lyapunov
    (PolynomialFieldCode.realize F)
    (rationalLyapunovValue p r)
    (contDiff_polynomialFieldCode_realize F)
    (differentiable_rationalLyapunovValue hp)
    valueCert.real_epsilon_pos
  · intro x
    simpa [p, r, valueCert, dist_zero_right] using
      checkedRationalLyapunov_lower_bound F candidate hcheck x
  · exact fderiv_rationalLyapunov_nonpos_of_check
      F candidate hcheck

/-- Full semantic soundness of the primitive-recursive rational Lyapunov
checker.  Homogeneity of the input field is needed only to establish the
origin as an equilibrium; callers may supply that identity directly. -/
theorem globallyAsymptoticallyStable_of_checkRationalLyapunov
    (F : PolynomialFieldCode n)
    (candidate : RationalLyapunovCandidate n)
    (hcheck : checkRationalLyapunov F candidate = true)
    (hequilibrium : PolynomialFieldCode.realize F 0 = 0) :
    GloballyAsymptoticallyStable
      (PolynomialFieldCode.realize F) 0 :=
  globallyAsymptoticallyStable_of_checkRationalLyapunov_of_forwardComplete
    F candidate hcheck hequilibrium
      (forwardComplete_of_checkRationalLyapunov F candidate hcheck)

/-- A sparse field whose decoded coordinates are homogeneous of one
positive degree has the origin as an equilibrium. -/
theorem polynomialFieldCode_realize_zero_of_homogeneous
    (F : PolynomialFieldCode n) {d : ℕ} (hd : 0 < d)
    (hhomogeneous :
      ∀ i : Fin n,
        (PolynomialCode.decode (F i)).IsHomogeneous d) :
    PolynomialFieldCode.realize F 0 = 0 := by
  funext i
  rw [PolynomialFieldCode.realize_apply,
    ← ratMvPolynomialEval_eq_eval₂Hom]
  exact ratMvPolynomialEval_zero_of_isHomogeneous
    (hhomogeneous i) hd

/-- Paper-facing soundness statement for a valid positive-degree
homogeneous input code. -/
theorem globallyAsymptoticallyStable_of_check_of_homogeneous
    (F : PolynomialFieldCode n) {d : ℕ} (hd : 0 < d)
    (hhomogeneous :
      ∀ i : Fin n,
        (PolynomialCode.decode (F i)).IsHomogeneous d)
    (candidate : RationalLyapunovCandidate n)
    (hcheck : checkRationalLyapunov F candidate = true) :
    GloballyAsymptoticallyStable
      (PolynomialFieldCode.realize F) 0 :=
  globallyAsymptoticallyStable_of_checkRationalLyapunov
    F candidate hcheck
      (polynomialFieldCode_realize_zero_of_homogeneous
        F hd hhomogeneous)

end

end HGAS
