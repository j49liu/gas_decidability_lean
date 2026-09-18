import HGAS.Modular.JacobiThetaJointLocalInverse
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Joint differentiability of the elliptic theta derivative

Mathlib defines the two-variable Jacobi theta function and its derivative
in the elliptic variable by normally convergent series.  It proves joint
continuity of the latter, but the moving-modulus Bloch calculation needs
joint differentiability.

This file supplies that missing regularity.  We differentiate each term
of the elliptic-derivative series.  On a local strip its derivative is
bounded by a Gaussian times `|n|³`, which is summable.  The standard
termwise Fréchet differentiation theorem then applies.
-/

namespace HGAS.Modular

open Complex Filter Real Set Topology

noncomputable section

/-- Fréchet derivative of one summand in the elliptic-derivative theta
series. -/
def jacobiTheta₂PrimeTermFDeriv
    (n : ℤ) (z τ : ℂ) :
    (ℂ × ℂ) →L[ℂ] ℂ :=
  (2 * π * I * n) •
    jacobiTheta₂_term_fderiv n z τ

/-- The jointly summed Fréchet derivative of the differentiated theta
series. -/
def jacobiTheta₂PrimeFDeriv
    (z τ : ℂ) :
    (ℂ × ℂ) →L[ℂ] ℂ :=
  ∑' n : ℤ,
    jacobiTheta₂PrimeTermFDeriv n z τ

theorem hasFDerivAt_jacobiTheta₂PrimeTerm
    (n : ℤ) (z τ : ℂ) :
    HasFDerivAt
      (fun p : ℂ × ℂ =>
        jacobiTheta₂'_term n p.1 p.2)
      (jacobiTheta₂PrimeTermFDeriv n z τ)
      (z, τ) := by
  simpa only [jacobiTheta₂'_term,
    jacobiTheta₂PrimeTermFDeriv, smul_eq_mul] using
    (hasFDerivAt_jacobiTheta₂_term n z τ).const_mul
      (2 * π * I * n)

/-- Cubic-polynomial Gaussian bound for the differentiated summand. -/
theorem norm_jacobiTheta₂PrimeTermFDeriv_le
    (n : ℤ) (z τ : ℂ) :
    ‖jacobiTheta₂PrimeTermFDeriv n z τ‖ ≤
      6 * π ^ 2 * |n| ^ 3 *
        ‖jacobiTheta₂_term n z τ‖ := by
  rw [jacobiTheta₂PrimeTermFDeriv, norm_smul]
  calc
    ‖(2 : ℂ) * π * I * (n : ℂ)‖ *
          ‖jacobiTheta₂_term_fderiv n z τ‖ ≤
        (2 * π * |n|) *
          (3 * π * |n| ^ 2 *
            ‖jacobiTheta₂_term n z τ‖) := by
      apply mul_le_mul
      · simp only [norm_mul, Complex.norm_two,
          Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos pi_pos, norm_I, norm_intCast,
          mul_one, Int.cast_abs]
        exact le_rfl
      · exact norm_jacobiTheta₂_term_fderiv_le n z τ
      · exact norm_nonneg _
      · positivity
    _ =
        6 * π ^ 2 * |n| ^ 3 *
          ‖jacobiTheta₂_term n z τ‖ := by
      ring

/-- The full joint Fréchet derivative of Mathlib's differentiated theta
series. -/
theorem hasFDerivAt_jacobiTheta₂Prime_joint
    (z τ : ℂ) (hτ : 0 < im τ) :
    HasFDerivAt
      (fun p : ℂ × ℂ =>
        jacobiTheta₂' p.1 p.2)
      (jacobiTheta₂PrimeFDeriv z τ)
      (z, τ) := by
  obtain ⟨T, hT, hτ'⟩ := exists_between hτ
  obtain ⟨S, hz⟩ := exists_gt |im z|
  let V : Set (ℂ × ℂ) :=
    {u | |im u| < S} ×ˢ {v | T < im v}
  have hVo : IsOpen V := by
    exact
      ((_root_.continuous_abs.comp continuous_im).isOpen_preimage
          (Set.Iio S) isOpen_Iio).prod
        (continuous_im.isOpen_preimage (Set.Ioi T) isOpen_Ioi)
  have hVp : IsPreconnected V := by
    refine (Convex.isPreconnected ?_).prod
      (convex_halfSpace_im_gt T).isPreconnected
    simpa only [abs_lt] using
      (convex_halfSpace_im_gt (-S)).inter
        (convex_halfSpace_im_lt S)
  let f : ℤ → ℂ × ℂ → ℂ :=
    fun n p => jacobiTheta₂'_term n p.1 p.2
  let f' : ℤ → ℂ × ℂ →
      (ℂ × ℂ →L[ℂ] ℂ) :=
    fun n p =>
      jacobiTheta₂PrimeTermFDeriv n p.1 p.2
  let u : ℤ → ℝ :=
    fun n =>
      6 * π ^ 2 * |n| ^ 3 *
        Real.exp
          (-π * (T * n ^ 2 - 2 * S * |n|))
  have hu : Summable u := by
    simp_rw [u, mul_assoc (6 * π ^ 2)]
    exact
      (summable_pow_mul_jacobiTheta₂_term_bound
        S hT 3).mul_left (6 * π ^ 2)
  have hfderiv :
      ∀ n p, p ∈ V →
        HasFDerivAt (f n) (f' n p) p := by
    intro n p _hp
    simpa only [f, f'] using
      hasFDerivAt_jacobiTheta₂PrimeTerm n p.1 p.2
  have hbound :
      ∀ n p, p ∈ V →
        ‖f' n p‖ ≤ u n := by
    intro n p hp
    exact
      (norm_jacobiTheta₂PrimeTermFDeriv_le
        n p.1 p.2).trans (by
          simp_rw [u, mul_assoc (6 * π ^ 2)]
          refine mul_le_mul_of_nonneg_left ?_
            (by positivity)
          refine mul_le_mul_of_nonneg_left ?_
            (pow_nonneg (Int.cast_nonneg
              (abs_nonneg n)) 3)
          exact
            norm_jacobiTheta₂_term_le hT
              (le_of_lt hp.1) (le_of_lt hp.2) n)
  have hsum :
      Summable (fun n => f n (z, τ)) := by
    simpa only [f] using
      (summable_jacobiTheta₂'_term_iff z τ).mpr hτ
  have hVmem : (z, τ) ∈ V := ⟨hz, hτ'⟩
  simpa only [jacobiTheta₂PrimeFDeriv, f'] using
    hasFDerivAt_tsum_of_isPreconnected
      hu hVo hVp hfderiv hbound
      hVmem hsum hVmem

/-- Mathlib's two-variable theta derivative is jointly differentiable
throughout the upper-half-plane region. -/
theorem differentiableAt_jacobiTheta₂Prime_joint
    (z τ : ℂ) (hτ : 0 < im τ) :
    DifferentiableAt ℂ
      (fun p : ℂ × ℂ =>
        jacobiTheta₂' p.1 p.2)
      (z, τ) :=
  (hasFDerivAt_jacobiTheta₂Prime_joint
    z τ hτ).differentiableAt

/-! ## Transfer to the four characteristic conventions

The remaining three derivatives are obtained from the basic series by
affine changes of variables, multiplication by an exponential, and
addition.  Keeping these lemmas separate makes the analytic series
argument above reusable independently of our choice of theta
characteristics. -/

theorem differentiableAt_jacobiTheta3Prime_joint
    (z τ : ℂ) (hτ : 0 < im τ) :
    DifferentiableAt ℂ
      (fun p : ℂ × ℂ =>
        jacobiTheta3Prime p.1 p.2)
      (z, τ) := by
  simpa only [jacobiTheta3Prime] using
    differentiableAt_jacobiTheta₂Prime_joint z τ hτ

theorem differentiableAt_jacobiTheta4Prime_joint
    (z τ : ℂ) (hτ : 0 < im τ) :
    DifferentiableAt ℂ
      (fun p : ℂ × ℂ =>
        jacobiTheta4Prime p.1 p.2)
      (z, τ) := by
  have haffine :
      DifferentiableAt ℂ
        (fun p : ℂ × ℂ =>
          (p.1 + 1 / 2, p.2))
        (z, τ) := by
    fun_prop
  simpa only [jacobiTheta4Prime,
    Function.comp_apply] using
    (differentiableAt_jacobiTheta₂Prime_joint
      (z + 1 / 2) τ hτ).comp
        (z, τ) haffine

theorem differentiableAt_jacobiTheta2Prime_joint
    (z τ : ℂ) (hτ : 0 < im τ) :
    DifferentiableAt ℂ
      (fun p : ℂ × ℂ =>
        jacobiTheta2Prime p.1 p.2)
      (z, τ) := by
  have haffine :
      DifferentiableAt ℂ
        (fun p : ℂ × ℂ =>
          (p.1 + p.2 / 2, p.2))
        (z, τ) := by
    fun_prop
  have htheta :
      DifferentiableAt ℂ
        (fun p : ℂ × ℂ =>
          jacobiTheta₂
            (p.1 + p.2 / 2) p.2)
        (z, τ) := by
    simpa only [Function.comp_apply] using
      (contDiffAt_one_jacobiTheta₂_joint
        (z + τ / 2) τ hτ).differentiableAt_one.comp
          (z, τ) haffine
  have hprime :
      DifferentiableAt ℂ
        (fun p : ℂ × ℂ =>
          jacobiTheta₂'
            (p.1 + p.2 / 2) p.2)
        (z, τ) := by
    simpa only [Function.comp_apply] using
      (differentiableAt_jacobiTheta₂Prime_joint
        (z + τ / 2) τ hτ).comp
          (z, τ) haffine
  have hexponential :
      DifferentiableAt ℂ
        (fun p : ℂ × ℂ =>
          cexp (π * I * (p.2 / 4 + p.1)))
        (z, τ) := by
    fun_prop
  simpa only [jacobiTheta2Prime] using
    hexponential.mul
      ((differentiableAt_const (c := π * I)).mul
          htheta |>.add hprime)

theorem differentiableAt_jacobiTheta1Prime_joint
    (z τ : ℂ) (hτ : 0 < im τ) :
    DifferentiableAt ℂ
      (fun p : ℂ × ℂ =>
        jacobiTheta1Prime p.1 p.2)
      (z, τ) := by
  have haffine :
      DifferentiableAt ℂ
        (fun p : ℂ × ℂ =>
          (p.1 + 1 / 2, p.2))
        (z, τ) := by
    fun_prop
  simpa only [jacobiTheta1Prime,
    Function.comp_apply] using
    ((differentiableAt_jacobiTheta2Prime_joint
      (z + 1 / 2) τ hτ).comp
        (z, τ) haffine).neg

/-- Every elliptic derivative coordinate of the four-theta vector is
jointly differentiable in the elliptic and modular variables. -/
theorem differentiableAt_jacobiThetaVectorPrime_component_joint
    (j : Fin 4) (z τ : ℂ) (hτ : 0 < im τ) :
    DifferentiableAt ℂ
      (fun p : ℂ × ℂ =>
        jacobiThetaVectorPrime p.1 p.2 j)
      (z, τ) := by
  fin_cases j
  · simpa only [jacobiThetaVectorPrime,
      Matrix.cons_val_zero] using
      differentiableAt_jacobiTheta1Prime_joint z τ hτ
  · simpa only [jacobiThetaVectorPrime,
      Matrix.cons_val_one, Matrix.cons_val_zero] using
      differentiableAt_jacobiTheta2Prime_joint z τ hτ
  · simpa only [jacobiThetaVectorPrime,
      Matrix.cons_val_one, Matrix.cons_val_zero] using
      differentiableAt_jacobiTheta3Prime_joint z τ hτ
  · simpa only [jacobiThetaVectorPrime,
      Matrix.cons_val_one, Matrix.cons_val_zero] using
      differentiableAt_jacobiTheta4Prime_joint z τ hτ

end

end HGAS.Modular
