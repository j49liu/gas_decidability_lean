import HGAS.Modular.JacobiThetaHeatEquationVector

/-!
# The differentiated theta heat equation

To establish the modular equation for the Jacobi derivative coordinate
`Delta`, one needs the heat equation differentiated once in the elliptic
variable.  We prove it directly from the normally convergent defining
series:

```
                  ∂w³ θ = 4 π i ∂τ(∂w θ).
```

The cubic Gaussian majorant is the same one used for joint
differentiability of `jacobiTheta₂'`.
-/

namespace HGAS.Modular

open Complex Real Filter Set Topology
open UpperHalfPlane hiding I

noncomputable section

/-- The termwise third elliptic derivative of Mathlib's theta series. -/
def jacobiTheta₂ThirdTerm
    (n : ℤ) (z τ : ℂ) : ℂ :=
  (2 * π * I * (n : ℂ)) ^ 3 *
    jacobiTheta₂_term n z τ

/-- The third elliptic derivative series. -/
def jacobiTheta₂Third
    (z τ : ℂ) : ℂ :=
  ∑' n : ℤ, jacobiTheta₂ThirdTerm n z τ

theorem summable_jacobiTheta₂ThirdTerm
    (z : ℂ) {τ : ℂ} (hτ : 0 < im τ) :
    Summable
      (fun n : ℤ =>
        jacobiTheta₂ThirdTerm n z τ) := by
  let b : ℤ → ℝ := fun n =>
    (|n| ^ 3 : ℝ) *
      Real.exp
        (-π *
          (im τ * n ^ 2 -
            2 * |im z| * |n|))
  let u : ℤ → ℝ := fun n =>
    8 * π ^ 3 * b n
  have hb : Summable b := by
    simpa only [b] using
      summable_pow_mul_jacobiTheta₂_term_bound
        |im z| hτ 3
  have hu : Summable u :=
    hb.mul_left (8 * π ^ 3)
  apply hu.of_norm_bounded
  intro n
  calc
    ‖jacobiTheta₂ThirdTerm n z τ‖ =
        8 * π ^ 3 * (↑|n| : ℝ) ^ 3 *
          ‖jacobiTheta₂_term n z τ‖ := by
      unfold jacobiTheta₂ThirdTerm
      rw [norm_mul, norm_pow]
      simp only [norm_mul, Complex.norm_two,
        norm_I, Complex.norm_of_nonneg pi_pos.le,
        norm_intCast, ← Int.cast_abs]
      ring_nf
    _ ≤
        8 * π ^ 3 * (↑|n| : ℝ) ^ 3 *
          Real.exp
            (-π *
              (im τ * (n : ℝ) ^ 2 -
                2 * |im z| * (↑|n| : ℝ))) := by
      apply mul_le_mul_of_nonneg_left
      · exact norm_jacobiTheta₂_term_le
          hτ le_rfl le_rfl n
      · positivity
    _ = u n := by
      simp only [u, b]
      ring_nf

/-- The Fréchet derivatives of the prime summands are summable at each
upper-half-plane point. -/
theorem summable_jacobiTheta₂PrimeTermFDeriv
    (z : ℂ) {τ : ℂ} (hτ : 0 < im τ) :
    Summable
      (fun n : ℤ =>
        jacobiTheta₂PrimeTermFDeriv n z τ) := by
  let b : ℤ → ℝ := fun n =>
    (|n| ^ 3 : ℝ) *
      Real.exp
        (-π *
          (im τ * n ^ 2 -
            2 * |im z| * |n|))
  let u : ℤ → ℝ := fun n =>
    6 * π ^ 2 * b n
  have hb : Summable b := by
    simpa only [b] using
      summable_pow_mul_jacobiTheta₂_term_bound
        |im z| hτ 3
  have hu : Summable u :=
    hb.mul_left (6 * π ^ 2)
  apply hu.of_norm_bounded
  intro n
  exact
    (norm_jacobiTheta₂PrimeTermFDeriv_le
      n z τ).trans (by
        simp_rw [u, b, mul_assoc (6 * π ^ 2)]
        refine mul_le_mul_of_nonneg_left ?_
          (by positivity)
        refine mul_le_mul_of_nonneg_left ?_
          (pow_nonneg
            (Int.cast_nonneg (abs_nonneg n)) 3)
        exact norm_jacobiTheta₂_term_le
          hτ le_rfl le_rfl n)

/-- One second-derivative summand differentiates to the corresponding
third-derivative summand. -/
theorem hasDerivAt_jacobiTheta₂SecondTerm
    (n : ℤ) (z τ : ℂ) :
    HasDerivAt
      (fun w =>
        jacobiTheta₂SecondTerm n w τ)
      (jacobiTheta₂ThirdTerm n z τ) z := by
  let a : ℂ := 2 * π * I * (n : ℂ)
  have hlinear :
      HasDerivAt
        (fun w : ℂ =>
          a * w + π * I * (n : ℂ) ^ 2 * τ)
        a z := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id z).const_mul a).add_const
        (π * I * (n : ℂ) ^ 2 * τ)
  convert
    hlinear.cexp.const_mul (a ^ 2) using 1
  all_goals
    simp only [a, jacobiTheta₂_term,
      jacobiTheta₂ThirdTerm]
    ring

/-- Termwise differentiation of the second elliptic derivative series. -/
theorem hasDerivAt_jacobiTheta₂Second_fst
    (z : ℂ) {τ : ℂ} (hτ : 0 < im τ) :
    HasDerivAt
      (fun w =>
        jacobiTheta₂Second w τ)
      (jacobiTheta₂Third z τ) z := by
  obtain ⟨S, hS⟩ := exists_gt |im z|
  let V : Set ℂ := {w | |im w| < S}
  have hVo : IsOpen V := by
    exact
      (_root_.continuous_abs.comp Complex.continuous_im)
        |>.isOpen_preimage _ isOpen_Iio
  have hVp : IsPreconnected V := by
    simpa only [V, Set.mem_setOf_eq, abs_lt] using
      ((convex_halfSpace_im_gt (-S)).inter
        (convex_halfSpace_im_lt S)).isPreconnected
  have hzV : z ∈ V := hS
  let b : ℤ → ℝ := fun n =>
    (|n| ^ 3 : ℝ) *
      Real.exp
        (-π *
          (im τ * n ^ 2 - 2 * S * |n|))
  let u : ℤ → ℝ := fun n =>
    8 * π ^ 3 * b n
  have hb : Summable b := by
    simpa only [b] using
      summable_pow_mul_jacobiTheta₂_term_bound
        S hτ 3
  have hu : Summable u :=
    hb.mul_left (8 * π ^ 3)
  have hbound :
      ∀ n w, w ∈ V →
        ‖jacobiTheta₂ThirdTerm n w τ‖ ≤ u n := by
    intro n w hw
    calc
      ‖jacobiTheta₂ThirdTerm n w τ‖ =
          8 * π ^ 3 * (↑|n| : ℝ) ^ 3 *
            ‖jacobiTheta₂_term n w τ‖ := by
        unfold jacobiTheta₂ThirdTerm
        rw [norm_mul, norm_pow]
        simp only [norm_mul, Complex.norm_two,
          norm_I, Complex.norm_of_nonneg pi_pos.le,
          norm_intCast, ← Int.cast_abs]
        ring_nf
      _ ≤
          8 * π ^ 3 * (↑|n| : ℝ) ^ 3 *
            Real.exp
              (-π *
                (im τ * (n : ℝ) ^ 2 -
                  2 * S * (↑|n| : ℝ))) := by
        apply mul_le_mul_of_nonneg_left
        · exact norm_jacobiTheta₂_term_le
            hτ (le_of_lt hw) le_rfl n
        · positivity
      _ = u n := by
        simp only [u, b]
        ring_nf
  have hsum :=
    summable_jacobiTheta₂SecondTerm z hτ
  simpa only [jacobiTheta₂Second,
    jacobiTheta₂Third] using
    hasDerivAt_tsum_of_isPreconnected
      (u := u) (t := V)
      (g := fun n w =>
        jacobiTheta₂SecondTerm n w τ)
      (g' := fun n w =>
        jacobiTheta₂ThirdTerm n w τ)
      (y₀ := z) (y := z)
      hu hVo hVp
      (fun n w _ =>
        hasDerivAt_jacobiTheta₂SecondTerm
          n w τ)
      hbound hzV hsum hzV

/-- The termwise cubic identity underlying the differentiated heat
equation. -/
theorem jacobiTheta₂ThirdTerm_eq_primeFDeriv_snd
    (n : ℤ) (z τ : ℂ) :
    jacobiTheta₂ThirdTerm n z τ =
      4 * π * I *
        (jacobiTheta₂PrimeTermFDeriv
          n z τ) (0, 1) := by
  simp only [jacobiTheta₂ThirdTerm,
    jacobiTheta₂PrimeTermFDeriv,
    ContinuousLinearMap.coe_smul',
    Pi.smul_apply, smul_eq_mul,
    jacobiTheta₂_term_fderiv,
    smul_add, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd',
    mul_zero, mul_one, zero_add,
    jacobiTheta₂_term]
  ring

/-- Differentiated heat equation for Mathlib's basic theta series. -/
theorem jacobiTheta₂Prime_heat_equation
    (z : ℂ) {τ : ℂ} (hτ : 0 < im τ) :
    jacobiTheta₂Third z τ =
      4 * π * I *
        (jacobiTheta₂PrimeFDeriv z τ) (0, 1) := by
  have hsumApply :
      HasSum
        (fun n : ℤ =>
          (jacobiTheta₂PrimeTermFDeriv
            n z τ) (0, 1))
        ((jacobiTheta₂PrimeFDeriv
          z τ) (0, 1)) := by
    simpa only [jacobiTheta₂PrimeFDeriv] using
      (ContinuousLinearMap.apply ℂ ℂ
        ((0, 1) : ℂ × ℂ)).hasSum
          (summable_jacobiTheta₂PrimeTermFDeriv
            z hτ).hasSum
  calc
    jacobiTheta₂Third z τ =
        ∑' n : ℤ,
          4 * π * I *
            (jacobiTheta₂PrimeTermFDeriv
              n z τ) (0, 1) := by
      unfold jacobiTheta₂Third
      apply tsum_congr
      intro n
      exact
        jacobiTheta₂ThirdTerm_eq_primeFDeriv_snd
          n z τ
    _ =
        4 * π * I *
          (jacobiTheta₂PrimeFDeriv
            z τ) (0, 1) :=
      (hsumApply.mul_left (4 * π * I)).tsum_eq

/-- Ordinary modular-variable derivative form of the differentiated
heat equation. -/
theorem jacobiTheta₂Prime_heat_equation_deriv_snd
    (z : ℂ) (τ : ℍ) :
    jacobiTheta₂Third z (τ : ℂ) =
      4 * π * I *
        deriv
          (fun u : ℂ =>
            jacobiTheta₂' z u)
          (τ : ℂ) := by
  have hcurve :
      HasDerivAt
        (fun u : ℂ => (z, u))
        (0, 1) (τ : ℂ) :=
    (hasDerivAt_const (τ : ℂ) z).prodMk
      (hasDerivAt_id (τ : ℂ))
  have hjoint :=
    (hasFDerivAt_jacobiTheta₂Prime_joint
      z (τ : ℂ) τ.im_pos).comp_hasDerivAt
        (τ : ℂ) hcurve
  have hderiv :
      deriv
          (fun u : ℂ =>
            jacobiTheta₂' z u)
          (τ : ℂ) =
        (jacobiTheta₂PrimeFDeriv
          z (τ : ℂ)) (0, 1) :=
    hjoint.deriv
  rw [hderiv]
  exact jacobiTheta₂Prime_heat_equation
    z τ.im_pos

end

end HGAS.Modular
