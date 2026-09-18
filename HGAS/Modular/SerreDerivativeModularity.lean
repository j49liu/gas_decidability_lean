import Mathlib.NumberTheory.ModularForms.Derivative
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Tactic

/-!
# The Serre derivative preserves level-one modularity

Mathlib defines the normalized derivative

`D F = (2 π i)⁻¹ F'`

and the Serre derivative

`∂ₖ F = D F - (k / 12) E₂ F`,

but deliberately leaves the modularity theorem as a TODO.  This file
supplies that theorem.  It is kept separate from the HGAS-specific theta
system because the result is useful in any formalization involving
differential identities between modular forms.

The proof exposes the cancellation which motivates the definition.  The
ordinary derivative of a weight-`k` slash transform has an anomalous term
proportional to `c / (cτ+d)`.  Mathlib's transformation law for `E₂` has
exactly the same anomaly, with the opposite coefficient.  Subtracting
`(k/12) E₂ F` therefore restores weight `k+2` covariance.

The calculation follows the proof in the Sphere-Packing-Lean project,
adapted to Mathlib's current `Derivative.normalizedDerivOfComplex` and
`Derivative.serreDerivative` API.  Unlike importing that project, this
module has no additional dependency and is checked against the same
Mathlib version as the rest of the HGAS development.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I
open Complex Real
open ModularForm ModularGroup SlashAction EisensteinSeries
open scoped Manifold MatrixGroups ModularForm

noncomputable section

local notation "D" => Derivative.normalizedDerivOfComplex
local notation "∂[" k "]" => Derivative.serreDerivative k

/-! ## Elementary complex derivatives used by the slash calculation -/

section SlashHelpers

variable (γ : SL(2, ℤ))

/-- The derivative of `c z + d` is `c`. -/
private lemma deriv_denom (z : ℂ) :
    deriv (fun w ↦ denom γ w) z = ((γ 1 0 : ℤ) : ℂ) := by
  simp only [denom]
  rw [deriv_add_const, deriv_const_mul _ differentiableAt_id, deriv_id'', mul_one]
  simp

/-- The derivative of `a z + b` is `a`. -/
private lemma deriv_num (z : ℂ) :
    deriv (fun w ↦ num γ w) z = ((γ 0 0 : ℤ) : ℂ) := by
  simp only [num]
  rw [deriv_add_const, deriv_const_mul _ differentiableAt_id, deriv_id'', mul_one]
  simp

private lemma differentiableAt_denom (z : ℂ) :
    DifferentiableAt ℂ (fun w ↦ denom γ w) z := by
  simp only [denom]
  fun_prop

private lemma differentiableAt_num (z : ℂ) :
    DifferentiableAt ℂ (fun w ↦ num γ w) z := by
  simp only [num]
  fun_prop

/-- The derivative of the fractional-linear action of an integral
determinant-one matrix. -/
private lemma deriv_moebius (z : ℍ) :
    deriv (fun w ↦ num γ w / denom γ w) z =
      1 / (denom γ z) ^ 2 := by
  have hz : denom γ z ≠ 0 := UpperHalfPlane.denom_ne_zero γ z
  have hdet :
      ((γ 0 0 : ℤ) : ℂ) * (γ 1 1 : ℤ) -
        ((γ 0 1 : ℤ) : ℂ) * (γ 1 0 : ℤ) = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    simp only [Matrix.det_fin_two, ← Int.cast_mul, ← Int.cast_sub] at h ⊢
    exact_mod_cast h
  rw [deriv_fun_div (differentiableAt_num γ z)
      (differentiableAt_denom γ z) hz,
    deriv_num, deriv_denom]
  simp only [denom_apply, num, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Int.coe_castRingHom, Matrix.map_apply, ofReal_intCast] at *
  have hnum :
      ((γ 0 0 : ℤ) : ℂ) *
          (((γ 1 0 : ℤ) : ℂ) * z + (γ 1 1 : ℤ)) -
        (((γ 0 0 : ℤ) : ℂ) * z + (γ 0 1 : ℤ)) *
          (γ 1 0 : ℤ) = 1 := by
    linear_combination hdet
  simp only [hnum, one_div]

/-- Logarithmic-power derivative:
`d(cz+d)⁻ᵏ/dz = -k c (cz+d)⁻ᵏ⁻¹`. -/
private lemma deriv_denom_zpow (k : ℤ) (z : ℍ) :
    deriv (fun w ↦ (denom γ w) ^ (-k)) z =
      (-k : ℂ) * ((γ 1 0 : ℤ) : ℂ) *
        (denom γ z) ^ (-k - 1) := by
  have hz : denom γ z ≠ 0 := UpperHalfPlane.denom_ne_zero γ z
  have hdiff := differentiableAt_denom γ (z : ℂ)
  have hzpow := hasDerivAt_zpow (-k) (denom γ z) (Or.inl hz)
  have hdenom :
      HasDerivAt (fun w ↦ denom γ w) ((γ 1 0 : ℤ) : ℂ) (z : ℂ) := by
    rw [← deriv_denom]
    exact hdiff.hasDerivAt
  have hcomp := hzpow.comp (z : ℂ) hdenom
  have heq :
      (fun w ↦ w ^ (-k)) ∘ (fun w ↦ denom γ w) =
        fun w ↦ (denom γ w) ^ (-k) := rfl
  rw [← heq, hcomp.deriv]
  simp only [Int.cast_neg]
  ring

end SlashHelpers

/-! ## The ordinary derivative anomaly -/

/-- Exact interaction of the normalized derivative with a slash transform.

The first summand has the expected new weight `k+2`; the second summand is
the derivative anomaly that will be cancelled by `E₂`. -/
theorem normalizedDeriv_slash
    (k : ℤ) (F : ℍ → ℂ) (hF : MDiff F) (γ : SL(2, ℤ)) :
    D (F ∣[k] γ) =
      (D F ∣[k + 2] γ) -
        (fun z : ℍ ↦
          (k : ℂ) * (2 * π * I)⁻¹ *
            (γ 1 0 / denom γ z) * (F ∣[k] γ) z) := by
  ext z
  unfold Derivative.normalizedDerivOfComplex
  simp only [Pi.sub_apply]
  have hzden : denom γ z ≠ 0 := UpperHalfPlane.denom_ne_zero γ z
  have hdet : (0 : ℝ) < ((γ : GL (Fin 2) ℝ).det).val := by simp
  have hlocal :
      deriv ((F ∣[k] γ) ∘ ofComplex) z =
        deriv
          (fun w ↦
            (F ∘ ofComplex) (num γ w / denom γ w) *
              (denom γ w) ^ (-k)) z := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw]
    rw [ModularForm.SL_slash_apply (f := F) (k := k) γ ⟨w, hw⟩]
    congr 1
    let gz : ℍ := γ • ⟨w, hw⟩
    have hcoe : (gz : ℂ) = num γ w / denom γ w := by
      have h := UpperHalfPlane.coe_smul_of_det_pos hdet ⟨w, hw⟩
      simpa only [gz] using h
    have him : 0 < (num γ w / denom γ w).im := by
      rw [← hcoe]
      exact gz.im_pos
    congr 1
    apply UpperHalfPlane.ext
    rw [ofComplex_apply_of_im_pos him]
    exact hcoe
  rw [hlocal]
  have hden :
      ∀ w : ℂ, 0 < w.im → denom γ w ≠ 0 :=
    fun w hw ↦ UpperHalfPlane.denom_ne_zero γ ⟨w, hw⟩
  have hpow :
      DifferentiableAt ℂ (fun w ↦ (denom γ w) ^ (-k)) z :=
    DifferentiableAt.zpow (differentiableAt_denom γ z)
      (Or.inl (hden z z.im_pos))
  have hmob :
      DifferentiableAt ℂ (fun w ↦ num γ w / denom γ w) z :=
    (differentiableAt_num γ z).div (differentiableAt_denom γ z)
      (hden z z.im_pos)
  have him : 0 < (num γ z / denom γ z).im := by
    rw [← UpperHalfPlane.coe_smul_of_det_pos hdet z]
    exact (γ • z).im_pos
  have hFmob :
      DifferentiableAt ℂ (F ∘ ofComplex) (num γ z / denom γ z) :=
    UpperHalfPlane.mdifferentiableAt_iff.mp
      (hF ⟨num γ z / denom γ z, him⟩)
  have hcomp :
      (fun w ↦ (F ∘ ofComplex) (num γ w / denom γ w)) =
        (F ∘ ofComplex) ∘ (fun w ↦ num γ w / denom γ w) := rfl
  have hFcomp :
      DifferentiableAt ℂ
        (fun w ↦ (F ∘ ofComplex) (num γ w / denom γ w)) z := by
    rw [hcomp]
    exact hFmob.comp (z : ℂ) hmob
  have hfun :
      (fun w ↦
          (F ∘ ofComplex) (num γ w / denom γ w) *
            (denom γ w) ^ (-k)) =
        (fun w ↦ (F ∘ ofComplex) (num γ w / denom γ w)) *
          (fun w ↦ (denom γ w) ^ (-k)) := rfl
  rw [hfun, deriv_mul hFcomp hpow]
  have hchain :
      deriv
          (fun w ↦ (F ∘ ofComplex) (num γ w / denom γ w)) z =
        deriv (F ∘ ofComplex) (num γ z / denom γ z) *
          deriv (fun w ↦ num γ w / denom γ w) z := by
    rw [hcomp, (hFmob.hasDerivAt.comp (z : ℂ) hmob.hasDerivAt).deriv]
  rw [hchain, deriv_moebius γ z, deriv_denom_zpow γ k z]
  have hmobEq : ↑(γ • z) = num γ z / denom γ z :=
    UpperHalfPlane.coe_smul_of_det_pos hdet z
  have hFvalue :
      (F ∘ ofComplex) (num γ z / denom γ z) = F (γ • z) := by
    simp only [Function.comp_apply, ← hmobEq, ofComplex_apply]
  simp only [ModularForm.SL_slash_apply, hFvalue, hmobEq]
  have hcombine :
      1 / (denom γ z) ^ 2 * (denom γ z) ^ (-k) =
        (denom γ z) ^ (-(k + 2)) := by
    rw [one_div, ← zpow_natCast (denom γ z) 2, ← zpow_neg,
      ← zpow_add₀ hzden]
    congr 1
    ring
  have hminusOne :
      (denom γ z) ^ (-k - 1) =
        (denom γ z) ^ (-1 : ℤ) * (denom γ z) ^ (-k) := by
    rw [← zpow_add₀ hzden]
    congr 1
    ring
  conv_lhs =>
    rw [mul_assoc
      (deriv (F ∘ ofComplex) (num γ z / denom γ z))
      (1 / denom γ z ^ 2) _]
    rw [hcombine, hminusOne]
  simp only [zpow_neg_one]
  ring

/-! ## Cancellation with the quasimodular transformation of `E₂` -/

/-- The Serre derivative is equivariant under the level-one slash action. -/
theorem serreDerivative_slash_equivariant
    (k : ℤ) (F : ℍ → ℂ) (hF : MDiff F) (γ : SL(2, ℤ)) :
    (∂[(k : ℂ)] F ∣[k + 2] γ) =
      ∂[(k : ℂ)] (F ∣[k] γ) := by
  have hD := normalizedDeriv_slash k F hF γ
  have hE := EisensteinSeries.E2_slash_action γ
  have hmul := ModularForm.mul_slash_SL2 (2 : ℤ) k γ
    EisensteinSeries.E2 F
  ext z
  simp only [Derivative.serreDerivative_apply]
  have hlhs :
      (∂[(k : ℂ)] F ∣[k + 2] γ) z =
        (D F ∣[k + 2] γ) z -
          (k : ℂ) * 12⁻¹ *
            ((EisensteinSeries.E2 ∣[(2 : ℤ)] γ) z *
              (F ∣[k] γ) z) := by
    have h := congrFun hmul z
    simp only [Pi.mul_apply, show (2 : ℤ) + k = k + 2 by omega] at h
    simp only [ModularForm.SL_slash_apply,
      Derivative.serreDerivative_apply, Pi.mul_apply] at h ⊢
    rw [← h]
    ring
  rw [hlhs]
  have hEz := congrFun hE z
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hEz
  rw [hEz]
  have hDz := congrFun hD z
  simp only [Pi.sub_apply] at hDz
  rw [hDz]
  simp only [EisensteinSeries.D2, riemannZeta_two]
  have hpi : (π : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hden : denom γ z ≠ 0 :=
    UpperHalfPlane.denom_ne_zero γ z
  field_simp [hden, hpi]
  ring_nf
  simp only [I_sq]
  ring

/-- In particular, the Serre derivative of a weight-`k` invariant
holomorphic function is invariant of weight `k+2`. -/
theorem serreDerivative_slash_invariant
    (k : ℤ) (F : ℍ → ℂ) (hF : MDiff F)
    (γ : SL(2, ℤ)) (h : F ∣[k] γ = F) :
    (∂[(k : ℂ)] F ∣[k + 2] γ) = ∂[(k : ℂ)] F := by
  rw [serreDerivative_slash_equivariant k F hF γ, h]

end

end HGAS.Modular
