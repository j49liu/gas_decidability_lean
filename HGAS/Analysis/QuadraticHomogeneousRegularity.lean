import HGAS.Analysis.ConeTipRegularity
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

/-!
# Global `C¹` regularity of degree-two homogeneous functions

Rosier's construction first produces a function which is smooth on the
punctured space and positively homogeneous of degree two.  The origin is a
cone tip, so smoothness there does not follow from the punctured formula.
This module proves the exact bridge needed by the converse theorem:

> on a finite-dimensional real normed space, every degree-two positively
> homogeneous function which is smooth away from zero and vanishes at zero
> is globally `C¹`.

The proof is quantitative.  Compactness bounds the function and its
derivative on the unit sphere.  Homogeneity transports these to an
`O(‖x‖²)` function bound and an `O(‖x‖)` derivative bound.  The generic
cone-tip lemma then completes the extension.
-/

namespace HGAS

open Metric Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E]

/-- The metric unit sphere does not contain the origin. -/
theorem unitSphere_subset_compl_zero :
    sphere (0 : E) 1 ⊆ ({0} : Set E)ᶜ := by
  intro x hx
  rw [mem_sphere_zero_iff_norm] at hx
  simp only [mem_compl_iff, mem_singleton_iff]
  intro hzero
  subst x
  simp at hx

variable [NormedSpace ℝ E]

/-- A nonzero vector is its norm times its normalized direction. -/
theorem norm_smul_inv_norm_smul
    {x : E} (hx : x ≠ 0) :
    ‖x‖ • ((‖x‖ : ℝ)⁻¹ • x) = x := by
  rw [smul_smul]
  simp [norm_ne_zero_iff.mpr hx]

/-- Normalizing a nonzero vector by its norm lands on the metric unit
sphere. -/
theorem inv_norm_smul_mem_unitSphere
    {x : E} (hx : x ≠ 0) :
    (‖x‖ : ℝ)⁻¹ • x ∈ sphere (0 : E) 1 := by
  rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)

/-- Differentiating positive degree-two homogeneity makes the Fréchet
derivative positively homogeneous of degree one. -/
theorem fderiv_pos_smul_of_twoHomogeneous
    (V : E → ℝ)
    (hhomogeneous :
      ∀ (a : ℝ), 0 < a → ∀ x : E,
        V (a • x) = a ^ 2 * V x)
    (a : ℝ) (ha : 0 < a) (x : E) :
    fderiv ℝ V (a • x) = a • fderiv ℝ V x := by
  have hfun :
      (fun y : E ↦ V (a • y)) = (a ^ 2) • V := by
    funext y
    simpa only [Pi.smul_apply, smul_eq_mul] using
      hhomogeneous a ha y
  have hderiv :=
    congrArg (fun f : E → ℝ ↦ fderiv ℝ f x) hfun
  change fderiv ℝ (fun y : E ↦ V (a • y)) x =
    fderiv ℝ ((a ^ 2) • V) x at hderiv
  rw [fderiv_comp_smul] at hderiv
  have hright :
      fderiv ℝ ((a ^ 2) • V) x =
        (a ^ 2) • fderiv ℝ V x := by
    simpa only [Pi.smul_apply] using
      congrFun (fderiv_const_smul_field (𝕜 := ℝ)
        (f := V) (a ^ 2)) x
  rw [hright] at hderiv
  ext v
  have hv :=
    congrArg (fun L : E →L[ℝ] ℝ ↦ L v) hderiv
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul] at hv ⊢
  apply mul_left_cancel₀ ha.ne'
  simpa only [pow_two, mul_assoc] using hv

variable [FiniteDimensional ℝ E]

/-- Compactness of the unit sphere turns punctured continuity and
degree-two homogeneity into a global quadratic bound. -/
theorem exists_quadratic_bound_of_twoHomogeneous
    (V : E → ℝ)
    (hVzero : V 0 = 0)
    (hVcontinuous_off_zero :
      ContinuousOn V ({0} : Set E)ᶜ)
    (hhomogeneous :
      ∀ (a : ℝ), 0 < a → ∀ x : E,
        V (a • x) = a ^ 2 * V x) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : E, ‖V x‖ ≤ C * ‖x‖ ^ 2 := by
  have hcontinuousSphere :
      ContinuousOn V (sphere (0 : E) 1) :=
    hVcontinuous_off_zero.mono unitSphere_subset_compl_zero
  obtain ⟨M, hM⟩ :=
    (isCompact_sphere (0 : E) 1).exists_bound_of_continuousOn
      hcontinuousSphere
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro x
  by_cases hx : x = 0
  · subst x
    simp [hVzero]
  · let u : E := (‖x‖ : ℝ)⁻¹ • x
    have hu : u ∈ sphere (0 : E) 1 := by
      simpa only [u] using inv_norm_smul_mem_unitSphere hx
    have hrpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hxray : ‖x‖ • u = x := by
      simpa only [u] using norm_smul_inv_norm_smul hx
    have hscale := hhomogeneous ‖x‖ hrpos u
    rw [hxray] at hscale
    rw [hscale, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg ‖x‖)]
    calc
      ‖x‖ ^ 2 * ‖V u‖ ≤
          ‖x‖ ^ 2 * max M 0 :=
        mul_le_mul_of_nonneg_left
          ((hM u hu).trans (le_max_left _ _))
          (sq_nonneg ‖x‖)
      _ = max M 0 * ‖x‖ ^ 2 := by ring

/-- Compactness of the unit sphere and differentiated homogeneity give a
global linear bound on the off-origin Fréchet derivative. -/
theorem exists_fderiv_linear_bound_of_twoHomogeneous
    (V : E → ℝ)
    (hVcontDiff_off_zero :
      ContDiffOn ℝ 1 V ({0} : Set E)ᶜ)
    (hhomogeneous :
      ∀ (a : ℝ), 0 < a → ∀ x : E,
        V (a • x) = a ^ 2 * V x) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : E, x ≠ 0 →
        ‖fderiv ℝ V x‖ ≤ C * ‖x‖ := by
  have hDcontinuousOff :
      ContinuousOn (fderiv ℝ V) ({0} : Set E)ᶜ :=
    hVcontDiff_off_zero.continuousOn_fderiv_of_isOpen
      isOpen_compl_singleton (by simp)
  have hDcontinuousSphere :
      ContinuousOn (fderiv ℝ V) (sphere (0 : E) 1) :=
    hDcontinuousOff.mono unitSphere_subset_compl_zero
  obtain ⟨M, hM⟩ :=
    (isCompact_sphere (0 : E) 1).exists_bound_of_continuousOn
      hDcontinuousSphere
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro x hx
  let u : E := (‖x‖ : ℝ)⁻¹ • x
  have hu : u ∈ sphere (0 : E) 1 := by
    simpa only [u] using inv_norm_smul_mem_unitSphere hx
  have hrpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hxray : ‖x‖ • u = x := by
    simpa only [u] using norm_smul_inv_norm_smul hx
  have hscale :=
    fderiv_pos_smul_of_twoHomogeneous
      V hhomogeneous ‖x‖ hrpos u
  rw [hxray] at hscale
  calc
    ‖fderiv ℝ V x‖ =
        ‖‖x‖ • fderiv ℝ V u‖ := by rw [hscale]
    _ = ‖x‖ * ‖fderiv ℝ V u‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_norm]
    _ ≤ ‖x‖ * max M 0 :=
      mul_le_mul_of_nonneg_left
        ((hM u hu).trans (le_max_left _ _))
        (norm_nonneg x)
    _ = max M 0 * ‖x‖ := by ring

/-- **Quadratic homogeneous cone theorem, minimal `C¹` form.**

A degree-two positively homogeneous function which vanishes at zero and is
`C¹` on the punctured finite-dimensional space is globally `C¹`. -/
theorem contDiff_one_of_twoHomogeneous_contDiffOn_compl_zero
    (V : E → ℝ)
    (hVzero : V 0 = 0)
    (hVcontDiff_off_zero :
      ContDiffOn ℝ 1 V ({0} : Set E)ᶜ)
    (hhomogeneous :
      ∀ (a : ℝ), 0 < a → ∀ x : E,
        V (a • x) = a ^ 2 * V x) :
    ContDiff ℝ 1 V := by
  obtain ⟨C₀, _hC₀, hVbound⟩ :=
    exists_quadratic_bound_of_twoHomogeneous
      V hVzero hVcontDiff_off_zero.continuousOn hhomogeneous
  obtain ⟨C₁, _hC₁, hDbound⟩ :=
    exists_fderiv_linear_bound_of_twoHomogeneous
      V hVcontDiff_off_zero hhomogeneous
  have hVfderivZero :
      fderiv ℝ V 0 = 0 :=
    coneTip_fderiv_zero V hVzero C₀ hVbound
  apply coneTip_contDiff_one V (fderiv ℝ V)
      C₀ C₁ hVzero hVbound hVfderivZero
  · intro x
    by_cases hx : x = 0
    · simp [hx, hVfderivZero]
    · exact hDbound x hx
  · exact hVcontDiff_off_zero.continuousOn_fderiv_of_isOpen
      isOpen_compl_singleton (by simp)
  · intro x hx
    have hx' : x ∈ ({0} : Set E)ᶜ := by simpa
    have hdiffWithin :
        DifferentiableWithinAt ℝ V ({0} : Set E)ᶜ x :=
      hVcontDiff_off_zero.differentiableOn (by norm_num) x hx'
    exact (hdiffWithin.differentiableAt
      (isOpen_compl_singleton.mem_nhds hx')).hasFDerivAt

/-- Smoothness away from zero is a convenient stronger hypothesis for the
minimal quadratic homogeneous cone theorem. -/
theorem contDiff_one_of_twoHomogeneous_smooth_off_zero
    (V : E → ℝ)
    (hVzero : V 0 = 0)
    (hVsmooth_off_zero :
      ContDiffOn ℝ ⊤ V ({0} : Set E)ᶜ)
    (hhomogeneous :
      ∀ (a : ℝ), 0 < a → ∀ x : E,
        V (a • x) = a ^ 2 * V x) :
    ContDiff ℝ 1 V :=
  contDiff_one_of_twoHomogeneous_contDiffOn_compl_zero
    V hVzero (hVsmooth_off_zero.of_le (by norm_num)) hhomogeneous

end

end HGAS
