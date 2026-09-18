import HGAS.Analysis.RadialC1Extension
import HGAS.Dynamics.AngularGAS
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Differential of the quadratic radial extension

For a smooth ambient angular profile `v`, recall

```
V(x) = ‖x‖² v(x / ‖x‖).
```

At a unit vector `x`, normalization removes precisely the radial component
of a variation:

```
D(x ↦ x / ‖x‖)_x h = h - ⟪x,h⟫ x.
```

Consequently

```
DV(x)[h]
  = 2 ⟪x,h⟫ v(x)
      + Dv(x)[h - ⟪x,h⟫ x].
```

For `h = F(x)`, the second direction is the angular field and the first
coefficient is the radial reward.  This is the cancellation identity used
to convert the finite-cocycle profile equation into a strict Lyapunov
inequality for the original homogeneous vector field.
-/

namespace HGAS

open Filter
open scoped RealInnerProductSpace Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- The norm of a differentiable curve through a unit vector has derivative
given by the radial inner product. -/
theorem HasDerivAt.norm_of_norm_eq_one
    {γ : ℝ → E} {γ' : E} {t : ℝ}
    (hγ : HasDerivAt γ γ' t)
    (hunit : ‖γ t‖ = 1) :
    HasDerivAt (fun s ↦ ‖γ s‖) ⟪γ t, γ'⟫ t := by
  have hsq := hγ.norm_sq
  have hsqrt := hsq.sqrt (by simp [hunit])
  convert hsqrt using 1
  · funext s
    rw [Real.sqrt_sq (norm_nonneg (γ s))]
  · simp [hunit]

omit [FiniteDimensional ℝ E] in
/-- Along a differentiable curve through the unit sphere, normalization
deletes the radial velocity. -/
theorem HasDerivAt.normDirection_of_norm_eq_one
    {γ : ℝ → E} {γ' : E} {t : ℝ}
    (hγ : HasDerivAt γ γ' t)
    (hunit : ‖γ t‖ = 1) :
    HasDerivAt (fun s ↦ normDirection (γ s))
      (γ' - ⟪γ t, γ'⟫ • γ t) t := by
  have hnorm :=
    HGAS.HasDerivAt.norm_of_norm_eq_one hγ hunit
  have hnorm_ne : ‖γ t‖ ≠ 0 := by simp [hunit]
  have hinv := hnorm.inv hnorm_ne
  have hsmul := hinv.smul hγ
  simpa [normDirection, hunit, sub_eq_add_neg] using hsmul

/-- Directional derivative of the quadratic radial extension at a unit
vector. -/
theorem fderiv_quadraticRadialExtension_unit
    (v : E → ℝ) (hv : ContDiff ℝ 1 v)
    (x h : E) (hx : ‖x‖ = 1) :
    fderiv ℝ (quadraticRadialExtension v) x h =
      2 * ⟪x, h⟫ * v x +
        fderiv ℝ v x (h - ⟪x, h⟫ • x) := by
  let γ : ℝ → E := fun s ↦ x + s • h
  have hγ : HasDerivAt γ h 0 := by
    convert
      (hasDerivAt_const (x := (0 : ℝ)) x).add
        ((hasDerivAt_id (𝕜 := ℝ) 0).smul_const h) using 1
    simp
  have hxne : x ≠ 0 := by
    intro hzero
    simp [hzero] at hx
  have hγzero : γ 0 = x := by simp [γ]
  have hnormSq : HasDerivAt (fun s ↦ ‖γ s‖ ^ 2)
      (2 * ⟪x, h⟫) 0 := by
    simpa only [hγzero] using hγ.norm_sq
  have hdir :
      HasDerivAt (fun s ↦ normDirection (γ s))
        (h - ⟪x, h⟫ • x) 0 := by
    simpa only [hγzero] using
      HGAS.HasDerivAt.normDirection_of_norm_eq_one hγ
        (by simpa only [hγzero] using hx)
  have hvcomp :
      HasDerivAt (fun s ↦ v (normDirection (γ s)))
        (fderiv ℝ v x (h - ⟪x, h⟫ • x)) 0 := by
    have hvx : HasFDerivAt v (fderiv ℝ v x) x :=
      (hv.differentiable one_ne_zero x).hasFDerivAt
    have hvdir :
        HasFDerivAt v (fderiv ℝ v x)
          (normDirection (γ 0)) := by
      simpa [hγzero, normDirection, hx] using hvx
    have hcomp := hvdir.comp_hasDerivAt 0 hdir
    simpa [hγzero, normDirection, hx] using hcomp
  have hproduct :=
    hnormSq.mul hvcomp
  have hformula :
      (fun s ↦ quadraticRadialExtension v (γ s)) =ᶠ[𝓝 (0 : ℝ)]
        (fun s ↦ ‖γ s‖ ^ 2 * v (normDirection (γ s))) := by
    have hcontinuous : ContinuousAt γ 0 := hγ.continuousAt
    have hne : ∀ᶠ s in 𝓝 (0 : ℝ), γ s ≠ 0 :=
      hcontinuous.preimage_mem_nhds
        (isOpen_compl_singleton.mem_nhds (by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, hγzero]
            using hxne))
    filter_upwards [hne] with s hs
    exact quadraticRadialExtension_of_ne v hs
  have halong :
      HasDerivAt (fun s ↦ quadraticRadialExtension v (γ s))
        (2 * ⟪x, h⟫ * v x +
          fderiv ℝ v x (h - ⟪x, h⟫ • x)) 0 := by
    have hchanged :=
      hproduct.congr_of_eventuallyEq hformula
    convert hchanged using 1
    simp [hγzero, normDirection, hx]
  have hext :
      HasDerivAt (fun s ↦ quadraticRadialExtension v (γ s))
        (fderiv ℝ (quadraticRadialExtension v) x h) 0 := by
    have hV :
        HasFDerivAt (quadraticRadialExtension v)
          (fderiv ℝ (quadraticRadialExtension v) x) x :=
      ((contDiff_one_quadraticRadialExtension v hv).differentiable
        one_ne_zero x).hasFDerivAt
    have hVγ :
        HasFDerivAt (quadraticRadialExtension v)
          (fderiv ℝ (quadraticRadialExtension v) x)
          (γ 0) := by
      simpa only [hγzero] using hV
    have hcomp := hVγ.comp_hasDerivAt 0 hγ
    simpa only [hγzero] using hcomp
  exact hext.unique halong

/-- Specialization to a vector field: the tangential derivative and radial
reward are exactly the two terms in the radial-extension differential. -/
theorem fderiv_quadraticRadialExtension_along_field_unit
    (v : E → ℝ) (hv : ContDiff ℝ 1 v)
    (F : E → E) (x : E) (hx : ‖x‖ = 1) :
    fderiv ℝ (quadraticRadialExtension v) x (F x) =
      fderiv ℝ v x (innerAngularField F x) +
        2 * innerRadialReward F x * v x := by
  rw [fderiv_quadraticRadialExtension_unit v hv x (F x) hx]
  unfold innerAngularField innerRadialReward
  ring

omit [FiniteDimensional ℝ E] in
/-- The Lie derivative of a degree-two homogeneous function along a
degree-`d` homogeneous field scales with degree `d + 1`. -/
theorem fderiv_along_pos_smul_of_twoHomogeneous
    (V : E → ℝ)
    (hV :
      ∀ (a : ℝ), 0 < a → ∀ x : E,
        V (a • x) = a ^ 2 * V x)
    (F : E → E) (d : ℕ)
    (hF : ScalesAsDegree ℝ d F)
    (a : ℝ) (ha : 0 < a) (x : E) :
    fderiv ℝ V (a • x) (F (a • x)) =
      a ^ (d + 1) * fderiv ℝ V x (F x) := by
  rw [fderiv_pos_smul_of_twoHomogeneous V hV a ha x,
    hF a x]
  simp only [ContinuousLinearMap.smul_apply, map_smul, smul_eq_mul]
  rw [pow_succ]
  ring

end

end HGAS
