import HGAS.Dynamics.CompactlySupportedFlow
import HGAS.Dynamics.AngularGAS
import HGAS.Analysis.LinearODEZero
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Tactic

/-!
# A global cutoff flow for the Euclidean angular field

For a smooth field `F` on a finite-dimensional real inner-product space,
the angular field

```
Y(x) = F(x) - ⟪x,F(x)⟫ x
```

is tangent to the unit sphere but generally grows polynomially at infinity.
This file multiplies it by a smooth compactly supported bump which is one
on the unit ball.  The resulting field has a global continuous flow, and
the unit sphere is invariant.  Hence orbits starting on the sphere solve
the original, uncut angular ODE.

The same bump is applied to the radial reward.  This produces a bounded
continuous observable on the whole ambient space which agrees with
`⟪x,F(x)⟫` on the sphere.  It is the observable used by the finite-cocycle
Lyapunov profile.
-/

namespace HGAS

open Filter Function Metric Set
open scoped BoundedContinuousFunction RealInnerProductSpace Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-! ## Smooth compactly supported extensions -/

omit [FiniteDimensional ℝ E] in
theorem contDiff_innerRadialReward
    {F : E → E} (hF : ContDiff ℝ 1 F) :
    ContDiff ℝ 1 (innerRadialReward F) := by
  unfold innerRadialReward
  exact contDiff_id.inner ℝ hF

omit [FiniteDimensional ℝ E] in
theorem contDiff_innerAngularField
    {F : E → E} (hF : ContDiff ℝ 1 F) :
    ContDiff ℝ 1 (innerAngularField F) := by
  unfold innerAngularField
  exact hF.sub ((contDiff_innerRadialReward hF).smul contDiff_id)

/-- A smooth bump equal to one throughout the closed unit ball. -/
noncomputable def euclideanAngularBump :
    ContDiffBump (0 : E) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- Compactly supported extension of the angular field. -/
def cutoffInnerAngularField (F : E → E) : E → E :=
  fun x ↦ euclideanAngularBump (E := E) x • innerAngularField F x

/-- Compactly supported extension of the radial reward. -/
def cutoffInnerRadialReward (F : E → E) : E → ℝ :=
  fun x ↦ euclideanAngularBump (E := E) x * innerRadialReward F x

theorem contDiff_cutoffInnerAngularField
    {F : E → E} (hF : ContDiff ℝ 1 F) :
    ContDiff ℝ 1 (cutoffInnerAngularField F) := by
  unfold cutoffInnerAngularField
  exact (euclideanAngularBump (E := E)).contDiff.smul
    (contDiff_innerAngularField hF)

theorem contDiff_cutoffInnerRadialReward
    {F : E → E} (hF : ContDiff ℝ 1 F) :
    ContDiff ℝ 1 (cutoffInnerRadialReward F) := by
  unfold cutoffInnerRadialReward
  exact (euclideanAngularBump (E := E)).contDiff.mul
    (contDiff_innerRadialReward hF)

theorem hasCompactSupport_cutoffInnerAngularField
    (F : E → E) :
    HasCompactSupport (cutoffInnerAngularField F) := by
  unfold cutoffInnerAngularField
  exact (euclideanAngularBump (E := E)).hasCompactSupport.smul_right

theorem hasCompactSupport_cutoffInnerRadialReward
    (F : E → E) :
    HasCompactSupport (cutoffInnerRadialReward F) := by
  unfold cutoffInnerRadialReward
  exact (euclideanAngularBump (E := E)).hasCompactSupport.mul_right

/-- The bumped radial reward, bundled as a bounded continuous function. -/
noncomputable def boundedCutoffInnerRadialReward
    (F : E → E) (hF : ContDiff ℝ 1 F) : E →ᵇ ℝ := by
  let hbound : ∃ C : ℝ, ∀ x, ‖cutoffInnerRadialReward F x‖ ≤ C :=
    (hasCompactSupport_cutoffInnerRadialReward F).exists_bound_of_continuous
      (contDiff_cutoffInnerRadialReward hF).continuous
  let C : ℝ := Classical.choose hbound
  exact BoundedContinuousFunction.ofNormedAddCommGroup
    (cutoffInnerRadialReward F)
    (contDiff_cutoffInnerRadialReward hF).continuous
    C (Classical.choose_spec hbound)

@[simp]
theorem boundedCutoffInnerRadialReward_apply
    (F : E → E) (hF : ContDiff ℝ 1 F) (x : E) :
    boundedCutoffInnerRadialReward F hF x =
      cutoffInnerRadialReward F x :=
  rfl

/-- The cutoff is one at every unit vector. -/
theorem euclideanAngularBump_eq_one_of_norm_eq_one
    (x : E) (hx : ‖x‖ = 1) :
    euclideanAngularBump (E := E) x = 1 := by
  apply (euclideanAngularBump (E := E)).one_of_mem_closedBall
  simp [euclideanAngularBump, Metric.mem_closedBall,
    dist_zero_right, hx]

theorem cutoffInnerRadialReward_eq_of_norm_eq_one
    (F : E → E) (x : E) (hx : ‖x‖ = 1) :
    cutoffInnerRadialReward F x = innerRadialReward F x := by
  simp [cutoffInnerRadialReward,
    euclideanAngularBump_eq_one_of_norm_eq_one x hx]

/-! ## The ambient flow and sphere invariance -/

/-- Global flow of the compactly supported angular extension. -/
noncomputable def euclideanAngularFlow
    (F : E → E) (hF : ContDiff ℝ 1 F) : Flow ℝ E :=
  compactlySupportedContDiffFlow
    (cutoffInnerAngularField F)
    (contDiff_cutoffInnerAngularField hF)
    (hasCompactSupport_cutoffInnerAngularField F)

theorem euclideanAngularFlow_isIntegralCurve_cutoff
    (F : E → E) (hF : ContDiff ℝ 1 F) (x : E) :
    IsIntegralCurve
      (fun t ↦ euclideanAngularFlow F hF t x)
      (fun _ ↦ cutoffInnerAngularField F) :=
  compactlySupportedContDiffFlow_isIntegralCurve
    (cutoffInnerAngularField F)
    (contDiff_cutoffInnerAngularField hF)
    (hasCompactSupport_cutoffInnerAngularField F) x

omit [FiniteDimensional ℝ E] in
/-- The radial defect of the angular field is proportional to
`1-‖x‖²`. -/
theorem inner_self_innerAngularField
    (F : E → E) (x : E) :
    ⟪x, innerAngularField F x⟫ =
      innerRadialReward F x * (1 - ‖x‖ ^ 2) := by
  rw [innerAngularField, inner_sub_right, real_inner_smul_right,
    innerRadialReward, real_inner_self_eq_norm_sq]
  ring

theorem inner_self_cutoffInnerAngularField
    (F : E → E) (x : E) :
    ⟪x, cutoffInnerAngularField F x⟫ =
      euclideanAngularBump (E := E) x *
        innerRadialReward F x * (1 - ‖x‖ ^ 2) := by
  rw [cutoffInnerAngularField, real_inner_smul_right,
    inner_self_innerAngularField]
  ring

/-- The cutoff angular flow preserves the Euclidean unit sphere for all
positive and negative times. -/
theorem euclideanAngularFlow_preserves_norm
    (F : E → E) (hF : ContDiff ℝ 1 F)
    (x : E) (hx : ‖x‖ = 1) :
    ∀ t, ‖euclideanAngularFlow F hF t x‖ = 1 := by
  let γ : ℝ → E := fun t ↦ euclideanAngularFlow F hF t x
  let z : ℝ → ℝ := fun t ↦ ‖γ t‖ ^ 2 - 1
  let b : ℝ → ℝ := fun t ↦
    -2 * euclideanAngularBump (E := E) (γ t) *
      innerRadialReward F (γ t)
  have hγ :
      IsIntegralCurve γ (fun _ ↦ cutoffInnerAngularField F) := by
    simpa only [γ] using
      euclideanAngularFlow_isIntegralCurve_cutoff F hF x
  have hz : ∀ t, HasDerivAt z (b t * z t) t := by
    intro t
    have hsq := (hγ t).norm_sq
    have hsub := hsq.sub_const (1 : ℝ)
    convert hsub using 1
    rw [inner_self_cutoffInnerAngularField]
    simp only [z, b, γ]
    ring
  have hb : Continuous b := by
    have hγcont : Continuous γ := hγ.continuous
    have hbump :
        Continuous
          (fun t ↦ euclideanAngularBump (E := E) (γ t)) :=
      (euclideanAngularBump (E := E)).continuous.comp hγcont
    have hreward :
        Continuous (fun t ↦ innerRadialReward F (γ t)) :=
      (contDiff_innerRadialReward hF).continuous.comp hγcont
    dsimp only [b]
    fun_prop
  have hzero : z 0 = 0 := by
    simp [z, γ, Flow.map_zero_apply, hx]
  have hall :=
    eq_zero_of_hasDerivAt_eq_mul_self z b hz hb hzero
  intro t
  have hsq : ‖γ t‖ ^ 2 = 1 := by
    have := hall t
    dsimp only [z] at this
    linarith
  have hnonneg : 0 ≤ ‖γ t‖ := norm_nonneg _
  nlinarith

theorem euclideanAngularFlow_isIntegralCurve
    (F : E → E) (hF : ContDiff ℝ 1 F)
    (x : E) (hx : ‖x‖ = 1) :
    IsIntegralCurve
      (fun t ↦ euclideanAngularFlow F hF t x)
      (fun _ ↦ innerAngularField F) := by
  intro t
  have hcut :=
    euclideanAngularFlow_isIntegralCurve_cutoff F hF x t
  have hnorm :=
    euclideanAngularFlow_preserves_norm F hF x hx t
  have hbump :=
    euclideanAngularBump_eq_one_of_norm_eq_one
      (euclideanAngularFlow F hF t x) hnorm
  simpa [cutoffInnerAngularField, hbump] using hcut

end

end HGAS
