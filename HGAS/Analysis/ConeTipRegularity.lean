import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Regularity at a quadratic cone tip

This file packages a reusable `k = 2` cone-tip lemma.  It is the analytic
fact needed when a smooth angular profile is extended to the origin as a
positively homogeneous function of degree two.

The proof uses exactly the two estimates suggested by homogeneity:

* the function is `O(‖x‖²)`, so its derivative at the cone tip is zero;
* its off-tip derivative is `O(‖x‖)`, so that derivative extends
  continuously by zero.

No particular formula for the angular profile occurs in the statement.
Consequently the module can be reused both for the Rosier converse
construction and for explicit homogeneous Lyapunov functions.

The argument is adapted from the Apache-2.0 Lean development
`j49liu/homogeneous-lyapunov-counterexample-lean`,
`HomogeneousObstruction/ConeTipRegularity.lean` (2026).
-/

namespace HGAS

open Asymptotics Filter Set
open scoped Topology

noncomputable section

variable {E G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A quadratically bounded function whose derivative is linearly bounded
and continuous away from the origin is globally `C¹`.

The derivative field `D` is required to be the Fréchet derivative away
from the origin and to take the value zero at the origin.  The bounds are
stated globally because this is the form produced immediately by positive
homogeneity and compactness of the unit sphere. -/
theorem coneTip_contDiff_one
    (F : E → G) (D : E → E →L[ℝ] G)
    (C₀ C₁ : ℝ)
    (hF_zero : F 0 = 0)
    (hF_bound : ∀ x, ‖F x‖ ≤ C₀ * ‖x‖ ^ 2)
    (hD_zero : D 0 = 0)
    (hD_bound : ∀ x, ‖D x‖ ≤ C₁ * ‖x‖)
    (hD_continuous_off_zero : ContinuousOn D ({0} : Set E)ᶜ)
    (hF_deriv_off_zero : ∀ x ≠ 0, HasFDerivAt F (D x) x) :
    ContDiff ℝ 1 F := by
  have hF_bigO : F =O[nhds (0 : E)] fun x : E ↦ ‖x‖ ^ 2 :=
    IsBigO.of_bound C₀ (Filter.Eventually.of_forall fun x ↦ by
      simpa using hF_bound x)
  have hF_littleO : F =o[nhds (0 : E)] fun x : E ↦ x :=
    hF_bigO.trans_isLittleO (isLittleO_norm_pow_id one_lt_two)
  have hF_deriv_zero : HasFDerivAt F (0 : E →L[ℝ] G) 0 := by
    apply HasFDerivAt.of_isLittleO
    simpa [hF_zero] using hF_littleO
  have hD_bigO : D =O[nhds (0 : E)] fun x : E ↦ ‖x‖ :=
    IsBigO.of_bound C₁ (Filter.Eventually.of_forall fun x ↦ by
      simpa using hD_bound x)
  have hD_tendsto_zero : Tendsto D (nhds (0 : E)) (nhds 0) :=
    hD_bigO.trans_tendsto tendsto_norm_zero
  have hD_continuous_at_zero : ContinuousAt D 0 := by
    rw [ContinuousAt, hD_zero]
    exact hD_tendsto_zero
  have hD_continuous : Continuous D := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x = 0
    · simpa [hx] using hD_continuous_at_zero
    · have hx' : x ∈ ({0} : Set E)ᶜ := by simpa
      exact (hD_continuous_off_zero x hx').continuousAt
        (isOpen_compl_singleton.mem_nhds hx')
  rw [contDiff_one_iff_hasFDerivAt]
  refine ⟨D, hD_continuous, ?_⟩
  intro x
  by_cases hx : x = 0
  · simpa [hx, hD_zero] using hF_deriv_zero
  · exact hF_deriv_off_zero x hx

/-- The quadratic bound alone identifies the derivative at the cone tip:
it is the zero continuous linear map. -/
theorem coneTip_fderiv_zero
    (F : E → G)
    (hF_zero : F 0 = 0)
    (C₀ : ℝ)
    (hF_bound : ∀ x, ‖F x‖ ≤ C₀ * ‖x‖ ^ 2) :
    fderiv ℝ F 0 = 0 := by
  have hF_bigO : F =O[nhds (0 : E)] fun x : E ↦ ‖x‖ ^ 2 :=
    IsBigO.of_bound C₀ (Filter.Eventually.of_forall fun x ↦ by
      simpa using hF_bound x)
  have hF_littleO : F =o[nhds (0 : E)] fun x : E ↦ x :=
    hF_bigO.trans_isLittleO (isLittleO_norm_pow_id one_lt_two)
  have hF_deriv_zero : HasFDerivAt F (0 : E →L[ℝ] G) 0 := by
    apply HasFDerivAt.of_isLittleO
    simpa [hF_zero] using hF_littleO
  exact hF_deriv_zero.fderiv

/-- Convenience form using `fderiv` itself as the derivative field.
Smoothness away from the origin supplies all off-tip regularity, while the
two cone estimates supply differentiability and derivative continuity at
the origin. -/
theorem coneTip_contDiff_one_of_smooth_off_zero
    (F : E → G)
    (C₀ C₁ : ℝ)
    (hF_zero : F 0 = 0)
    (hF_bound : ∀ x, ‖F x‖ ≤ C₀ * ‖x‖ ^ 2)
    (hF_smooth_off_zero : ContDiffOn ℝ ⊤ F ({0} : Set E)ᶜ)
    (hF_fderiv_bound : ∀ x ≠ 0, ‖fderiv ℝ F x‖ ≤ C₁ * ‖x‖) :
    ContDiff ℝ 1 F := by
  have hF_fderiv_zero : fderiv ℝ F 0 = 0 :=
    coneTip_fderiv_zero F hF_zero C₀ hF_bound
  apply coneTip_contDiff_one F (fderiv ℝ F) C₀ C₁
      hF_zero hF_bound
  · exact hF_fderiv_zero
  · intro x
    by_cases hx : x = 0
    · simp [hx, hF_fderiv_zero]
    · exact hF_fderiv_bound x hx
  · exact hF_smooth_off_zero.continuousOn_fderiv_of_isOpen
      isOpen_compl_singleton (by simp)
  · intro x hx
    have hx' : x ∈ ({0} : Set E)ᶜ := by simpa
    have hdiffWithin :
        DifferentiableWithinAt ℝ F ({0} : Set E)ᶜ x :=
      hF_smooth_off_zero.differentiableOn (by simp) x hx'
    exact (hdiffWithin.differentiableAt
      (isOpen_compl_singleton.mem_nhds hx')).hasFDerivAt

end

end HGAS
