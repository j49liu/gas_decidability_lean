import HGAS.Wrapper.AngularAverageGAS
import Mathlib.Tactic

/-!
# Reassembling an angular field and a radial reward

The last homogeneous wrapper has the form

`F(x) = Y(x) + A(x) • x`,

where `Y` is tangent to centered spheres and `A` is the angular radial
reward.  This file records the exact analytic identities needed to connect
that formula to `SemanticProductSphere`.
-/

namespace HGAS

open scoped RealInnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Add the scalar radial component `A(x)x` to an angular field `Y`. -/
def angularRadialField
    (Y : E → E) (A : E → ℝ) : E → E :=
  fun x ↦ Y x + A x • x

/-- Smoothness of the assembled field. -/
theorem contDiff_angularRadialField
    {Y : E → E} {A : E → ℝ} {r : WithTop ℕ∞}
    (hY : ContDiff ℝ r Y) (hA : ContDiff ℝ r A) :
    ContDiff ℝ r (angularRadialField Y A) := by
  unfold angularRadialField
  exact hY.add (hA.smul contDiff_id)

/-- The assembled field is homogeneous of degree `d` when `Y` has degree
`d` and `A` has degree `d-1`. -/
theorem scalesAsDegree_angularRadialField
    {Y : E → E} {A : E → ℝ} {d : ℕ}
    (hd : 0 < d)
    (hY : ScalesAsDegree ℝ d Y)
    (hA : ScalesAsDegree ℝ (d - 1) A) :
    ScalesAsDegree ℝ d (angularRadialField Y A) := by
  intro c x
  have hdegree : d - 1 + 1 = d :=
    Nat.sub_add_cancel hd
  rw [angularRadialField, angularRadialField, hY, hA]
  rw [smul_add, smul_smul, smul_smul]
  congr 1
  have hpow : c ^ (d - 1) * c = c ^ d := by
    calc
      c ^ (d - 1) * c = c ^ (d - 1 + 1) := by
        rw [pow_succ]
      _ = c ^ d := by rw [hdegree]
  have hscalar :
      (c ^ (d - 1) • A x) * c = c ^ d * A x := by
    simp only [smul_eq_mul]
    rw [mul_assoc, mul_comm (A x) c, ← mul_assoc, hpow]
  rw [hscalar]

/-- Tangency makes the radial reward of the assembled field equal to
`A(x)‖x‖²`. -/
theorem innerRadialReward_angularRadialField
    (Y : E → E) (A : E → ℝ) (x : E)
    (htangent : ⟪x, Y x⟫ = 0) :
    innerRadialReward (angularRadialField Y A) x =
      A x * ‖x‖ ^ 2 := by
  rw [innerRadialReward, angularRadialField,
    inner_add_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, htangent, zero_add]

/-- On the unit sphere, the radial reward is exactly `A`. -/
theorem innerRadialReward_angularRadialField_of_norm_eq_one
    (Y : E → E) (A : E → ℝ) (x : E)
    (htangent : ⟪x, Y x⟫ = 0)
    (hx : ‖x‖ = 1) :
    innerRadialReward (angularRadialField Y A) x = A x := by
  rw [innerRadialReward_angularRadialField Y A x htangent, hx]
  ring

/-- On the unit sphere, the angular part of `Y+A x` is exactly `Y`. -/
theorem innerAngularField_angularRadialField_of_norm_eq_one
    (Y : E → E) (A : E → ℝ) (x : E)
    (htangent : ⟪x, Y x⟫ = 0)
    (hx : ‖x‖ = 1) :
    innerAngularField (angularRadialField Y A) x = Y x := by
  rw [innerAngularField,
    innerRadialReward_angularRadialField_of_norm_eq_one
      Y A x htangent hx,
    angularRadialField]
  abel

/-- The bounded cutoff reward used by the GAS criterion also equals `A`
on the unit sphere. -/
theorem boundedCutoffInnerRadialReward_angularRadialField
    [FiniteDimensional ℝ E]
    (Y : E → E) (A : E → ℝ)
    (hF : ContDiff ℝ 1 (angularRadialField Y A))
    (x : E)
    (htangent : ⟪x, Y x⟫ = 0)
    (hx : ‖x‖ = 1) :
    boundedCutoffInnerRadialReward
        (angularRadialField Y A) hF x =
      A x := by
  rw [boundedCutoffInnerRadialReward_apply,
    cutoffInnerRadialReward_eq_of_norm_eq_one _ x hx,
    innerRadialReward_angularRadialField_of_norm_eq_one
      Y A x htangent hx]

end

end HGAS
