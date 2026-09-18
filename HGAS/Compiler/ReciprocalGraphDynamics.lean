import HGAS.Analysis.LinearODEZero
import HGAS.Compiler.ReciprocalGraph
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-!
# Trajectory-level reciprocal graphs

The algebraic identity in `ReciprocalGraph` says that the residual

```
                    R(t) = (1 - η w(t)) g(t) - 1
```

has formal velocity

```
                    R'(t) = η w'(t) g(t) R(t)
```

when the auxiliary reciprocal coordinate is assigned the polynomial
velocity `g' = η w' g²`.  Formal ideal invariance alone is not enough for
the reduction: one needs the graph equation to propagate along every
genuine trajectory.  This file supplies that analytic step by applying
uniqueness for scalar time-dependent linear ODEs.

The final lemmas record the elementary but important fact used by the
Poisson-kernel compiler.  If `w` lies on the complex unit circle and
`0 ≤ η < 1`, then `1 - η w` is nonzero, so the zero-residual graph contains
exactly one reciprocal coordinate.
-/

namespace HGAS

noncomputable section

/-- Componentwise trajectory interface for one polynomial reciprocal
extension.

The source velocity `wdot` is kept explicit.  In a larger polynomial
system it is simply the already-compiled coordinate of the source field.
Continuity of `wdot` is exactly what is needed to invoke linear-ODE
uniqueness for the residual. -/
structure IsReciprocalGraphTrajectory
    (η : ℂ) (w g wdot : ℝ → ℂ) : Prop where
  w_hasDerivAt :
    ∀ t, HasDerivAt w (wdot t) t
  g_hasDerivAt :
    ∀ t,
      HasDerivAt g
        (reciprocalVelocity η (wdot t) (g t)) t
  continuous_wdot : Continuous wdot

namespace IsReciprocalGraphTrajectory

variable {η : ℂ} {w g wdot : ℝ → ℂ}

theorem continuous_w
    (h : IsReciprocalGraphTrajectory η w g wdot) :
    Continuous w :=
  continuous_iff_continuousAt.mpr
    fun t ↦ (h.w_hasDerivAt t).continuousAt

theorem continuous_g
    (h : IsReciprocalGraphTrajectory η w g wdot) :
    Continuous g :=
  continuous_iff_continuousAt.mpr
    fun t ↦ (h.g_hasDerivAt t).continuousAt

/-- The reciprocal residual satisfies its exact scalar homogeneous ODE
along every reciprocal-graph trajectory. -/
theorem residual_hasDerivAt
    (h : IsReciprocalGraphTrajectory η w g wdot)
    (t : ℝ) :
    HasDerivAt
      (fun s ↦ reciprocalResidual η (w s) (g s))
      (η * wdot t * g t *
        reciprocalResidual η (w t) (g t)) t := by
  have hleft :
      HasDerivAt (fun s ↦ 1 - η * w s)
        (-η * wdot t) t := by
    convert
      (hasDerivAt_const t (1 : ℂ)).sub
        ((h.w_hasDerivAt t).const_mul η) using 1
    all_goals ring
  have hraw :=
    (hleft.mul (h.g_hasDerivAt t)).sub_const 1
  convert hraw using 1
  exact (reciprocalResidualVelocity_eq_mul_residual
    η (w t) (wdot t) (g t)).symm

/-- The continuous coefficient in the scalar residual equation. -/
def residualCoefficient
    (η : ℂ) (g wdot : ℝ → ℂ) (t : ℝ) : ℂ :=
  η * wdot t * g t

theorem continuous_residualCoefficient
    (h : IsReciprocalGraphTrajectory η w g wdot) :
    Continuous (residualCoefficient η g wdot) := by
  unfold residualCoefficient
  exact
    (continuous_const.mul h.continuous_wdot).mul h.continuous_g

/-- **Trajectory-level reciprocal-graph invariance.**

If the reciprocal equation holds at one time, it holds at every real
time.  This is a uniqueness theorem, not merely a formal tangency
calculation. -/
theorem residual_eq_zero
    (h : IsReciprocalGraphTrajectory η w g wdot)
    {t₀ : ℝ}
    (hzero : reciprocalResidual η (w t₀) (g t₀) = 0) :
    ∀ t, reciprocalResidual η (w t) (g t) = 0 := by
  have hident :=
    complex_eq_zero_of_hasDerivAt_eq_mul
      (residualCoefficient η g wdot)
      (fun t ↦ reciprocalResidual η (w t) (g t))
      h.continuous_residualCoefficient
      (fun t ↦ by
        simpa only [residualCoefficient] using
          h.residual_hasDerivAt t)
      hzero
  intro t
  exact congrFun hident t

end IsReciprocalGraphTrajectory

/-! ## Uniqueness and a quantitative denominator bound on the unit circle -/

/-- A Poisson denominator cannot vanish on the unit circle when
`0 ≤ η < 1`. -/
theorem one_sub_real_mul_ne_zero_of_norm_eq_one
    {η : ℝ} {w : ℂ}
    (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hw : ‖w‖ = 1) :
    1 - (η : ℂ) * w ≠ 0 := by
  intro hzero
  have hmul : (η : ℂ) * w = 1 :=
    (sub_eq_zero.mp hzero).symm
  have hnorm := congrArg norm hmul
  have hηeq : η = 1 := by
    simpa [norm_mul, hw, Real.norm_eq_abs,
      abs_of_nonneg hη0] using hnorm
  linarith

/-- Reverse triangle inequality gives the uniform lower bound
`1 - η ≤ ‖1 - ηw‖` on the unit circle. -/
theorem one_sub_real_le_norm_one_sub_real_mul
    {η : ℝ} {w : ℂ}
    (hη0 : 0 ≤ η)
    (hw : ‖w‖ = 1) :
    1 - η ≤ ‖1 - (η : ℂ) * w‖ := by
  have hreverse :
      ‖(1 : ℂ)‖ - ‖(η : ℂ) * w‖ ≤
        ‖(1 : ℂ) - (η : ℂ) * w‖ :=
    norm_sub_norm_le (1 : ℂ) ((η : ℂ) * w)
  simpa [norm_mul, hw, Real.norm_eq_abs,
    abs_of_nonneg hη0] using hreverse

/-- On the unit circle the zero-residual condition selects the literal
reciprocal, with no extra branch. -/
theorem reciprocalResidual_eq_zero_iff_eq_inv_of_unit
    {η : ℝ} {w g : ℂ}
    (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hw : ‖w‖ = 1) :
    reciprocalResidual (η : ℂ) w g = 0 ↔
      g = (1 - (η : ℂ) * w)⁻¹ :=
  reciprocalResidual_eq_zero_iff_eq_inv
    (η : ℂ) w g
    (one_sub_real_mul_ne_zero_of_norm_eq_one
      hη0 hη1 hw)

/-- The reciprocal selected on the unit circle has the expected uniform
norm bound. -/
theorem norm_inv_one_sub_real_mul_le
    {η : ℝ} {w : ℂ}
    (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hw : ‖w‖ = 1) :
    ‖(1 - (η : ℂ) * w)⁻¹‖ ≤ (1 - η)⁻¹ := by
  rw [norm_inv]
  have hgap : 0 < 1 - η := by
    linarith
  have hlower :=
    one_sub_real_le_norm_one_sub_real_mul hη0 hw
  have hnorm : 0 < ‖1 - (η : ℂ) * w‖ :=
    hgap.trans_le hlower
  exact (inv_le_inv₀ hnorm hgap).2 hlower

end

end HGAS
