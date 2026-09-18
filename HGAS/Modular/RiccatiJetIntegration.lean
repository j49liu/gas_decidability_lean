import HGAS.Analysis.LinearODEZero
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic

/-!
# Exact integration of the modular Riccati two-jet

The local completeness argument for the unary modular system reconstructs
three functions satisfying

```
                  u' = -u²,   v' = -2uv,   T' = v.
```

This module integrates that system without appealing to a closed-form ODE
solver.  Relative to a base time `t₀`, put

```
                   d(t) = 1 + u(t₀)(t-t₀).
```

Linear residual equations first give

```
                   d(t)u(t) = u(t₀),
                   d(t)²v(t) = v(t₀).
```

They also show that `d` cannot vanish along a globally defined solution.
A final elementary differentiation then yields

```
 T(t) = T(t₀) + v(t₀)(t-t₀)/d(t).
```

These are exactly the affine and fractional-linear formulas used in the
paper's reconstruction of the modular state.
-/

namespace HGAS.Modular

open HGAS

noncomputable section

/-- A real-parametrized complex solution of the Riccati two-jet system. -/
structure IsRiccatiJetTrajectory
    (u v T : ℝ → ℂ) : Prop where
  u_eq : ∀ t : ℝ,
    HasDerivAt u (-(u t) ^ 2) t
  v_eq : ∀ t : ℝ,
    HasDerivAt v (-2 * u t * v t) t
  T_eq : ∀ t : ℝ,
    HasDerivAt T (v t) t

namespace IsRiccatiJetTrajectory

variable {u v T : ℝ → ℂ}

/-- The affine denominator determined by the initial Riccati value. -/
def denominator (u : ℝ → ℂ) (t₀ t : ℝ) : ℂ :=
  1 + u t₀ * ((t - t₀ : ℝ) : ℂ)

/-- Derivative of the affine denominator. -/
theorem denominator_hasDerivAt
    (u : ℝ → ℂ) (t₀ t : ℝ) :
    HasDerivAt (denominator u t₀) (u t₀) t := by
  have hdelta :
      HasDerivAt
        (fun s : ℝ ↦ ((s - t₀ : ℝ) : ℂ)) 1 t :=
    ((hasDerivAt_id t).sub_const t₀).ofReal_comp
  have hmul := HasDerivAt.const_mul (u t₀) hdelta
  convert (hasDerivAt_const t (1 : ℂ)).add hmul using 1
  all_goals simp

@[simp] theorem denominator_at_base
    (u : ℝ → ℂ) (t₀ : ℝ) :
    denominator u t₀ t₀ = 1 := by
  simp [denominator]

/-- First exact integral:
`d(t)u(t)=u(t₀)`. -/
theorem denominator_mul_u
    (h : IsRiccatiJetTrajectory u v T)
    (t₀ t : ℝ) :
    denominator u t₀ t * u t = u t₀ := by
  let r : ℝ → ℂ :=
    fun s ↦ denominator u t₀ s * u s - u t₀
  have huContinuous : Continuous u :=
    continuous_iff_continuousAt.mpr
      fun s ↦ (h.u_eq s).continuousAt
  have hr :
      ∀ s : ℝ,
        HasDerivAt r ((-u s) * r s) s := by
    intro s
    have hraw :=
      ((denominator_hasDerivAt u t₀ s).mul
        (h.u_eq s)).sub_const (u t₀)
    convert hraw using 1
    simp only [r]
    ring
  have hrzero :
      r = fun _ ↦ 0 := by
    exact
      complex_eq_zero_of_hasDerivAt_eq_mul
        (fun s ↦ -u s) r huContinuous.neg hr
        (t₀ := t₀) (by simp [r])
  have ht := congrFun hrzero t
  simpa [r] using sub_eq_zero.mp ht

/-- The affine denominator cannot vanish anywhere along a globally defined
Riccati trajectory. -/
theorem denominator_ne_zero
    (h : IsRiccatiJetTrajectory u v T)
    (t₀ t : ℝ) :
    denominator u t₀ t ≠ 0 := by
  intro hzero
  have hu0 : u t₀ = 0 := by
    have hmul := h.denominator_mul_u t₀ t
    simpa [hzero] using hmul.symm
  simp [denominator, hu0] at hzero

/-- Explicit Riccati formula for `u`. -/
theorem u_eq_div_denominator
    (h : IsRiccatiJetTrajectory u v T)
    (t₀ t : ℝ) :
    u t = u t₀ / denominator u t₀ t := by
  apply (eq_div_iff (h.denominator_ne_zero t₀ t)).mpr
  rw [mul_comm]
  exact h.denominator_mul_u t₀ t

/-- Second exact integral:
`d(t)²v(t)=v(t₀)`. -/
theorem denominator_sq_mul_v
    (h : IsRiccatiJetTrajectory u v T)
    (t₀ t : ℝ) :
    denominator u t₀ t ^ 2 * v t = v t₀ := by
  let r : ℝ → ℂ :=
    fun s ↦ denominator u t₀ s ^ 2 * v s - v t₀
  have hr :
      ∀ s : ℝ, HasDerivAt r 0 s := by
    intro s
    have hdenSq :=
      (denominator_hasDerivAt u t₀ s).fun_pow 2
    have hraw :=
      (hdenSq.mul (h.v_eq s)).sub_const (v t₀)
    convert hraw using 1
    have hu :=
      h.denominator_mul_u t₀ s
    rw [← hu]
    ring
  have hrzero :
      r = fun _ ↦ 0 := by
    exact
      complex_eq_zero_of_hasDerivAt_eq_mul
        (fun _ ↦ 0) r continuous_const
        (fun s ↦ by simpa using hr s)
        (t₀ := t₀) (by simp [r])
  have ht := congrFun hrzero t
  simpa [r] using sub_eq_zero.mp ht

/-- Explicit formula for the scale derivative `v`. -/
theorem v_eq_div_denominator_sq
    (h : IsRiccatiJetTrajectory u v T)
    (t₀ t : ℝ) :
    v t = v t₀ / denominator u t₀ t ^ 2 := by
  apply
    (eq_div_iff
      (pow_ne_zero 2 (h.denominator_ne_zero t₀ t))).mpr
  rw [mul_comm]
  exact h.denominator_sq_mul_v t₀ t

/-- The fractional-linear candidate reconstructed from the initial
two-jet. -/
def fractionalLinearCandidate
    (u v T : ℝ → ℂ) (t₀ t : ℝ) : ℂ :=
  T t₀ +
    v t₀ * ((t - t₀ : ℝ) : ℂ) /
      denominator u t₀ t

@[simp] theorem fractionalLinearCandidate_at_base
    (u v T : ℝ → ℂ) (t₀ : ℝ) :
    fractionalLinearCandidate u v T t₀ t₀ = T t₀ := by
  simp [fractionalLinearCandidate]

/-- The fractional-linear candidate has derivative `v`. -/
theorem fractionalLinearCandidate_hasDerivAt
    (h : IsRiccatiJetTrajectory u v T)
    (t₀ t : ℝ) :
    HasDerivAt
      (fractionalLinearCandidate u v T t₀)
      (v t) t := by
  have hdelta :
      HasDerivAt
        (fun s : ℝ ↦ ((s - t₀ : ℝ) : ℂ)) 1 t :=
    ((hasDerivAt_id t).sub_const t₀).ofReal_comp
  have hnum :
      HasDerivAt
        (fun s : ℝ ↦
          v t₀ * ((s - t₀ : ℝ) : ℂ))
        (v t₀) t := by
    simpa using HasDerivAt.const_mul (v t₀) hdelta
  have hquot :=
    hnum.div (denominator_hasDerivAt u t₀ t)
      (h.denominator_ne_zero t₀ t)
  have hsum :=
    (hasDerivAt_const t (T t₀)).add hquot
  convert hsum using 1
  rw [zero_add]
  change
    v t =
      (v t₀ * denominator u t₀ t -
          v t₀ * ((t - t₀ : ℝ) : ℂ) * u t₀) /
        denominator u t₀ t ^ 2
  rw [h.v_eq_div_denominator_sq t₀ t]
  field_simp [h.denominator_ne_zero t₀ t]
  simp only [denominator]
  ring

/-- Exact fractional-linear integration of `T`. -/
theorem T_eq_fractionalLinearCandidate
    (h : IsRiccatiJetTrajectory u v T)
    (t₀ t : ℝ) :
    T t = fractionalLinearCandidate u v T t₀ t := by
  let r : ℝ → ℂ :=
    fun s ↦ T s -
      fractionalLinearCandidate u v T t₀ s
  have hr :
      ∀ s : ℝ, HasDerivAt r 0 s := by
    intro s
    have hraw :=
      (h.T_eq s).sub
        (h.fractionalLinearCandidate_hasDerivAt t₀ s)
    simpa [r] using hraw
  have hrzero :
      r = fun _ ↦ 0 := by
    exact
      complex_eq_zero_of_hasDerivAt_eq_mul
        (fun _ ↦ 0) r continuous_const
        (fun s ↦ by simpa using hr s)
        (t₀ := t₀) (by simp [r])
  have ht := congrFun hrzero t
  exact sub_eq_zero.mp (by simpa [r] using ht)

/-- Expanded fractional-linear formula. -/
theorem T_eq_fractionalLinear
    (h : IsRiccatiJetTrajectory u v T)
    (t₀ t : ℝ) :
    T t =
      T t₀ +
        v t₀ * ((t - t₀ : ℝ) : ℂ) /
          (1 + u t₀ * ((t - t₀ : ℝ) : ℂ)) := by
  simpa [fractionalLinearCandidate, denominator] using
    h.T_eq_fractionalLinearCandidate t₀ t

end IsRiccatiJetTrajectory

end

end HGAS.Modular
