import HGAS.Analysis.LinearODEZero
import HGAS.Modular.UnaryAlgebra
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Trajectory-level invariance for the unary modular block

`UnaryAlgebra` proves the polynomial Lie-derivative identities.  This file
turns the first of those formal identities into an honest statement about
every differentiable complex trajectory.

Physical trajectories in the paper satisfy

```
                         Z'(t) = κ · D Z(t),
```

with the constant `κ = i ω`.  Keeping an arbitrary complex scale `κ`
makes the result insensitive to the chosen clock normalization.

The key point is not merely that the Jacobi residual has zero derivative
*on* its zero set.  Along an arbitrary trajectory it satisfies a scalar
linear homogeneous ODE.  The reusable uniqueness theorem in
`Analysis.LinearODEZero` therefore proves that vanishing at one time forces
vanishing at every time.
-/

namespace HGAS.Modular

open HGAS

noncomputable section

/-- Componentwise formulation of a trajectory of the complex unary modular
system, with a constant complex clock multiplier `κ`. -/
structure IsScaledUnaryModularTrajectory
    (κ : ℂ) (z : ℝ → UnaryModularState ℂ) : Prop where
  A : ∀ t : ℝ,
    HasDerivAt (fun s ↦ (z s).A)
      (κ * (UnaryModularState.vectorField (z t)).A) t
  C : ∀ t : ℝ,
    HasDerivAt (fun s ↦ (z s).C)
      (κ * (UnaryModularState.vectorField (z t)).C) t
  E : ∀ t : ℝ,
    HasDerivAt (fun s ↦ (z s).E)
      (κ * (UnaryModularState.vectorField (z t)).E) t
  Y : ∀ t : ℝ,
    HasDerivAt (fun s ↦ (z s).Y)
      (κ * (UnaryModularState.vectorField (z t)).Y) t

namespace IsScaledUnaryModularTrajectory

variable {κ : ℂ} {z : ℝ → UnaryModularState ℂ}

/-- Coordinate continuity extracted from the trajectory equations. -/
theorem continuous_A (hz : IsScaledUnaryModularTrajectory κ z) :
    Continuous (fun t ↦ (z t).A) :=
  continuous_iff_continuousAt.mpr fun t ↦ (hz.A t).continuousAt

/-- Coordinate continuity extracted from the trajectory equations. -/
theorem continuous_C (hz : IsScaledUnaryModularTrajectory κ z) :
    Continuous (fun t ↦ (z t).C) :=
  continuous_iff_continuousAt.mpr fun t ↦ (hz.C t).continuousAt

/-- Coordinate continuity extracted from the trajectory equations. -/
theorem continuous_E (hz : IsScaledUnaryModularTrajectory κ z) :
    Continuous (fun t ↦ (z t).E) :=
  continuous_iff_continuousAt.mpr fun t ↦ (hz.E t).continuousAt

/-- Coordinate continuity extracted from the trajectory equations. -/
theorem continuous_Y (hz : IsScaledUnaryModularTrajectory κ z) :
    Continuous (fun t ↦ (z t).Y) :=
  continuous_iff_continuousAt.mpr fun t ↦ (hz.Y t).continuousAt

/-- Along every scaled trajectory, the Jacobi residual satisfies its exact
scalar linear evolution equation. -/
theorem jacobiResidual_hasDerivAt
    (hz : IsScaledUnaryModularTrajectory κ z) (t : ℝ) :
    HasDerivAt
      (fun s ↦ UnaryModularState.jacobiResidual (z s))
      (κ * ((1 / 3 : ℂ) * ((z t).E + (z t).A - (z t).C)) *
        UnaryModularState.jacobiResidual (z t)) t := by
  have hraw :=
    (((hz.Y t).fun_pow 4).sub (hz.A t)).sub (hz.C t)
  convert hraw using 1
  change
    κ * ((1 / 3 : ℂ) * ((z t).E + (z t).A - (z t).C)) *
          UnaryModularState.jacobiResidual (z t) =
      4 * (z t).Y ^ 3 *
          (κ * (UnaryModularState.vectorField (z t)).Y) -
        κ * (UnaryModularState.vectorField (z t)).A -
        κ * (UnaryModularState.vectorField (z t)).C
  calc
    _ = κ * UnaryModularState.jacobiResidualLie (z t) := by
      rw [UnaryModularState.jacobiResidualLie_eq]
      ring
    _ = _ := by
      simp only [UnaryModularState.jacobiResidualLie]
      ring

/-- The complex coefficient in the residual equation, regarded as a real
continuous linear endomorphism of `ℂ`. -/
def jacobiResidualOperator (κ : ℂ)
    (z : ℝ → UnaryModularState ℂ) (t : ℝ) : ℂ →L[ℝ] ℂ :=
  ContinuousLinearMap.lsmul ℝ ℂ
    (κ * ((1 / 3 : ℂ) * ((z t).E + (z t).A - (z t).C)))

/-- The residual operator varies continuously along every differentiable
trajectory. -/
theorem continuous_jacobiResidualOperator
    (hz : IsScaledUnaryModularTrajectory κ z) :
    Continuous (jacobiResidualOperator κ z) := by
  have hA := continuous_A hz
  have hC := continuous_C hz
  have hE := continuous_E hz
  apply (ContinuousLinearMap.lsmul ℝ ℂ).continuous.comp
  fun_prop

/-- **Trajectory-level Jacobi invariance.**  If `Y⁴-A-C` vanishes at one
time of a complex scaled modular trajectory, it vanishes at every time. -/
theorem jacobiResidual_eq_zero
    (hz : IsScaledUnaryModularTrajectory κ z)
    {t₀ : ℝ}
    (hzero : UnaryModularState.jacobiResidual (z t₀) = 0) :
    ∀ t : ℝ, UnaryModularState.jacobiResidual (z t) = 0 := by
  have hident :=
    eq_zero_of_hasDerivAt_eq_continuousLinearMap
      (jacobiResidualOperator κ z)
      (fun t ↦ UnaryModularState.jacobiResidual (z t))
      (continuous_jacobiResidualOperator hz)
      (fun t ↦ by
        simpa [jacobiResidualOperator] using
          jacobiResidual_hasDerivAt hz t)
      hzero
  intro t
  exact congrFun hident t

/-! ## Invariant coordinate divisors -/

/-- The divisor `A=0` is invariant along every scaled trajectory. -/
theorem A_eq_zero
    (hz : IsScaledUnaryModularTrajectory κ z)
    {t₀ : ℝ} (hzero : (z t₀).A = 0) :
    ∀ t : ℝ, (z t).A = 0 := by
  let a : ℝ → ℂ :=
    fun t ↦ κ * ((1 / 3 : ℂ) *
      ((z t).E + (z t).A + 2 * (z t).C))
  have ha : Continuous a := by
    have hA := continuous_A hz
    have hC := continuous_C hz
    have hE := continuous_E hz
    fun_prop
  have hderiv :
      ∀ t : ℝ,
        HasDerivAt (fun s ↦ (z s).A)
          (a t * (z t).A) t := by
    intro t
    convert hz.A t using 1
    simp only [a, UnaryModularState.vectorField]
    ring
  have hident :=
    complex_eq_zero_of_hasDerivAt_eq_mul
      a (fun t ↦ (z t).A) ha hderiv hzero
  intro t
  exact congrFun hident t

/-- If `A` is nonzero at one time, it is nonzero for the entire
trajectory. -/
theorem A_ne_zero
    (hz : IsScaledUnaryModularTrajectory κ z)
    {t₀ : ℝ} (hA₀ : (z t₀).A ≠ 0) :
    ∀ t : ℝ, (z t).A ≠ 0 := by
  intro t hAt
  exact hA₀ (hz.A_eq_zero hAt t₀)

/-- The divisor `C=0` is invariant along every scaled trajectory. -/
theorem C_eq_zero
    (hz : IsScaledUnaryModularTrajectory κ z)
    {t₀ : ℝ} (hzero : (z t₀).C = 0) :
    ∀ t : ℝ, (z t).C = 0 := by
  let a : ℝ → ℂ :=
    fun t ↦ κ * ((1 / 3 : ℂ) *
      ((z t).E - 2 * (z t).A - (z t).C))
  have ha : Continuous a := by
    have hA := continuous_A hz
    have hC := continuous_C hz
    have hE := continuous_E hz
    fun_prop
  have hderiv :
      ∀ t : ℝ,
        HasDerivAt (fun s ↦ (z s).C)
          (a t * (z t).C) t := by
    intro t
    convert hz.C t using 1
    simp only [a, UnaryModularState.vectorField]
    ring
  have hident :=
    complex_eq_zero_of_hasDerivAt_eq_mul
      a (fun t ↦ (z t).C) ha hderiv hzero
  intro t
  exact congrFun hident t

/-- If `C` is nonzero at one time, it is nonzero for the entire
trajectory. -/
theorem C_ne_zero
    (hz : IsScaledUnaryModularTrajectory κ z)
    {t₀ : ℝ} (hC₀ : (z t₀).C ≠ 0) :
    ∀ t : ℝ, (z t).C ≠ 0 := by
  intro t hCt
  exact hC₀ (hz.C_eq_zero hCt t₀)

/-- The divisor `Y=0` is invariant along every scaled trajectory. -/
theorem Y_eq_zero
    (hz : IsScaledUnaryModularTrajectory κ z)
    {t₀ : ℝ} (hzero : (z t₀).Y = 0) :
    ∀ t : ℝ, (z t).Y = 0 := by
  let a : ℝ → ℂ :=
    fun t ↦ κ * ((1 / 12 : ℂ) *
      ((z t).E + (z t).A - (z t).C))
  have ha : Continuous a := by
    have hA := continuous_A hz
    have hC := continuous_C hz
    have hE := continuous_E hz
    fun_prop
  have hderiv :
      ∀ t : ℝ,
        HasDerivAt (fun s ↦ (z s).Y)
          (a t * (z t).Y) t := by
    intro t
    convert hz.Y t using 1
    simp only [a, UnaryModularState.vectorField]
    ring
  have hident :=
    complex_eq_zero_of_hasDerivAt_eq_mul
      a (fun t ↦ (z t).Y) ha hderiv hzero
  intro t
  exact congrFun hident t

/-- The divisor `A+C=0` is invariant.  This is the third degenerate
component used in the recurrent-orbit classification. -/
theorem B_eq_zero
    (hz : IsScaledUnaryModularTrajectory κ z)
    {t₀ : ℝ}
    (hzero : UnaryModularState.B (z t₀) = 0) :
    ∀ t : ℝ, UnaryModularState.B (z t) = 0 := by
  let a : ℝ → ℂ :=
    fun t ↦ κ * ((1 / 3 : ℂ) *
      ((z t).E + (z t).A - (z t).C))
  have ha : Continuous a := by
    have hA := continuous_A hz
    have hC := continuous_C hz
    have hE := continuous_E hz
    fun_prop
  have hderiv :
      ∀ t : ℝ,
        HasDerivAt
          (fun s ↦ UnaryModularState.B (z s))
          (a t * UnaryModularState.B (z t)) t := by
    intro t
    have hsum := (hz.A t).add (hz.C t)
    convert hsum using 1
    change
      a t * UnaryModularState.B (z t) =
        κ * (UnaryModularState.vectorField (z t)).A +
          κ * (UnaryModularState.vectorField (z t)).C
    rw [← mul_add]
    change
      a t * UnaryModularState.B (z t) =
        κ * UnaryModularState.BLie (z t)
    rw [UnaryModularState.BLie_eq]
    simp only [a]
    ring
  have hident :=
    complex_eq_zero_of_hasDerivAt_eq_mul
      a (fun t ↦ UnaryModularState.B (z t)) ha hderiv hzero
  intro t
  exact congrFun hident t

end IsScaledUnaryModularTrajectory

end

end HGAS.Modular
