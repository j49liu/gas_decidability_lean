import HGAS.Modular.RiccatiJetIntegration
import HGAS.Modular.UnaryLambdaDynamics
import Mathlib.Tactic

/-!
# Two-jet reconstruction from a lifted modular solution

This module formalizes the cancellation at the heart of the complete
integral for the unary modular system.  It is intentionally stated for an
arbitrary reference solution rather than only for the theta constants.
That makes the result reusable whenever two solutions have the same
lambda coordinate.

Let `z` be a solution in the original independent variable and let `r` be
a reference solution evaluated at a lifted parameter `T`.  Put

```
       v = (A_z + C_z) / (A_r + C_r),
       u = (E_z - v E_r) / (6 i / π).
```

If the two lambda coordinates agree, then

```
       A_z = v A_r,   C_z = v C_r,
       E_z = v E_r + (6 i / π) u.
```

The original trajectory has clock multiplier `πi`, while the lifted
reference trajectory has multiplier `πiv`.  Direct differentiation and
polynomial cancellation then give

```
                         v' = -2uv,
                         u' = -u².
```

Consequently, as soon as the lifted parameter satisfies `T'=v`, the triple
`(u,v,T)` is exactly the Riccati two-jet integrated in
`RiccatiJetIntegration`.  In particular `T` is fractional linear.

The only nonvanishing hypotheses are the two denominators `A+C`; no theta
constant is divided by separately.
-/

namespace HGAS.Modular

open Complex

noncomputable section

/-- A unary modular trajectory whose complex clock multiplier may vary
with real time. -/
structure IsVariableScaledUnaryModularTrajectory
    (κ : ℝ → ℂ) (z : ℝ → UnaryModularState ℂ) : Prop where
  A : ∀ t : ℝ,
    HasDerivAt (fun s ↦ (z s).A)
      (κ t * (UnaryModularState.vectorField (z t)).A) t
  C : ∀ t : ℝ,
    HasDerivAt (fun s ↦ (z s).C)
      (κ t * (UnaryModularState.vectorField (z t)).C) t
  E : ∀ t : ℝ,
    HasDerivAt (fun s ↦ (z s).E)
      (κ t * (UnaryModularState.vectorField (z t)).E) t
  Y : ∀ t : ℝ,
    HasDerivAt (fun s ↦ (z s).Y)
      (κ t * (UnaryModularState.vectorField (z t)).Y) t

namespace IsVariableScaledUnaryModularTrajectory

variable {κ : ℝ → ℂ} {z : ℝ → UnaryModularState ℂ}

/-- Derivative of `B=A+C` for a variable-clock trajectory. -/
theorem B_hasDerivAt
    (hz : IsVariableScaledUnaryModularTrajectory κ z)
    (t : ℝ) :
    HasDerivAt
      (fun s ↦ UnaryModularState.B (z s))
      (κ t * UnaryModularState.BLie (z t)) t := by
  have hraw := (hz.A t).add (hz.C t)
  convert hraw using 1
  simp only [UnaryModularState.BLie]
  ring

end IsVariableScaledUnaryModularTrajectory

/-- The standard complex multiplier converting the paper-normalized
derivation into differentiation in the modular variable. -/
def modularIndependentVariableClock : ℂ :=
  (Real.pi : ℂ) * I

/-- The quasimodular anomaly coefficient in the complete unary integral. -/
def modularEisensteinAnomaly : ℂ :=
  6 * I / (Real.pi : ℂ)

theorem modularIndependentVariableClock_ne_zero :
    modularIndependentVariableClock ≠ 0 := by
  exact mul_ne_zero
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    I_ne_zero

theorem modularEisensteinAnomaly_ne_zero :
    modularEisensteinAnomaly ≠ 0 := by
  exact div_ne_zero
    (mul_ne_zero (by norm_num) I_ne_zero)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)

@[simp] theorem complex_I_pow_three :
    (I : ℂ) ^ 3 = -I := by
  rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_add,
    I_sq, pow_one, neg_one_mul]

/-- The two normalization constants have precisely the product needed in
the Riccati cancellation. -/
theorem modularClock_mul_EisensteinAnomaly :
    modularIndependentVariableClock *
      modularEisensteinAnomaly = -6 := by
  unfold modularIndependentVariableClock
    modularEisensteinAnomaly
  field_simp [Real.pi_ne_zero]
  exact I_sq

/-- Relative weight-two scale between an original state and a reference
state. -/
def unaryComparisonV
    (z r : ℝ → UnaryModularState ℂ) (t : ℝ) : ℂ :=
  UnaryModularState.B (z t) /
    UnaryModularState.B (r t)

/-- Relative quasimodular two-jet coordinate. -/
def unaryComparisonU
    (z r : ℝ → UnaryModularState ℂ) (t : ℝ) : ℂ :=
  ((z t).E - unaryComparisonV z r t * (r t).E) /
    modularEisensteinAnomaly

/-- Equality of lambda coordinates forces equality of the `A` coordinate
after applying the relative weight-two scale. -/
theorem unaryComparison_A_eq
    (z r : ℝ → UnaryModularState ℂ) (t : ℝ)
    (hBz : UnaryModularState.B (z t) ≠ 0)
    (hBr : UnaryModularState.B (r t) ≠ 0)
    (hLambda :
      UnaryModularState.lambdaCoordinate (z t) =
        UnaryModularState.lambdaCoordinate (r t)) :
    (z t).A = unaryComparisonV z r t * (r t).A := by
  unfold UnaryModularState.lambdaCoordinate at hLambda
  unfold unaryComparisonV
  field_simp [hBz, hBr] at hLambda ⊢
  linear_combination hLambda

/-- The relative scale carries the reference `B` coordinate to the
original `B` coordinate. -/
theorem unaryComparison_B_eq
    (z r : ℝ → UnaryModularState ℂ) (t : ℝ)
    (hBr : UnaryModularState.B (r t) ≠ 0) :
    UnaryModularState.B (z t) =
      unaryComparisonV z r t *
        UnaryModularState.B (r t) := by
  unfold unaryComparisonV
  field_simp

/-- Equality of lambda coordinates also forces the scaled `C`
identity. -/
theorem unaryComparison_C_eq
    (z r : ℝ → UnaryModularState ℂ) (t : ℝ)
    (hBz : UnaryModularState.B (z t) ≠ 0)
    (hBr : UnaryModularState.B (r t) ≠ 0)
    (hLambda :
      UnaryModularState.lambdaCoordinate (z t) =
        UnaryModularState.lambdaCoordinate (r t)) :
    (z t).C = unaryComparisonV z r t * (r t).C := by
  have hA :=
    unaryComparison_A_eq z r t hBz hBr hLambda
  have hB := unaryComparison_B_eq z r t hBr
  simp only [UnaryModularState.B] at hB
  linear_combination hB - hA

/-- The definition of `u` is equivalently the affine transformation law
for the quasimodular `E` coordinate. -/
theorem unaryComparison_E_eq
    (z r : ℝ → UnaryModularState ℂ) (t : ℝ) :
    (z t).E =
      unaryComparisonV z r t * (r t).E +
        modularEisensteinAnomaly *
          unaryComparisonU z r t := by
  unfold unaryComparisonU
  field_simp [modularEisensteinAnomaly_ne_zero]
  ring

/-- The reference trajectory hypothesis used in the two-jet
reconstruction: its clock is the standard modular clock multiplied by the
relative derivative `v`. -/
def IsUnaryComparisonReferenceTrajectory
    (z r : ℝ → UnaryModularState ℂ) : Prop :=
  IsVariableScaledUnaryModularTrajectory
    (fun t ↦
      modularIndependentVariableClock *
        unaryComparisonV z r t)
    r

/-- Exact first two-jet equation `v'=-2uv`. -/
theorem unaryComparisonV_hasDerivAt
    {z r : ℝ → UnaryModularState ℂ}
    (hz :
      IsScaledUnaryModularTrajectory
        modularIndependentVariableClock z)
    (hr : IsUnaryComparisonReferenceTrajectory z r)
    (hBz : ∀ t, UnaryModularState.B (z t) ≠ 0)
    (hBr : ∀ t, UnaryModularState.B (r t) ≠ 0)
    (hLambda : ∀ t,
      UnaryModularState.lambdaCoordinate (z t) =
        UnaryModularState.lambdaCoordinate (r t))
    (t : ℝ) :
    HasDerivAt
      (unaryComparisonV z r)
      (-2 * unaryComparisonU z r t *
        unaryComparisonV z r t) t := by
  have hraw :=
    (hz.B_hasDerivAt t).div
      (hr.B_hasDerivAt t) (hBr t)
  have hA :=
    unaryComparison_A_eq z r t
      (hBz t) (hBr t) (hLambda t)
  have hC :=
    unaryComparison_C_eq z r t
      (hBz t) (hBr t) (hLambda t)
  have hB :=
    unaryComparison_B_eq z r t (hBr t)
  have hE := unaryComparison_E_eq z r t
  convert hraw using 1
  simp only [UnaryModularState.BLie_eq]
  rw [hA, hC, hB, hE]
  field_simp [hBr t]
  linear_combination
    (-(unaryComparisonU z r t *
      unaryComparisonV z r t)) *
        modularClock_mul_EisensteinAnomaly

/-- Exact Riccati equation `u'=-u²`. -/
theorem unaryComparisonU_hasDerivAt
    {z r : ℝ → UnaryModularState ℂ}
    (hz :
      IsScaledUnaryModularTrajectory
        modularIndependentVariableClock z)
    (hr : IsUnaryComparisonReferenceTrajectory z r)
    (hBz : ∀ t, UnaryModularState.B (z t) ≠ 0)
    (hBr : ∀ t, UnaryModularState.B (r t) ≠ 0)
    (hLambda : ∀ t,
      UnaryModularState.lambdaCoordinate (z t) =
        UnaryModularState.lambdaCoordinate (r t))
    (t : ℝ) :
    HasDerivAt
      (unaryComparisonU z r)
      (-(unaryComparisonU z r t) ^ 2) t := by
  have hv :=
    unaryComparisonV_hasDerivAt
      hz hr hBz hBr hLambda t
  have hraw :=
    ((hz.E t).sub (hv.mul (hr.E t))).div_const
      modularEisensteinAnomaly
  have hA :=
    unaryComparison_A_eq z r t
      (hBz t) (hBr t) (hLambda t)
  have hC :=
    unaryComparison_C_eq z r t
      (hBz t) (hBr t) (hLambda t)
  have hE := unaryComparison_E_eq z r t
  convert hraw using 1
  simp only [UnaryModularState.vectorField]
  rw [hA, hC, hE]
  field_simp [modularEisensteinAnomaly_ne_zero]
  linear_combination
    (-(2 * unaryComparisonU z r t *
          unaryComparisonV z r t * (r t).E +
        unaryComparisonU z r t ^ 2 *
          modularEisensteinAnomaly)) *
      modularClock_mul_EisensteinAnomaly

/-- **Modular two-jet reconstruction.**  A lambda lift whose derivative is
the relative weight-two scale produces a Riccati jet and hence a
fractional-linear lifted parameter. -/
theorem unaryComparison_isRiccatiJetTrajectory
    {z r : ℝ → UnaryModularState ℂ}
    {T : ℝ → ℂ}
    (hz :
      IsScaledUnaryModularTrajectory
        modularIndependentVariableClock z)
    (hr : IsUnaryComparisonReferenceTrajectory z r)
    (hBz : ∀ t, UnaryModularState.B (z t) ≠ 0)
    (hBr : ∀ t, UnaryModularState.B (r t) ≠ 0)
    (hLambda : ∀ t,
      UnaryModularState.lambdaCoordinate (z t) =
        UnaryModularState.lambdaCoordinate (r t))
    (hT : ∀ t,
      HasDerivAt T (unaryComparisonV z r t) t) :
    IsRiccatiJetTrajectory
      (unaryComparisonU z r)
      (unaryComparisonV z r)
      T where
  u_eq :=
    unaryComparisonU_hasDerivAt
      hz hr hBz hBr hLambda
  v_eq :=
    unaryComparisonV_hasDerivAt
      hz hr hBz hBr hLambda
  T_eq := hT

/-- Expanded fractional-linear formula for every reconstructed lift. -/
theorem unaryComparison_T_eq_fractionalLinear
    {z r : ℝ → UnaryModularState ℂ}
    {T : ℝ → ℂ}
    (hz :
      IsScaledUnaryModularTrajectory
        modularIndependentVariableClock z)
    (hr : IsUnaryComparisonReferenceTrajectory z r)
    (hBz : ∀ t, UnaryModularState.B (z t) ≠ 0)
    (hBr : ∀ t, UnaryModularState.B (r t) ≠ 0)
    (hLambda : ∀ t,
      UnaryModularState.lambdaCoordinate (z t) =
        UnaryModularState.lambdaCoordinate (r t))
    (hT : ∀ t,
      HasDerivAt T (unaryComparisonV z r t) t)
    (t₀ t : ℝ) :
    T t =
      T t₀ +
        unaryComparisonV z r t₀ *
          ((t - t₀ : ℝ) : ℂ) /
          (1 + unaryComparisonU z r t₀ *
            ((t - t₀ : ℝ) : ℂ)) := by
  exact
    (unaryComparison_isRiccatiJetTrajectory
      hz hr hBz hBr hLambda hT).T_eq_fractionalLinear
        t₀ t

end

end HGAS.Modular
