import HGAS.Modular.UnaryDynamics
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

/-!
# The modular-lambda coordinate of the unary system

Away from the divisor `A+C=0`, the quotient

```
                       ℓ = A/(A+C)
```

satisfies the autonomous covering equation

```
                       ℓ' = κ B ℓ(1-ℓ),
                       B = A+C,
```

along a trajectory scaled by `κ`.  This is the trajectory-level version
of `UnaryModularState.lambdaQuotientNumeratorLie_eq` and is the entry
point for lifting a generic solution through the modular lambda covering.
-/

namespace HGAS.Modular

noncomputable section

/-- The lambda quotient of a unary state. -/
def UnaryModularState.lambdaCoordinate
    (z : UnaryModularState ℂ) : ℂ :=
  z.A / UnaryModularState.B z

namespace IsScaledUnaryModularTrajectory

variable {κ : ℂ} {z : ℝ → UnaryModularState ℂ}

/-- Derivative of `B=A+C` along a scaled unary trajectory. -/
theorem B_hasDerivAt
    (hz : IsScaledUnaryModularTrajectory κ z)
    (t : ℝ) :
    HasDerivAt
      (fun s ↦ UnaryModularState.B (z s))
      (κ * UnaryModularState.BLie (z t)) t := by
  have hraw := (hz.A t).add (hz.C t)
  convert hraw using 1
  simp only [UnaryModularState.BLie]
  ring

/-- Exact derivative of the modular-lambda quotient at every point where
`B` is nonzero. -/
theorem lambdaCoordinate_hasDerivAt
    (hz : IsScaledUnaryModularTrajectory κ z)
    (t : ℝ)
    (hB : UnaryModularState.B (z t) ≠ 0) :
    HasDerivAt
      (fun s ↦
        UnaryModularState.lambdaCoordinate (z s))
      (κ * UnaryModularState.B (z t) *
        UnaryModularState.lambdaCoordinate (z t) *
        (1 - UnaryModularState.lambdaCoordinate (z t))) t := by
  have hquot :=
    (hz.A t).div (hz.B_hasDerivAt t) hB
  convert hquot using 1
  unfold UnaryModularState.lambdaCoordinate
  change
    (κ * UnaryModularState.B (z t)) *
        ((z t).A / UnaryModularState.B (z t)) *
          (1 - (z t).A /
            UnaryModularState.B (z t)) =
      (κ * (UnaryModularState.vectorField (z t)).A *
          UnaryModularState.B (z t) -
        (z t).A *
          (κ * UnaryModularState.BLie (z t))) /
        UnaryModularState.B (z t) ^ 2
  rw [show
      κ * (UnaryModularState.vectorField (z t)).A *
            UnaryModularState.B (z t) -
          (z t).A *
            (κ * UnaryModularState.BLie (z t)) =
        κ *
          UnaryModularState.lambdaQuotientNumeratorLie
            (z t) by
      simp only [UnaryModularState.lambdaQuotientNumeratorLie]
      ring,
    UnaryModularState.lambdaQuotientNumeratorLie_eq]
  have hC :
      (z t).C =
        UnaryModularState.B (z t) - (z t).A := by
    simp [UnaryModularState.B]
  rw [hC]
  field_simp [hB]

/-- If `B` is nonzero at one time, it is nonzero at every time.  This is
the contrapositive form of divisor invariance and lets the lambda quotient
be used globally along a generic trajectory. -/
theorem B_ne_zero
    (hz : IsScaledUnaryModularTrajectory κ z)
    {t₀ : ℝ}
    (hB₀ : UnaryModularState.B (z t₀) ≠ 0) :
    ∀ t : ℝ, UnaryModularState.B (z t) ≠ 0 := by
  intro t hBt
  have hBall := hz.B_eq_zero hBt
  exact hB₀ (hBall t₀)

/-- Global lambda-coordinate differential equation on a trajectory which
starts off the divisor `B=0`. -/
theorem lambdaCoordinate_hasDerivAt_of_initial
    (hz : IsScaledUnaryModularTrajectory κ z)
    {t₀ : ℝ}
    (hB₀ : UnaryModularState.B (z t₀) ≠ 0)
    (t : ℝ) :
    HasDerivAt
      (fun s ↦
        UnaryModularState.lambdaCoordinate (z s))
      (κ * UnaryModularState.B (z t) *
        UnaryModularState.lambdaCoordinate (z t) *
        (1 - UnaryModularState.lambdaCoordinate (z t))) t :=
  hz.lambdaCoordinate_hasDerivAt t
    (hz.B_ne_zero hB₀ t)

end IsScaledUnaryModularTrajectory

end

end HGAS.Modular
