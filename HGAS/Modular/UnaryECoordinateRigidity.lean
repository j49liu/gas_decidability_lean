import HGAS.Modular.UnaryDynamics
import Mathlib.Tactic

/-!
# Rigidity of the unary Eisenstein coordinate

The polynomial unary state contains the quasimodular coordinate `E`.
Once two nondegenerate trajectories have the same `A`, `C`, and `Y`
coordinates, `E` is not an independent choice.  Indeed,

```text
  Y' = κ · (E + A - C)Y / 12.
```

For a nonzero clock `κ` and nonvanishing `Y`, equality of the two `Y`
curves and uniqueness of their derivatives forces equality of `E`
pointwise.  This small cancellation lemma is reusable whenever a
projective modular identification has already fixed the three theta
coordinates but not the quasimodular lift.
-/

namespace HGAS.Modular

noncomputable section

/-- Equality of `A`, `C`, and a nonzero `Y` along two trajectories with
the same nonzero clock forces equality of their `E` coordinates. -/
theorem unaryE_eq_of_A_C_Y_eq
    {κ : ℂ} (hκ : κ ≠ 0)
    {z r : ℝ → UnaryModularState ℂ}
    (hz : IsScaledUnaryModularTrajectory κ z)
    (hr : IsScaledUnaryModularTrajectory κ r)
    (hA : ∀ t, (z t).A = (r t).A)
    (hC : ∀ t, (z t).C = (r t).C)
    (hY : ∀ t, (z t).Y = (r t).Y)
    (hYne : ∀ t, (r t).Y ≠ 0) :
    ∀ t, (z t).E = (r t).E := by
  intro t
  have hrY :
      HasDerivAt
        (fun s ↦ (z s).Y)
        (κ * (UnaryModularState.vectorField (r t)).Y) t :=
    (hr.Y t).congr_of_eventuallyEq
      (Filter.Eventually.of_forall hY)
  have hderivative :=
    (hz.Y t).unique hrY
  simp only [UnaryModularState.vectorField] at hderivative
  rw [hA t, hC t, hY t] at hderivative
  have hfactor :
      κ * (1 / 12 : ℂ) * (r t).Y ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero hκ (by norm_num))
      (hYne t)
  have hscaled :
      (κ * (1 / 12 : ℂ) * (r t).Y) * (z t).E =
        (κ * (1 / 12 : ℂ) * (r t).Y) * (r t).E := by
    linear_combination hderivative
  exact mul_left_cancel₀ hfactor hscaled

end

end HGAS.Modular
