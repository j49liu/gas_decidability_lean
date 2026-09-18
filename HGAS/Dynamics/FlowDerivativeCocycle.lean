import HGAS.Dynamics.InvariantFlowCocycle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# From a flow derivative to its time-one cocycle

The affine-chart obstruction is stated using the exact time-one increment

```
             z(ϕ 1 x) - z(x) = ∫ t in 0..1, g(ϕ t x).
```

For an ODE this identity is simply the fundamental theorem of calculus.
This small module records that passage once, both in scalar and
finite-coordinate form.
-/

noncomputable section

open MeasureTheory Set
open scoped Interval

namespace HGAS.Dynamics

variable {X : Type*} [TopologicalSpace X]

/-- Integrating the derivative of a scalar coordinate along a flow gives
its exact time-one increment. -/
theorem flow_increment_eq_intervalIntegral
    (ϕ : Flow ℝ X)
    (z : X → ℝ) (g : X → ℝ)
    (hderiv :
      ∀ x t,
        HasDerivAt (fun s ↦ z (ϕ s x)) (g (ϕ t x)) t)
    (hg : Continuous g) :
    ∀ x,
      z (ϕ 1 x) - z x =
        ∫ t in (0 : ℝ)..1, g (ϕ t x) := by
  intro x
  symm
  have hcurve :
      Continuous (fun t : ℝ ↦ ϕ t x) :=
    ϕ.continuous continuous_id continuous_const
  have hint :
      IntervalIntegrable (fun t ↦ g (ϕ t x)) volume 0 1 :=
    (hg.comp hcurve).intervalIntegrable 0 1
  simpa only [ϕ.map_zero_apply] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ ↦ hderiv x t) hint

/-- Coordinatewise finite-dimensional version of
`flow_increment_eq_intervalIntegral`. -/
theorem flow_coordinateIncrement_eq_intervalIntegral
    {m : ℕ}
    (ϕ : Flow ℝ X)
    (z : X → (Fin m → ℝ))
    (g : X → (Fin m → ℝ))
    (hderiv :
      ∀ x i t,
        HasDerivAt
          (fun s ↦ z (ϕ s x) i)
          (g (ϕ t x) i) t)
    (hg : Continuous g) :
    ∀ x i,
      z (ϕ 1 x) i - z x i =
        ∫ t in (0 : ℝ)..1, g (ϕ t x) i := by
  intro x i
  apply flow_increment_eq_intervalIntegral
    ϕ (fun y ↦ z y i) (fun y ↦ g y i)
    (fun y t ↦ hderiv y i t)
  exact (continuous_apply i).comp hg

end HGAS.Dynamics

end
