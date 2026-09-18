import HGAS.Modular.HorizontalThetaFirstMoment
import Mathlib.Tactic

/-!
# Selecting the horizontal theta height

The first detector character may carry an arbitrary constant phase because
the selected clock orbit need not start at the phase origin.  Its norm is
one, however.  This module packages the final height argument in exactly
that phase-invariant form.

On a unit-speed horizontal line, the first `θ₃` moment is

```text
             η · 2 exp(π i x - π y),
```

where `‖η‖=1`.  Therefore the normalized value `1/128` forces
`exp(-πy)=1/256`, independently of both `x` and `η`.
-/

namespace HGAS.Modular

open Filter Topology

noncomputable section

/-- An arbitrary unit initial phase does not affect the height selected by
the normalized first harmonic. -/
theorem thetaGaugeHeight_of_horizontal_firstMoment
    (x y : ℝ) (hy : 0 < y)
    (η : ℂ) (hη : ‖η‖ = 1)
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop)
    (hmoment :
      Tendsto
        (fun n ↦
          HGAS.Analysis.cesaroMeanAt
            (fun t ↦
              theta₃ (horizontalLine x y 1 hy t) *
                (η * standardUnaryFirstCharacter t))
            (T n))
        atTop (𝓝 (1 / 128 : ℂ))) :
    y = thetaGaugeHeight := by
  have hbase :=
    cesaroMeanAt_theta₃_first_horizontalLine_tendsto
      x y hy hT
  have hscaled :=
    hbase.const_mul η
  have hselected :
      Tendsto
        (fun n ↦
          HGAS.Analysis.cesaroMeanAt
            (fun t ↦
              theta₃ (horizontalLine x y 1 hy t) *
                (η * standardUnaryFirstCharacter t))
            (T n))
        atTop
        (𝓝
          (η *
            (2 * theta3HorizontalCoefficient x y hy 1))) := by
    simpa only [cesaroMeanAt_const_mul, mul_assoc, mul_left_comm, mul_comm] using
      hscaled
  apply thetaGaugeHeight_of_unitPhase_firstCoefficient
    x y hy η hη
  exact tendsto_nhds_unique hselected hmoment

end

end HGAS.Modular
