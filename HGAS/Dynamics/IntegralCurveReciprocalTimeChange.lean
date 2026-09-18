import HGAS.Dynamics.IntegralCurveStateTimeChange
import Mathlib.Tactic

/-!
# Slowing a complete integral curve by a reciprocal clock

The companion theorem in `IntegralCurveStateTimeChange` removes a positive
state-dependent slowdown.  This module records the reverse construction.

If `γ` is a complete solution of

```text
                             γ' = F(γ)
```

and the reciprocal speed along the orbit,

```text
                             w(t) = 1 / a(γ(t)),
```

defines a global positive integral clock, then the inverse clock `B`
satisfies

```text
                             B' = a(γ(B)).
```

Consequently `γ ∘ B` is a complete solution of the slowed equation
`x' = a(x) F(x)`.  Keeping this elementary chain-rule step separate makes
it reusable for compactifications other than the canonical detector.
-/

namespace HGAS

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Reparametrize a complete integral curve by the inverse integral of
the reciprocal state speed. -/
theorem IsIntegralCurve.reparametrize_to_timeScaledField
    {a : E → ℝ} {F : E → E} {γ : ℝ → E}
    (hγ : IsIntegralCurve γ (fun _ x ↦ F x))
    (hclock :
      PositiveIntegralClock (fun t ↦ (a (γ t))⁻¹)) :
    IsIntegralCurve
      (fun τ ↦
        γ ((PositiveIntegralClock.orderIso hclock).symm τ))
      (fun _ x ↦ timeScaledField a F x) := by
  let B : ℝ → ℝ :=
    fun τ ↦ (PositiveIntegralClock.orderIso hclock).symm τ
  intro t
  have hcomp :=
    (hγ (B t)).scomp t
      (PositiveIntegralClock.symm_hasDerivAt hclock t)
  simpa only [B, inv_inv, timeScaledField] using hcomp

end

end HGAS
