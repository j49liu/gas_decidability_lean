import HGAS.Dynamics.StateTimeChange
import Mathlib.Tactic

/-!
# Two-sided time changes of integral curves

`IsForwardTrajectory.reparametrize_from_timeScaledField` is the right
interface for stability theory, but a recurrent classification often
benefits from a genuine integral curve on all of `ℝ`.

If `γ` solves

```text
                 γ' = a(γ) F(γ)
```

for every real time and the unmodified clock

```text
                 C(t) = ∫₀ᵗ a(γ(s)) ds
```

is a positive integral clock, then composing with `C⁻¹` gives a complete
integral curve of `F`.  This module records the direct chain-rule proof.
-/

namespace HGAS

open Function

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A complete trajectory of a positively state-scaled field becomes a
complete trajectory of the original field after inversion of the direct
clock. -/
theorem IsIntegralCurve.reparametrize_from_timeScaledField
    {a : E → ℝ} {F : E → E} {γ : ℝ → E}
    (hγ :
      IsIntegralCurve γ
        (fun _ x ↦ timeScaledField a F x))
    (hclock :
      PositiveIntegralClock (fun t ↦ a (γ t))) :
    IsIntegralCurve
      (fun τ ↦
        γ ((PositiveIntegralClock.orderIso hclock).symm τ))
      (fun _ x ↦ F x) := by
  let B : ℝ → ℝ :=
    fun τ ↦ (PositiveIntegralClock.orderIso hclock).symm τ
  intro t
  have hcomp :=
    (hγ (B t)).scomp t
      (PositiveIntegralClock.symm_hasDerivAt hclock t)
  have hapos : 0 < a (γ (B t)) := by
    simpa only [B] using hclock.positive (B t)
  simpa only [B, timeScaledField, smul_smul,
    inv_mul_cancel₀ (ne_of_gt hapos), one_smul] using hcomp

end

end HGAS
