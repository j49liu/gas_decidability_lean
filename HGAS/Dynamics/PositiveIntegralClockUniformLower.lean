import HGAS.Dynamics.StateTimeChange
import Mathlib.Tactic

/-!
# Global positive clocks from a uniform lower bound

This small module records a reusable sufficient condition for an integral
clock to parametrize the whole real line.

Suppose that the clock speed `w` is continuous and satisfies

```text
                         0 < c ≤ w(t)
```

for every real time `t`.  The integral clock

```text
                         T(t) = ∫₀ᵗ w(s) ds
```

then tends to `+∞` as `t → +∞` and to `-∞` as `t → -∞`.  Thus it is a
global orientation-preserving change of time.  The positive-time assertion
already appears in `StateTimeChange`; the only point here is to derive the
negative-time assertion by applying it to the reflected speed `t ↦ w(-t)`.
-/

namespace HGAS

open Filter Function

noncomputable section

/-- Reversing a clock speed reverses its integral clock. -/
theorem integralClock_reflect
    (w : ℝ → ℝ) (T : ℝ) :
    integralClock (fun t ↦ w (-t)) T =
      -integralClock w (-T) := by
  rw [integralClock, intervalIntegral.integral_comp_neg]
  simp only [neg_zero]
  rw [intervalIntegral.integral_symm]
  rfl

/-- A continuous clock speed that is uniformly bounded below by a positive
constant is a global positive integral clock.

The conclusion packages the clock as an order isomorphism `ℝ ≃o ℝ`; in
particular, its inverse is defined at every real compact time and has the
reciprocal derivative supplied by `PositiveIntegralClock.symm_hasDerivAt`.
-/
theorem positiveIntegralClock_of_uniformLowerBound
    {w : ℝ → ℝ} (hw : Continuous w)
    {c : ℝ} (hc : 0 < c)
    (hge : ∀ t, c ≤ w t) :
    PositiveIntegralClock w := by
  let wrev : ℝ → ℝ := fun t ↦ w (-t)
  have hwpos : ∀ t, 0 < w t :=
    fun t ↦ hc.trans_le (hge t)
  have hwrev : Continuous wrev :=
    hw.comp continuous_neg
  have hwrevGe : ∀ t, c ≤ wrev t :=
    fun t ↦ hge (-t)
  have htop :
      Tendsto (integralClock w) atTop atTop :=
    integralClock_tendsto_atTop_of_eventually_ge
      hw hc (Eventually.of_forall hge)
  have hrevTop :
      Tendsto (integralClock wrev) atTop atTop :=
    integralClock_tendsto_atTop_of_eventually_ge
      hwrev hc (Eventually.of_forall hwrevGe)
  have hnegRev :
      Tendsto (fun T ↦ -integralClock wrev T)
        atTop atBot :=
    tendsto_neg_atTop_atBot.comp hrevTop
  have hcomp :
      Tendsto (fun T ↦ integralClock w (-T))
        atTop atBot := by
    apply hnegRev.congr'
    exact Eventually.of_forall fun T ↦ by
      change
        -integralClock (fun t ↦ w (-t)) T =
          integralClock w (-T)
      rw [integralClock_reflect]
      ring
  have hbot :
      Tendsto (integralClock w) atBot atBot := by
    have h :=
      hcomp.comp (tendsto_neg_atBot_atTop :
        Tendsto (fun t : ℝ ↦ -t) atBot atTop)
    simpa only [Function.comp_def, neg_neg] using h
  exact
    { continuous := hw
      positive := hwpos
      tendsto_atTop := htop
      tendsto_atBot := hbot }

end

end HGAS
