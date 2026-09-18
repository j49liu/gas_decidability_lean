import HGAS.Compiler.AllAffineCompactSourceTwoSidedClock
import Mathlib.Tactic

/-!
# Reverse recurrence through a two-sided physical clock

If a compact orbit is recurrent for the reversed flow, its complete
physical trajectory is recurrent after physical time is reversed.  The
proof uses the reversed speed `w(-t)`.  Its clock is

```text
  B_rev(t) = -B(-t),
```

so its inverse satisfies

```text
  -B_rev^{-1}(τ) = B^{-1}(-τ).
```

The module packages these elementary identities independently of the
detector construction.
-/

namespace HGAS

open Filter Function Set Topology

noncomputable section

namespace CompactAccumulatorPipelineCode

namespace AllAffineCompactSourceReverseRecurrence

open AllAffineCompactSourceChart
open AllAffineCompactSourceClock
open AllAffineCompactSourceTwoSidedClock

/-- Reversing time in a positive integral clock again gives a positive
integral clock. -/
def reverseClock
    {w : ℝ → ℝ}
    (hclock : PositiveIntegralClock w) :
    PositiveIntegralClock (fun t ↦ w (-t)) where
  continuous := hclock.continuous.comp continuous_neg
  positive := fun t ↦ hclock.positive (-t)
  tendsto_atTop := by
    have hneg :
        Tendsto (fun t : ℝ ↦ -t) atTop atBot :=
      tendsto_neg_atTop_atBot
    have hclockNeg :
        Tendsto (fun t : ℝ ↦ integralClock w (-t))
          atTop atBot :=
      hclock.tendsto_atBot.comp hneg
    have hresult :
        Tendsto (fun t : ℝ ↦ -integralClock w (-t))
          atTop atTop :=
      tendsto_neg_atBot_atTop.comp hclockNeg
    apply hresult.congr'
    exact Eventually.of_forall fun t ↦
      (integralClock_comp_neg w t).symm
  tendsto_atBot := by
    have hneg :
        Tendsto (fun t : ℝ ↦ -t) atBot atTop :=
      tendsto_neg_atBot_atTop
    have hclockNeg :
        Tendsto (fun t : ℝ ↦ integralClock w (-t))
          atBot atTop :=
      hclock.tendsto_atTop.comp hneg
    have hresult :
        Tendsto (fun t : ℝ ↦ -integralClock w (-t))
          atBot atBot :=
      tendsto_neg_atTop_atBot.comp hclockNeg
    apply hresult.congr'
    exact Eventually.of_forall fun t ↦
      (integralClock_comp_neg w t).symm

/-- Exact relation between the inverses of a clock and its reversal. -/
theorem neg_reverseClock_symm
    {w : ℝ → ℝ}
    (hclock : PositiveIntegralClock w)
    (τ : ℝ) :
    -(PositiveIntegralClock.orderIso (reverseClock hclock)).symm τ =
      (PositiveIntegralClock.orderIso hclock).symm (-τ) := by
  apply (PositiveIntegralClock.orderIso hclock).injective
  rw [PositiveIntegralClock.orderIso_apply]
  have hrev :
      integralClock (fun t ↦ w (-t))
          ((PositiveIntegralClock.orderIso (reverseClock hclock)).symm τ) =
        τ := by
    rw [← PositiveIntegralClock.orderIso_apply]
    exact
      (PositiveIntegralClock.orderIso
        (reverseClock hclock)).apply_symm_apply τ
  calc
    integralClock w
        (-(PositiveIntegralClock.orderIso (reverseClock hclock)).symm τ) =
        -integralClock (fun t ↦ w (-t))
          ((PositiveIntegralClock.orderIso
            (reverseClock hclock)).symm τ) := by
          rw [integralClock_comp_neg]
          ring
    _ = -τ := by rw [hrev]
    _ =
        (PositiveIntegralClock.orderIso hclock)
          ((PositiveIntegralClock.orderIso hclock).symm (-τ)) := by
          rw [
            (PositiveIntegralClock.orderIso hclock).apply_symm_apply]

variable {n m : ℕ}

variable
  (K : ℕ)
  (ϕ : Flow ℝ (SourceSpace n m))
  (hinv :
    IsInvariant ϕ (sourceFiniteInteriorSet (m := m) (layout n)))

/-- Reverse compact recurrence survives the inverse clock as recurrence
of the physical trajectory with physical time reversed. -/
theorem physicalCurve_reverse_forwardRecurrentAt
    (v : FiniteSourceSpace n m)
    (hclock :
      PositiveIntegralClock
        (twoSidedClockWeight K (affineCurve ϕ hinv v)))
    (hrecReverse :
      ForwardRecurrentAt
        (fun t : ℝ ↦ (ϕ.restrict hinv).reverse t v) 0) :
    ForwardRecurrentAt
      (fun τ ↦ physicalCurve K ϕ hinv v hclock (-τ)) 0 := by
  have hrecAffine :=
    hrecReverse.map continuous_affinePoint
  have hrecPhysical :=
    hrecAffine.inverseClock (reverseClock hclock)
  have hrecPhysical' :
      ForwardRecurrentAt
        (fun τ ↦
          affinePoint
            ((ϕ.restrict hinv)
              (-(PositiveIntegralClock.orderIso
                (reverseClock hclock)).symm τ) v)) 0 := by
    simpa only [Flow.reverse] using hrecPhysical
  have hcurve :
      (fun τ ↦
        affinePoint
          ((ϕ.restrict hinv)
            (-(PositiveIntegralClock.orderIso
              (reverseClock hclock)).symm τ) v)) =
        fun τ ↦
          affinePoint
            ((ϕ.restrict hinv)
              ((PositiveIntegralClock.orderIso hclock).symm (-τ)) v) := by
    funext τ
    rw [neg_reverseClock_symm]
  rw [hcurve] at hrecPhysical'
  simpa only [
    AllAffineCompactSourceTwoSidedClock.physicalCurve,
    AllAffineCompactSourceClock.affineCurve] using hrecPhysical'

end AllAffineCompactSourceReverseRecurrence

end CompactAccumulatorPipelineCode

end

end HGAS
