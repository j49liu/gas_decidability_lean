import HGAS.Compactification.StereographicChart
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Dynamic conjugacy on the finite accumulator chart

The compact vector accumulator satisfies

```
 U' = (1+W)g - (U·g)U,
 W' = -(1+W)(U·g).
```

On `W ≠ -1`, differentiating `Z = U/(1+W)` and using these two equations
gives exactly `Z' = g`.  This file records the chain-rule statement for an
arbitrary differentiable trajectory.  It is independent of how the base
flow produces `g`.
-/

namespace HGAS

noncomputable section

variable {n : ℕ}

/-- Along any differentiable compact-accumulator trajectory staying in the
finite chart, the affine chart coordinate has derivative `g`. -/
theorem accumulatorChartCoordinate_hasDerivAt
    (q : ℝ → FiniteAccumulatorChart n)
    (g : ℝ → FinVector n ℝ)
    (t : ℝ)
    (hU :
      ∀ i,
        HasDerivAt
          (fun s ↦ (q s).1.1.1 i)
          (accumulatorUField
            (q t).1.1.1 (q t).1.1.2 (g t) i) t)
    (hW :
      HasDerivAt
        (fun s ↦ (q s).1.1.2)
        (accumulatorWField
          (q t).1.1.1 (q t).1.1.2 (g t)) t) :
    ∀ i,
      HasDerivAt
        (fun s ↦ accumulatorChartCoordinate (q s) i)
        (g t i) t := by
  intro i
  have hden : 1 + (q t).1.1.2 ≠ 0 := by
    intro h
    apply (q t).2
    linarith
  have hdenDeriv :
      HasDerivAt
        (fun s ↦ 1 + (q s).1.1.2)
        (accumulatorWField
          (q t).1.1.1 (q t).1.1.2 (g t)) t :=
    hW.const_add 1
  have hquot := (hU i).div hdenDeriv hden
  change
    HasDerivAt
      (fun s ↦ (q s).1.1.1 i / (1 + (q s).1.1.2))
      (g t i) t
  rw [← accumulatorChartFieldDerivative_eq (q t) (g t) i]
  exact hquot

end

end HGAS
