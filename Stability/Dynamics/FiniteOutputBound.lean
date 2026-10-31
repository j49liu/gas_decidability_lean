import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Uniform output bounds on finite solution segments

The bound is chosen before the initial state, segment length, and
trajectory. This formulation does not require forward completeness and
is suited to positive time changes that may accelerate an infinite
trajectory into finite time.
-/

namespace Stability

open Set MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def HasBoundedFiniteOutput (F : E → E) (g : E → ℝ) : Prop :=
  ∃ M : ℝ, ∀ (T : ℝ), 0 ≤ T → ∀ y : ℝ → E,
    ContinuousOn y (Icc 0 T) →
    (∀ t ∈ Ioo 0 T, HasDerivAt y (F (y t)) t) →
    (∫ t in 0..T, g (y t)) ≤ M

end Stability
