import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# `C¹` curves from a continuous velocity field

For real-parameter curves, an everywhere derivative which varies
continuously is exactly the data needed for `C¹` regularity.  This small
lemma packages that fact in the Fréchet-derivative form used by the rest of
the development.
-/

namespace HGAS

open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A curve with a prescribed continuous velocity and the corresponding
pointwise derivative is continuously differentiable. -/
theorem contDiff_one_curve_of_continuous_velocity
    (γ v : ℝ → E)
    (hv : Continuous v)
    (hγ : ∀ t, HasDerivAt γ (v t) t) :
    ContDiff ℝ 1 γ := by
  rw [contDiff_one_iff_hasFDerivAt]
  refine
    ⟨fun t ↦ ContinuousLinearMap.toSpanSingleton ℝ (v t), ?_, ?_⟩
  · exact
      (ContinuousLinearMap.toSpanSingletonCLE
        (𝕜 := ℝ) (E := E)).continuous.comp hv
  · intro t
    exact (hγ t).hasFDerivAt

end HGAS
