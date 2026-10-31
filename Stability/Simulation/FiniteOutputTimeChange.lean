import Stability.Simulation.FiniteTimeChange
import Stability.Dynamics.FiniteOutputBound

/-!
# Uniform finite output bounds under positive time changes

Finite trajectory reparametrization preserves the output integral and
the same uniform bound. No forward completeness or bounded speed is
required for either vector field.
-/

namespace Stability

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Positive state-dependent acceleration preserves uniform boundedness
of finite output integrals when the output is multiplied by the same speed. -/
theorem hasBoundedFiniteOutput_iff_timeScaled {F : E → E} {Q g : E → ℝ}
    (hQ : Continuous Q) (hg : Continuous g) (hpositive : ∀ x, 0 < Q x) :
    HasBoundedFiniteOutput F g ↔
      HasBoundedFiniteOutput (fun x ↦ Q x • F x) (fun x ↦ Q x * g x) := by
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨M, ?_⟩
    intro T hT x hx hderiv
    obtain ⟨S, hS, z, hz, _, _, _, hdz, hint⟩ :=
      TimeChange.exists_decelerated_segment hT hx (hQ.comp_continuousOn hx)
        (hg.comp_continuousOn hx) hderiv (fun t _ ↦ hpositive (x t))
    rw [← hint]
    exact hM S hS z hz hdz
  · rintro ⟨M, hM⟩
    refine ⟨M, ?_⟩
    intro T hT x hx hderiv
    obtain ⟨S, hS, z, hz, _, _, _, hdz, hint⟩ :=
      TimeChange.exists_accelerated_segment hT hx (hQ.comp_continuousOn hx)
        (hg.comp_continuousOn hx) hderiv (fun t _ ↦ hpositive (x t))
    rw [← hint]
    exact hM S hS z hz hdz

end Stability
