import HGAS.Dynamics.HomogeneousScaling
import Mathlib.Tactic

/-!
# A uniform orbit bound from homogeneous Lyapunov stability

For a general globally asymptotically stable system, boundedness of all
trajectories starting on the unit sphere is usually obtained from compact
dependence on initial conditions.  Homogeneity gives a shorter and more
robust argument which uses only Lyapunov stability.

Choose a radius `δ` whose trajectories stay in the unit ball.  If `γ`
starts on the unit sphere and `c = δ/2`, homogeneity says that

```
t ↦ c • γ (c^k t)
```

is another trajectory, now starting in the `δ`-ball.  Stability therefore
gives

```
‖c • γ(t)‖ < 1
```

at every nonnegative time.  Thus all unit-sphere trajectories obey the
single bound `‖γ(t)‖ < 1/c`.

This lemma is one of the continuation inputs in the angular-to-physical
time-change proof, and it avoids assuming a global backward flow for the
original homogeneous polynomial field.
-/

namespace HGAS

open Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Lyapunov stability of a degree-`k+1` homogeneous field gives one
uniform forward bound for every trajectory starting on the unit sphere. -/
theorem GloballyAsymptoticallyStable.exists_uniform_unit_trajectory_bound
    {F : E → E} {k : ℕ}
    (hgas : GloballyAsymptoticallyStable F 0)
    (hF : ScalesAsDegree ℝ (k + 1) F) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (x₀ : E), ‖x₀‖ = 1 →
        ∀ (γ : ℝ → E), IsForwardTrajectory F γ x₀ →
          ∀ t : ℝ, 0 ≤ t → ‖γ t‖ < B := by
  obtain ⟨δ, hδ, hstay⟩ :=
    hgas.stable 1 zero_lt_one
  let c : ℝ := δ / 2
  let B : ℝ := c⁻¹
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  have hc_lt_delta : c < δ := by
    dsimp only [c]
    linarith
  have hB : 0 < B := by
    dsimp only [B]
    positivity
  refine ⟨B, hB, ?_⟩
  intro x₀ hx₀ γ hγ t ht
  let s : ℝ := t / c ^ k
  have hs : 0 ≤ s := by
    dsimp only [s]
    positivity
  have hscaled :
      IsForwardTrajectory F
        (scaledForwardCurve k c γ) (c • x₀) :=
    hγ.scale_of_homogeneous F k hF c hc.le
  have hinitial :
      dist (c • x₀) 0 < δ := by
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hc, hx₀, mul_one]
    exact hc_lt_delta
  have hsmall :=
    hstay (c • x₀) hinitial
      (scaledForwardCurve k c γ) hscaled s hs
  have htime : s * c ^ k = t := by
    dsimp only [s]
    field_simp [pow_ne_zero k hc.ne']
  have hscaledNorm :
      c * ‖γ t‖ < 1 := by
    simpa only [scaledForwardCurve, htime, dist_zero_right,
      norm_smul, Real.norm_eq_abs, abs_of_pos hc] using hsmall
  have hdivide : ‖γ t‖ < c⁻¹ := by
    have :
        ‖γ t‖ < c⁻¹ * 1 :=
      (lt_inv_mul_iff₀ hc).2 hscaledNorm
    simpa using this
  simpa only [B] using hdivide

end

end HGAS
