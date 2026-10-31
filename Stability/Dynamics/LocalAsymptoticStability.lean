import HGAS.Stability.KordaLyapunov

/-!
# Local asymptotic stability and homogeneous scaling

Local attraction includes existence of forward trajectories. This prevents
finite-time blow-up from making a universal statement about global
trajectories vacuous. For polynomial fields, local uniqueness identifies this
trajectory formulation with the usual initial-value formulation.

Homogeneity makes a local basin of attraction global: shrink an arbitrary
initial state into the basin, apply local attraction, and undo the positive
space and time scalings. No ODE existence or uniqueness theorem is assumed
in this argument; the required local existence is part of the hypothesis.
-/

namespace Stability

open HGAS

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- All states in some neighborhood admit global forward trajectories,
and every such trajectory converges to the equilibrium. -/
def LocallyAttractiveWithExistence (F : E → E) (xEq : E) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∀ x₀ : E, dist x₀ xEq < r →
    (∃ γ : ℝ → E, IsForwardTrajectory F γ x₀) ∧
      ∀ γ : ℝ → E, IsForwardTrajectory F γ x₀ →
        ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 ≤ T ∧
          ∀ t : ℝ, T ≤ t → dist (γ t) xEq < ε

/-- Local asymptotic stability with nonvacuous local existence and
attraction, using the published trajectory semantics. -/
structure LocallyAsymptoticallyStable (F : E → E) (xEq : E) : Prop where
  equilibrium : F xEq = 0
  stable : LyapunovStableWithExistence F xEq
  attractive : LocallyAttractiveWithExistence F xEq

/-- Global asymptotic stability implies local asymptotic stability. -/
theorem locallyAsymptoticallyStable_of_globallyAsymptoticallyStable
    {F : E → E} {xEq : E} (h : GloballyAsymptoticallyStable F xEq) :
    LocallyAsymptoticallyStable F xEq := by
  refine ⟨h.equilibrium, h.lyapunovStableWithExistence, 1, one_pos, ?_⟩
  intro x₀ _
  exact ⟨h.forwardComplete x₀, h.attractive x₀⟩

/-- For a homogeneous vector field of positive integer degree,
local and global asymptotic stability at the origin coincide. -/
theorem locallyAsymptoticallyStable_iff_globallyAsymptoticallyStable
    (F : E → E) (k : ℕ)
    (hF : ∀ (c : ℝ) (x : E), F (c • x) = c ^ (k + 1) • F x) :
    LocallyAsymptoticallyStable F 0 ↔ GloballyAsymptoticallyStable F 0 := by
  refine ⟨?_, locallyAsymptoticallyStable_of_globallyAsymptoticallyStable⟩
  intro h
  obtain ⟨C, _, hbound⟩ :=
    (lyapunovStableWithExistence_iff_uniformLinearTrajectoryBound F k hF).mp h.stable
  refine ⟨h.equilibrium, fun x₀ ↦ (hbound x₀).1,
    h.stable.lyapunovStable, ?_⟩
  obtain ⟨r, hr, hbasin⟩ := h.attractive
  intro x₀ γ hγ ε hε
  let c : ℝ := r / (2 * (‖x₀‖ + 1))
  have hc : 0 < c := div_pos hr (by positivity)
  have hcx : dist (c • x₀) 0 < r := by
    rw [dist_zero_right, norm_smul, Real.norm_of_nonneg hc.le]
    dsimp [c]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : 0 < 2 * (‖x₀‖ + 1))]
    nlinarith [norm_nonneg x₀]
  have hscaled := hγ.scale_of_homogeneous F k hF c hc.le
  obtain ⟨T, hT, htail⟩ := (hbasin (c • x₀) hcx).2 _ hscaled (c * ε) (mul_pos hc hε)
  have hck : 0 < c ^ k := pow_pos hc k
  refine ⟨T * c ^ k, mul_nonneg hT hck.le, ?_⟩
  intro t ht
  have htime : T ≤ t * (c ^ k)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hck]
    exact ht
  have hcancel : t * (c ^ k)⁻¹ * c ^ k = t := by
    field_simp
  have hsmall := htail (t * (c ^ k)⁻¹) htime
  simp only [scaledForwardCurve, hcancel, dist_zero_right, norm_smul,
    Real.norm_of_nonneg hc.le] at hsmall
  rw [dist_zero_right]
  exact (mul_lt_mul_iff_right₀ hc).mp hsmall

end Stability
