import Stability.Simulation.ClockGain
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Aligning an arbitrary oscillator phase

Every supplied oscillator solution containing one full period reaches a
compute-start phase within that period. The construction uses the complex
argument of the initial data and also covers zero amplitude. This is a
finite-segment result, not a global-existence assertion.

Source: the phase decomposition in Section 4,
https://arxiv.org/html/2609.22058v2#S4.
-/

namespace Stability.Simulation

open Set

/-- An oscillator reaches `u = 0`, `v = -radius` within one forward
period, with the original amplitude and a nonnegative radius. -/
theorem exists_aligned_oscillator_phase
    {a b : ℝ} {u v : ℝ → ℝ}
    (hlength : a + 2 * Real.pi ≤ b)
    (hu : ContinuousOn u (Icc a b)) (hv : ContinuousOn v (Icc a b))
    (hdu : ∀ t ∈ Ioo a b, HasDerivAt u (-v t) t)
    (hdv : ∀ t ∈ Ioo a b, HasDerivAt v (u t) t) :
    ∃ τ ∈ Icc a (a + 2 * Real.pi), ∃ radius : ℝ,
      0 ≤ radius ∧ radius ^ 2 = u a ^ 2 + v a ^ 2 ∧ u τ = 0 ∧ v τ = -radius := by
  let z : ℂ := ⟨-v a, -u a⟩
  let phase := if 0 ≤ Complex.arg z then Complex.arg z else Complex.arg z + 2 * Real.pi
  have hphase : phase ∈ Icc 0 (2 * Real.pi) := by
    by_cases h : 0 ≤ Complex.arg z
    · simp only [phase, h, if_true]
      exact ⟨h, by linarith [Complex.arg_le_pi z, Real.pi_pos]⟩
    · simp only [phase, h, if_false]
      exact ⟨by linarith [Complex.neg_pi_lt_arg z, Real.pi_pos], by linarith⟩
  have hsin : Real.sin phase = Real.sin (Complex.arg z) := by
    by_cases h : 0 ≤ Complex.arg z <;> simp [phase, h, Real.sin_add_two_pi]
  have hcos : Real.cos phase = Real.cos (Complex.arg z) := by
    by_cases h : 0 ≤ Complex.arg z <;> simp [phase, h, Real.cos_add_two_pi]
  have hnormSin : ‖z‖ * Real.sin phase = -u a := by
    rw [hsin]
    exact Complex.norm_mul_sin_arg z
  have hnormCos : ‖z‖ * Real.cos phase = -v a := by
    rw [hcos]
    exact Complex.norm_mul_cos_arg z
  have huInitial : u a = -‖z‖ * Real.sin phase := by linarith
  have hvInitial : v a = -‖z‖ * Real.cos phase := by linarith
  have htime : a + phase ∈ Icc a b :=
    ⟨by linarith [hphase.1], (by linarith [hphase.2] : a + phase ≤ a + 2 * Real.pi).trans hlength⟩
  have hrotation := oscillator_eq_rotation hu hv hdu hdv htime
  refine ⟨a + phase, ⟨by linarith [hphase.1], by linarith [hphase.2]⟩,
    ‖z‖, norm_nonneg _, ?_, ?_, ?_⟩
  · rw [Complex.sq_norm, Complex.normSq_apply]
    dsimp [z]
    ring
  · rw [hrotation.1, add_sub_cancel_left, huInitial, hvInitial]
    ring
  · rw [hrotation.2, add_sub_cancel_left, huInitial, hvInitial]
    calc
      _ = -‖z‖ * (Real.sin phase ^ 2 + Real.cos phase ^ 2) := by ring
      _ = -‖z‖ := by rw [Real.sin_sq_add_cos_sq, mul_one]

end Stability.Simulation
