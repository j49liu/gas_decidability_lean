import Stability.Simulation.HeldBufferMotion

/-!
# A clean reset from a held-label event

Small forcing and one visit to the output-support strip force the entire
compute interval into the clean-reset strip. The actual compute/copy
equations then approximate the reset map with the usual turn error.

Source: Lemma 4.3(iii), https://arxiv.org/html/2609.22058v2.
-/

namespace Stability.Simulation

open Set MeasureTheory

/-- The reset conclusion is derived from a label event, not assumed as
a local target identity. The structural strip identity for `H` is the
property to be supplied by the explicit real transition map. -/
theorem doubleBuffer_reset_update_error_le
    {ι : Type*} [Fintype ι] {t₀ t₁ t₂ : ℝ} (label : ι)
    {a b forcingA forcingB : ℝ → ι → ℝ}
    {computeRate copyRate : ℝ → ℝ} {H reset : (ι → ℝ) → ι → ℝ}
    (h₀₁ : t₀ ≤ t₁) (h₁₂ : t₁ ≤ t₂)
    (ha : ContinuousOn a (Icc t₀ t₂)) (hb : ContinuousOn b (Icc t₀ t₂))
    (hforcingA : ContinuousOn forcingA (Icc t₀ t₂))
    (hforcingB : ContinuousOn forcingB (Icc t₀ t₂))
    (hcompute : ContinuousOn computeRate (Icc t₀ t₁))
    (hcopy : ContinuousOn copyRate (Icc t₁ t₂))
    (hcomputeNonneg : ∀ t ∈ Icc t₀ t₁, 0 ≤ computeRate t)
    (hcopyNonneg : ∀ t ∈ Icc t₁ t₂, 0 ≤ copyRate t)
    (hcomputeGain : 0 < ∫ t in t₀..t₁, computeRate t)
    (hcopyGain : 0 < ∫ t in t₁..t₂, copyRate t)
    (hreset : LipschitzWith 1 reset)
    (hstrip : ∀ x : ι → ℝ, |x label| ≤ 1 / 8 → H x = reset x)
    (haCompute : ∀ i t, t ∈ Ioo t₀ t₁ →
      HasDerivAt (fun s ↦ a s i) (forcingA t i) t)
    (hbCompute : ∀ i t, t ∈ Ioo t₀ t₁ →
      HasDerivAt (fun s ↦ b s i)
        (computeRate t * (H (a t) i - b t i) ^ 3 + forcingB t i) t)
    (hbCopy : ∀ i t, t ∈ Ioo t₁ t₂ →
      HasDerivAt (fun s ↦ b s i) (forcingB t i) t)
    (haCopy : ∀ i t, t ∈ Ioo t₁ t₂ →
      HasDerivAt (fun s ↦ a s i)
        (copyRate t * (b t i - a t i) ^ 3 + forcingA t i) t)
    (hmass : forcingMass (jointForcingMagnitude forcingA forcingB) t₀ t₁ ≤ 1 / 16)
    (hevent : ∃ t ∈ Icc t₀ t₁, |a t label| < 1 / 16) :
    ‖a t₂ - reset (a t₀)‖ ≤
      2 * (forcingMass (jointForcingMagnitude forcingA forcingB) t₀ t₁ +
        forcingMass (jointForcingMagnitude forcingA forcingB) t₁ t₂) +
      (Real.sqrt (2 * (∫ t in t₀..t₁, computeRate t)))⁻¹ +
      (Real.sqrt (2 * (∫ t in t₁..t₂, copyRate t)))⁻¹ := by
  have hleft : Icc t₀ t₁ ⊆ Icc t₀ t₂ := Icc_subset_Icc le_rfl h₁₂
  have hnear := held_label_lt_one_eighth_of_event
    ((continuous_apply label).comp_continuousOn (ha.mono hleft))
    ((continuous_apply label).comp_continuousOn (hforcingA.mono hleft))
    ((hforcingA.norm.sup hforcingB.norm).mono hleft)
    (fun t _ ↦ (norm_le_pi_norm (forcingA t) label).trans (le_max_left _ _))
    (haCompute label) hmass hevent
  exact doubleBuffer_update_error_le h₀₁ h₁₂ ha hb hforcingA hforcingB hcompute hcopy
    hcomputeNonneg hcopyNonneg hcomputeGain hcopyGain hreset
    (fun t ht ↦ hstrip (a t) (hnear t ht).le) haCompute hbCompute hbCopy haCopy

end Stability.Simulation
