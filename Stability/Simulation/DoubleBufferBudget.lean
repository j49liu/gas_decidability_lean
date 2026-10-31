import Stability.Simulation.DoubleBufferUpdate

/-!
# One-sided budget estimates for compute/copy dynamics

Only a lower bound on the computed target is needed to control the
budget coordinate. The identity lower bound gives an ordinary update;
the map `x ↦ max (x + 1) 1` gives the productive-reset recurrence.

Source: Lemma 4.3, https://arxiv.org/html/2609.22058v2.
-/

namespace Stability.Simulation

open Set MeasureTheory

private theorem scalar_forcingMass_le
    {start finish : ℝ} {forcing magnitude : ℝ → ℝ}
    (horder : start ≤ finish)
    (hforcing : ContinuousOn forcing (Icc start finish))
    (hmagnitude : ContinuousOn magnitude (Icc start finish))
    (hbound : ∀ t ∈ Icc start finish, |forcing t| ≤ magnitude t) :
    forcingMass forcing start finish ≤ forcingMass magnitude start finish :=
  intervalIntegral.integral_mono_on horder
    (hforcing.abs.intervalIntegrable_of_Icc horder)
    (hmagnitude.abs.intervalIntegrable_of_Icc horder)
    (fun t ht ↦ (hbound t ht).trans (le_abs_self _))

/-- A nonexpansive scalar lower bound on the computed target propagates
through a full forced compute/copy turn. This does not require an upper
bound on the target or either buffer. -/
theorem doubleBuffer_scalar_lower_bound
    {t₀ t₁ t₂ : ℝ} {a b target forcingA forcingB magnitude computeRate copyRate : ℝ → ℝ}
    {f : ℝ → ℝ}
    (h₀₁ : t₀ ≤ t₁) (h₁₂ : t₁ ≤ t₂)
    (ha : ContinuousOn a (Icc t₀ t₂)) (hb : ContinuousOn b (Icc t₀ t₂))
    (hforcingA : ContinuousOn forcingA (Icc t₀ t₂))
    (hforcingB : ContinuousOn forcingB (Icc t₀ t₂))
    (hmagnitude : ContinuousOn magnitude (Icc t₀ t₂))
    (hboundA : ∀ t ∈ Icc t₀ t₂, |forcingA t| ≤ magnitude t)
    (hboundB : ∀ t ∈ Icc t₀ t₂, |forcingB t| ≤ magnitude t)
    (hcompute : ContinuousOn computeRate (Icc t₀ t₁))
    (hcopy : ContinuousOn copyRate (Icc t₁ t₂))
    (hcomputeNonneg : ∀ t ∈ Icc t₀ t₁, 0 ≤ computeRate t)
    (hcopyNonneg : ∀ t ∈ Icc t₁ t₂, 0 ≤ copyRate t)
    (hcomputeGain : 0 < ∫ t in t₀..t₁, computeRate t)
    (hcopyGain : 0 < ∫ t in t₁..t₂, copyRate t)
    (hf : LipschitzWith 1 f)
    (htarget : ∀ t ∈ Icc t₀ t₁, f (a t) ≤ target t)
    (haCompute : ∀ t ∈ Ioo t₀ t₁, HasDerivAt a (forcingA t) t)
    (hbCompute : ∀ t ∈ Ioo t₀ t₁,
      HasDerivAt b (computeRate t * (target t - b t) ^ 3 + forcingB t) t)
    (hbCopy : ∀ t ∈ Ioo t₁ t₂, HasDerivAt b (forcingB t) t)
    (haCopy : ∀ t ∈ Ioo t₁ t₂,
      HasDerivAt a (copyRate t * (b t - a t) ^ 3 + forcingA t) t) :
    f (a t₀) - (2 * (forcingMass magnitude t₀ t₁ + forcingMass magnitude t₁ t₂) +
      (Real.sqrt (2 * (∫ t in t₀..t₁, computeRate t)))⁻¹ +
      (Real.sqrt (2 * (∫ t in t₁..t₂, copyRate t)))⁻¹) ≤ a t₂ := by
  let Ec := forcingMass magnitude t₀ t₁
  let Ep := forcingMass magnitude t₁ t₂
  let ηc := (Real.sqrt (2 * (∫ t in t₀..t₁, computeRate t)))⁻¹
  let ηp := (Real.sqrt (2 * (∫ t in t₁..t₂, copyRate t)))⁻¹
  have hleft : Icc t₀ t₁ ⊆ Icc t₀ t₂ := Icc_subset_Icc le_rfl h₁₂
  have hright : Icc t₁ t₂ ⊆ Icc t₀ t₂ := Icc_subset_Icc h₀₁ le_rfl
  have haHeld (t : ℝ) (ht : t ∈ Icc t₀ t₁) : |a t - a t₀| ≤ Ec :=
    norm_sub_le_forcingMass_of_hasDerivAt (ha.mono hleft) (hforcingA.mono hleft)
      (hmagnitude.mono hleft) (fun s hs ↦ hboundA s (hleft hs)) haCompute ht
  have htargetCompute (t : ℝ) (ht : t ∈ Icc t₀ t₁) : f (a t₀) - Ec ≤ target t := by
    have h := hf.dist_le_mul (a t) (a t₀)
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
    have hlower := (abs_le.mp (h.trans (haHeld t ht))).1
    linarith [htarget t ht]
  have hmassB : forcingMass forcingB t₀ t₁ ≤ Ec :=
    scalar_forcingMass_le h₀₁ (hforcingB.mono hleft) (hmagnitude.mono hleft)
      (fun s hs ↦ hboundB s (hleft hs))
  have hbComputed : f (a t₀) - 2 * Ec - ηc ≤ b t₁ := by
    have h := lower_sub_inv_sqrt_integral_sub_forcingMass_lt h₀₁
      (hb.mono hleft) hcompute (hforcingB.mono hleft) hcomputeNonneg
      htargetCompute hbCompute hcomputeGain
    change f (a t₀) - Ec - ηc - forcingMass forcingB t₀ t₁ < b t₁ at h
    linarith
  have hbHeld (t : ℝ) (ht : t ∈ Icc t₁ t₂) : |b t - b t₁| ≤ Ep :=
    norm_sub_le_forcingMass_of_hasDerivAt (hb.mono hright) (hforcingB.mono hright)
      (hmagnitude.mono hright) (fun s hs ↦ hboundB s (hright hs)) hbCopy ht
  have htargetCopy (t : ℝ) (ht : t ∈ Icc t₁ t₂) :
      f (a t₀) - 2 * Ec - ηc - Ep ≤ b t := by
    have h := (abs_le.mp (hbHeld t ht)).1
    linarith
  have hmassA : forcingMass forcingA t₁ t₂ ≤ Ep :=
    scalar_forcingMass_le h₁₂ (hforcingA.mono hright) (hmagnitude.mono hright)
      (fun s hs ↦ hboundA s (hright hs))
  have h := lower_sub_inv_sqrt_integral_sub_forcingMass_lt h₁₂
    (ha.mono hright) hcopy (hforcingA.mono hright) hcopyNonneg
    htargetCopy haCopy hcopyGain
  change f (a t₀) - 2 * Ec - ηc - Ep - ηp - forcingMass forcingA t₁ t₂ < a t₂ at h
  change f (a t₀) - (2 * (Ec + Ep) + ηc + ηp) ≤ a t₂
  linarith

/-- Increasing a restart budget and flooring it at one is nonexpansive. -/
theorem lipschitzWith_resetBudget : LipschitzWith 1 (fun x : ℝ ↦ max (x + 1) 1) := by
  have hshift : LipschitzWith 1 (fun x : ℝ ↦ x + 1) := by
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro x y
    simp [Real.dist_eq]
  exact hshift.max_const 1

end Stability.Simulation
