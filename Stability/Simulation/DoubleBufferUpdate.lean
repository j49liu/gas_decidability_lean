import Stability.Simulation.ForcedCubicRelaxation
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Normed.Group.Uniform

/-!
# A forced compute/copy update

A double-buffer update consists of two intervals. On the first, `a` is
held while `b` relaxes toward `H(a)`; on the second, `b` is held while
`a` relaxes toward `b`. The held variables still move under their actual
forcing. The error estimate below follows from these component equations.

The hypothesis identifying `H` with a nonexpansive map along the compute
interval is local to the supplied trajectory. Construction of that real
extension and verification of this hypothesis are separate obligations.

Source: Lemma 4.3, https://arxiv.org/html/2609.22058v2.
-/

namespace Stability.Simulation

open Set MeasureTheory

noncomputable section

/-- Actual joint forcing magnitude for two finite-coordinate buffers. -/
def jointForcingMagnitude {ι : Type*} [Fintype ι]
    (forcingA forcingB : ℝ → ι → ℝ) (t : ℝ) : ℝ :=
  max ‖forcingA t‖ ‖forcingB t‖

theorem jointForcingMagnitude_nonneg {ι : Type*} [Fintype ι]
    (forcingA forcingB : ℝ → ι → ℝ) (t : ℝ) :
    0 ≤ jointForcingMagnitude forcingA forcingB t :=
  (norm_nonneg _).trans (le_max_left _ _)

/-- A held variable moves by at most the accumulated forcing majorant.
The conclusion holds at every time in the supplied finite interval. -/
theorem norm_sub_le_forcingMass_of_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {start finish : ℝ} {y forcing : ℝ → E} {magnitude : ℝ → ℝ}
    (hy : ContinuousOn y (Icc start finish))
    (hforcing : ContinuousOn forcing (Icc start finish))
    (hmagnitude : ContinuousOn magnitude (Icc start finish))
    (hbound : ∀ t ∈ Icc start finish, ‖forcing t‖ ≤ magnitude t)
    (hderiv : ∀ t ∈ Ioo start finish, HasDerivAt y (forcing t) t)
    {t : ℝ} (ht : t ∈ Icc start finish) :
    ‖y t - y start‖ ≤ forcingMass magnitude start finish := by
  have hsub : Icc start t ⊆ Icc start finish := Icc_subset_Icc le_rfl ht.2
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    (hy.mono hsub) (fun s hs ↦ hderiv s ⟨hs.1, hs.2.trans_le ht.2⟩)
    ((hforcing.mono hsub).intervalIntegrable_of_Icc ht.1)
  calc
    ‖y t - y start‖ = ‖∫ s in start..t, forcing s‖ := congrArg norm hFTC.symm
    _ ≤ ∫ s in start..t, ‖forcing s‖ :=
      intervalIntegral.norm_integral_le_integral_norm ht.1
    _ ≤ forcingMass magnitude start t := by
      exact intervalIntegral.integral_mono_on ht.1
        ((hforcing.norm.mono hsub).intervalIntegrable_of_Icc ht.1)
        ((hmagnitude.abs.mono hsub).intervalIntegrable_of_Icc ht.1)
        (fun s hs ↦ (hbound s (hsub hs)).trans (le_abs_self _))
    _ ≤ forcingMass magnitude start finish := forcingMass_le hmagnitude ht

private theorem coordinate_forcingMass_le
    {ι : Type*} [Fintype ι] {start finish : ℝ}
    {forcing : ℝ → ι → ℝ} {magnitude : ℝ → ℝ}
    (horder : start ≤ finish)
    (hforcing : ContinuousOn forcing (Icc start finish))
    (hmagnitude : ContinuousOn magnitude (Icc start finish))
    (hbound : ∀ t ∈ Icc start finish, ‖forcing t‖ ≤ magnitude t) (i : ι) :
    forcingMass (fun t ↦ forcing t i) start finish ≤
      forcingMass magnitude start finish := by
  apply intervalIntegral.integral_mono_on horder
    (((continuous_apply i).comp_continuousOn hforcing).abs.intervalIntegrable_of_Icc horder)
    (hmagnitude.abs.intervalIntegrable_of_Icc horder)
  intro t ht
  exact (norm_le_pi_norm (forcing t) i).trans ((hbound t ht).trans (le_abs_self _))

/-- Coordinatewise cubic relaxation gives the same estimate in the
finite sup norm, with one common forcing majorant. -/
theorem norm_sub_le_radius_add_inv_sqrt_integral_add_forcingMass
    {ι : Type*} [Fintype ι] {start finish radius : ℝ} {center : ι → ℝ}
    {y target forcing : ℝ → ι → ℝ} {rate magnitude : ℝ → ℝ}
    (horder : start ≤ finish)
    (hy : ContinuousOn y (Icc start finish))
    (hrate : ContinuousOn rate (Icc start finish))
    (hforcing : ContinuousOn forcing (Icc start finish))
    (hmagnitude : ContinuousOn magnitude (Icc start finish))
    (hnonneg : ∀ t ∈ Icc start finish, 0 ≤ rate t)
    (hbound : ∀ t ∈ Icc start finish, ‖forcing t‖ ≤ magnitude t)
    (htarget : ∀ t ∈ Icc start finish, ‖target t - center‖ ≤ radius)
    (hderiv : ∀ i t, t ∈ Ioo start finish →
      HasDerivAt (fun s ↦ y s i)
        (rate t * (target t i - y t i) ^ 3 + forcing t i) t)
    (hgain : 0 < ∫ t in start..finish, rate t) :
    ‖y finish - center‖ ≤ radius + (Real.sqrt (2 * (∫ t in start..finish, rate t)))⁻¹ +
      forcingMass magnitude start finish := by
  have hradius : 0 ≤ radius :=
    (norm_nonneg _).trans (htarget start ⟨le_rfl, horder⟩)
  apply (pi_norm_le_iff_of_nonneg (by
    have := forcingMass_nonneg magnitude horder
    positivity)).mpr
  intro i
  have hscalar := abs_sub_lt_radius_add_inv_sqrt_integral_add_forcingMass horder
    ((continuous_apply i).comp_continuousOn hy) hrate
    ((continuous_apply i).comp_continuousOn hforcing) hnonneg
    (fun t ht ↦ (norm_le_pi_norm (target t - center) i).trans (htarget t ht))
    (hderiv i) hgain
  exact hscalar.le.trans (add_le_add le_rfl
    (coordinate_forcingMass_le horder hforcing hmagnitude hbound i))

/-- One actual compute/copy turn. The two relaxation errors and twice
the joint forcing mass bound the update error, independently of the
initial contents of the temporary buffer `b`. -/
theorem doubleBuffer_update_error_le
    {ι : Type*} [Fintype ι] {t₀ t₁ t₂ : ℝ}
    {a b forcingA forcingB : ℝ → ι → ℝ}
    {computeRate copyRate : ℝ → ℝ} {H F : (ι → ℝ) → ι → ℝ}
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
    (hF : LipschitzWith 1 F)
    (hlocal : ∀ t ∈ Icc t₀ t₁, H (a t) = F (a t))
    (haCompute : ∀ i t, t ∈ Ioo t₀ t₁ →
      HasDerivAt (fun s ↦ a s i) (forcingA t i) t)
    (hbCompute : ∀ i t, t ∈ Ioo t₀ t₁ →
      HasDerivAt (fun s ↦ b s i)
        (computeRate t * (H (a t) i - b t i) ^ 3 + forcingB t i) t)
    (hbCopy : ∀ i t, t ∈ Ioo t₁ t₂ →
      HasDerivAt (fun s ↦ b s i) (forcingB t i) t)
    (haCopy : ∀ i t, t ∈ Ioo t₁ t₂ →
      HasDerivAt (fun s ↦ a s i)
        (copyRate t * (b t i - a t i) ^ 3 + forcingA t i) t) :
    ‖a t₂ - F (a t₀)‖ ≤
      2 * (forcingMass (jointForcingMagnitude forcingA forcingB) t₀ t₁ +
        forcingMass (jointForcingMagnitude forcingA forcingB) t₁ t₂) +
      (Real.sqrt (2 * (∫ t in t₀..t₁, computeRate t)))⁻¹ +
      (Real.sqrt (2 * (∫ t in t₁..t₂, copyRate t)))⁻¹ := by
  let magnitude := jointForcingMagnitude forcingA forcingB
  let Ecompute := forcingMass magnitude t₀ t₁
  let Ecopy := forcingMass magnitude t₁ t₂
  let ηcompute := (Real.sqrt (2 * (∫ t in t₀..t₁, computeRate t)))⁻¹
  let ηcopy := (Real.sqrt (2 * (∫ t in t₁..t₂, copyRate t)))⁻¹
  have hleft : Icc t₀ t₁ ⊆ Icc t₀ t₂ := Icc_subset_Icc le_rfl h₁₂
  have hright : Icc t₁ t₂ ⊆ Icc t₀ t₂ := Icc_subset_Icc h₀₁ le_rfl
  have hmagnitude : ContinuousOn magnitude (Icc t₀ t₂) :=
    hforcingA.norm.sup hforcingB.norm
  have hboundA (t : ℝ) : ‖forcingA t‖ ≤ magnitude t := le_max_left _ _
  have hboundB (t : ℝ) : ‖forcingB t‖ ≤ magnitude t := le_max_right _ _
  have haHeld (t : ℝ) (ht : t ∈ Icc t₀ t₁) : ‖a t - a t₀‖ ≤ Ecompute :=
    norm_sub_le_forcingMass_of_hasDerivAt (ha.mono hleft) (hforcingA.mono hleft)
      (hmagnitude.mono hleft) (fun s _ ↦ hboundA s)
      (fun s hs ↦ hasDerivAt_pi.mpr (fun i ↦ haCompute i s hs)) ht
  have htargetCompute (t : ℝ) (ht : t ∈ Icc t₀ t₁) :
      ‖H (a t) - F (a t₀)‖ ≤ Ecompute := by
    rw [hlocal t ht]
    have h := hF.dist_le_mul (a t) (a t₀)
    simp only [dist_eq_norm, NNReal.coe_one, one_mul] at h
    exact h.trans (haHeld t ht)
  have hbComputed : ‖b t₁ - F (a t₀)‖ ≤ 2 * Ecompute + ηcompute := by
    have h := norm_sub_le_radius_add_inv_sqrt_integral_add_forcingMass h₀₁
      (hb.mono hleft) hcompute (hforcingB.mono hleft) (hmagnitude.mono hleft)
      hcomputeNonneg (fun s _ ↦ hboundB s) htargetCompute hbCompute hcomputeGain
    change ‖b t₁ - F (a t₀)‖ ≤ Ecompute + ηcompute + Ecompute at h
    linarith
  have hbHeld (t : ℝ) (ht : t ∈ Icc t₁ t₂) : ‖b t - b t₁‖ ≤ Ecopy :=
    norm_sub_le_forcingMass_of_hasDerivAt (hb.mono hright) (hforcingB.mono hright)
      (hmagnitude.mono hright) (fun s _ ↦ hboundB s)
      (fun s hs ↦ hasDerivAt_pi.mpr (fun i ↦ hbCopy i s hs)) ht
  have htargetCopy (t : ℝ) (ht : t ∈ Icc t₁ t₂) :
      ‖b t - F (a t₀)‖ ≤ 2 * Ecompute + ηcompute + Ecopy := by
    calc
      ‖b t - F (a t₀)‖ ≤ ‖b t - b t₁‖ + ‖b t₁ - F (a t₀)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ Ecopy + (2 * Ecompute + ηcompute) := add_le_add (hbHeld t ht) hbComputed
      _ = 2 * Ecompute + ηcompute + Ecopy := by ring
  have h := norm_sub_le_radius_add_inv_sqrt_integral_add_forcingMass h₁₂
    (ha.mono hright) hcopy (hforcingA.mono hright) (hmagnitude.mono hright)
    hcopyNonneg (fun s _ ↦ hboundA s) htargetCopy haCopy hcopyGain
  change ‖a t₂ - F (a t₀)‖ ≤
    (2 * Ecompute + ηcompute + Ecopy) + ηcopy + Ecopy at h
  change ‖a t₂ - F (a t₀)‖ ≤ 2 * (Ecompute + Ecopy) + ηcompute + ηcopy
  linarith

end

end Stability.Simulation
