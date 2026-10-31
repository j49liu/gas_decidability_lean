import Stability.Simulation.DoubleBufferUpdate

/-!
# Motion within a held-buffer interval

The forcing mass controls motion between any two times in the interval,
without a factor of two. A single visit to the output-support strip thus
places the entire compute interval inside the clean-reset strip.

Source: Lemma 4.3(iii), https://arxiv.org/html/2609.22058v2.
-/

namespace Stability.Simulation

open Set MeasureTheory

/-- The actual forcing integral bounds displacement between any two
times, not only displacement from the initial time. -/
theorem norm_sub_le_forcingMass_of_hasDerivAt_pairwise
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {start finish : ℝ} {y forcing : ℝ → E} {magnitude : ℝ → ℝ}
    (hy : ContinuousOn y (Icc start finish))
    (hforcing : ContinuousOn forcing (Icc start finish))
    (hmagnitude : ContinuousOn magnitude (Icc start finish))
    (hbound : ∀ t ∈ Icc start finish, ‖forcing t‖ ≤ magnitude t)
    (hderiv : ∀ t ∈ Ioo start finish, HasDerivAt y (forcing t) t)
    {s t : ℝ} (hs : s ∈ Icc start finish) (ht : t ∈ Icc start finish) :
    ‖y t - y s‖ ≤ forcingMass magnitude start finish := by
  have hordered {r q : ℝ} (hr : r ∈ Icc start finish) (hq : q ∈ Icc start finish)
      (hrq : r ≤ q) : ‖y q - y r‖ ≤ forcingMass magnitude start finish := by
    have hsub : Icc r q ⊆ Icc start finish := Icc_subset_Icc hr.1 hq.2
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hrq
      (hy.mono hsub) (fun z hz ↦ hderiv z ⟨hr.1.trans_lt hz.1, hz.2.trans_le hq.2⟩)
      ((hforcing.mono hsub).intervalIntegrable_of_Icc hrq)
    calc
      ‖y q - y r‖ = ‖∫ z in r..q, forcing z‖ := congrArg norm hFTC.symm
      _ ≤ ∫ z in r..q, ‖forcing z‖ := intervalIntegral.norm_integral_le_integral_norm hrq
      _ ≤ ∫ z in r..q, |magnitude z| :=
        intervalIntegral.integral_mono_on hrq
          ((hforcing.norm.mono hsub).intervalIntegrable_of_Icc hrq)
          ((hmagnitude.abs.mono hsub).intervalIntegrable_of_Icc hrq)
          (fun z hz ↦ (hbound z (hsub hz)).trans (le_abs_self _))
      _ ≤ forcingMass magnitude start finish :=
        intervalIntegral.integral_mono_interval hr.1 hrq hq.2
          (Filter.Eventually.of_forall fun _ ↦ abs_nonneg _)
          (hmagnitude.abs.intervalIntegrable_of_Icc (hr.1.trans hr.2))
  rcases le_total s t with hst | hts
  · exact hordered hs ht hst
  · simpa only [norm_sub_rev] using hordered ht hs hts

/-- One visit to the output-support strip, together with small total
forcing, puts the whole held-label trajectory inside the reset strip. -/
theorem held_label_lt_one_eighth_of_event
    {start finish : ℝ} {label forcing magnitude : ℝ → ℝ}
    (hlabel : ContinuousOn label (Icc start finish))
    (hforcing : ContinuousOn forcing (Icc start finish))
    (hmagnitude : ContinuousOn magnitude (Icc start finish))
    (hbound : ∀ t ∈ Icc start finish, |forcing t| ≤ magnitude t)
    (hderiv : ∀ t ∈ Ioo start finish, HasDerivAt label (forcing t) t)
    (hmass : forcingMass magnitude start finish ≤ 1 / 16)
    (hevent : ∃ s ∈ Icc start finish, |label s| < 1 / 16) :
    ∀ t ∈ Icc start finish, |label t| < 1 / 8 := by
  obtain ⟨s, hs, hsmall⟩ := hevent
  intro t ht
  have hmotion := norm_sub_le_forcingMass_of_hasDerivAt_pairwise
    hlabel hforcing hmagnitude hbound hderiv hs ht
  have htriangle : |label t| ≤ |label t - label s| + |label s| := by
    simpa only [sub_add_cancel] using abs_add_le (label t - label s) (label s)
  change |label t - label s| ≤ forcingMass magnitude start finish at hmotion
  linarith

end Stability.Simulation
