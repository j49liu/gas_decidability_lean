import Stability.Simulation.DoubleBufferBudget
import Stability.Simulation.HalfTurnGain
import Stability.Simulation.HalfTurnErrorBudget

/-!
# Budget-coordinate bounds for the oscillator-gated monitor

The actual scalar buffer equations imply both the ordinary budget bound
and the stronger reset bound, under their corresponding target inequalities.
Clock phase alignment and existence of the supplied solution segment are
explicit hypotheses, not conclusions of these finite-interval estimates.

Source: Lemma 4.3, https://arxiv.org/html/2609.22058v2.
-/

namespace Stability.Simulation

open Set MeasureTheory

section

variable {origin finish radius gain : ℝ}
  {clock u v a b target forcingA forcingB magnitude : ℝ → ℝ}
  (hgain : 0 < gain) (hradius : 0 ≤ radius)
  (hamplitude : (1 / 2 : ℝ) < radius ^ 2)
  (hclock : ContinuousOn clock (Icc origin finish))
  (hdclock : ∀ t ∈ Ioo origin finish, HasDerivAt clock 1 t)
  (hu : ContinuousOn u (Icc origin finish))
  (hv : ContinuousOn v (Icc origin finish))
  (hdu : ∀ t ∈ Ioo origin finish, HasDerivAt u (-v t) t)
  (hdv : ∀ t ∈ Ioo origin finish, HasDerivAt v (u t) t)
  (hu0 : u origin = 0) (hv0 : v origin = -radius)
  (ha : ContinuousOn a (Icc origin finish))
  (hb : ContinuousOn b (Icc origin finish))
  (hforcingA : ContinuousOn forcingA (Icc origin finish))
  (hforcingB : ContinuousOn forcingB (Icc origin finish))
  (hmagnitude : ContinuousOn magnitude (Icc origin finish))
  (hboundA : ∀ t ∈ Icc origin finish, |forcingA t| ≤ magnitude t)
  (hboundB : ∀ t ∈ Icc origin finish, |forcingB t| ≤ magnitude t)
  (hda : ∀ t ∈ Ioo origin finish,
    HasDerivAt a
      (gain * (1 + clock t ^ 2) ^ 2 * max (-u t) 0 * (b t - a t) ^ 3 + forcingA t) t)
  (hdb : ∀ t ∈ Ioo origin finish,
    HasDerivAt b
      (gain * (1 + clock t ^ 2) ^ 2 * max (u t) 0 * (target t - b t) ^ 3 + forcingB t) t)

include hgain hradius hamplitude hclock hdclock hu hv hdu hdv hu0 hv0
  ha hb hforcingA hforcingB hmagnitude hboundA hboundB hda hdb

/-- Any nonexpansive scalar lower bound on the compute target yields
a one-sided update bound with the concrete clock allowances. -/
theorem clocked_budget_lower_bound {f : ℝ → ℝ} (hf : LipschitzWith 1 f)
    (j : ℕ) (hend : halfTurnBoundary origin (2 * j + 2) ≤ finish)
    (htarget : ∀ t ∈ Icc (halfTurnBoundary origin (2 * j))
      (halfTurnBoundary origin (2 * j + 1)), f (a t) ≤ target t) :
    f (a (halfTurnBoundary origin (2 * j))) -
      (halfTurnErrorAllowance gain (clock origin) origin magnitude (2 * j) +
        halfTurnErrorAllowance gain (clock origin) origin magnitude (2 * j + 1)) ≤
      a (halfTurnBoundary origin (2 * j + 2)) := by
  have hstart : origin ≤ halfTurnBoundary origin (2 * j) := by
    simpa only [halfTurnBoundary_zero] using
      (halfTurnBoundary_strictMono origin).monotone (Nat.zero_le (2 * j))
  have h₀₁ : halfTurnBoundary origin (2 * j) ≤ halfTurnBoundary origin (2 * j + 1) :=
    (halfTurnBoundary_strictMono origin).monotone (by omega)
  have h₁₂ : halfTurnBoundary origin (2 * j + 1) ≤ halfTurnBoundary origin (2 * j + 2) :=
    (halfTurnBoundary_strictMono origin).monotone (by omega)
  have hcomputeEnd := h₁₂.trans hend
  have hcopyEnd : halfTurnBoundary origin (2 * j + 1 + 1) ≤ finish := by
    simpa only [Nat.add_assoc] using hend
  have hturn := Icc_subset_Icc hstart hend
  have hcompute := Icc_subset_Icc hstart hcomputeEnd
  have hcopy := Icc_subset_Icc (hstart.trans h₀₁) hend
  have hcomputeOpen := Ioo_subset_Ioo hstart hcomputeEnd
  have hcopyOpen := Ioo_subset_Ioo (hstart.trans h₀₁) hend
  have haCompute : ∀ t ∈ Ioo (halfTurnBoundary origin (2 * j))
      (halfTurnBoundary origin (2 * j + 1)), HasDerivAt a (forcingA t) t := by
    intro t ht
    have hz := oppositeWeight_eq_zero_on_halfTurn hu hv hdu hdv hu0 hv0 hradius
      (2 * j) (hcompute (Ioo_subset_Icc_self ht)) (Ioo_subset_Icc_self ht)
    have hz' : max (-u t) 0 = 0 := by simpa [pow_mul] using hz
    simpa only [hz', mul_zero, zero_mul, zero_add] using hda t (hcomputeOpen ht)
  have hbCopy : ∀ t ∈ Ioo (halfTurnBoundary origin (2 * j + 1))
      (halfTurnBoundary origin (2 * j + 2)), HasDerivAt b (forcingB t) t := by
    intro t ht
    have hhalf : t ∈ Icc (halfTurnBoundary origin (2 * j + 1))
        (halfTurnBoundary origin (2 * j + 1 + 1)) := by
      simpa only [Nat.add_assoc] using Ioo_subset_Icc_self ht
    have hz := oppositeWeight_eq_zero_on_halfTurn hu hv hdu hdv hu0 hv0 hradius
      (2 * j + 1) (hcopy (Ioo_subset_Icc_self ht)) hhalf
    have hz' : max (u t) 0 = 0 := by simpa [pow_add, pow_mul] using hz
    simpa only [hz', mul_zero, zero_mul, zero_add] using hdb t (hcopyOpen ht)
  have hcomputeGain := halfTurn_integral_pos hgain hradius hamplitude
    hclock hdclock hu hv hdu hdv hu0 hv0 (2 * j) hcomputeEnd
  have hcopyGain := halfTurn_integral_pos hgain hradius hamplitude
    hclock hdclock hu hv hdu hdv hu0 hv0 (2 * j + 1) hcopyEnd
  have hupdate := doubleBuffer_scalar_lower_bound
    (computeRate := halfTurnRate gain clock u (2 * j))
    (copyRate := halfTurnRate gain clock u (2 * j + 1))
    h₀₁ h₁₂ (ha.mono hturn) (hb.mono hturn) (hforcingA.mono hturn) (hforcingB.mono hturn)
    (hmagnitude.mono hturn) (fun t ht ↦ hboundA t (hturn ht))
    (fun t ht ↦ hboundB t (hturn ht))
    ((continuousOn_halfTurnRate hclock hu (2 * j)).mono hcompute)
    ((continuousOn_halfTurnRate hclock hu (2 * j + 1)).mono hcopy)
    (fun t _ ↦ halfTurnRate_nonneg hgain.le clock u (2 * j) t)
    (fun t _ ↦ halfTurnRate_nonneg hgain.le clock u (2 * j + 1) t)
    hcomputeGain (by simpa only [Nat.add_assoc] using hcopyGain) hf htarget haCompute
    (fun t ht ↦ by simpa [halfTurnRate, pow_mul] using hdb t (hcomputeOpen ht)) hbCopy
    (fun t ht ↦ by simpa [halfTurnRate, pow_add, pow_mul] using hda t (hcopyOpen ht))
  have hcomputeError := halfTurn_relaxationError_le hgain hradius hamplitude
    hclock hdclock hu hv hdu hdv hu0 hv0 (2 * j) hcomputeEnd
  have hcopyError := halfTurn_relaxationError_le hgain hradius hamplitude
    hclock hdclock hu hv hdu hdv hu0 hv0 (2 * j + 1) hcopyEnd
  simp only [Nat.add_assoc] at hcopyError
  unfold halfTurnErrorAllowance
  simp only [Nat.add_assoc]
  linarith

/-- A target that never lowers the current budget loses at most the
turn's error allowance under the actual forced dynamics. -/
theorem clocked_budget_nondecrease
    (j : ℕ) (hend : halfTurnBoundary origin (2 * j + 2) ≤ finish)
    (htarget : ∀ t ∈ Icc (halfTurnBoundary origin (2 * j))
      (halfTurnBoundary origin (2 * j + 1)), a t ≤ target t) :
    a (halfTurnBoundary origin (2 * j)) -
      (halfTurnErrorAllowance gain (clock origin) origin magnitude (2 * j) +
        halfTurnErrorAllowance gain (clock origin) origin magnitude (2 * j + 1)) ≤
      a (halfTurnBoundary origin (2 * j + 2)) :=
  clocked_budget_lower_bound hgain hradius hamplitude hclock hdclock hu hv hdu hdv hu0 hv0
    ha hb hforcingA hforcingB hmagnitude hboundA hboundB hda hdb LipschitzWith.id j hend htarget

/-- During a reset, the budget gains one and is floored at one, up to
the same turn error. This is the productive-step recurrence. -/
theorem clocked_budget_reset
    (j : ℕ) (hend : halfTurnBoundary origin (2 * j + 2) ≤ finish)
    (htarget : ∀ t ∈ Icc (halfTurnBoundary origin (2 * j))
      (halfTurnBoundary origin (2 * j + 1)), max (a t + 1) 1 ≤ target t) :
    max (a (halfTurnBoundary origin (2 * j)) + 1) 1 -
      (halfTurnErrorAllowance gain (clock origin) origin magnitude (2 * j) +
        halfTurnErrorAllowance gain (clock origin) origin magnitude (2 * j + 1)) ≤
      a (halfTurnBoundary origin (2 * j + 2)) :=
  clocked_budget_lower_bound hgain hradius hamplitude hclock hdclock hu hv hdu hdv hu0 hv0
    ha hb hforcingA hforcingB hmagnitude hboundA hboundB hda hdb
    lipschitzWith_resetBudget j hend htarget

end

end Stability.Simulation
