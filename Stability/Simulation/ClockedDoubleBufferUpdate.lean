import Stability.Simulation.DoubleBufferUpdate
import Stability.Simulation.HalfTurnGain
import Stability.Simulation.HalfTurnErrorBudget

/-!
# Compute/copy error for the oscillator-gated monitor

This estimate uses the actual two-buffer differential equations and the
clock equations. The gates, integrated gains, and update error are derived,
not assumed. The starting oscillator phase is explicitly aligned; reaching
such a phase from arbitrary initial oscillator data is a separate step.

Source: Lemma 4.3, https://arxiv.org/html/2609.22058v2.
-/

namespace Stability.Simulation

open Set MeasureTheory

/-- Every complete compute/copy turn satisfies the explicit error
allowance. Locally, the real transition map must agree with a supplied
nonexpansive map along the held buffer's compute trajectory. -/
theorem clocked_doubleBuffer_update_error_le
    {ι : Type*} [Fintype ι] {origin finish radius gain : ℝ}
    {clock u v : ℝ → ℝ} {a b forcingA forcingB : ℝ → ι → ℝ}
    {H F : (ι → ℝ) → ι → ℝ}
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
    (hda : ∀ i t, t ∈ Ioo origin finish →
      HasDerivAt (fun s ↦ a s i)
        (gain * (1 + clock t ^ 2) ^ 2 * max (-u t) 0 * (b t i - a t i) ^ 3 +
          forcingA t i) t)
    (hdb : ∀ i t, t ∈ Ioo origin finish →
      HasDerivAt (fun s ↦ b s i)
        (gain * (1 + clock t ^ 2) ^ 2 * max (u t) 0 * (H (a t) i - b t i) ^ 3 +
          forcingB t i) t)
    (hF : LipschitzWith 1 F)
    (j : ℕ) (hend : halfTurnBoundary origin (2 * j + 2) ≤ finish)
    (hlocal : ∀ t ∈ Icc (halfTurnBoundary origin (2 * j))
        (halfTurnBoundary origin (2 * j + 1)), H (a t) = F (a t)) :
    ‖a (halfTurnBoundary origin (2 * j + 2)) - F (a (halfTurnBoundary origin (2 * j)))‖ ≤
      halfTurnErrorAllowance gain (clock origin) origin
        (jointForcingMagnitude forcingA forcingB) (2 * j) +
      halfTurnErrorAllowance gain (clock origin) origin
        (jointForcingMagnitude forcingA forcingB) (2 * j + 1) := by
  have hboundary (n : ℕ) (hn : n ≤ 2 * j + 2) : halfTurnBoundary origin n ≤ finish :=
    ((halfTurnBoundary_strictMono origin).monotone hn).trans hend
  have hstart : origin ≤ halfTurnBoundary origin (2 * j) := by
    simpa only [halfTurnBoundary_zero] using
      (halfTurnBoundary_strictMono origin).monotone (Nat.zero_le (2 * j))
  have h₀₁ : halfTurnBoundary origin (2 * j) ≤ halfTurnBoundary origin (2 * j + 1) :=
    (halfTurnBoundary_strictMono origin).monotone (by omega)
  have h₁₂ : halfTurnBoundary origin (2 * j + 1) ≤ halfTurnBoundary origin (2 * j + 2) :=
    (halfTurnBoundary_strictMono origin).monotone (by omega)
  have hcomputeEnd := hboundary (2 * j + 1) (by omega)
  have hcopyEnd : halfTurnBoundary origin (2 * j + 1 + 1) ≤ finish := by
    simpa only [Nat.add_assoc] using hend
  have hturn : Icc (halfTurnBoundary origin (2 * j))
      (halfTurnBoundary origin (2 * j + 2)) ⊆ Icc origin finish :=
    Icc_subset_Icc hstart hend
  have hcompute : Icc (halfTurnBoundary origin (2 * j))
      (halfTurnBoundary origin (2 * j + 1)) ⊆ Icc origin finish :=
    Icc_subset_Icc hstart hcomputeEnd
  have hcopy : Icc (halfTurnBoundary origin (2 * j + 1))
      (halfTurnBoundary origin (2 * j + 2)) ⊆ Icc origin finish :=
    Icc_subset_Icc (hstart.trans h₀₁) hend
  have hcomputeOpen : Ioo (halfTurnBoundary origin (2 * j))
      (halfTurnBoundary origin (2 * j + 1)) ⊆ Ioo origin finish :=
    Ioo_subset_Ioo hstart hcomputeEnd
  have hcopyOpen : Ioo (halfTurnBoundary origin (2 * j + 1))
      (halfTurnBoundary origin (2 * j + 2)) ⊆ Ioo origin finish :=
    Ioo_subset_Ioo (hstart.trans h₀₁) hend
  have haCompute : ∀ i t, t ∈ Ioo (halfTurnBoundary origin (2 * j))
      (halfTurnBoundary origin (2 * j + 1)) →
      HasDerivAt (fun s ↦ a s i) (forcingA t i) t := by
    intro i t ht
    have hz := oppositeWeight_eq_zero_on_halfTurn hu hv hdu hdv hu0 hv0 hradius
      (2 * j) (hcompute (Ioo_subset_Icc_self ht)) (Ioo_subset_Icc_self ht)
    have hz' : max (-u t) 0 = 0 := by simpa [pow_mul] using hz
    simpa only [hz', mul_zero, zero_mul, zero_add] using hda i t (hcomputeOpen ht)
  have hbCopy : ∀ i t, t ∈ Ioo (halfTurnBoundary origin (2 * j + 1))
      (halfTurnBoundary origin (2 * j + 2)) →
      HasDerivAt (fun s ↦ b s i) (forcingB t i) t := by
    intro i t ht
    have hhalf : t ∈ Icc (halfTurnBoundary origin (2 * j + 1))
        (halfTurnBoundary origin (2 * j + 1 + 1)) := by
      simpa only [Nat.add_assoc] using Ioo_subset_Icc_self ht
    have hz := oppositeWeight_eq_zero_on_halfTurn hu hv hdu hdv hu0 hv0 hradius
      (2 * j + 1) (hcopy (Ioo_subset_Icc_self ht)) hhalf
    have hz' : max (u t) 0 = 0 := by simpa [pow_add, pow_mul] using hz
    simpa only [hz', mul_zero, zero_mul, zero_add] using hdb i t (hcopyOpen ht)
  have hcomputeGain := halfTurn_integral_pos hgain hradius hamplitude
    hclock hdclock hu hv hdu hdv hu0 hv0 (2 * j) hcomputeEnd
  have hcopyGain := halfTurn_integral_pos hgain hradius hamplitude
    hclock hdclock hu hv hdu hdv hu0 hv0 (2 * j + 1) hcopyEnd
  have hupdate := doubleBuffer_update_error_le
    (computeRate := halfTurnRate gain clock u (2 * j))
    (copyRate := halfTurnRate gain clock u (2 * j + 1))
    h₀₁ h₁₂ (ha.mono hturn) (hb.mono hturn) (hforcingA.mono hturn) (hforcingB.mono hturn)
    ((continuousOn_halfTurnRate hclock hu (2 * j)).mono hcompute)
    ((continuousOn_halfTurnRate hclock hu (2 * j + 1)).mono hcopy)
    (fun t _ ↦ halfTurnRate_nonneg hgain.le clock u (2 * j) t)
    (fun t _ ↦ halfTurnRate_nonneg hgain.le clock u (2 * j + 1) t)
    hcomputeGain (by simpa only [Nat.add_assoc] using hcopyGain) hF hlocal haCompute
    (fun i t ht ↦ by
      simpa [halfTurnRate, pow_mul] using hdb i t (hcomputeOpen ht)) hbCopy
    (fun i t ht ↦ by
      simpa [halfTurnRate, pow_add, pow_mul] using hda i t (hcopyOpen ht))
  have hcomputeError := halfTurn_relaxationError_le hgain hradius hamplitude
    hclock hdclock hu hv hdu hdv hu0 hv0 (2 * j) hcomputeEnd
  have hcopyError := halfTurn_relaxationError_le hgain hradius hamplitude
    hclock hdclock hu hv hdu hdv hu0 hv0 (2 * j + 1) hcopyEnd
  simp only [Nat.add_assoc] at hcopyError
  unfold halfTurnErrorAllowance
  simp only [Nat.add_assoc]
  linarith

end Stability.Simulation
