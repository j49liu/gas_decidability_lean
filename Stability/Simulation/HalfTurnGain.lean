import Stability.Simulation.AlternatingClock
import Stability.Simulation.ClockErrorSummability

/-!
# Integrated gain of an actual oscillator half-turn

The clock and oscillator equations identify the central arc with the
explicit cosine rate. Positivity on the remaining parts of the half-turn
then gives the gain and relaxation-error estimates for the full interval.

Source: Section 4, https://arxiv.org/html/2609.22058v2#S4.
-/

namespace Stability.Simulation

open Set MeasureTheory

noncomputable section

/-- The active clock rate in half-turn `n`, including its alternating sign. -/
def halfTurnRate (gain : ℝ) (clock u : ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  gain * (1 + clock t ^ 2) ^ 2 * max ((-1 : ℝ) ^ n * u t) 0

theorem halfTurnRate_nonneg {gain : ℝ} (hgain : 0 ≤ gain)
    (clock u : ℝ → ℝ) (n : ℕ) (t : ℝ) :
    0 ≤ halfTurnRate gain clock u n t := by
  unfold halfTurnRate
  positivity

theorem continuousOn_halfTurnRate {gain : ℝ} {clock u : ℝ → ℝ} {s : Set ℝ}
    (hclock : ContinuousOn clock s) (hu : ContinuousOn u s) (n : ℕ) :
    ContinuousOn (halfTurnRate gain clock u n) s :=
  (continuousOn_const.mul ((continuousOn_const.add (hclock.pow 2)).pow 2)).mul
    ((continuousOn_const.mul hu).sup continuousOn_const)

/-- Translation identifies the central cosine integral; monotonicity of
the nonnegative integral includes the two remaining parts of the half-turn. -/
theorem centralArc_integral_le_halfTurn_integral
    {origin finish radius gain : ℝ} {clock u v : ℝ → ℝ}
    (hgain : 0 ≤ gain)
    (hclock : ContinuousOn clock (Icc origin finish))
    (hdclock : ∀ t ∈ Ioo origin finish, HasDerivAt clock 1 t)
    (hu : ContinuousOn u (Icc origin finish))
    (hv : ContinuousOn v (Icc origin finish))
    (hdu : ∀ t ∈ Ioo origin finish, HasDerivAt u (-v t) t)
    (hdv : ∀ t ∈ Ioo origin finish, HasDerivAt v (u t) t)
    (hu0 : u origin = 0) (hv0 : v origin = -radius)
    (n : ℕ) (hend : halfTurnBoundary origin (n + 1) ≤ finish) :
    (∫ s in -(Real.pi / 3)..Real.pi / 3,
      clockedRelaxationRate gain (clock origin + Real.pi / 2 + (n : ℝ) * Real.pi) radius s) ≤
      ∫ t in halfTurnBoundary origin n..halfTurnBoundary origin (n + 1),
        halfTurnRate gain clock u n t := by
  let center := halfTurnCenter origin n
  have horder : -(Real.pi / 3) ≤ Real.pi / 3 := by linarith [Real.pi_pos]
  have hsub : Icc (halfTurnBoundary origin n) (halfTurnBoundary origin (n + 1)) ⊆
      Icc origin finish :=
    (halfTurn_Icc_subset origin (Nat.lt_succ_self n)).trans (Icc_subset_Icc le_rfl hend)
  have hleft := centralArc_mem_halfTurn origin n (left_mem_Icc.mpr horder)
  have hright := centralArc_mem_halfTurn origin n (right_mem_Icc.mpr horder)
  have htranslate :
      (∫ s in -(Real.pi / 3)..Real.pi / 3,
        halfTurnRate gain clock u n (center + s)) =
      ∫ t in center + -(Real.pi / 3)..center + Real.pi / 3,
        halfTurnRate gain clock u n t :=
    intervalIntegral.integral_comp_add_left _ center
  have heq :
      (∫ s in -(Real.pi / 3)..Real.pi / 3,
        clockedRelaxationRate gain (clock origin + Real.pi / 2 + (n : ℝ) * Real.pi) radius s) =
      ∫ t in center + -(Real.pi / 3)..center + Real.pi / 3,
        halfTurnRate gain clock u n t := by
    rw [← htranslate]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le horder] at hs
    exact (centeredClockRate_eq hclock hdclock hu hv hdu hdv hu0 hv0 n s
      (hsub (centralArc_mem_halfTurn origin n hs))).symm
  rw [heq]
  apply intervalIntegral.integral_mono_interval hleft.1 (by linarith) hright.2
    (Filter.Eventually.of_forall (halfTurnRate_nonneg hgain clock u n))
  exact ((continuousOn_halfTurnRate hclock hu n).mono hsub).intervalIntegrable_of_Icc
    ((halfTurnBoundary_strictMono origin).monotone (Nat.le_succ n))

/-- An actual admissible half-turn has strictly positive integrated gain. -/
theorem halfTurn_integral_pos
    {origin finish radius gain : ℝ} {clock u v : ℝ → ℝ}
    (hgain : 0 < gain) (hradius : 0 ≤ radius)
    (hamplitude : (1 / 2 : ℝ) < radius ^ 2)
    (hclock : ContinuousOn clock (Icc origin finish))
    (hdclock : ∀ t ∈ Ioo origin finish, HasDerivAt clock 1 t)
    (hu : ContinuousOn u (Icc origin finish))
    (hv : ContinuousOn v (Icc origin finish))
    (hdu : ∀ t ∈ Ioo origin finish, HasDerivAt u (-v t) t)
    (hdv : ∀ t ∈ Ioo origin finish, HasDerivAt v (u t) t)
    (hu0 : u origin = 0) (hv0 : v origin = -radius)
    (n : ℕ) (hend : halfTurnBoundary origin (n + 1) ≤ finish) :
    0 < ∫ t in halfTurnBoundary origin n..halfTurnBoundary origin (n + 1),
      halfTurnRate gain clock u n t :=
  (centralArc_integral_pos hgain hradius hamplitude _).trans_le
    (centralArc_integral_le_halfTurn_integral hgain.le hclock hdclock hu hv hdu hdv hu0 hv0 n hend)

/-- The relaxation error on an actual half-turn is bounded by the
corresponding term in the summable clock-error lattice. -/
theorem halfTurn_relaxationError_le
    {origin finish radius gain : ℝ} {clock u v : ℝ → ℝ}
    (hgain : 0 < gain) (hradius : 0 ≤ radius)
    (hamplitude : (1 / 2 : ℝ) < radius ^ 2)
    (hclock : ContinuousOn clock (Icc origin finish))
    (hdclock : ∀ t ∈ Ioo origin finish, HasDerivAt clock 1 t)
    (hu : ContinuousOn u (Icc origin finish))
    (hv : ContinuousOn v (Icc origin finish))
    (hdu : ∀ t ∈ Ioo origin finish, HasDerivAt u (-v t) t)
    (hdv : ∀ t ∈ Ioo origin finish, HasDerivAt v (u t) t)
    (hu0 : u origin = 0) (hv0 : v origin = -radius)
    (n : ℕ) (hend : halfTurnBoundary origin (n + 1) ≤ finish) :
    (Real.sqrt (2 * (∫ t in halfTurnBoundary origin n..halfTurnBoundary origin (n + 1),
      halfTurnRate gain clock u n t)))⁻¹ ≤
      (Real.sqrt gain)⁻¹ * clockError (clock origin + Real.pi / 2 + (n : ℝ) * Real.pi) := by
  have hcentral := centralArc_integral_pos hgain hradius hamplitude
    (clock origin + Real.pi / 2 + (n : ℝ) * Real.pi)
  have hcompare := centralArc_integral_le_halfTurn_integral hgain.le
    hclock hdclock hu hv hdu hdv hu0 hv0 n hend
  have hroot := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hcompare (by norm_num : (0 : ℝ) ≤ 2))
  have hinv := one_div_le_one_div_of_le (Real.sqrt_pos.mpr (mul_pos (by norm_num) hcentral)) hroot
  simp only [one_div] at hinv
  exact hinv.trans (centralArc_relaxationError_le hgain hradius hamplitude _)

end

end Stability.Simulation
