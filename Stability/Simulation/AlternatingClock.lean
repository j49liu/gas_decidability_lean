import Stability.Simulation.ClockGain
import Mathlib.Order.Interval.Set.Disjoint

/-!
# Alternating half-turns of the simulation clock

Reference: the compute and copy intervals in Section 4,
https://arxiv.org/html/2609.22058v2#S4.

The oscillator formulas below assume an explicitly aligned starting phase.
They follow from the differential equations, not from a simulation
correctness hypothesis. Aligning an arbitrary initial phase is separate.
-/

namespace Stability.Simulation

open Set

/-- The boundary between consecutive oscillator half-turns. -/
noncomputable def halfTurnBoundary (origin : ℝ) (n : ℕ) : ℝ :=
  origin + (n : ℝ) * Real.pi

/-- The midpoint of a half-turn. -/
noncomputable def halfTurnCenter (origin : ℝ) (n : ℕ) : ℝ :=
  halfTurnBoundary origin n + Real.pi / 2

@[simp] theorem halfTurnBoundary_zero (origin : ℝ) :
    halfTurnBoundary origin 0 = origin := by
  simp [halfTurnBoundary]

/-- Consecutive half-turn boundaries are exactly `π` apart. -/
theorem halfTurnBoundary_succ (origin : ℝ) (n : ℕ) :
    halfTurnBoundary origin (n + 1) = halfTurnBoundary origin n + Real.pi := by
  simp only [halfTurnBoundary, Nat.cast_add, Nat.cast_one]
  ring

/-- Half-turn boundaries are strictly increasing. -/
theorem halfTurnBoundary_strictMono (origin : ℝ) : StrictMono (halfTurnBoundary origin) := by
  intro n m hnm
  have hcast : (n : ℝ) < m := by exact_mod_cast hnm
  have hscaled := mul_lt_mul_of_pos_right hcast Real.pi_pos
  unfold halfTurnBoundary
  linarith

/-- Half-open half-turn intervals are pairwise disjoint. -/
theorem halfTurn_Ioc_disjoint (origin : ℝ) {n m : ℕ} (hne : n ≠ m) :
    Disjoint (Ioc (halfTurnBoundary origin n) (halfTurnBoundary origin (n + 1)))
      (Ioc (halfTurnBoundary origin m) (halfTurnBoundary origin (m + 1))) := by
  rcases lt_or_gt_of_ne hne with hnm | hmn
  · exact Ioc_disjoint_Ioc_of_le
      ((halfTurnBoundary_strictMono origin).monotone (Nat.succ_le_of_lt hnm))
  · exact (Ioc_disjoint_Ioc_of_le
      ((halfTurnBoundary_strictMono origin).monotone (Nat.succ_le_of_lt hmn))).symm

/-- Each of the first `N` half-turns lies in the initial segment ending at
boundary `N`. -/
theorem halfTurn_Icc_subset (origin : ℝ) {n N : ℕ} (hn : n < N) :
    Icc (halfTurnBoundary origin n) (halfTurnBoundary origin (n + 1)) ⊆
      Icc origin (halfTurnBoundary origin N) := by
  apply Icc_subset_Icc
  · simpa only [halfTurnBoundary_zero] using
      (halfTurnBoundary_strictMono origin).monotone (Nat.zero_le n)
  · exact (halfTurnBoundary_strictMono origin).monotone (Nat.succ_le_of_lt hn)

/-- The central arc fits inside its half-turn, leaving a margin at each
endpoint. -/
theorem centralArc_mem_halfTurn (origin : ℝ) (n : ℕ) {s : ℝ}
    (hs : s ∈ Icc (-(Real.pi / 3)) (Real.pi / 3)) :
    halfTurnCenter origin n + s ∈
      Icc (halfTurnBoundary origin n) (halfTurnBoundary origin (n + 1)) := by
  rw [halfTurnBoundary_succ]
  unfold halfTurnCenter
  constructor <;> linarith [Real.pi_pos, hs.1, hs.2]

/-- Removing the alternating sign expresses an aligned oscillator in the
local sine coordinate of each half-turn. The formula holds at every
time in the supplied solution segment. -/
theorem normalizedOscillator_eq_sin
    {origin finish radius : ℝ} {u v : ℝ → ℝ}
    (hu : ContinuousOn u (Icc origin finish))
    (hv : ContinuousOn v (Icc origin finish))
    (hdu : ∀ s ∈ Ioo origin finish, HasDerivAt u (-v s) s)
    (hdv : ∀ s ∈ Ioo origin finish, HasDerivAt v (u s) s)
    (hu0 : u origin = 0) (hv0 : v origin = -radius)
    (n : ℕ) {t : ℝ} (ht : t ∈ Icc origin finish) :
    (-1 : ℝ) ^ n * u t = radius * Real.sin (t - halfTurnBoundary origin n) := by
  have hform := (oscillator_eq_rotation hu hv hdu hdv ht).1
  rw [hu0, hv0] at hform
  have hphase : t - origin = (t - halfTurnBoundary origin n) + (n : ℝ) * Real.pi := by
    unfold halfTurnBoundary
    ring
  rw [hphase, Real.sin_add_nat_mul_pi] at hform
  have hsign : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    (-1 : ℝ) ^ n * u t =
        radius * ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) *
          Real.sin (t - halfTurnBoundary origin n) := by rw [hform]; ring
    _ = _ := by rw [hsign]; ring

/-- The normalized oscillator weight is nonnegative throughout each
half-turn. -/
theorem normalizedOscillator_nonneg_on_halfTurn
    {origin finish radius : ℝ} {u v : ℝ → ℝ}
    (hu : ContinuousOn u (Icc origin finish))
    (hv : ContinuousOn v (Icc origin finish))
    (hdu : ∀ s ∈ Ioo origin finish, HasDerivAt u (-v s) s)
    (hdv : ∀ s ∈ Ioo origin finish, HasDerivAt v (u s) s)
    (hu0 : u origin = 0) (hv0 : v origin = -radius) (hradius : 0 ≤ radius)
    (n : ℕ) {t : ℝ} (ht : t ∈ Icc origin finish)
    (hhalf : t ∈ Icc (halfTurnBoundary origin n) (halfTurnBoundary origin (n + 1))) :
    0 ≤ (-1 : ℝ) ^ n * u t := by
  rw [normalizedOscillator_eq_sin hu hv hdu hdv hu0 hv0 n ht]
  apply mul_nonneg hradius
  apply Real.sin_nonneg_of_mem_Icc
  rw [halfTurnBoundary_succ] at hhalf
  exact ⟨by linarith [hhalf.1], by linarith [hhalf.2]⟩

/-- The opposite oscillator weight vanishes on a half-turn. At even indices
this is the copy weight, and at odd indices it is the compute weight. -/
theorem oppositeWeight_eq_zero_on_halfTurn
    {origin finish radius : ℝ} {u v : ℝ → ℝ}
    (hu : ContinuousOn u (Icc origin finish))
    (hv : ContinuousOn v (Icc origin finish))
    (hdu : ∀ s ∈ Ioo origin finish, HasDerivAt u (-v s) s)
    (hdv : ∀ s ∈ Ioo origin finish, HasDerivAt v (u s) s)
    (hu0 : u origin = 0) (hv0 : v origin = -radius) (hradius : 0 ≤ radius)
    (n : ℕ) {t : ℝ} (ht : t ∈ Icc origin finish)
    (hhalf : t ∈ Icc (halfTurnBoundary origin n) (halfTurnBoundary origin (n + 1))) :
    max (-((-1 : ℝ) ^ n * u t)) 0 = 0 := by
  exact max_eq_right (neg_nonpos.mpr
    (normalizedOscillator_nonneg_on_halfTurn hu hv hdu hdv hu0 hv0 hradius n ht hhalf))

/-- Centering a half-turn turns the normalized oscillator into the cosine
weight used in the concrete gain estimate. -/
theorem normalizedOscillator_eq_cos
    {origin finish radius : ℝ} {u v : ℝ → ℝ}
    (hu : ContinuousOn u (Icc origin finish))
    (hv : ContinuousOn v (Icc origin finish))
    (hdu : ∀ s ∈ Ioo origin finish, HasDerivAt u (-v s) s)
    (hdv : ∀ s ∈ Ioo origin finish, HasDerivAt v (u s) s)
    (hu0 : u origin = 0) (hv0 : v origin = -radius)
    (n : ℕ) (s : ℝ) (ht : halfTurnCenter origin n + s ∈ Icc origin finish) :
    (-1 : ℝ) ^ n * u (halfTurnCenter origin n + s) = radius * Real.cos s := by
  rw [normalizedOscillator_eq_sin hu hv hdu hdv hu0 hv0 n ht]
  have hphase : halfTurnCenter origin n + s - halfTurnBoundary origin n = s + Real.pi / 2 := by
    unfold halfTurnCenter
    ring
  rw [hphase, Real.sin_add_pi_div_two]

/-- A unit-speed clock evaluated at half-turn centers is exactly the
translated `π`-lattice used by the summability estimate. -/
theorem unitSpeedClock_at_halfTurnCenter
    {origin finish : ℝ} {clock : ℝ → ℝ}
    (hclock : ContinuousOn clock (Icc origin finish))
    (hderiv : ∀ s ∈ Ioo origin finish, HasDerivAt clock 1 s)
    (n : ℕ) (ht : halfTurnCenter origin n ∈ Icc origin finish) :
    clock (halfTurnCenter origin n) = clock origin + Real.pi / 2 + (n : ℝ) * Real.pi := by
  rw [unitSpeedClock_eq hclock hderiv ht]
  unfold halfTurnCenter halfTurnBoundary
  ring

/-- The actual clock-dependent gain, expressed in a centered half-turn
coordinate, is exactly the explicit rate used in the gain estimate. -/
theorem centeredClockRate_eq
    {origin finish radius gain : ℝ} {clock u v : ℝ → ℝ}
    (hclock : ContinuousOn clock (Icc origin finish))
    (hdclock : ∀ t ∈ Ioo origin finish, HasDerivAt clock 1 t)
    (hu : ContinuousOn u (Icc origin finish))
    (hv : ContinuousOn v (Icc origin finish))
    (hdu : ∀ t ∈ Ioo origin finish, HasDerivAt u (-v t) t)
    (hdv : ∀ t ∈ Ioo origin finish, HasDerivAt v (u t) t)
    (hu0 : u origin = 0) (hv0 : v origin = -radius)
    (n : ℕ) (s : ℝ) (ht : halfTurnCenter origin n + s ∈ Icc origin finish) :
    gain * (1 + clock (halfTurnCenter origin n + s) ^ 2) ^ 2 *
        max ((-1 : ℝ) ^ n * u (halfTurnCenter origin n + s)) 0 =
      clockedRelaxationRate gain (clock origin + Real.pi / 2 + (n : ℝ) * Real.pi) radius s := by
  have htime : clock (halfTurnCenter origin n + s) =
      clock origin + Real.pi / 2 + (n : ℝ) * Real.pi + s := by
    rw [unitSpeedClock_eq hclock hdclock ht]
    unfold halfTurnCenter halfTurnBoundary
    ring
  rw [htime, normalizedOscillator_eq_cos hu hv hdu hdv hu0 hv0 n s ht]
  rfl

end Stability.Simulation
