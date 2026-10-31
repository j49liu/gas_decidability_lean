import Stability.Simulation.OscillatorPhase
import Stability.Simulation.AlternatingClock

/-!
# Finite phase partitions from arbitrary oscillator data

An explicit sine phase is chosen from the initial oscillator state. Its
origin lies at most one period before the initial time, so clipping the
half-turn grid to any finite interval gives a finite partition with
constant oscillator sign on every piece. No future solution is assumed
in order to choose that grid.
-/

namespace Stability.Simulation

open Set

/-- An arbitrary oscillator solution has a sine phase whose origin lies
in the preceding period. The conclusion also covers zero amplitude. -/
theorem exists_oscillator_sine_phase
    {a b : ℝ} {u v : ℝ → ℝ}
    (hu : ContinuousOn u (Icc a b)) (hv : ContinuousOn v (Icc a b))
    (hdu : ∀ t ∈ Ioo a b, HasDerivAt u (-v t) t)
    (hdv : ∀ t ∈ Ioo a b, HasDerivAt v (u t) t) :
    ∃ origin ∈ Icc (a - 2 * Real.pi) a, ∃ radius : ℝ,
      0 ≤ radius ∧ radius ^ 2 = u a ^ 2 + v a ^ 2 ∧
      ∀ t ∈ Icc a b, u t = radius * Real.sin (t - origin) := by
  let z : ℂ := ⟨-v a, -u a⟩
  let phase := if Complex.arg z ≤ 0 then Complex.arg z else Complex.arg z - 2 * Real.pi
  have hphase : phase ∈ Icc (-(2 * Real.pi)) 0 := by
    by_cases h : Complex.arg z ≤ 0
    · simp only [phase, h, if_true]
      exact ⟨by linarith [Complex.neg_pi_lt_arg z, Real.pi_pos], h⟩
    · simp only [phase, h, if_false]
      exact ⟨by linarith, by linarith [Complex.arg_le_pi z, Real.pi_pos]⟩
  have hsin : Real.sin phase = Real.sin (Complex.arg z) := by
    by_cases h : Complex.arg z ≤ 0 <;> simp [phase, h, Real.sin_sub_two_pi]
  have hcos : Real.cos phase = Real.cos (Complex.arg z) := by
    by_cases h : Complex.arg z ≤ 0 <;> simp [phase, h, Real.cos_sub_two_pi]
  have huInitial : u a = -‖z‖ * Real.sin phase := by
    have hnorm : ‖z‖ * Real.sin phase = -u a := by
      rw [hsin]
      exact Complex.norm_mul_sin_arg z
    linarith
  have hvInitial : v a = -‖z‖ * Real.cos phase := by
    have hnorm : ‖z‖ * Real.cos phase = -v a := by
      rw [hcos]
      exact Complex.norm_mul_cos_arg z
    linarith
  refine ⟨a + phase, ⟨by linarith [hphase.1], by linarith [hphase.2]⟩,
    ‖z‖, norm_nonneg _, ?_, ?_⟩
  · rw [Complex.sq_norm, Complex.normSq_apply]
    dsimp [z]
    ring
  · intro t ht
    rw [(oscillator_eq_rotation hu hv hdu hdv ht).1, huInitial, hvInitial]
    have harg : t - (a + phase) = (t - a) - phase := by ring
    rw [harg, Real.sin_sub (t - a) phase]
    ring

/-- Clip a half-turn grid to a fixed finite time interval. Repeated
endpoints represent harmless empty phases at either end of the grid. -/
noncomputable def clippedHalfTurnBoundary (a b origin : ℝ) (n : ℕ) : ℝ :=
  max a (min b (halfTurnBoundary origin n))

theorem clippedHalfTurnBoundary_mem {a b origin : ℝ} (hab : a ≤ b) (n : ℕ) :
    clippedHalfTurnBoundary a b origin n ∈ Icc a b := by
  exact ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

theorem clippedHalfTurnBoundary_monotone (a b origin : ℝ) :
    Monotone (clippedHalfTurnBoundary a b origin) := by
  intro n m hnm
  exact max_le_max le_rfl (min_le_min le_rfl
    ((halfTurnBoundary_strictMono origin).monotone hnm))

theorem clippedHalfTurnBoundary_zero {a b origin : ℝ} (horigin : origin ≤ a) :
    clippedHalfTurnBoundary a b origin 0 = a := by
  simp only [clippedHalfTurnBoundary, halfTurnBoundary_zero]
  exact max_eq_left ((min_le_right _ _).trans horigin)

theorem clippedHalfTurnBoundary_eq_end {a b origin : ℝ} (hab : a ≤ b) (n : ℕ)
    (hend : b ≤ halfTurnBoundary origin n) : clippedHalfTurnBoundary a b origin n = b := by
  simp only [clippedHalfTurnBoundary, min_eq_left hend, max_eq_right hab]

/-- Every clipped phase has one fixed oscillator sign. A degenerate
piece is treated as a singleton, without imposing a parity condition. -/
theorem oscillator_constantSign_on_clipped_halfTurn
    {a b origin radius : ℝ} {u : ℝ → ℝ} (hab : a ≤ b) (hradius : 0 ≤ radius)
    (hform : ∀ t ∈ Icc a b, u t = radius * Real.sin (t - origin)) (n : ℕ) :
    (∀ t ∈ Icc (clippedHalfTurnBoundary a b origin n)
      (clippedHalfTurnBoundary a b origin (n + 1)), 0 ≤ u t) ∨
    (∀ t ∈ Icc (clippedHalfTurnBoundary a b origin n)
      (clippedHalfTurnBoundary a b origin (n + 1)), u t ≤ 0) := by
  let left := clippedHalfTurnBoundary a b origin n
  let right := clippedHalfTurnBoundary a b origin (n + 1)
  by_cases heq : left = right
  · have hpoint (t : ℝ) (ht : t ∈ Icc left right) : t = left := by
      rw [← heq] at ht
      exact le_antisymm ht.2 ht.1
    rcases le_total 0 (u left) with h | h
    · exact Or.inl (fun t ht ↦ by rw [hpoint t ht]; exact h)
    · exact Or.inr (fun t ht ↦ by rw [hpoint t ht]; exact h)
  have hlt : left < right := lt_of_le_of_ne
    (clippedHalfTurnBoundary_monotone a b origin (Nat.le_succ n)) heq
  have htime (t : ℝ) (ht : t ∈ Icc left right) : t ∈ Icc a b :=
    ⟨(clippedHalfTurnBoundary_mem hab n).1.trans ht.1,
      ht.2.trans (clippedHalfTurnBoundary_mem hab (n + 1)).2⟩
  have hgrid (t : ℝ) (ht : t ∈ Icc left right) :
      t ∈ Icc (halfTurnBoundary origin n) (halfTurnBoundary origin (n + 1)) := by
    have hleftEnd : left < b := hlt.trans_le (clippedHalfTurnBoundary_mem hab (n + 1)).2
    have hrightStart : a < right := (clippedHalfTurnBoundary_mem hab n).1.trans_lt hlt
    have hleftGrid : halfTurnBoundary origin n ≤ left := by
      by_cases h : halfTurnBoundary origin n ≤ b
      · exact (min_eq_right h).symm ▸ le_max_right a (min b (halfTurnBoundary origin n))
      · have hl : left = b := clippedHalfTurnBoundary_eq_end hab n (le_of_not_ge h)
        exact False.elim ((ne_of_lt hleftEnd) hl)
    have hrightGrid : right ≤ halfTurnBoundary origin (n + 1) := by
      have hmin : a < min b (halfTurnBoundary origin (n + 1)) := by
        simpa only [right, clippedHalfTurnBoundary, lt_max_iff, lt_self_iff_false,
          false_or] using hrightStart
      change max a (min b (halfTurnBoundary origin (n + 1))) ≤ _
      rw [max_eq_right hmin.le]
      exact min_le_right _ _
    exact ⟨hleftGrid.trans ht.1, ht.2.trans hrightGrid⟩
  have hsin (t : ℝ) (ht : t ∈ Icc left right) :
      0 ≤ Real.sin (t - halfTurnBoundary origin n) := by
    have hg := hgrid t ht
    rw [halfTurnBoundary_succ] at hg
    exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hg.1], by linarith [hg.2]⟩
  have hvalue (t : ℝ) (ht : t ∈ Icc left right) :
      u t = ((-1 : ℝ) ^ n) * (radius * Real.sin (t - halfTurnBoundary origin n)) := by
    rw [hform t (htime t ht)]
    have harg : t - origin = (t - halfTurnBoundary origin n) + (n : ℝ) * Real.pi := by
      simp only [halfTurnBoundary]
      ring
    rw [harg, Real.sin_add_nat_mul_pi]
    ring
  rcases le_total 0 ((-1 : ℝ) ^ n) with h | h
  · exact Or.inl (fun t ht ↦ by
      rw [hvalue t ht]
      exact mul_nonneg h (mul_nonneg hradius (hsin t ht)))
  · exact Or.inr (fun t ht ↦ by
      rw [hvalue t ht]
      exact mul_nonpos_of_nonpos_of_nonneg h (mul_nonneg hradius (hsin t ht)))

/-- A prescribed number of clipped half-turns suffices whenever its
length covers the interval plus one period. Thus the number of pieces
can be fixed using only a time-horizon cap, before seeing a solution. -/
theorem exists_oscillator_sign_partition
    {a b : ℝ} {N : ℕ} {u v : ℝ → ℝ} (hab : a ≤ b)
    (hcount : b - a + 2 * Real.pi ≤ (N : ℝ) * Real.pi)
    (hu : ContinuousOn u (Icc a b)) (hv : ContinuousOn v (Icc a b))
    (hdu : ∀ t ∈ Ioo a b, HasDerivAt u (-v t) t)
    (hdv : ∀ t ∈ Ioo a b, HasDerivAt v (u t) t) :
    ∃ boundary : ℕ → ℝ, boundary 0 = a ∧ boundary N = b ∧
      Monotone boundary ∧ (∀ n, boundary n ∈ Icc a b) ∧
      ∀ n < N,
        (∀ t ∈ Icc (boundary n) (boundary (n + 1)), 0 ≤ u t) ∨
        (∀ t ∈ Icc (boundary n) (boundary (n + 1)), u t ≤ 0) := by
  obtain ⟨origin, horigin, radius, hradius, _, hform⟩ :=
    exists_oscillator_sine_phase hu hv hdu hdv
  refine ⟨clippedHalfTurnBoundary a b origin,
    clippedHalfTurnBoundary_zero horigin.2, ?_,
    clippedHalfTurnBoundary_monotone a b origin,
    clippedHalfTurnBoundary_mem hab, fun n _ ↦ ?_⟩
  · apply clippedHalfTurnBoundary_eq_end hab N
    unfold halfTurnBoundary
    linarith [horigin.1]
  · exact oscillator_constantSign_on_clipped_halfTurn hab hradius hform n

end Stability.Simulation
