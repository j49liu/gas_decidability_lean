import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Explicit clock dynamics and relaxation gain

Clock identities and the central-arc gain estimate used in Section 4 of
M. Korda, *Lyapunov stability of polynomial vector fields is undecidable*,
https://arxiv.org/html/2609.22058v2#S4.
-/

namespace Stability.Simulation

open Set MeasureTheory

private theorem eq_initial_of_hasDerivAt_zero
    {a b : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hderiv : ∀ s ∈ Ioo a b, HasDerivAt f 0 s)
    {t : ℝ} (ht : t ∈ Icc a b) :
    f t = f a := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    (hf.mono (Icc_subset_Icc le_rfl ht.2))
    (fun s hs ↦ hderiv s ⟨hs.1, hs.2.trans_le ht.2⟩)
    (intervalIntegrable_const (c := (0 : ℝ)))
  simp only [intervalIntegral.integral_zero] at hFTC
  linarith

/-- A clock with derivative one records elapsed time exactly. -/
theorem unitSpeedClock_eq
    {a b : ℝ} {clock : ℝ → ℝ}
    (hclock : ContinuousOn clock (Icc a b))
    (hderiv : ∀ s ∈ Ioo a b, HasDerivAt clock 1 s)
    {t : ℝ} (ht : t ∈ Icc a b) :
    clock t = clock a + (t - a) := by
  have hconstant := eq_initial_of_hasDerivAt_zero
    (hclock.sub continuousOn_id)
    (fun s hs ↦ by simpa using (hderiv s hs).sub (hasDerivAt_id s)) ht
  change clock t - t = clock a - a at hconstant
  linarith

/-- Every solution segment of the harmonic oscillator has the explicit
rotation formula, with no restriction on its initial amplitude or phase. -/
theorem oscillator_eq_rotation
    {a b : ℝ} {u v : ℝ → ℝ}
    (hu : ContinuousOn u (Icc a b))
    (hv : ContinuousOn v (Icc a b))
    (hdu : ∀ s ∈ Ioo a b, HasDerivAt u (-v s) s)
    (hdv : ∀ s ∈ Ioo a b, HasDerivAt v (u s) s)
    {t : ℝ} (ht : t ∈ Icc a b) :
    u t = u a * Real.cos (t - a) - v a * Real.sin (t - a) ∧
      v t = u a * Real.sin (t - a) + v a * Real.cos (t - a) := by
  have hcos : ContinuousOn (fun s : ℝ ↦ Real.cos (s - a)) (Icc a b) := by
    fun_prop
  have hsin : ContinuousOn (fun s : ℝ ↦ Real.sin (s - a)) (Icc a b) := by
    fun_prop
  have hdcos (s : ℝ) :
      HasDerivAt (fun s ↦ Real.cos (s - a)) (-Real.sin (s - a)) s := by
    simpa using (Real.hasDerivAt_cos (s - a)).comp s ((hasDerivAt_id s).sub_const a)
  have hdsin (s : ℝ) :
      HasDerivAt (fun s ↦ Real.sin (s - a)) (Real.cos (s - a)) s := by
    simpa using (Real.hasDerivAt_sin (s - a)).comp s ((hasDerivAt_id s).sub_const a)
  have hfirst : u t * Real.cos (t - a) + v t * Real.sin (t - a) = u a := by
    have hconstant := eq_initial_of_hasDerivAt_zero
      ((hu.mul hcos).add (hv.mul hsin))
      (fun s hs ↦ by
        convert ((hdu s hs).mul (hdcos s)).add ((hdv s hs).mul (hdsin s)) using 1
        ring) ht
    simpa using hconstant
  have hsecond : v t * Real.cos (t - a) - u t * Real.sin (t - a) = v a := by
    have hconstant := eq_initial_of_hasDerivAt_zero
      ((hv.mul hcos).sub (hu.mul hsin))
      (fun s hs ↦ by
        convert ((hdv s hs).mul (hdcos s)).sub ((hdu s hs).mul (hdsin s)) using 1
        ring) ht
    simpa using hconstant
  constructor
  · calc
      u t = u t * (Real.cos (t - a) ^ 2 + Real.sin (t - a) ^ 2) := by
        rw [Real.cos_sq_add_sin_sq, mul_one]
      _ = (u t * Real.cos (t - a) + v t * Real.sin (t - a)) * Real.cos (t - a) -
          (v t * Real.cos (t - a) - u t * Real.sin (t - a)) * Real.sin (t - a) := by ring
      _ = _ := by rw [hfirst, hsecond]
  · calc
      v t = v t * (Real.cos (t - a) ^ 2 + Real.sin (t - a) ^ 2) := by
        rw [Real.cos_sq_add_sin_sq, mul_one]
      _ = (u t * Real.cos (t - a) + v t * Real.sin (t - a)) * Real.sin (t - a) +
          (v t * Real.cos (t - a) - u t * Real.sin (t - a)) * Real.cos (t - a) := by ring
      _ = _ := by rw [hfirst, hsecond]

/-- The squared oscillator amplitude is constant on every supplied
solution segment. -/
theorem oscillator_amplitude_sq_eq
    {a b : ℝ} {u v : ℝ → ℝ}
    (hu : ContinuousOn u (Icc a b))
    (hv : ContinuousOn v (Icc a b))
    (hdu : ∀ s ∈ Ioo a b, HasDerivAt u (-v s) s)
    (hdv : ∀ s ∈ Ioo a b, HasDerivAt v (u s) s)
    {t : ℝ} (ht : t ∈ Icc a b) :
    u t ^ 2 + v t ^ 2 = u a ^ 2 + v a ^ 2 := by
  apply eq_initial_of_hasDerivAt_zero ((hu.pow 2).add (hv.pow 2)) ?_ ht
  intro s hs
  convert ((hdu s hs).pow 2).add ((hdv s hs).pow 2) using 1
  ring

/-- The active relaxation rate in coordinates centered at a compute or
copy arc. The clock offset is arbitrary. -/
noncomputable def clockedRelaxationRate (gain offset radius time : ℝ) : ℝ :=
  gain * (1 + (offset + time) ^ 2) ^ 2 * max (radius * Real.cos time) 0

/-- The explicit relaxation rate is continuous in time. -/
theorem continuous_clockedRelaxationRate (gain offset radius : ℝ) :
    Continuous (clockedRelaxationRate gain offset radius) := by
  unfold clockedRelaxationRate
  fun_prop

/-- A nonnegative gain gives a nonnegative relaxation rate at every time. -/
theorem clockedRelaxationRate_nonneg
    {gain offset radius time : ℝ} (hgain : 0 ≤ gain) :
    0 ≤ clockedRelaxationRate gain offset radius time := by
  unfold clockedRelaxationRate
  positivity

/-- The integrated gain on the central arc is bounded below uniformly in
the clock offset. Only the lower amplitude cutoff is needed here; the
upper cutoff used by the output is irrelevant to this lower bound. -/
theorem centralArc_gain_lowerBound
    {gain radius : ℝ} (hgain : 0 < gain) (hradius : 0 ≤ radius)
    (hamplitude : (1 / 2 : ℝ) < radius ^ 2) (offset : ℝ) :
    gain * (1 + (max (|offset| - Real.pi / 3) 0) ^ 2) ^ 2 ≤
      2 * (∫ t in -(Real.pi / 3)..Real.pi / 3,
        clockedRelaxationRate gain offset radius t) := by
  let distance : ℝ := max (|offset| - Real.pi / 3) 0
  have hdist_nonneg : 0 ≤ distance := le_max_right _ _
  have hradius_lower : (2 / 3 : ℝ) < radius := by nlinarith
  have hpoint : ∀ t ∈ Icc (-(Real.pi / 3)) (Real.pi / 3),
      gain * (1 + distance ^ 2) ^ 2 / 3 ≤
        clockedRelaxationRate gain offset radius t := by
    intro t ht
    have habs : |t| ≤ Real.pi / 3 := abs_le.mpr ht
    have hdist : distance ≤ |offset + t| := by
      apply max_le ?_ (abs_nonneg _)
      have htriangle : |offset| ≤ |offset + t| + |t| := by
        simpa using abs_add_le (offset + t) (-t)
      linarith
    have hsquare : distance ^ 2 ≤ (offset + t) ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ hdist_nonneg (abs_nonneg _)).mpr hdist
    have hpoly : (1 + distance ^ 2) ^ 2 ≤ (1 + (offset + t) ^ 2) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by positivity)).mpr (by linarith)
    have hcos : (1 / 2 : ℝ) ≤ Real.cos t := by
      have h := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg t)
        (show Real.pi / 3 ≤ Real.pi by linarith [Real.pi_pos]) habs
      simpa only [Real.cos_pi_div_three, Real.cos_abs] using h
    have hweight : (1 / 3 : ℝ) ≤ max (radius * Real.cos t) 0 := by
      have hscaled := mul_le_mul_of_nonneg_left hcos hradius
      have hmax := le_max_left (radius * Real.cos t) (0 : ℝ)
      linarith
    have hproduct := mul_le_mul hpoly hweight
      (by norm_num : (0 : ℝ) ≤ 1 / 3)
      (by positivity : 0 ≤ (1 + (offset + t) ^ 2) ^ 2)
    have hscaled := mul_le_mul_of_nonneg_left hproduct hgain.le
    unfold clockedRelaxationRate
    nlinarith
  have hinterval : -(Real.pi / 3) ≤ Real.pi / 3 := by linarith [Real.pi_pos]
  have hintegral := intervalIntegral.integral_mono_on (μ := volume) hinterval
    (intervalIntegrable_const (c := gain * (1 + distance ^ 2) ^ 2 / 3))
    ((continuous_clockedRelaxationRate gain offset radius).intervalIntegrable _ _) hpoint
  rw [intervalIntegral.integral_const, smul_eq_mul] at hintegral
  have hpositive : 0 ≤ gain * (1 + distance ^ 2) ^ 2 := by positivity
  have hpi : 0 ≤ 4 * Real.pi - 9 := by linarith [Real.pi_gt_three]
  have hscaled := mul_nonneg hpi hpositive
  change gain * (1 + distance ^ 2) ^ 2 ≤ _
  nlinarith

/-- Every admissible central arc supplies strictly positive integrated
relaxation gain. -/
theorem centralArc_integral_pos
    {gain radius : ℝ} (hgain : 0 < gain) (hradius : 0 ≤ radius)
    (hamplitude : (1 / 2 : ℝ) < radius ^ 2) (offset : ℝ) :
    0 < ∫ t in -(Real.pi / 3)..Real.pi / 3,
      clockedRelaxationRate gain offset radius t := by
  have hbound := centralArc_gain_lowerBound hgain hradius hamplitude offset
  have hpositive : 0 < gain * (1 + (max (|offset| - Real.pi / 3) 0) ^ 2) ^ 2 := by
    positivity
  linarith

/-- The concrete central-arc gain gives the clock-decaying error term used
in the scalar cubic-relaxation bound. -/
theorem centralArc_relaxationError_le
    {gain radius : ℝ} (hgain : 0 < gain) (hradius : 0 ≤ radius)
    (hamplitude : (1 / 2 : ℝ) < radius ^ 2) (offset : ℝ) :
    (Real.sqrt (2 * (∫ t in -(Real.pi / 3)..Real.pi / 3,
      clockedRelaxationRate gain offset radius t)))⁻¹ ≤
        (Real.sqrt gain)⁻¹ * (1 + (max (|offset| - Real.pi / 3) 0) ^ 2)⁻¹ := by
  have hbound := centralArc_gain_lowerBound hgain hradius hamplitude offset
  have hroot : Real.sqrt gain * (1 + (max (|offset| - Real.pi / 3) 0) ^ 2) ≤
      Real.sqrt (2 * (∫ t in -(Real.pi / 3)..Real.pi / 3,
        clockedRelaxationRate gain offset radius t)) := by
    apply Real.le_sqrt_of_sq_le
    rw [mul_pow, Real.sq_sqrt hgain.le]
    exact hbound
  have hpositive : 0 < Real.sqrt gain * (1 + (max (|offset| - Real.pi / 3) 0) ^ 2) := by
    exact mul_pos (Real.sqrt_pos.mpr hgain) (by positivity)
  simpa only [one_div, mul_inv_rev, mul_comm] using
    one_div_le_one_div_of_le hpositive hroot

end Stability.Simulation
