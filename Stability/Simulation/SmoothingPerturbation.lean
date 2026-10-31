import Stability.Simulation.FormulaSmoothness
import Stability.Simulation.ClockGain
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The actual smoothing perturbation along a clock trajectory

The coordinate estimates for a finite formula family give a sup-norm
bound for its vector error. If a supplied trajectory has a unit-speed
clock, the integral of this actual error norm over any finite forward
interval is less than `ε * π`, independently of the other coordinates.
-/

namespace Stability.Simulation.AbsFormula

open Set MeasureTheory Filter
open scoped Topology

noncomputable section

variable {σ ι : Type*} [Fintype ι]

/-- The difference of the explicitly smoothed family and the original
family, as a vector in the finite sup-norm coordinate space. -/
def smoothingError (formulas : ι → AbsFormula σ) (clock : σ) (ε : ℚ)
    (x : σ → ℝ) : ι → ℝ := fun i ↦
  smoothEval (polynomialValue x (precisionPolynomial formulas clock ε)) x (formulas i) -
    eval x (formulas i)

theorem norm_smoothingError_le_clockTail (formulas : ι → AbsFormula σ)
    (clock : σ) {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1) (x : σ → ℝ) :
    ‖smoothingError formulas clock ε x‖ ≤ (ε : ℝ) / (1 + (x clock) ^ 2) := by
  have hεReal : (0 : ℝ) < ε := by exact_mod_cast hε
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  exact smoothEval_error_le_clockTail formulas clock hε hεOne x i

theorem continuous_smoothingError [Finite σ]
    (formulas : ι → AbsFormula σ) (clock : σ)
    {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1) :
    Continuous (smoothingError formulas clock ε) := by
  letI := Fintype.ofFinite σ
  apply (contDiff_smoothedFamily formulas clock hε hεOne).continuous.sub
  apply continuous_pi
  intro i
  exact continuous_eval (fun j ↦ continuous_apply j) (formulas i)

/-- A unit-speed clock makes the vector perturbation uniformly
integrable on every supplied finite forward solution segment. The curve
need not satisfy any ODE in its other coordinates for this estimate. -/
theorem integral_norm_smoothingError_lt_pi [Finite σ]
    (formulas : ι → AbsFormula σ) (clock : σ)
    {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1)
    {a b : ℝ} (hab : a ≤ b) {x : ℝ → σ → ℝ}
    (hx : ContinuousOn x (Icc a b))
    (hclock : ∀ t ∈ Ioo a b, HasDerivAt (fun s ↦ x s clock) 1 t) :
    (∫ t in a..b, ‖smoothingError formulas clock ε (x t)‖) < (ε : ℝ) * Real.pi := by
  have hεReal : (0 : ℝ) < ε := by exact_mod_cast hε
  have hclockContinuous := (continuous_apply clock).comp_continuousOn hx
  have hclockValue (t : ℝ) (ht : t ∈ Icc a b) :
      x t clock = (x a clock - a) + t := by
    have h := unitSpeedClock_eq hclockContinuous hclock ht
    simp only [Function.comp_apply] at h
    linarith
  have herrorContinuous : ContinuousOn
      (fun t ↦ ‖smoothingError formulas clock ε (x t)‖) (Icc a b) :=
    ((continuous_smoothingError formulas clock hε hεOne).comp_continuousOn hx).norm
  have htailContinuous : Continuous
      (fun t : ℝ ↦ (ε : ℝ) / (1 + ((x a clock - a) + t) ^ 2)) := by
    exact continuous_const.div (by fun_prop) (fun t ↦ ne_of_gt (by positivity))
  have hcomparison := intervalIntegral.integral_mono_on (μ := volume) hab
    (herrorContinuous.intervalIntegrable_of_Icc hab)
    (htailContinuous.intervalIntegrable a b)
    (fun t ht ↦ by
      simpa only [hclockValue t ht] using
        norm_smoothingError_le_clockTail formulas clock hε hεOne (x t))
  exact hcomparison.trans_lt (integral_clockTail_lt_pi hεReal (x a clock - a) a b)

/-- On a complete forward clock trajectory the actual vector error is
integrable, not merely bounded on each fixed finite interval. -/
theorem integrableOn_smoothingError_Ioi [Finite σ]
    (formulas : ι → AbsFormula σ) (clock : σ)
    {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1)
    {a : ℝ} {x : ℝ → σ → ℝ}
    (hx : ContinuousOn x (Ici a))
    (hclock : ∀ t ∈ Ioi a, HasDerivAt (fun s ↦ x s clock) 1 t) :
    IntegrableOn (fun t ↦ smoothingError formulas clock ε (x t)) (Ioi a) := by
  refine integrableOn_Ioi_of_intervalIntegral_norm_bounded ((ε : ℝ) * Real.pi) a
    (b := fun b : ℝ ↦ b) ?_ tendsto_id ?_
  · intro b
    have hcont := (continuous_smoothingError formulas clock hε hεOne).comp_continuousOn
      (hx.mono (show Icc a b ⊆ Ici a from fun _ ht ↦ ht.1))
    exact hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  · filter_upwards [eventually_ge_atTop a] with b hab
    exact (integral_norm_smoothingError_lt_pi formulas clock hε hεOne hab
      (hx.mono (fun _ ht ↦ ht.1)) (fun t ht ↦ hclock t ht.1)).le

/-- The entire forward perturbation budget is at most `ε * π`.
Integrability is proved above, so this is an ordinary integral of the
actual error norm, not the default value of an undefined integral. -/
theorem integral_Ioi_norm_smoothingError_le_pi [Finite σ]
    (formulas : ι → AbsFormula σ) (clock : σ)
    {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1)
    {a : ℝ} {x : ℝ → σ → ℝ}
    (hx : ContinuousOn x (Ici a))
    (hclock : ∀ t ∈ Ioi a, HasDerivAt (fun s ↦ x s clock) 1 t) :
    (∫ t in Ioi a, ‖smoothingError formulas clock ε (x t)‖) ≤ (ε : ℝ) * Real.pi := by
  have hint := integrableOn_smoothingError_Ioi formulas clock hε hεOne hx hclock
  have hlimit := intervalIntegral_tendsto_integral_Ioi a hint.norm
    (tendsto_id : Tendsto (fun b : ℝ ↦ b) atTop atTop)
  apply le_of_tendsto hlimit
  filter_upwards [eventually_ge_atTop a] with b hab
  exact (integral_norm_smoothingError_lt_pi formulas clock hε hεOne hab
    (hx.mono (fun _ ht ↦ ht.1)) (fun t ht ↦ hclock t ht.1)).le

end

end Stability.Simulation.AbsFormula
