import HGAS.Modular.GammaTwoC0RightTranslation
import HGAS.Modular.FlowGenericPointMeanErgodic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic

/-!
# Quantitative finite-time comparison in anisotropic shear boxes

This module turns the exact matrix identity from
`HorocycleShearingAlgebra` into the analytic estimate used in the
Hubbard--Miller good-times proof.

There are two stages.

First, strong continuity of the right regular action on `C₀` implies that
the exact stable-sheet correction changes an observable uniformly by a
small amount.  The small variables are the lower coordinate `r`, the
diagonal coordinate `t`, and the product `r*s`.

Second, the proof compares four successive integrals.  It inserts the
Jacobian of the exact time change, applies interval-integral
substitution, controls the changed endpoint by the mean-value theorem,
and bounds the final upper-horocycle displacement by two boundary
intervals.  The result is an explicit error

`ρ * (1 + 4 * ‖f‖)`

for normalized integer averages.  No geometric metric on the quotient
and no unformalized change-of-variables step remain in this estimate.
-/

namespace HGAS.Modular

open Filter Function _root_.MeasureTheory Set Topology
open scoped BoundedContinuousFunction Interval ZeroAtInfty

noncomputable section

local instance gammaTwoFrameQuotientMetricSpaceShear :
    MetricSpace GammaTwoFrameQuotient :=
  TopologicalSpace.metrizableSpaceMetric GammaTwoFrameQuotient

local instance realModularFrameMetricSpaceShear :
    MetricSpace RealModularFrame :=
  TopologicalSpace.metrizableSpaceMetric RealModularFrame

/-- The stable-sheet correction appearing on the right side of the
exact shear identity. -/
def horocycleShearCorrection
    (r t s : ℝ) : RealModularFrame :=
  lowerUnipotent (r / (1 - r * s)) *
    geodesicFrame (t + 2 * Real.log (1 - r * s))

/-- The same correction, with `v = r*s` exposed as an independent
small parameter. -/
def horocycleShearCorrectionParameters
    (p : ℝ × (ℝ × ℝ)) : RealModularFrame :=
  lowerUnipotent (p.1 / (1 - p.2.2)) *
    geodesicFrame
      (p.2.1 + 2 * Real.log (1 - p.2.2))

@[simp]
theorem horocycleShearCorrectionParameters_zero :
    horocycleShearCorrectionParameters (0, (0, 0)) = 1 := by
  simp [horocycleShearCorrectionParameters]

theorem continuousAt_horocycleShearCorrectionParameters :
    ContinuousAt horocycleShearCorrectionParameters
      (0, (0, 0)) := by
  unfold horocycleShearCorrectionParameters
  apply ContinuousAt.mul
  · apply lowerUnipotent_continuous.continuousAt.comp
    exact continuousAt_fst.div₀
      (continuousAt_const.sub (continuousAt_snd.snd))
      (by norm_num)
  · apply geodesicFrame_continuous.continuousAt.comp
    have hlog :
        ContinuousAt
          (fun p : ℝ × (ℝ × ℝ) ↦
            Real.log (1 - p.2.2))
          (0, (0, 0)) := by
      exact (Real.continuousAt_log (by norm_num)).comp
        (continuousAt_const.sub (continuousAt_snd.snd))
    fun_prop

/-- Uniform `C₀` comparison supplied by the exact shear identity.

The transverse lower coordinate is of order `1/T`; hence both `r` and
`r*s` are small for `0 ≤ s ≤ T` once `T ≥ 1`. -/
theorem exists_delta_gammaTwoHorocycleFlow_shear_observable_close
    (f : C₀(GammaTwoFrameQuotient, ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧
      ∀ (T r t s : ℝ) (q : GammaTwoFrameQuotient),
        1 ≤ T →
        |r| < δ / T →
        |t| < δ →
        0 ≤ s →
        s ≤ T →
        |f (gammaTwoHorocycleFlow s q) -
          f (gammaTwoHorocycleFlow
            (horocycleShearTime r t s)
            (gammaTwoFrameRightMul
              (lowerUnipotent r * geodesicFrame t) q))| < ε := by
  let P : ℝ × (ℝ × ℝ) → C₀(GammaTwoFrameQuotient, ℝ) :=
    fun p ↦ gammaTwoC0RightTranslate
      (horocycleShearCorrectionParameters p) f
  have hcorr :
      Tendsto horocycleShearCorrectionParameters
        (𝓝 (0, (0, 0))) (𝓝 1) :=
    by
      rw [← horocycleShearCorrectionParameters_zero]
      exact continuousAt_horocycleShearCorrectionParameters
  have hP :
      Tendsto P (𝓝 (0, (0, 0))) (𝓝 f) := by
    simpa only [P] using
      (tendsto_gammaTwoC0RightTranslate_one f).comp hcorr
  have hevent :
      {p : ℝ × (ℝ × ℝ) | dist (P p) f < ε} ∈
        𝓝 (0, (0, 0)) :=
    Metric.tendsto_nhds.mp hP ε hε
  obtain ⟨η, hη, hclose⟩ :=
    Metric.mem_nhds_iff.mp hevent
  let δ : ℝ := min η (1 / 2)
  have hδ : 0 < δ :=
    lt_min hη (by norm_num)
  refine ⟨δ, hδ, min_le_right _ _, ?_⟩
  intro T r t s q hT hr ht hs hsT
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hrδ : |r| < δ := by
    calc
      |r| < δ / T := hr
      _ ≤ δ := by
        rw [div_le_iff₀ hTpos]
        nlinarith
  have hrsδ : |r * s| < δ := by
    calc
      |r * s| = |r| * s := by
        rw [abs_mul, abs_of_nonneg hs]
      _ ≤ |r| * T :=
        mul_le_mul_of_nonneg_left hsT (abs_nonneg r)
      _ < (δ / T) * T :=
        mul_lt_mul_of_pos_right hr hTpos
      _ = δ := by field_simp
  have hparam :
      dist (r, (t, r * s))
          ((0 : ℝ), ((0 : ℝ), (0 : ℝ))) < η := by
    simp only [Prod.dist_eq, Real.dist_eq, sub_zero,
      max_lt_iff]
    exact ⟨hrδ.trans_le (min_le_left _ _),
      ht.trans_le (min_le_left _ _),
      hrsδ.trans_le (min_le_left _ _)⟩
  have hnormClose :
      ‖P (r, (t, r * s)) - f‖ < ε := by
    simpa only [dist_eq_norm] using hclose hparam
  have hdenpos : 0 < 1 - r * s := by
    have hvupper := (abs_lt.mp hrsδ).2
    have hδhalf : δ ≤ 1 / 2 := min_le_right _ _
    linarith
  have hshear :=
    gammaTwoHorocycleFlow_shear q r t s hdenpos
  rw [hshear]
  change
    |f (gammaTwoHorocycleFlow s q) -
      gammaTwoC0RightTranslate
        (horocycleShearCorrection r t s) f
        (gammaTwoHorocycleFlow s q)| < ε
  have hcEq :
      horocycleShearCorrection r t s =
        horocycleShearCorrectionParameters
          (r, (t, r * s)) := rfl
  rw [hcEq]
  exact
    lt_of_le_of_lt
      (by
        have hbound :=
          BoundedContinuousFunction.norm_coe_le_norm
            (P (r, (t, r * s)) - f).toBCF
            (gammaTwoHorocycleFlow s q)
        change
          |(P (r, (t, r * s)) - f)
            (gammaTwoHorocycleFlow s q)| ≤
            ‖P (r, (t, r * s)) - f‖ at hbound
        simpa only [ZeroAtInftyContinuousMap.sub_apply, P,
          abs_sub_comm] using hbound)
      hnormClose

set_option maxHeartbeats 1600000 in
-- This theorem combines interval substitution, mean-value estimates, and
-- four norm bounds; elaborating the resulting dependent expressions needs
-- a larger deterministic budget.
/-- The full finite-time shear comparison.

For a point in the anisotropic box

`q · v(r) a(t) u(h)`,

with widths `|r| < δ/T`, `|t| < δ`, and `|h| < ρ T`,
the unnormalized length-`T` orbit integrals differ by at most

`ρ T (1 + 4 ‖f‖)`.

The four contributions are, respectively:

* uniform observable comparison along the sheared paths;
* insertion of the shear Jacobian;
* the endpoint error in the time change;
* the two boundary intervals caused by the upper-horocycle shift.
-/
theorem exists_delta_orbitIntegral_shear_box_close
    (f : C₀(GammaTwoFrameQuotient, ℝ))
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧
      ∀ (T r t h : ℝ) (q : GammaTwoFrameQuotient),
        1 ≤ T →
        |r| < δ / T →
        |t| < δ →
        |h| < ρ * T →
        |HGAS.Dynamics.orbitIntegral
            gammaTwoHorocycleFlow f.toBCF T q -
          HGAS.Dynamics.orbitIntegral
            gammaTwoHorocycleFlow f.toBCF T
              (gammaTwoFrameRightMul
                (lowerUnipotent r * geodesicFrame t *
                  upperUnipotent h) q)| ≤
          ρ * T * (1 + 4 * ‖f‖) := by
  obtain ⟨δf, hδf, hδfhalf, hfclose⟩ :=
    exists_delta_gammaTwoHorocycleFlow_shear_observable_close
      f hρ
  obtain ⟨δα, hδα, hδαhalf, hαclose⟩ :=
    exists_delta_horocycleShearTime_derivative_close hρ
  let δ : ℝ := min δf δα
  have hδ : 0 < δ := lt_min hδf hδα
  have hδhalf : δ ≤ 1 / 2 :=
    (min_le_left δf δα).trans hδfhalf
  refine ⟨δ, hδ, hδhalf, ?_⟩
  intro T r t h q hT hr ht hh
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hr_f : |r| < δf / T := by
    exact hr.trans_le
      (div_le_div_of_nonneg_right
        (min_le_left δf δα) hTpos.le)
  have ht_f : |t| < δf :=
    ht.trans_le (min_le_left δf δα)
  have hr_α : |r| < δα / T := by
    exact hr.trans_le
      (div_le_div_of_nonneg_right
        (min_le_right δf δα) hTpos.le)
  have ht_α : |t| < δα :=
    ht.trans_le (min_le_right δf δα)
  let z : GammaTwoFrameQuotient :=
    gammaTwoFrameRightMul
      (lowerUnipotent r * geodesicFrame t) q
  let y : GammaTwoFrameQuotient :=
    gammaTwoFrameRightMul
      (lowerUnipotent r * geodesicFrame t *
        upperUnipotent h) q
  let α : ℝ → ℝ := horocycleShearTime r t
  let D : ℝ → ℝ :=
    fun s ↦ Real.exp (-t) / (1 - r * s) ^ 2
  let gq : ℝ → ℝ :=
    fun s ↦ f (gammaTwoHorocycleFlow s q)
  let gzα : ℝ → ℝ :=
    fun s ↦ f (gammaTwoHorocycleFlow (α s) z)
  let gz : ℝ → ℝ :=
    fun s ↦ f (gammaTwoHorocycleFlow s z)
  have hrsδ (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
      |r * s| < δ := by
    calc
      |r * s| = |r| * s := by
        rw [abs_mul, abs_of_nonneg hs.1]
      _ ≤ |r| * T :=
        mul_le_mul_of_nonneg_left hs.2 (abs_nonneg r)
      _ < (δ / T) * T :=
        mul_lt_mul_of_pos_right hr hTpos
      _ = δ := by field_simp
  have hdenpos (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
      0 < 1 - r * s := by
    have hupper := (abs_lt.mp (hrsδ s hs)).2
    linarith
  have hDclose (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
      |D s - 1| < ρ := by
    dsimp only [D]
    exact hαclose T r t s hTpos hr_α ht_α
      hs.1 hs.2
  have hαderiv (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
      HasDerivAt α (D s) s := by
    dsimp only [α, D]
    exact hasDerivAt_horocycleShearTime r t s
      (ne_of_gt (hdenpos s hs))
  have hαcontinuous :
      ContinuousOn α (Icc (0 : ℝ) T) := by
    intro s hs
    exact (hαderiv s hs).continuousAt.continuousWithinAt
  have hendpoint :
      |α T - T| ≤ ρ * T := by
    let β : ℝ → ℝ := fun s ↦ α s - s
    let β' : ℝ → ℝ := fun s ↦ D s - 1
    have hβcontinuous :
        ContinuousOn β (Icc (0 : ℝ) T) := by
      intro s hs
      exact
        ((hαderiv s hs).sub (hasDerivAt_id s)).continuousAt
          |>.continuousWithinAt
    have hβderiv :
        ∀ s ∈ Ico (0 : ℝ) T,
          HasDerivWithinAt β (β' s) (Ici s) s := by
      intro s hs
      have hs' : s ∈ Icc (0 : ℝ) T :=
        Ico_subset_Icc_self hs
      exact
        ((hαderiv s hs').sub (hasDerivAt_id s))
          |>.hasDerivWithinAt
    have hβbound :
        ∀ s ∈ Ico (0 : ℝ) T, ‖β' s‖ ≤ ρ := by
      intro s hs
      have hs' : s ∈ Icc (0 : ℝ) T :=
        Ico_subset_Icc_self hs
      simpa only [β', Real.norm_eq_abs] using
        (hDclose s hs').le
    have hmv :=
      norm_image_sub_le_of_norm_deriv_right_le_segment
        hβcontinuous hβderiv hβbound T
        ⟨hTpos.le, le_rfl⟩
    have hαzero : α 0 = 0 := by
      simp [α, horocycleShearTime]
    simpa only [β, hαzero, sub_zero, Real.norm_eq_abs]
      using hmv
  have hobs (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
      |gq s - gzα s| < ρ := by
    dsimp only [gq, gzα, z, α]
    exact hfclose T r t s q hT hr_f ht_f hs.1 hs.2
  have hgq_cont : Continuous gq := by
    dsimp only [gq]
    exact f.continuous.comp
      (gammaTwoHorocycleFlow.continuous
        continuous_id continuous_const)
  have hgz_cont : Continuous gz := by
    dsimp only [gz]
    exact f.continuous.comp
      (gammaTwoHorocycleFlow.continuous
        continuous_id continuous_const)
  have hα_cont : ContinuousOn α (uIcc (0 : ℝ) T) := by
    simpa only [uIcc_of_le hTpos.le] using hαcontinuous
  have hgzα_cont : ContinuousOn gzα (Icc (0 : ℝ) T) := by
    dsimp only [gzα]
    exact hgz_cont.comp_continuousOn hαcontinuous
  have hgzα_ucont : ContinuousOn gzα (uIcc (0 : ℝ) T) := by
    simpa only [uIcc_of_le hTpos.le] using hgzα_cont
  have hfirst :
      |(∫ s in (0 : ℝ)..T, gq s) -
        ∫ s in (0 : ℝ)..T, gzα s| ≤ ρ * T := by
    rw [← intervalIntegral.integral_sub
      (hgq_cont.intervalIntegrable 0 T)
      (hgzα_ucont.intervalIntegrable)]
    simpa only [Real.norm_eq_abs, abs_of_nonneg hTpos.le,
      sub_zero] using
      (intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0 : ℝ)) (b := T) (C := ρ)
        (f := fun s ↦ gq s - gzα s)
        (fun s hs ↦ by
          have hs' : s ∈ Icc (0 : ℝ) T := by
            apply (show uIoc (0 : ℝ) T ⊆
              uIcc (0 : ℝ) T from uIoc_subset_uIcc)
              at hs
            simpa only [uIcc_of_le hTpos.le] using hs
          simpa only [Real.norm_eq_abs] using
            (hobs s hs').le))
  have hD_cont :
      ContinuousOn D (Icc (0 : ℝ) T) := by
    intro s hs
    dsimp only [D]
    exact
      (continuousAt_const.div₀
        ((continuousAt_const.sub
          (continuousAt_const.mul continuousAt_id)).pow 2)
        (pow_ne_zero 2 (ne_of_gt (hdenpos s hs))))
      |>.continuousWithinAt
  have hsecond :
      |(∫ s in (0 : ℝ)..T, gzα s) -
        ∫ s in (0 : ℝ)..T, gzα s * D s| ≤
          ‖f‖ * ρ * T := by
    have hprodInt :
        IntervalIntegrable (fun s ↦ gzα s * D s)
          volume 0 T :=
      (by
        apply ContinuousOn.intervalIntegrable
        simpa only [uIcc_of_le hTpos.le] using
          hgzα_cont.mul hD_cont)
    rw [← intervalIntegral.integral_sub
      hgzα_ucont.intervalIntegrable hprodInt]
    simpa only [Real.norm_eq_abs, abs_of_nonneg hTpos.le,
      sub_zero] using
      (intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0 : ℝ)) (b := T) (C := ‖f‖ * ρ)
        (f := fun s ↦ gzα s - gzα s * D s)
        (fun s hs ↦ by
          have hs' : s ∈ Icc (0 : ℝ) T := by
            apply (show uIoc (0 : ℝ) T ⊆
              uIcc (0 : ℝ) T from uIoc_subset_uIcc)
              at hs
            simpa only [uIcc_of_le hTpos.le] using hs
          change |gzα s - gzα s * D s| ≤ ‖f‖ * ρ
          rw [show gzα s - gzα s * D s =
            gzα s * (1 - D s) by ring, abs_mul,
            abs_sub_comm]
          exact mul_le_mul
            (f.toBCF.norm_coe_le_norm _)
            (hDclose s hs').le
            (abs_nonneg _) (norm_nonneg _)))
  have hDnonneg (s : ℝ)
      (hs : s ∈ Ioo (min (0 : ℝ) T) (max (0 : ℝ) T)) :
      0 ≤ D s := by
    dsimp only [D]
    positivity
  have hsubstitution :
      (∫ s in (0 : ℝ)..T, gzα s * D s) =
        ∫ s in α 0..α T, gz s := by
    have hsubst :=
      intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
        (g := gz) hα_cont
        (fun s hs ↦ hαderiv s <| by
          rw [min_eq_left hTpos.le,
            max_eq_right hTpos.le] at hs
          exact ⟨hs.1.le, hs.2.le⟩)
        hDnonneg
    simpa only [Function.comp_apply, gzα, gz] using hsubst
  have hαzero : α 0 = 0 := by
    simp [α, horocycleShearTime]
  have hthird :
      |HGAS.Dynamics.orbitIntegral
          gammaTwoHorocycleFlow f.toBCF (α T) z -
        HGAS.Dynamics.orbitIntegral
          gammaTwoHorocycleFlow f.toBCF T z| ≤
          ‖f‖ * ρ * T := by
    have hadd :=
      HGAS.Dynamics.orbitIntegral_add
        gammaTwoHorocycleFlow f.toBCF T (α T - T) z
    rw [show T + (α T - T) = α T by ring] at hadd
    rw [hadd, add_sub_cancel_left]
    calc
      |HGAS.Dynamics.orbitIntegral
          gammaTwoHorocycleFlow f.toBCF (α T - T)
            (gammaTwoHorocycleFlow T z)| ≤
          ‖f.toBCF‖ * |α T - T| := by
            simpa only [Real.norm_eq_abs] using
              HGAS.Dynamics.norm_orbitIntegral_le
                gammaTwoHorocycleFlow f.toBCF
                (α T - T)
                (gammaTwoHorocycleFlow T z)
      _ ≤ ‖f‖ * (ρ * T) := by
        rw [ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
        exact mul_le_mul_of_nonneg_left hendpoint
          (norm_nonneg f)
      _ = ‖f‖ * ρ * T := by ring
  have hyflow :
      y = gammaTwoHorocycleFlow h z := by
    dsimp only [y, z]
    have hmul :=
      congrFun
        (gammaTwoFrameRightMul_mul
          (lowerUnipotent r * geodesicFrame t)
          (upperUnipotent h)) q
    change
      gammaTwoFrameRightMul
          (lowerUnipotent r * geodesicFrame t *
            upperUnipotent h) q =
        gammaTwoFrameRightMul (upperUnipotent h)
          (gammaTwoFrameRightMul
            (lowerUnipotent r * geodesicFrame t) q)
    simpa only [Function.comp_apply] using hmul
  have hfourth :
      |HGAS.Dynamics.orbitIntegral
          gammaTwoHorocycleFlow f.toBCF T z -
        HGAS.Dynamics.orbitIntegral
          gammaTwoHorocycleFlow f.toBCF T y| ≤
          2 * ‖f‖ * ρ * T := by
    rw [hyflow]
    have hshift :=
      HGAS.Dynamics.orbitIntegral_flow_sub
        gammaTwoHorocycleFlow f.toBCF T h z
    have hbound1 :=
      HGAS.Dynamics.norm_orbitIntegral_le
        gammaTwoHorocycleFlow f.toBCF h
          (gammaTwoHorocycleFlow T z)
    have hbound2 :=
      HGAS.Dynamics.norm_orbitIntegral_le
        gammaTwoHorocycleFlow f.toBCF h z
    calc
      |HGAS.Dynamics.orbitIntegral
          gammaTwoHorocycleFlow f.toBCF T z -
        HGAS.Dynamics.orbitIntegral
          gammaTwoHorocycleFlow f.toBCF T
            (gammaTwoHorocycleFlow h z)| =
          |HGAS.Dynamics.orbitIntegral
            gammaTwoHorocycleFlow f.toBCF T
              (gammaTwoHorocycleFlow h z) -
          HGAS.Dynamics.orbitIntegral
            gammaTwoHorocycleFlow f.toBCF T z| :=
        abs_sub_comm _ _
      _ =
          |HGAS.Dynamics.orbitIntegral
            gammaTwoHorocycleFlow f.toBCF h
              (gammaTwoHorocycleFlow T z) -
          HGAS.Dynamics.orbitIntegral
            gammaTwoHorocycleFlow f.toBCF h z| := by
        rw [hshift]
      _ ≤
          |HGAS.Dynamics.orbitIntegral
            gammaTwoHorocycleFlow f.toBCF h
              (gammaTwoHorocycleFlow T z)| +
          |HGAS.Dynamics.orbitIntegral
            gammaTwoHorocycleFlow f.toBCF h z| :=
        abs_sub _ _
      _ ≤ ‖f.toBCF‖ * |h| + ‖f.toBCF‖ * |h| := by
        gcongr <;> simpa only [Real.norm_eq_abs]
      _ ≤ ‖f‖ * (ρ * T) + ‖f‖ * (ρ * T) := by
        rw [ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
        exact add_le_add
          (mul_le_mul_of_nonneg_left hh.le (norm_nonneg f))
          (mul_le_mul_of_nonneg_left hh.le (norm_nonneg f))
      _ = 2 * ‖f‖ * ρ * T := by ring
  change
    |(∫ s in (0 : ℝ)..T, gq s) -
      HGAS.Dynamics.orbitIntegral
        gammaTwoHorocycleFlow f.toBCF T y| ≤
      ρ * T * (1 + 4 * ‖f‖)
  have hrewrite :
      (∫ s in (0 : ℝ)..T, gzα s * D s) =
        HGAS.Dynamics.orbitIntegral
          gammaTwoHorocycleFlow f.toBCF (α T) z := by
    rw [hsubstitution, hαzero]
    rfl
  have htotal :
      |(∫ s in (0 : ℝ)..T, gq s) -
        HGAS.Dynamics.orbitIntegral
          gammaTwoHorocycleFlow f.toBCF T y| ≤
        |(∫ s in (0 : ℝ)..T, gq s) -
          ∫ s in (0 : ℝ)..T, gzα s| +
        (|(∫ s in (0 : ℝ)..T, gzα s) -
          ∫ s in (0 : ℝ)..T, gzα s * D s| +
        (|HGAS.Dynamics.orbitIntegral
            gammaTwoHorocycleFlow f.toBCF (α T) z -
          HGAS.Dynamics.orbitIntegral
            gammaTwoHorocycleFlow f.toBCF T z| +
        |HGAS.Dynamics.orbitIntegral
            gammaTwoHorocycleFlow f.toBCF T z -
          HGAS.Dynamics.orbitIntegral
            gammaTwoHorocycleFlow f.toBCF T y|)) := by
    rw [hrewrite]
    calc
      |(∫ s in (0 : ℝ)..T, gq s) -
          HGAS.Dynamics.orbitIntegral
            gammaTwoHorocycleFlow f.toBCF T y| ≤
          |(∫ s in (0 : ℝ)..T, gq s) -
            ∫ s in (0 : ℝ)..T, gzα s| +
          |(∫ s in (0 : ℝ)..T, gzα s) -
            HGAS.Dynamics.orbitIntegral
              gammaTwoHorocycleFlow f.toBCF T y| :=
        abs_sub_le _ _ _
      _ ≤
          |(∫ s in (0 : ℝ)..T, gq s) -
            ∫ s in (0 : ℝ)..T, gzα s| +
          (|(∫ s in (0 : ℝ)..T, gzα s) -
            HGAS.Dynamics.orbitIntegral
              gammaTwoHorocycleFlow f.toBCF (α T) z| +
          |HGAS.Dynamics.orbitIntegral
              gammaTwoHorocycleFlow f.toBCF (α T) z -
            HGAS.Dynamics.orbitIntegral
              gammaTwoHorocycleFlow f.toBCF T y|) := by
        gcongr
        exact abs_sub_le _ _ _
      _ ≤
          |(∫ s in (0 : ℝ)..T, gq s) -
            ∫ s in (0 : ℝ)..T, gzα s| +
          (|(∫ s in (0 : ℝ)..T, gzα s) -
            HGAS.Dynamics.orbitIntegral
              gammaTwoHorocycleFlow f.toBCF (α T) z| +
          (|HGAS.Dynamics.orbitIntegral
              gammaTwoHorocycleFlow f.toBCF (α T) z -
            HGAS.Dynamics.orbitIntegral
              gammaTwoHorocycleFlow f.toBCF T z| +
          |HGAS.Dynamics.orbitIntegral
              gammaTwoHorocycleFlow f.toBCF T z -
            HGAS.Dynamics.orbitIntegral
              gammaTwoHorocycleFlow f.toBCF T y|)) := by
        gcongr
        exact abs_sub_le _ _ _
  calc
    |(∫ s in (0 : ℝ)..T, gq s) -
        HGAS.Dynamics.orbitIntegral
          gammaTwoHorocycleFlow f.toBCF T y| ≤
        |(∫ s in (0 : ℝ)..T, gq s) -
          ∫ s in (0 : ℝ)..T, gzα s| +
        (|(∫ s in (0 : ℝ)..T, gzα s) -
          ∫ s in (0 : ℝ)..T, gzα s * D s| +
        (|HGAS.Dynamics.orbitIntegral
            gammaTwoHorocycleFlow f.toBCF (α T) z -
          HGAS.Dynamics.orbitIntegral
            gammaTwoHorocycleFlow f.toBCF T z| +
        |HGAS.Dynamics.orbitIntegral
            gammaTwoHorocycleFlow f.toBCF T z -
          HGAS.Dynamics.orbitIntegral
            gammaTwoHorocycleFlow f.toBCF T y|)) :=
      htotal
    _ ≤ ρ * T + (‖f‖ * ρ * T +
        (‖f‖ * ρ * T + 2 * ‖f‖ * ρ * T)) :=
      add_le_add hfirst
        (add_le_add hsecond
          (add_le_add hthird hfourth))
    _ = ρ * T * (1 + 4 * ‖f‖) := by ring

/-- Integer-average form of
`exists_delta_orbitIntegral_shear_box_close`.  This is the interface used
by the good-return-time theorem. -/
theorem exists_delta_integerOrbitAverage_shear_box_close
    (f : C₀(GammaTwoFrameQuotient, ℝ))
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧
      ∀ (N : ℕ) (r t h : ℝ)
        (q : GammaTwoFrameQuotient),
        0 < N →
        |r| < δ / (N : ℝ) →
        |t| < δ →
        |h| < ρ * (N : ℝ) →
        |HGAS.Dynamics.integerOrbitAverageObservable
            gammaTwoHorocycleFlow f.toBCF N q -
          HGAS.Dynamics.integerOrbitAverageObservable
            gammaTwoHorocycleFlow f.toBCF N
              (gammaTwoFrameRightMul
                  (lowerUnipotent r * geodesicFrame t *
                  upperUnipotent h) q)| ≤
          ρ * (1 + 4 * ‖f‖) := by
  obtain ⟨δ, hδ, hδhalf, hδclose⟩ :=
    exists_delta_orbitIntegral_shear_box_close f hρ
  refine ⟨δ, hδ, hδhalf, ?_⟩
  intro N r t h q hN hr ht hh
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hraw :=
    hδclose (N : ℝ) r t h q
      (by exact_mod_cast hN) hr ht hh
  rw [HGAS.Dynamics.integerOrbitAverageObservable_apply,
    HGAS.Dynamics.integerOrbitAverageObservable_apply,
    ← mul_sub]
  rw [abs_mul, abs_of_pos (inv_pos.mpr hNR)]
  calc
    (N : ℝ)⁻¹ *
        |HGAS.Dynamics.orbitIntegral
            gammaTwoHorocycleFlow f.toBCF (N : ℝ) q -
          HGAS.Dynamics.orbitIntegral
            gammaTwoHorocycleFlow f.toBCF (N : ℝ)
              (gammaTwoFrameRightMul
                (lowerUnipotent r * geodesicFrame t *
                  upperUnipotent h) q)| ≤
        (N : ℝ)⁻¹ *
          (ρ * (N : ℝ) * (1 + 4 * ‖f‖)) :=
      mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hNR.le)
    _ = ρ * (1 + 4 * ‖f‖) := by
      field_simp

end

end HGAS.Modular
