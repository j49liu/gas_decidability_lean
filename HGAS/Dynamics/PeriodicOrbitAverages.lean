import HGAS.Dynamics.PeriodicOrbitMeasure
import HGAS.Modular.FlowGenericPointMeanErgodic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Time averages on a periodic orbit

This file proves the elementary counterpart to nonperiodic-orbit
equidistribution.  If a continuous real flow returns a point after a
positive time `T`, then every bounded continuous observable has a forward
time average at that point, and the limit is integration against the
canonical normalized probability on the periodic orbit.

The analytic core is reusable: the primitive of a continuous periodic
function after subtracting its mean is itself periodic, hence bounded.
Dividing that bounded primitive by the elapsed time gives the result.
-/

namespace HGAS.Dynamics

open Filter Function _root_.MeasureTheory Set Topology
open scoped BoundedContinuousFunction

noncomputable section

/-- Cesàro averages of a continuous periodic real function along the
positive integers converge to its mean over one positive period. -/
theorem tendsto_nat_average_intervalIntegral
    {g : ℝ → ℝ} {T : ℝ}
    (hg : Periodic g T) (hT : 0 < T)
    (hcontinuous : Continuous g) :
    Tendsto
      (fun n : ℕ ↦
        ((n + 1 : ℕ) : ℝ)⁻¹ *
          ∫ t in (0 : ℝ)..(n + 1 : ℕ), g t)
      atTop
      (𝓝 (T⁻¹ * ∫ t in (0 : ℝ)..T, g t)) := by
  let m : ℝ := T⁻¹ * ∫ t in (0 : ℝ)..T, g t
  let h : ℝ → ℝ := fun t ↦ g t - m
  let H : ℝ → ℝ := fun t ↦ ∫ u in (0 : ℝ)..t, h u
  have hh : Periodic h T := by
    intro t
    simp only [h]
    rw [hg]
  have hhc : Continuous h :=
    hcontinuous.sub continuous_const
  have hhInt :
      ∀ a b : ℝ, IntervalIntegrable h volume a b :=
    fun a b ↦ hhc.intervalIntegrable a b
  have hmean : (∫ t in (0 : ℝ)..T, h t) = 0 := by
    rw [intervalIntegral.integral_sub
      (hcontinuous.intervalIntegrable 0 T)
      (continuous_const.intervalIntegrable 0 T)]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    dsimp only [m]
    field_simp
    ring
  have hHperiodic : Periodic H T := by
    intro t
    dsimp only [H]
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hhInt 0 t) (hhInt t (t + T))]
    rw [hh.intervalIntegral_add_eq t 0]
    simp only [zero_add, hmean, add_zero]
  have hHcontinuous : Continuous H :=
    intervalIntegral.continuous_primitive hhInt 0
  obtain ⟨C, hC⟩ :=
    isBounded_iff_forall_norm_le.mp
      (hHperiodic.isBounded_of_continuous
        hT.ne' hHcontinuous)
  have hCnonneg : 0 ≤ C := by
    exact (norm_nonneg (H 0)).trans
      (hC (H 0) ⟨0, rfl⟩)
  have hinv :
      Tendsto
        (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹)
        atTop (𝓝 0) := by
    simpa only [Function.comp_apply] using
      ((tendsto_inv_atTop_nhds_zero_nat
        (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1))
  have hcentered :
      Tendsto
        (fun n : ℕ ↦
          ((n + 1 : ℕ) : ℝ)⁻¹ * H (n + 1 : ℕ))
        atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    refine squeeze_zero'
      (g := fun n : ℕ ↦
        ((n + 1 : ℕ) : ℝ)⁻¹ * C) ?_ ?_ ?_
    · exact Eventually.of_forall fun _ ↦ norm_nonneg _
    · exact Eventually.of_forall fun n ↦ by
        rw [Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (inv_nonneg.mpr (by positivity))]
        exact mul_le_mul_of_nonneg_left
          (hC (H (n + 1 : ℕ)) ⟨(n + 1 : ℕ), rfl⟩)
          (by positivity)
    · simpa only [zero_mul] using hinv.mul_const C
  have hsplit :
      ∀ n : ℕ,
        ((n + 1 : ℕ) : ℝ)⁻¹ *
            ∫ t in (0 : ℝ)..(n + 1 : ℕ), g t =
          m +
            ((n + 1 : ℕ) : ℝ)⁻¹ *
              H (n + 1 : ℕ) := by
    intro n
    have hN : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    have hsub :
        (∫ t in (0 : ℝ)..(n + 1 : ℕ), h t) =
          (∫ t in (0 : ℝ)..(n + 1 : ℕ), g t) -
            ((n + 1 : ℕ) : ℝ) * m := by
      rw [intervalIntegral.integral_sub
        (hcontinuous.intervalIntegrable 0 (n + 1 : ℕ))
        (continuous_const.intervalIntegrable 0 (n + 1 : ℕ))]
      simp only [intervalIntegral.integral_const, sub_zero,
        smul_eq_mul]
    dsimp only [H]
    rw [hsub]
    field_simp
    ring
  have hlimit :
      Tendsto
        (fun n : ℕ ↦
          m +
            ((n + 1 : ℕ) : ℝ)⁻¹ *
              H (n + 1 : ℕ))
        atTop (𝓝 (m + 0)) :=
    tendsto_const_nhds.add hcentered
  simpa only [hsplit, add_zero, m] using hlimit

variable {X : Type*}
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A periodic point is generic, along positive integer time lengths,
for its canonical normalized periodic-orbit probability. -/
theorem tendsto_integerOrbitAverage_of_periodic
    (ϕ : Flow ℝ X) (f : X →ᵇ ℝ) (x : X)
    {T : ℝ} (hT : 0 < T)
    (hperiod : ϕ T x = x) :
    Tendsto
      (fun n : ℕ ↦
        integerOrbitAverageObservable ϕ f (n + 1) x)
      atTop
      (𝓝 (∫ y, f y
        ∂((periodicOrbitInvariantProbability
          ϕ x hT hperiod).measure : Measure X))) := by
  let g : ℝ → ℝ := fun t ↦ f (ϕ t x)
  have hg : Function.Periodic g T := by
    intro t
    dsimp only [g]
    rw [ϕ.map_add, hperiod]
  have hgc : Continuous g :=
    f.continuous.comp
      (ϕ.continuous continuous_id continuous_const)
  have havg :=
    tendsto_nat_average_intervalIntegral hg hT hgc
  have hcanonical :
      (∫ y, f y
          ∂((periodicOrbitInvariantProbability
            ϕ x hT hperiod).measure : Measure X)) =
        T⁻¹ * orbitIntegral ϕ f T x := by
    rw [integral_periodicOrbitInvariantProbability]
    change
      (∫ θ : UnitAddCircle,
          f (periodicOrbitMap ϕ x T hperiod θ)
            ∂AddCircle.haarAddCircle) =
        T⁻¹ * orbitIntegral ϕ f T x
    rw [AddCircle.integral_haarAddCircle]
    simp only [inv_one, one_smul]
    rw [← UnitAddCircle.intervalIntegral_preimage 0]
    simp only [zero_add, periodicOrbitMap_coe]
    change
      (∫ r in (0 : ℝ)..1, g (T * r)) =
        T⁻¹ * orbitIntegral ϕ f T x
    rw [intervalIntegral.integral_comp_mul_left g hT.ne']
    simp only [mul_zero, mul_one, smul_eq_mul, orbitIntegral, g]
  rw [hcanonical]
  simpa only [integerOrbitAverageObservable_apply,
    orbitIntegral, g] using havg

end

end HGAS.Dynamics
