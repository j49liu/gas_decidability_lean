import HGAS.Dynamics.PointwiseErgodic
import HGAS.Modular.FlowGenericPointMeanErgodic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Pointwise ergodic theorem for bounded continuous observables of real flows

This module upgrades the continuous-time mean-ergodic theorem in
`FlowGenericPointMeanErgodic` from `L²` convergence to almost-everywhere
convergence of the full sequence of positive integer orbit averages.

The proof uses the reusable maximal-ergodic and Banach-principle
infrastructure from `PointwiseErgodic`.  The one-unit block observable
turns a continuous real flow into an ordinary discrete Birkhoff problem,
while a boundary estimate in the mean-ergodic module ensures that the
`L²` limit is the space mean even when the time-one map is not ergodic.
-/

open Filter Function MeasureTheory Set Topology
open scoped BoundedContinuousFunction

noncomputable section

namespace HGAS.Dynamics

variable {X : Type*}
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

/-- On a probability space, the `L¹` norm of a bounded continuous
function is at most its `L²` norm. -/
theorem InvariantProbabilityMeasure.integral_abs_le_norm_boundedContinuousToL2
    {ϕ : Flow ℝ X}
    (μ : InvariantProbabilityMeasure ϕ)
    (f : X →ᵇ ℝ) :
    (∫ x, |f x| ∂(μ.measure : Measure X)) ≤
      ‖μ.boundedContinuousToL2 f‖ := by
  let ν : Measure X := (μ.measure : Measure X)
  have hf_meas : AEStronglyMeasurable (f : X → ℝ) ν :=
    f.continuous.aestronglyMeasurable
  have hf_mem2 : MemLp (f : X → ℝ) 2 ν :=
    (BoundedContinuousFunction.memLp_top f).mono_exponent (by norm_num)
  have hcompare :
      eLpNorm (f : X → ℝ) 1 ν ≤
        eLpNorm (f : X → ℝ) 2 ν :=
    eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) hf_meas
  calc
    (∫ x, |f x| ∂ν) =
        ENNReal.toReal (eLpNorm (f : X → ℝ) 1 ν) := by
      rw [eLpNorm_one_eq_lintegral_enorm]
      simpa only [Real.norm_eq_abs] using
        integral_norm_eq_lintegral_enorm hf_meas
    _ ≤ ENNReal.toReal (eLpNorm (f : X → ℝ) 2 ν) :=
      ENNReal.toReal_mono hf_mem2.eLpNorm_ne_top hcompare
    _ = ‖μ.boundedContinuousToL2 f‖ := by
      rw [Lp.norm_def]
      congr 1
      exact eLpNorm_congr_ae
        (μ.boundedContinuousToL2_coeFn f).symm

/-- A constant bounded continuous function represents the corresponding
constant `L²` vector. -/
theorem InvariantProbabilityMeasure.boundedContinuousToL2_const
    {ϕ : Flow ℝ X}
    (μ : InvariantProbabilityMeasure ϕ) (c : ℝ) :
    μ.boundedContinuousToL2
        (BoundedContinuousFunction.const X c) =
      Lp.const (2 : ENNReal) (μ.measure : Measure X) c := by
  apply Lp.ext
  exact (μ.boundedContinuousToL2_coeFn
    (BoundedContinuousFunction.const X c)).trans <| by
      simpa only [BoundedContinuousFunction.const_apply',
        Function.const_apply] using
        (Lp.coeFn_const (2 : ENNReal)
          (μ.measure : Measure X) c).symm

/-- The integer orbit average centered by the space mean. -/
def centeredIntegerOrbitAverageObservable
    {ϕ : Flow ℝ X}
    (μ : InvariantProbabilityMeasure ϕ)
    (f : X →ᵇ ℝ) (n : ℕ) : X →ᵇ ℝ :=
  integerOrbitAverageObservable ϕ f n -
    BoundedContinuousFunction.const X
      (∫ x, f x ∂(μ.measure : Measure X))

@[simp]
theorem centeredIntegerOrbitAverageObservable_apply
    {ϕ : Flow ℝ X}
    (μ : InvariantProbabilityMeasure ϕ)
    (f : X →ᵇ ℝ) (n : ℕ) (x : X) :
    centeredIntegerOrbitAverageObservable μ f n x =
      integerOrbitAverageObservable ϕ f n x -
        ∫ y, f y ∂(μ.measure : Measure X) :=
  rfl

/-- Mean-ergodic `L²` convergence, recentered at zero. -/
theorem IsErgodicInvariantProbability.tendsto_centeredIntegerAverage_L2
    {ϕ : Flow ℝ X}
    (μ : InvariantProbabilityMeasure ϕ)
    (hμ : IsErgodicInvariantProbability ϕ μ.measure)
    (f : X →ᵇ ℝ) :
    Tendsto
      (fun n : ℕ ↦
        μ.boundedContinuousToL2
          (centeredIntegerOrbitAverageObservable μ f (n + 1)))
      atTop (𝓝 0) := by
  let c : ℝ := ∫ x, f x ∂(μ.measure : Measure X)
  have hbase := hμ.tendsto_integerAverage_L2 μ f
  have hsub :=
    hbase.sub
      (tendsto_const_nhds :
        Tendsto
          (fun _ : ℕ ↦
            Lp.const (2 : ENNReal)
              (μ.measure : Measure X) c)
          atTop
          (𝓝 (Lp.const (2 : ENNReal)
            (μ.measure : Measure X) c)))
  simpa only [centeredIntegerOrbitAverageObservable, map_sub,
    μ.boundedContinuousToL2_const, c, sub_self] using hsub

/-- The centered integer averages converge to zero in `L¹`. -/
theorem IsErgodicInvariantProbability.tendsto_integral_abs_centeredIntegerAverage
    {ϕ : Flow ℝ X}
    (μ : InvariantProbabilityMeasure ϕ)
    (hμ : IsErgodicInvariantProbability ϕ μ.measure)
    (f : X →ᵇ ℝ) :
    Tendsto
      (fun n : ℕ ↦
        ∫ x,
          |centeredIntegerOrbitAverageObservable μ f (n + 1) x|
            ∂(μ.measure : Measure X))
      atTop (𝓝 0) := by
  have hL2 := hμ.tendsto_centeredIntegerAverage_L2 μ f
  have hnorm :
      Tendsto
        (fun n : ℕ ↦
          ‖μ.boundedContinuousToL2
            (centeredIntegerOrbitAverageObservable μ f (n + 1))‖)
        atTop (𝓝 0) := by
    simpa only [norm_zero] using hL2.norm
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦
      integral_nonneg fun _ ↦ abs_nonneg _
  · exact Eventually.of_forall fun n ↦
      μ.integral_abs_le_norm_boundedContinuousToL2
        (centeredIntegerOrbitAverageObservable μ f (n + 1))
  · exact hnorm

/-- The one-unit block observable centered by the space mean. -/
def centeredUnitBlockObservable
    {ϕ : Flow ℝ X}
    (μ : InvariantProbabilityMeasure ϕ)
    (f : X →ᵇ ℝ) : X →ᵇ ℝ :=
  unitBlockObservable ϕ f -
    BoundedContinuousFunction.const X
      (∫ x, f x ∂(μ.measure : Measure X))

@[simp]
theorem centeredUnitBlockObservable_apply
    {ϕ : Flow ℝ X}
    (μ : InvariantProbabilityMeasure ϕ)
    (f : X →ᵇ ℝ) (x : X) :
    centeredUnitBlockObservable μ f x =
      unitBlockObservable ϕ f x -
        ∫ y, f y ∂(μ.measure : Measure X) :=
  rfl

omit [MeasurableSpace X] [BorelSpace X] in
/-- Ordinary time-one Birkhoff averages of the block observable are the
integer continuous-time orbit averages. -/
theorem birkhoffAverage_unitBlockObservable_eq_integerOrbitAverage
    (ϕ : Flow ℝ X) (f : X →ᵇ ℝ) (n : ℕ) (x : X) :
    birkhoffAverage ℝ (ϕ 1) (unitBlockObservable ϕ f) n x =
      integerOrbitAverageObservable ϕ f n x := by
  rw [integerOrbitAverageObservable_apply,
    orbitIntegral_nat_average_eq_birkhoffAverage]

/-- For positive lengths, centering commutes with the block Birkhoff
average. -/
theorem birkhoffAverage_centeredUnitBlockObservable_eq
    {ϕ : Flow ℝ X}
    (μ : InvariantProbabilityMeasure ϕ)
    (f : X →ᵇ ℝ) {n : ℕ} (hn : 0 < n) (x : X) :
    birkhoffAverage ℝ (ϕ 1)
        (centeredUnitBlockObservable μ f) n x =
      centeredIntegerOrbitAverageObservable μ f n x := by
  let c : ℝ := ∫ y, f y ∂(μ.measure : Measure X)
  change birkhoffAverage ℝ (ϕ 1)
      (unitBlockObservable ϕ f -
        BoundedContinuousFunction.const X c) n x =
    integerOrbitAverageObservable ϕ f n x - c
  change birkhoffAverage ℝ (ϕ 1)
      ((unitBlockObservable ϕ f : X → ℝ) -
        Function.const X c) n x =
    integerOrbitAverageObservable ϕ f n x - c
  rw [birkhoffAverage_sub]
  change birkhoffAverage ℝ (ϕ 1)
      (unitBlockObservable ϕ f) n x -
        birkhoffAverage ℝ (ϕ 1) (Function.const X c) n x =
    integerOrbitAverageObservable ϕ f n x - c
  rw [birkhoffAverage_unitBlockObservable_eq_integerOrbitAverage]
  congr 1
  simp [birkhoffAverage, birkhoffSum, Nat.ne_of_gt hn]

/-- The centered block averages converge to zero in `L¹`. -/
theorem IsErgodicInvariantProbability.tendsto_integral_abs_centeredUnitBlockAverage
    {ϕ : Flow ℝ X}
    (μ : InvariantProbabilityMeasure ϕ)
    (hμ : IsErgodicInvariantProbability ϕ μ.measure)
    (f : X →ᵇ ℝ) :
    Tendsto
      (fun n : ℕ ↦
        ∫ x,
          |birkhoffAverage ℝ (ϕ 1)
            (centeredUnitBlockObservable μ f) (n + 1) x|
            ∂(μ.measure : Measure X))
      atTop (𝓝 0) := by
  have h :=
    hμ.tendsto_integral_abs_centeredIntegerAverage μ f
  convert h using 1
  funext n
  apply integral_congr_ae
  exact Eventually.of_forall fun x ↦ by
    change
      |birkhoffAverage ℝ (ϕ 1)
        (centeredUnitBlockObservable μ f) (n + 1) x| =
      |centeredIntegerOrbitAverageObservable μ f (n + 1) x|
    rw [birkhoffAverage_centeredUnitBlockObservable_eq
      μ f (Nat.succ_pos n) x]

/-- **Pointwise ergodic theorem for bounded continuous observables of
an ergodic real flow, at positive integer times.**

Unlike the earlier subsequence theorem, the entire sequence of positive
integer orbit averages converges almost everywhere. -/
theorem IsErgodicInvariantProbability.ae_tendsto_integerOrbitAverage
    {ϕ : Flow ℝ X}
    (μ : InvariantProbabilityMeasure ϕ)
    (hμ : IsErgodicInvariantProbability ϕ μ.measure)
    (f : X →ᵇ ℝ) :
    ∀ᵐ x ∂(μ.measure : Measure X),
      Tendsto
        (fun n : ℕ ↦
          integerOrbitAverageObservable ϕ f (n + 1) x)
        atTop
        (𝓝 (∫ y, f y ∂(μ.measure : Measure X))) := by
  let g : X →ᵇ ℝ := centeredUnitBlockObservable μ f
  have hg_meas : Measurable (g : X → ℝ) :=
    g.continuous.measurable
  have hg_int : Integrable (g : X → ℝ)
      (μ.measure : Measure X) :=
    Integrable.of_bound hg_meas.aestronglyMeasurable ‖g‖
      (Eventually.of_forall fun x ↦ by
        simpa only [Real.norm_eq_abs] using g.norm_coe_le_norm x)
  have hg_point :=
    ae_tendsto_birkhoffAverage_zero_of_tendsto_integral_abs
      (μ.measurePreservingTime 1)
      hg_meas hg_int (norm_nonneg g)
      (fun x ↦ by
        simpa only [Real.norm_eq_abs] using g.norm_coe_le_norm x)
      (by
        simpa only [g] using
          hμ.tendsto_integral_abs_centeredUnitBlockAverage μ f)
  filter_upwards [hg_point] with x hx
  have hshift :=
    hx.comp (tendsto_add_atTop_nat 1)
  have hcenter :
      Tendsto
        (fun n : ℕ ↦
          centeredIntegerOrbitAverageObservable μ f (n + 1) x)
        atTop (𝓝 0) := by
    exact hshift.congr
      (fun n ↦ birkhoffAverage_centeredUnitBlockObservable_eq
        μ f (Nat.succ_pos n) x)
  have hadd :=
    hcenter.add_const
      (∫ y, f y ∂(μ.measure : Measure X))
  simpa only [centeredIntegerOrbitAverageObservable_apply,
    sub_add_cancel, zero_add] using hadd

end HGAS.Dynamics
